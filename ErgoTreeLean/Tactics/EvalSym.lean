/-
`eval_sym`: symbolic execution of a concrete ErgoTree inside a proof.

Given hypotheses of the form `eval c ctx env e = .ok v` or
`EvalHolds c ctx env signers e` about a *concrete* `e` (typically a whole
contract tree, after `unfold`ing its definition), `eval_sym` rewrites them with
the `eval_inv` rules (`Lemmas/EvalInv.lean`, `Lemmas/EvalHolds.lean`,
`Lemmas/Decode.lean`), which replace a node's success by facts about its
children with every runtime pattern match resolved, until what remains are
facts about the context (`ctx.outputs[0]? = some out`,
`out.register 5 = some (.vColl τ vs)`, `vs.length = 2`, plain `Int` equations
and bounds, …), `∀`-statements for collection loops, and disjunctions for `||`.

## The engine

`eval_sym` is a loop over the hypotheses, run until nothing changes:

1. split every `∧`/`∃` hypothesis into separate hypotheses;
2. substitute every equation that defines a variable;
3. merge two hypotheses `e = some a`, `e = some b` into `a = b`;
4. `simp` with the `eval_inv` rules, but only the hypotheses whose statement is
   new. A statement `simp` has already normalized, or a part of one, is never
   simplified again (unless a new rule can rewrite it), so the cost of a round
   is proportional to what changed;
5. when nothing else applies, split the goal on an `if` whose condition is
   undecided (a disjunction with a `Later` branch) and keep the branch
   condition as a rewrite rule for the rest of that branch, so every later
   `if` on the same condition loses its dead arm without being examined;
6. otherwise release the facts marked `Later` (`Lemmas/EvalInv.lean`). `simp`
   stops at a `Later`, so a block runs one definition at a time and every
   continuation is simplified once, with the definitions before it (and the
   branch taken by any `if` among them) already decoded.

Loop facts (`forallHelper … = .ok b` and the other `*Helper`s, and any
`∀`-statement about `eval`, such as the pointwise fact `mapHelper_getElem?`
gives) carry a whole loop body and are left alone unless an extra lemma about a
loop helper is given (`eval_sym [forallHelper_true_iff]` expands `forall` loops
under their binders; `Later`s under a binder are released by re-simplifying
that hypothesis). To execute one iteration, instantiate the loop fact at an
element first and run `eval_sym` on the resulting `eval … = .ok r`: under a
binder no `if` can be split, so a body executed there is re-simplified whole on
every round.

The goal is not changed while the engine runs: the derived facts live in a
local context of the engine's own, each with its proof term, and the proof is
assembled once at the end (see "The proof under construction" below).

`eval_simp` is one plain `simp` round with every `Later` released at once, for
use on a goal or under binders.
-/
import ErgoTreeLean.Lemmas.EvalHolds
import ErgoTreeLean.Lemmas.Decode
import ErgoTreeLean.Lemmas.Loops

namespace ErgoTreeLean

attribute [eval_inv] Value.vColl.injEq Value.vBox.injEq Value.vInt.injEq Value.vLong.injEq Value.vBool.injEq
  Value.vOption.injEq Value.vSigmaProp.injEq Value.vTuple.injEq Value.vGroupElement.injEq Value.vByte.injEq
  Value.vShort.injEq Value.vBigInt.injEq SigmaBoolean.trivial.injEq SigmaBoolean.proveDlog.injEq
  Option.some.injEq Prod.mk.injEq List.cons.injEq reduceCtorEq
  exists_eq_left exists_eq_right exists_eq_left' exists_eq_right' exists_and_left exists_and_right
  exists_exists_and_eq_and exists_exists_eq_and exists_eq_right_right exists_eq_right_right'
  and_assoc exists_const and_true true_and and_false false_and or_false false_or not_false_eq_true not_true_eq_false
  eq_self_iff_true ne_eq
  List.forall_mem_cons List.not_mem_nil false_implies implies_true forall_const
  List.getElem?_map Option.map_eq_some_iff List.getElem?_cons_zero List.getElem?_cons_succ List.getElem?_nil
  List.forall_mem_map List.mem_range List.length_map List.length_range List.length_cons List.length_nil
  Option.isSome_some Option.isSome_none
  if_true if_false Int.toNat_zero Int.toNat_natCast
  Bool.true_eq_false Bool.false_eq_true beq_iff_eq beq_self_eq_true
  Value.beq_vInt Value.beq_vLong Value.beq_vShort Value.beq_vByte Value.beq_vBigInt Value.beq_vBool
  Value.beq_vGroupElement bytesToVColl_beq_true typeOf SType.beq
  Bool.and_eq_true Bool.not_eq_true' Bool.not_eq_false' Bool.not_true Bool.not_false
  beq_eq_false_iff_ne Int.natCast_inj Int.ofNat_inj

/-- `simp` stops at a `Later` (see `Lemmas/EvalInv.lean`); `eval_sym` releases it. -/
simproc_decl laterStop (Later _) := fun e => return .done { expr := e }

/-- One round of `eval_inv` rewriting (plus the numeral/`if` simprocs it
    needs), with every `Later` released. -/
syntax (name := evalSimp) "eval_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| eval_simp $[$loc]?) =>
    `(tactic| simp only [eval_inv, later_iff, reduceIte, Nat.reduceEqDiff, Nat.reduceSub, Nat.reduceAdd,
        Int.reduceLE, Int.reduceLT, Nat.reduceLeDiff, Int.reduceEq, Int.reduceNe, Int.reduceAdd, Int.reduceSub,
        Int.reduceMul, Int.reduceNeg, Int.reducePow, Int.reduceToNat, decide_eq_true_eq, Int.natCast_nonneg]
        $[$loc]?)

/-- Loop helpers whose success facts `eval_sym` leaves alone. -/
def loopHelpers : List Lean.Name :=
  [``forallHelper, ``existsHelper, ``mapHelper, ``filterHelper, ``foldHelper]

end ErgoTreeLean

/-! The engine (in its own namespace: `ErgoTreeLean.Expr` would shadow `Lean.Expr`). -/
namespace ErgoTreeLeanEvalSym

open Lean Elab Tactic Meta

initialize registerTraceClass `eval_sym

/-- Per-branch engine state. -/
structure State where
  /-- Statements already in `simp` normal form under the current rules. -/
  done : Std.HashSet Expr := {}
  /-- Hypotheses used as rewrite rules, by user name (the engine replaces the
      free variables of rewritten hypotheses, not their names): branch
      conditions, local facts given as extra lemmas, and variable definitions
      `x = t` (flag: stated as `t = x`). -/
  rules : Array (Name × Bool) := #[]
  /-- Variables defined by a rule. -/
  defined : Std.HashSet FVarId := {}
  /-- The definitions: rule name and variable. -/
  defs : Array (Name × FVarId) := #[]

/-- Engine configuration. -/
structure Cfg where
  ctx : Simp.Context
  simprocs : Simp.SimprocsArray
  /-- Also simplify loop facts. -/
  loops : Bool
  /-- The locals of the goal `eval_sym` started on. -/
  root : Std.HashSet FVarId
  /-- The goal is a proposition (only then are `∃`s and `∨`s eliminated). -/
  propTarget : Bool

/-- A loop fact: a loop helper's success (`forallHelper … = .ok b` and the
    other `*Helper`s), or a `∀`-statement about `eval` (a loop body under its
    binder, e.g. the pointwise statement `mapHelper_getElem?` gives). Both are
    only simplified when a loop lemma is given: under a binder no `if` can be
    split, so executing a body there repeats the whole block on every round. -/
def isLoopFact (t : Expr) : Bool :=
  match t.eq? with
  | some (_, lhs, _) => ErgoTreeLean.loopHelpers.any (lhs.isAppOf ·)
  | none => t.isForall && (t.find? (·.isAppOf ``ErgoTreeLean.eval)).isSome

def containsLater (t : Expr) : Bool := (t.find? (·.isAppOf ``ErgoTreeLean.Later)).isSome

/-- Replace every `Later p` in `t` by `p` (a definitional unfolding). -/
partial def releaseAll (t : Expr) : Expr :=
  t.replace fun e => if e.isAppOfArity ``ErgoTreeLean.Later 1 then some (releaseAll e.appArg!) else none

/-! ## The proof under construction

The engine never changes the goal while it runs. It extends a local context
with the facts it derives (a `Tele`), recording how each new local is proved;
hypotheses the engine has rewritten are dropped from that context but stay in
the record. When the run ends, the remaining goal is created once, and the
proof is assembled in one pass: `(fun h => …) pf` for a fact,
`Exists.elim pf (fun w hw => …)` for an existential. A split on an `if` ends
the telescope with an `Or.elim` whose two branches are telescopes of their own.

Changing the goal every round instead (as `intro`/`clear` do) makes every round
a delayed assignment, and instantiating a chain of those at the end is
quadratic in the number of rounds. -/

/-- How a local of the telescope is proved: a fact `x : ty` by `val` (a term
    in the earlier locals), an existential's witness `w : α` and property
    `hw : ty` (`ty = p w`) by `Exists.elim pf`. -/
inductive Entry where
  | fact (x : FVarId) (n : Name) (ty val : Expr)
  | witness (w : FVarId) (wn : Name) (hw : FVarId) (hwn : Name) (u : Level) (α p pf ty : Expr)

/-- The locals introduced since the telescope started; `lctx` is the working
    context, without the hypotheses the engine has dropped. -/
structure Tele where
  lctx : LocalContext
  entries : Array Entry := #[]

def Tele.add (t : Tele) (n : Name) (ty val : Expr) : MetaM (Tele × Expr) := do
  let fv ← mkFreshFVarId
  return ({ t with lctx := t.lctx.mkLocalDecl fv n ty, entries := t.entries.push (.fact fv n ty val) }, .fvar fv)

def Tele.hide (t : Tele) (fvs : Array FVarId) : Tele :=
  { t with lctx := fvs.foldl (·.erase ·) t.lctx }

/-- Run `k` in the telescope's working context. -/
def Tele.run (t : Tele) (k : MetaM α) : MetaM α := do
  withLCtx t.lctx (← getLocalInstances) k

/-- The proof of `target` from `body`, a term in the telescope's context: the
    facts' proofs are substituted for them (as instantiating a chain of goals
    would), and every witness is bound by an `Exists.elim`. The witnesses are
    abstracted in one pass over the term (each subterm once per binder depth
    it occurs at), so the cost is linear in the size of the proof, not
    quadratic in the number of locals. -/
def Tele.close (t : Tele) (target body : Expr) : Expr := Id.run do
  -- Substitute the facts; the binder level of each witness.
  let mut m : Std.HashMap FVarId Expr := {}
  let mut lvl : Std.HashMap FVarId Nat := {}
  let mut ws := #[]
  let mut n := 0
  let subst (m : Std.HashMap FVarId Expr) (e : Expr) : Expr :=
    if m.isEmpty then e else
    e.replace fun x => if !x.hasFVar then some x else if x.isFVar then m[x.fvarId!]? else none
  for e in t.entries do
    match e with
    | .fact x _ _ val => m := m.insert x (subst m val)
    | .witness w wn hw hwn u α p pf ty =>
      lvl := (lvl.insert w n).insert hw (n + 1); n := n + 2
      ws := ws.push (wn, hwn, u, subst m α, subst m p, subst m pf, subst m ty)
  let body := subst m body
  let rec go (e : Expr) (d : Nat) : StateM (Std.HashMap (Expr × Nat) Expr) Expr := do
    if !e.hasFVar then return e
    if let some r := (← get)[(e, d)]? then return r
    let r ← match e with
      | .fvar f => pure (match lvl[f]? with | some l => .bvar (d - 1 - l) | none => e)
      | .app f a => pure <| e.updateApp! (← go f d) (← go a d)
      | .lam _ t b _ => pure <| e.updateLambdaE! (← go t d) (← go b (d + 1))
      | .forallE _ t b _ => pure <| e.updateForallE! (← go t d) (← go b (d + 1))
      | .letE _ t v b nd => pure <| e.updateLet! (← go t d) (← go v d) (← go b (d + 1)) nd
      | .mdata _ b => pure <| e.updateMData! (← go b d)
      | .proj _ _ b => pure <| e.updateProj! (← go b d)
      | _ => pure e
    modify (·.insert (e, d) r)
    return r
  let build : StateM (Std.HashMap (Expr × Nat) Expr) Expr := do
    let mut acc ← go body n
    let mut d := n
    for (wn, hwn, u, α, p, pf, ty) in ws.reverse do
      d := d - 2
      let α' ← go α d
      let body := Expr.lam wn α' (.lam hwn (← go ty (d + 1)) acc .default) .default
      acc := mkApp5 (mkConst ``Exists.elim [u]) α' (← go p d) target (← go pf d) body
    return acc
  return build.run' {}

/-- A new fact: its proof, its statement, whether the statement is known to be
    in normal form, and the user name to keep (a rewritten hypothesis keeps its
    name, which rules are looked up by). -/
abbrev Fact := Expr × Expr × Bool × Option Name

/-- Add the fact `pf : ty`, split into its `∧`/`∃` leaves. -/
partial def decompose (propTarget : Bool) (t : Tele) (st : State) (pf ty : Expr) (isDone : Bool) (name? : Option Name) :
    MetaM (Tele × State) := do
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    let (t, st) ← decompose propTarget t st (mkApp3 (mkConst ``And.left) a b pf) a isDone none
    decompose propTarget t st (mkApp3 (mkConst ``And.right) a b pf) b isDone none
  else if propTarget && ty.isAppOfArity ``Exists 2 then
    let α := ty.appFn!.appArg!
    let p := ty.appArg!
    let u ← t.run (getLevel α)
    let n := match p with | .lam n .. => n | _ => `w
    let w ← mkFreshFVarId
    let hw ← mkFreshFVarId
    let wn ← mkFreshUserName n
    let hwn ← mkFreshUserName `h
    let hty := p.beta #[.fvar w]
    let t := { t with
      lctx := (t.lctx.mkLocalDecl w wn α).mkLocalDecl hw hwn hty
      entries := t.entries.push (.witness w wn hw hwn u α p pf hty) }
    if hty.isAppOfArity ``And 2 || hty.isAppOfArity ``Exists 2 then
      let (t, st) ← decompose propTarget t st (.fvar hw) hty isDone none
      return (t.hide #[hw], st)
    return (t, if isDone then { st with done := st.done.insert hty } else st)
  else
    let (t, _) ← t.add (← name?.getDM (mkFreshUserName `h)) ty pf
    return (t, if isDone then { st with done := st.done.insert ty } else st)

/-- Register new variable definitions `x = t` / `t = x` (`x` a local, not in
    `t`) as rewrite rules. Rules stay acyclic: `t` must not mention a defined
    variable (it will, after rewriting, in a later round). Of two variables,
    an engine-introduced one is defined in terms of a user-named one, so a
    name the user gives with `obtain ⟨out, hout⟩ : ∃ out, … := ⟨_, ‹_›⟩`
    replaces the anonymous variable everywhere on the next `eval_sym`. -/
def addDefinitions (t : Tele) (st : State) : MetaM State := t.run do
  let lctx := t.lctx
  let mut st := st
  let ruleNames : Std.HashSet Name := st.rules.foldl (·.insert ·.1) {}
  for d in lctx do
    if d.isImplementationDetail then continue
    if ruleNames.contains d.userName then continue
    let ty ← instantiateMVars d.type
    let some (_, a, b) := ty.eq? | continue
    let isVar (e : Expr) : Bool :=
      e.isFVar && !(lctx.get! e.fvarId!).isLet && !st.defined.contains e.fvarId!
    let mentionsDefined (e : Expr) : Bool := e.hasAnyFVar (st.defined.contains ·)
    -- Of two variables, prefer to eliminate one the engine introduced
    -- (inaccessible name), then the one declared later.
    let later (x y : Expr) : Bool :=
      let dx := lctx.get! x.fvarId!
      let dy := lctx.get! y.fvarId!
      (dx.userName.hasMacroScopes && !dy.userName.hasMacroScopes) ||
        (dx.userName.hasMacroScopes == dy.userName.hasMacroScopes && dx.index > dy.index)
    let pick : Option (FVarId × Bool) :=
      if isVar a && isVar b then
        if later a b then some (a.fvarId!, false) else some (b.fvarId!, true)
      else if isVar a && !b.containsFVar a.fvarId! && !mentionsDefined b then some (a.fvarId!, false)
      else if isVar b && !a.containsFVar b.fvarId! && !mentionsDefined a then some (b.fvarId!, true)
      else none
    let some (x, flip) := pick | continue
    st := { st with
      rules := st.rules.push (d.userName, flip)
      defined := st.defined.insert x
      defs := st.defs.push (d.userName, x)
      done := st.done.filter fun e => !e.containsFVar x }
  return st

/-- One round's changes: every hypothesis whose statement is not in normal
    form is simplified (with the rules as extra rewrite rules), every `∧`/`∃`
    hypothesis is split, a second copy of a proposition is dropped, and of two
    hypotheses `e = some a`, `e = some b` (e.g. a register read twice) the
    second becomes `some a = some b`. Returns the new facts and the hypotheses
    they replace, or `.inl pf` if a hypothesis became `False` (`pf` proves the
    target). -/
def collect (cfg : Cfg) (target : Expr) (t : Tele) (st : State) :
    MetaM (Expr ⊕ (Array Fact × Array FVarId × State)) := t.run do
  let mut ctx := cfg.ctx
  for (n, flip) in st.rules do
    if let some d := t.lctx.findFromUserName? n then
      let pf ← if flip then mkEqSymm d.toExpr else pure d.toExpr
      ctx := ctx.setSimpTheorems (← ctx.simpTheorems.addTheorem (.fvar d.fvarId) pf)
  let mut st := st
  let mut facts : Array Fact := #[]
  let mut drop := #[]
  let mut types : Std.HashSet Expr := {}
  let mut seen : Std.HashMap Expr (Expr × Expr) := {}
  let ruleNames : Std.HashSet Name := st.rules.foldl (·.insert ·.1) {}
  for d in t.lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let isRule := ruleNames.contains d.userName
    if types.contains ty && !isRule then drop := drop.push d.fvarId; continue
    types := types.insert ty
    if ty.isAppOfArity ``And 2 || (cfg.propTarget && ty.isAppOfArity ``Exists 2) then
      facts := facts.push (d.toExpr, ty, st.done.contains ty, none)
      drop := drop.push d.fvarId
      continue
    if !st.done.contains ty && (cfg.loops || !isLoopFact ty) then
      let ctx' := ctx.setSimpTheorems (ctx.simpTheorems.eraseTheorem (.fvar d.fvarId))
      let t0 ← IO.monoMsNow
      let (r, _) ← simp ty ctx' cfg.simprocs none
      let dt := (← IO.monoMsNow) - t0
      trace[eval_sym] "simp {dt}ms: {ty.approxDepth} {if r.expr == ty then "(normal)" else ""}"
      if r.expr.isFalse then
        let pf ← match r.proof? with
          | some p => mkEqMP p d.toExpr
          | none => pure d.toExpr
        return .inl (← mkFalseElim target pf)
      if r.expr != ty then
        drop := drop.push d.fvarId
        unless r.expr.isTrue do
          let pf ← match r.proof? with
            | some p => mkEqMP p d.toExpr
            | none => mkExpectedTypeHint d.toExpr r.expr
          facts := facts.push (pf, r.expr, true, some d.userName)
        continue
      st := { st with done := st.done.insert ty }
    -- `ty` stays: look for a second read of the same `e = some _`.
    let some (_, l, rhs) := ty.eq? | continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    match seen[l]? with
    | none => seen := seen.insert l (d.toExpr, rhs)
    | some (h1, r1) =>
      if isRule then continue
      drop := drop.push d.fvarId
      unless r1 == rhs do
        let pf ← mkEqTrans (← mkEqSymm h1) d.toExpr
        facts := facts.push (pf, ← inferType pf, false, none)
  return .inr (facts, drop, st)

/-- Release the `Later`s of the hypotheses: at the top (`nested := false`),
    or under a binder in hypotheses other than disjunctions (`nested := true`),
    so `simp` continues there. -/
def release (cfg : Cfg) (t : Tele) (nested : Bool) : MetaM (Option Tele) := t.run do
  let mut out := t
  let mut progress := false
  for d in t.lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' ←
      if !nested then
        if ty.isAppOfArity ``ErgoTreeLean.Later 1 then pure ty.appArg! else continue
      else
        if ty.isAppOfArity ``Or 2 || (!cfg.loops && isLoopFact ty) || !containsLater ty then continue
        pure (releaseAll ty)
    let (o, _) ← out.add d.userName ty' d.toExpr
    out := o.hide #[d.fvarId]
    progress := true
  return if progress then some out else none

/-- A disjunction with a postponed branch (an `if` whose condition is still
    undecided). -/
def findBranch (t : Tele) : MetaM (Option LocalDecl) := t.run do
  for d in t.lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Or 2 && containsLater ty then return some d
  return none

/-- The definitions whose variable no longer occurs anywhere else (the
    rewriting has substituted it everywhere), to be hidden with it. -/
def unusedDefs (target : Expr) (t : Tele) (st : State) : MetaM (Array FVarId) := t.run do
  let mut out := #[]
  for (n, x) in st.defs do
    let some hd := t.lctx.findFromUserName? n | continue
    unless t.lctx.contains x do continue
    if target.containsFVar x then continue
    let mut used := false
    for d in t.lctx do
      if d.isImplementationDetail then continue
      if d.fvarId == hd.fvarId || d.fvarId == x then continue
      if (← instantiateMVars d.type).containsFVar x then used := true; break
    unless used do out := out.push hd.fvarId |>.push x
  return out

/-- The statements a new rule `a` can rewrite: those containing its left-hand
    side (for an equation), the negated proposition, or `a` itself. -/
def ruleSubject (a : Expr) : Expr :=
  match a.eq? with
  | some (_, l, _) => l
  | none => if a.isAppOfArity ``Not 1 then a.appArg! else a

inductive Step where
  | next (t : Tele) (st : State)
  /-- The proof of the target in the telescope's context, and the goals it
      leaves. -/
  | finish (pf : Expr) (goals : List MVarId)

mutual

/-- One round on the telescope. -/
partial def step (cfg : Cfg) (target : Expr) (tag : Name) (t : Tele) (st : State) : MetaM Step := do
  let isFalse ← t.run do
    for d in t.lctx do
      if !d.isImplementationDetail && (← instantiateMVars d.type).isFalse then return some d.toExpr
    return none
  if let some h := isFalse then return .finish (← t.run (mkFalseElim target h)) []
  let st ← addDefinitions t st
  match ← collect cfg target t st with
  | .inl pf => return .finish pf []
  | .inr (facts, drop, st) =>
    if !facts.isEmpty || !drop.isEmpty then
      let mut t := t.hide drop
      let mut st := st
      for (pf, ty, isDone, name?) in facts do
        (t, st) ← decompose cfg.propTarget t st pf ty isDone name?
      return .next t st
  -- An undecided `if` is split before its continuation is released, so the
  -- continuation sees the branch's value and condition.
  if cfg.propTarget then
    if let some d ← findBranch t then
      let (pf, goals) ← splitBranch cfg target tag (t.hide #[d.fvarId]) st d
      return .finish pf goals
  if let some t ← release cfg t false then return .next t st
  if let some t ← release cfg t true then return .next t st
  let t := t.hide (← unusedDefs target t st)
  -- The remaining goal takes the visible locals of the telescope as arguments
  -- (so the `let`s never close over a metavariable's context).
  let xs := t.lctx.foldl (init := #[]) fun xs d =>
    if d.isImplementationDetail || cfg.root.contains d.fvarId then xs else xs.push d.toExpr
  let baseLctx := xs.foldl (·.erase ·.fvarId!) t.lctx
  let gType ← t.run (mkForallFVars xs target)
  let G ← mkFreshExprMVarAt baseLctx (← getLocalInstances) gType .syntheticOpaque tag
  let (_, g) ← G.mvarId!.introNP xs.size
  return .finish (mkAppN G xs) [g]

/-- Run the engine on a telescope until it finishes; the proof of the target
    in the context the telescope started from. -/
partial def runTele (cfg : Cfg) (target : Expr) (tag : Name) (t : Tele) (st : State) :
    MetaM (Expr × List MVarId) := do
  let mut t := t
  let mut st := st
  repeat
    match ← step cfg target tag t st with
    | .next t' st' => t := t'; st := st'
    | .finish pf goals =>
      return (t.close target pf, goals)
  unreachable!

/-- Split on the disjunction `d`; in each branch the first conjunct (the branch
    condition) becomes a rule. -/
partial def splitBranch (cfg : Cfg) (target : Expr) (tag : Name) (t : Tele) (st : State) (d : LocalDecl) :
    MetaM (Expr × List MVarId) := do
  let ty ← t.run (instantiateMVars d.type)
  let a := ty.appFn!.appArg!
  let b := ty.appArg!
  let branch (side : Expr) : MetaM (Expr × List MVarId) := do
    let hfv ← mkFreshFVarId
    let hn ← mkFreshUserName `h
    let lctx := t.lctx.mkLocalDecl hfv hn side
    let h := Expr.fvar hfv
    let tb : Tele := { lctx }
    let (tb, st) ←
      if side.isAppOfArity ``And 2 then do
        let a1 := side.appFn!.appArg!
        let b1 := side.appArg!
        tb.run do trace[eval_sym] "split on {a1}"
        let gname ← mkFreshUserName `guard
        let (tb, _) ← tb.add gname a1 (mkApp3 (mkConst ``And.left) a1 b1 h)
        let (tb, _) ← tb.add (← mkFreshUserName `h) b1 (mkApp3 (mkConst ``And.right) a1 b1 h)
        -- A new rule: the statements it can rewrite must be looked at again.
        let s := ruleSubject a1
        pure (tb.hide #[hfv], { st with
          done := st.done.filter fun e => (e.find? (· == s)).isNone
          rules := st.rules.push (gname, false) })
      else pure (tb, st)
    let (pf, goals) ← runTele cfg target tag tb st
    return (← withLCtx lctx (← getLocalInstances) (mkLambdaFVars #[h] pf), goals)
  let (p1, g1) ← branch a
  let (p2, g2) ← branch b
  return (mkApp6 (mkConst ``Or.elim) a b target d.toExpr p1 p2, g1 ++ g2)

end

/-- Does `stx` (an extra simp lemma) mention a loop helper? -/
def mentionsLoopHelper (stx : Syntax) : TacticM Bool := do
  let some id := stx.find? (·.isIdent) | return false
  let some c := (← resolveGlobalName id.getId).head? | return false
  let some ci := (← getEnv).find? c.1 | return false
  return ErgoTreeLean.loopHelpers.any fun n => (ci.type.find? (·.isConstOf n)).isSome

def evalSym (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit :=
  withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 20000 }) do
  -- Local hypotheses among the extra lemmas are tracked by name, like branch
  -- conditions: the engine's substitutions replace their free variables.
  let lctx ← withMainContext getLCtx
  let mut locals := #[]
  let mut extra' := #[]
  for e in extra do
    let n := e.raw[2]
    if e.raw[0].isNone && e.raw[1].isNone && n.isIdent && (lctx.findFromUserName? n.getId).isSome then
      locals := locals.push n.getId
    else extra' := extra'.push e
  let extra := extra'
  let stx ← `(tactic| simp (config := { maxSteps := 4000000 }) only [eval_inv, ↓ErgoTreeLean.laterStop, reduceIte,
      Nat.reduceEqDiff, Nat.reduceSub, Nat.reduceAdd, Int.reduceLE, Int.reduceLT, Nat.reduceLeDiff, Int.reduceEq,
      Int.reduceNe, Int.reduceAdd, Int.reduceSub, Int.reduceMul, Int.reduceNeg, Int.reducePow, Int.reduceToNat,
      decide_eq_true_eq, Int.natCast_nonneg, $extra,*])
  let { ctx, simprocs, .. } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  let loops ← extra.anyM fun e => mentionsLoopHelper e.raw
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let target ← instantiateMVars (← g.getType)
    let cfg : Cfg := { ctx, simprocs, loops, root := lctx.foldl (·.insert ·.fvarId) {}, propTarget := ← isProp target }
    let (pf, goals) ← runTele cfg target (← g.getTag) { lctx } { rules := locals.map (·, false) }
    g.assign pf
    replaceMainGoal goals

end ErgoTreeLeanEvalSym


namespace ErgoTreeLean

/-- Symbolic execution of the `eval`/`EvalHolds` hypotheses (see the module
    docstring). `eval_sym [lemmas]` adds simp lemmas (hypotheses, or e.g.
    `forallHelper_true_iff` to expand collection loops under their binders).
    May split the goal on an undecided `if`. -/
syntax "eval_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
elab_rules : tactic
  | `(tactic| eval_sym) => ErgoTreeLeanEvalSym.evalSym #[]
  | `(tactic| eval_sym [$extra,*]) => ErgoTreeLeanEvalSym.evalSym extra.getElems

open Lean Elab Tactic Meta in
/-- Clear every loop fact (`forallHelper … = .ok b` and the other `*Helper`s),
    e.g. before `eval_sym [forallHelper_true_iff]` when only the loops that
    appear later need expanding. -/
elab "clear_loops" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ErgoTreeLeanEvalSym.isLoopFact (← instantiateMVars d.type) then g ← g.tryClear d.fvarId
  replaceMainGoal [g]

/-- Closes `inlineFuns t = some t` for a (unfolded) literal tree `t` with no
    `ValDef`-bound lambdas; use as `(by unfold myTree; inline_funs_id)`. -/
macro "inline_funs_id" : tactic =>
  `(tactic| simp [inlineFuns, rewriteExpr, rewriteDefs, rewriteExprList, isFuncValue])

end ErgoTreeLean
