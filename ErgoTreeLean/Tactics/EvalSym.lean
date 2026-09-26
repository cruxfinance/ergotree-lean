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
   simplified again, so the cost of a round is proportional to what changed;
5. when nothing else applies, split the goal on an `if` whose condition is
   undecided (a disjunction with a `Later` branch) and keep the branch
   condition as a rewrite rule for the rest of that branch, so every later
   `if` on the same condition loses its dead arm without being examined;
6. otherwise release the facts marked `Later` (`Lemmas/EvalInv.lean`). `simp`
   stops at a `Later`, so a block runs one definition at a time and every
   continuation is simplified once, with the definitions before it (and the
   branch taken by any `if` among them) already decoded.

Loop facts (`forallHelper … = .ok b` and the other `*Helper`s) carry a whole
loop body and are left alone unless an extra lemma about a loop helper is
given (`eval_sym [forallHelper_true_iff]` expands `forall` loops under their
binders; `Later`s under a binder are released by re-simplifying that
hypothesis).

`eval_simp` is one plain `simp` round with every `Later` released at once, for
use on a goal or under binders.
-/
import ErgoTreeLean.Lemmas.EvalHolds
import ErgoTreeLean.Lemmas.Decode

namespace ErgoTreeLean

attribute [eval_inv] Value.vColl.injEq Value.vBox.injEq Value.vInt.injEq Value.vLong.injEq Value.vBool.injEq
  Value.vOption.injEq Value.vSigmaProp.injEq Value.vTuple.injEq Value.vGroupElement.injEq Value.vByte.injEq
  Value.vShort.injEq Value.vBigInt.injEq SigmaBoolean.trivial.injEq SigmaBoolean.proveDlog.injEq
  Option.some.injEq Prod.mk.injEq List.cons.injEq reduceCtorEq
  exists_eq_left exists_eq_right exists_eq_left' exists_eq_right' exists_and_left exists_and_right
  and_assoc exists_const and_true true_and and_false false_and or_false false_or not_false_eq_true not_true_eq_false
  eq_self_iff_true ne_eq
  List.forall_mem_cons List.not_mem_nil false_implies implies_true forall_const
  List.getElem?_map Option.map_eq_some_iff List.getElem?_cons_zero List.getElem?_cons_succ
  List.forall_mem_map List.mem_range List.length_map List.length_range List.length_cons List.length_nil
  Option.isSome_some Option.isSome_none
  if_true if_false Int.toNat_zero Int.toNat_natCast
  Bool.true_eq_false Bool.false_eq_true beq_iff_eq beq_self_eq_true
  Value.beq_vInt Value.beq_vLong Value.beq_vShort Value.beq_vByte Value.beq_vBigInt Value.beq_vBool
  Value.beq_vGroupElement bytesToVColl_beq_true typeOf SType.beq
  Bool.and_eq_true Bool.not_eq_true' Bool.not_eq_false'
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

/-- Per-goal engine state. -/
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
  /-- Also simplify loop-helper facts. -/
  loops : Bool

def isLoopFact (t : Expr) : Bool :=
  match t.eq? with
  | some (_, lhs, _) => ErgoTreeLean.loopHelpers.any (lhs.isAppOf ·)
  | none => false

def containsLater (t : Expr) : Bool := (t.find? (·.isAppOf ``ErgoTreeLean.Later)).isSome

/-- Replace every `Later p` in `t` by `p` (a definitional unfolding). -/
partial def releaseAll (t : Expr) : Expr :=
  t.replace fun e => if e.isAppOfArity ``ErgoTreeLean.Later 1 then some (releaseAll e.appArg!) else none

/-! Every step below changes the goal at most once per round: each new goal
built by `intro`/`assert` becomes a delayed assignment, and instantiating a
long chain of those at the end costs more than the whole symbolic execution. -/

/-- Decompose the proof `pf : ty` into its `∧`/`∃` leaves. Witnesses and leaves
    become locals (`binders`, instantiated by `args`); `k` builds the rest of
    the proof with all of them in scope. `doneIdx`: binders that are leaves of a
    statement in normal form (and hence in normal form themselves). -/
partial def decompose (target : Expr) (propTarget : Bool) (pf ty : Expr) (isDone : Bool)
    (binders args : Array Expr) (doneIdx : Array Nat)
    (k : Array Expr → Array Expr → Array Nat → MetaM Expr) : MetaM Expr := do
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!
    let b := ty.appArg!
    decompose target propTarget (mkApp3 (mkConst ``And.left) a b pf) a isDone binders args doneIdx fun bs as ds =>
      decompose target propTarget (mkApp3 (mkConst ``And.right) a b pf) b isDone bs as ds k
  else if propTarget && ty.isAppOfArity ``Exists 2 then
    let α := ty.appFn!.appArg!
    let p := ty.appArg!
    let u ← getLevel α
    let n := match p with | .lam n .. => n | _ => `w
    withLocalDeclD n α fun w => do
      let bodyTy := p.beta #[w]
      withLocalDeclD `h bodyTy fun hw => do
        let body ← decompose target propTarget hw bodyTy isDone (binders.push w) (args.push w) doneIdx k
        return mkApp5 (mkConst ``Exists.elim [u]) α p target pf (← mkLambdaFVars #[w, hw] body)
  else
    withLocalDeclD `h ty fun x =>
      k (binders.push x) (args.push pf) (if isDone then doneIdx.push binders.size else doneIdx)

/-- Split every `∧`/`∃` hypothesis into its leaves, in one new goal. -/
def splitAll (g : MVarId) (st : State) : MetaM (MVarId × State × Bool) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  let propTarget ← isProp target
  let mut todo : Array (FVarId × Expr × Bool) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``And 2 || (propTarget && t.isAppOfArity ``Exists 2) then
      todo := todo.push (d.fvarId, t, st.done.contains t)
  if todo.isEmpty then return (g, st, false)
  let lctx ← getLCtx
  let linsts ← getLocalInstances
  let tag ← g.getTag
  let newGoal ← IO.mkRef (none : Option (MVarId × Array Nat × Nat))
  let rec go (j : Nat) (bs as : Array Expr) (ds : Array Nat) : MetaM Expr := do
    if h : j < todo.size then
      let (fv, t, isDone) := todo[j]
      decompose target propTarget (mkFVar fv) t isDone bs as ds (go (j + 1))
    else
      -- The new goal lives in the old context and takes the new locals as
      -- arguments, so building the proof needs no delayed assignment.
      let gType ← mkForallFVars bs target
      let G ← mkFreshExprMVarAt lctx linsts gType .syntheticOpaque tag
      newGoal.set (some (G.mvarId!, ds, bs.size))
      return mkAppN G as
  let pf ← go 0 #[] #[] #[]
  g.assign pf
  let some (G, ds, n) ← newGoal.get | throwError "eval_sym: split failed"
  let (fvs, G) ← G.introN n
  let G ← G.tryClearMany (todo.map (·.1))
  let st ← G.withContext do
    let mut done := st.done
    for i in ds do
      done := done.insert (← instantiateMVars (← fvs[i]!.getDecl).type)
    return { st with done }
  trace[eval_sym] "split {todo.size} hypotheses into {n}"
  return (G, st, true)

/-- Register new variable definitions `x = t` / `t = x` (`x` a local, not in
    `t`) as rewrite rules. Rules stay acyclic: `t` must not mention a defined
    variable (it will, after rewriting, in a later round). Of two variables,
    the one declared later is defined, so user-named variables survive. -/
def addDefinitions (g : MVarId) (st : State) : MetaM (State × Bool) := g.withContext do
  let lctx ← getLCtx
  let mut st := st
  let mut progress := false
  for d in lctx do
    if d.isImplementationDetail then continue
    if st.rules.any (·.1 == d.userName) then continue
    let t ← instantiateMVars d.type
    let some (_, a, b) := t.eq? | continue
    let isVar (e : Expr) : Bool :=
      e.isFVar && !(lctx.get! e.fvarId!).isLet && !st.defined.contains e.fvarId!
    let mentionsDefined (e : Expr) : Bool := e.hasAnyFVar (st.defined.contains ·)
    let pick : Option (FVarId × Bool) :=
      if isVar a && isVar b then
        if (lctx.get! a.fvarId!).index > (lctx.get! b.fvarId!).index then some (a.fvarId!, false)
        else some (b.fvarId!, true)
      else if isVar a && !b.containsFVar a.fvarId! && !mentionsDefined b then some (a.fvarId!, false)
      else if isVar b && !a.containsFVar b.fvarId! && !mentionsDefined a then some (b.fvarId!, true)
      else none
    let some (x, flip) := pick | continue
    if (st.rules.map (·.1)).contains d.userName then continue
    st := { st with
      rules := st.rules.push (d.userName, flip)
      defined := st.defined.insert x
      defs := st.defs.push (d.userName, x)
      done := st.done.filter fun e => !e.containsFVar x }
    progress := true
  return (st, progress)

/-- For hypotheses `e = some a` and `e = some b` (e.g. a register read twice),
    replace the second by `some a = some b`. -/
def mergeSomeEqs (g : MVarId) : MetaM (MVarId × Bool) := g.withContext do
  let mut seen : Std.HashMap Expr (Expr × Expr) := {}
  let mut toAssert := #[]
  let mut toClear := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let some (_, l, r) := t.eq? | continue
    unless r.isAppOfArity ``Option.some 2 do continue
    match seen[l]? with
    | none => seen := seen.insert l (d.toExpr, r)
    | some (h1, r1) =>
      toClear := toClear.push d.fvarId
      unless r1 == r do
        let pf ← mkEqTrans (← mkEqSymm h1) d.toExpr
        toAssert := toAssert.push { userName := ← mkFreshUserName `h, type := ← inferType pf, value := pf }
  if toClear.isEmpty then return (g, false)
  let (_, g) ← g.assertHypotheses toAssert
  return (← g.tryClearMany toClear, true)

/-- `simp` every hypothesis whose statement is not yet in normal form, with the
    rules as extra rewrite rules. Returns `none` if a hypothesis became `False`
    (goal closed). -/
def simpNew (cfg : Cfg) (g : MVarId) (st : State) : MetaM (Option (MVarId × State) × Bool) := g.withContext do
  let lctx ← getLCtx
  let mut ctx := cfg.ctx
  for (n, flip) in st.rules do
    if let some d := lctx.findFromUserName? n then
      let pf ← if flip then mkEqSymm d.toExpr else pure d.toExpr
      ctx := ctx.setSimpTheorems (← ctx.simpTheorems.addTheorem (.fvar d.fvarId) pf)
  let mut st := st
  let mut toAssert := #[]
  let mut toClear := #[]
  let mut progress := false
  for d in lctx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if st.done.contains t then continue
    unless ← isProp t do continue
    if !cfg.loops && isLoopFact t then continue
    let ctx' := ctx.setSimpTheorems (ctx.simpTheorems.eraseTheorem (.fvar d.fvarId))
    let t0 ← IO.monoMsNow
    let (r, _) ← simp t ctx' cfg.simprocs none
    let dt := (← IO.monoMsNow) - t0
    trace[eval_sym] "simp {dt}ms: {t.approxDepth} {if r.expr == t then "(normal)" else ""}"
    if dt > 5000 then trace[eval_sym] "slow: {t}"
    if r.expr.isFalse then
      let pf ← match r.proof? with
        | some p => mkEqMP p d.toExpr
        | none => pure d.toExpr
      g.assign (← mkFalseElim (← g.getType) pf)
      return (none, true)
    if r.expr == t then
      st := { st with done := st.done.insert t }
      continue
    progress := true
    toClear := toClear.push d.fvarId
    if r.expr.isTrue then continue
    let value ← match r.proof? with
      | some p => mkEqMP p d.toExpr
      | none => mkExpectedTypeHint d.toExpr r.expr
    toAssert := toAssert.push { userName := d.userName, type := r.expr, value }
    st := { st with done := st.done.insert r.expr }
  if !progress then return (some (g, st), false)
  let (_, g) ← g.assertHypotheses toAssert
  let g ← g.tryClearMany toClear
  return (some (g, st), progress)

/-- Release every top-level `Later` hypothesis. -/
def releaseTop (g : MVarId) : MetaM (MVarId × Bool) := g.withContext do
  let mut g := g
  let mut progress := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``ErgoTreeLean.Later 1 then
      g ← g.replaceLocalDeclDefEq d.fvarId t.appArg!
      progress := true
  return (g, progress)

/-- Release the `Later`s nested (under a binder) in hypotheses other than
    disjunctions, so `simp` continues there. -/
def releaseNested (cfg : Cfg) (g : MVarId) : MetaM (MVarId × Bool) := g.withContext do
  let mut g := g
  let mut progress := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Or 2 then continue
    if !cfg.loops && isLoopFact t then continue
    if containsLater t then
      g ← g.replaceLocalDeclDefEq d.fvarId (releaseAll t)
      progress := true
  return (g, progress)

/-- A disjunction with a postponed branch (an `if` whose condition is still
    undecided). -/
def findBranch (g : MVarId) : MetaM (Option FVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Or 2 && containsLater t then return some d.fvarId
  return none

/-- Split the goal on the disjunction `fv`; in each branch the first conjunct
    (the branch condition) becomes a rule. -/
def splitBranch (g : MVarId) (fv : FVarId) (st : State) : MetaM (List (MVarId × State)) := do
  let subgoals ← g.cases fv
  let mut out := []
  for sg in subgoals.reverse do
    let g := sg.mvarId
    let some field := sg.fields[0]? | out := (g, st) :: out; continue
    let some hfv := field.fvarId? | out := (g, st) :: out; continue
    let t ← g.withContext do instantiateMVars (← hfv.getDecl).type
    if t.isAppOfArity ``And 2 then
      let a := t.appFn!.appArg!
      let b := t.appArg!
      let gname ← mkFreshUserName `guard
      let (_, g1) ← g.withContext do g.assertHypotheses #[
        { userName := gname, type := a, value := mkApp3 (mkConst ``And.left) a b field },
        { userName := ← mkFreshUserName `h, type := b, value := mkApp3 (mkConst ``And.right) a b field }]
      let g2 ← g1.tryClear hfv
      -- A new rule: every statement must be looked at again.
      out := (g2, { st with done := {}, rules := st.rules.push (gname, false) }) :: out
    else
      out := (g, st) :: out
  return out

/-- Drop the definitions whose variable no longer occurs anywhere else (the
    rewriting has substituted it everywhere). -/
def cleanup (g : MVarId) (st : State) : MetaM MVarId := g.withContext do
  let lctx ← getLCtx
  let target ← instantiateMVars (← g.getType)
  let mut toClear := #[]
  for (n, x) in st.defs do
    let some hd := lctx.findFromUserName? n | continue
    unless lctx.contains x do continue
    if target.containsFVar x then continue
    let mut used := false
    for d in lctx do
      if d.fvarId == hd.fvarId || d.fvarId == x then continue
      if (← instantiateMVars d.type).containsFVar x then used := true; break
    unless used do toClear := toClear.push (hd.fvarId, x)
  let mut g := g
  for (h, x) in toClear do
    g ← g.tryClear h
    g ← g.tryClear x
  return g

/-- The `eval_sym` loop on one goal. -/
partial def run (cfg : Cfg) (g : MVarId) (st : State) : MetaM (List MVarId) := do
  let (g, st, _) ← splitAll g st
  let (st, _) ← addDefinitions g st
  let (g, _) ← mergeSomeEqs g
  let (r, progress) ← simpNew cfg g st
  let some (g, st) := r | return []
  if progress then return ← run cfg g st
  -- An undecided `if` is split before its continuation is released, so the
  -- continuation sees the branch's value and condition.
  if let some fv ← findBranch g then
    let branches ← splitBranch g fv st
    let mut out := []
    for (g', st') in branches do
      out := out ++ (← run cfg g' st')
    return out
  let (g, p) ← releaseTop g
  if p then return ← run cfg g st
  let (g, p) ← releaseNested cfg g
  if p then return ← run cfg g st
  return [← cleanup g st]

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
  let cfg : Cfg := { ctx, simprocs, loops }
  let goals ← run cfg (← getMainGoal) { rules := locals.map (·, false) }
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

/-- Closes `inlineFuns t = some t` for a (unfolded) literal tree `t` with no
    `ValDef`-bound lambdas; use as `(by unfold myTree; inline_funs_id)`. -/
macro "inline_funs_id" : tactic =>
  `(tactic| simp [inlineFuns, rewriteExpr, rewriteDefs, rewriteExprList, isFuncValue])

end ErgoTreeLean
