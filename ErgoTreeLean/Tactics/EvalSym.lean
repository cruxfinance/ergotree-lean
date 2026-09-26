/-
`eval_sym`: symbolic execution of a concrete ErgoTree inside a proof.

Given hypotheses of the form `eval c ctx env e = .ok v` or
`EvalHolds c ctx env signers e` about a *concrete* `e` (typically a whole
contract tree, after `unfold`ing its definition), `eval_sym` repeatedly
1. rewrites them with the `eval_inv` rules (`Lemmas/EvalInv.lean`,
   `Lemmas/EvalHolds.lean`), which replace a node's success by facts about its
   children with every runtime pattern match resolved,
2. splits the resulting `∧`/`∃` into separate hypotheses, and
3. substitutes every equation that defines a variable,
until nothing changes. What remains are facts about the context (`ctx.outputs[0]? = some out`,
`out.register 5 = some (.vColl τ vs)`, `vs.length = 2`, …), plus
`∀`-statements for collection loops and unexpanded disjunctions for `||`/`if`,
which the proof then handles in ordinary Lean.

`eval_simp` is step 1 alone, for use under binders (e.g. inside a `forall`
body) or when the default loop splits too eagerly.
-/
import ErgoTreeLean.Lemmas.EvalHolds
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.FailIfNoProgress

namespace ErgoTreeLean

attribute [eval_inv] Value.vColl.injEq Value.vBox.injEq Value.vInt.injEq Value.vLong.injEq Value.vBool.injEq
  Value.vOption.injEq Value.vSigmaProp.injEq Value.vTuple.injEq Value.vGroupElement.injEq Value.vByte.injEq
  Value.vShort.injEq Value.vBigInt.injEq SigmaBoolean.trivial.injEq SigmaBoolean.proveDlog.injEq
  Option.some.injEq Prod.mk.injEq List.cons.injEq reduceCtorEq
  exists_eq_left exists_eq_right exists_eq_left' exists_eq_right' exists_and_left exists_and_right
  and_assoc exists_const and_true true_and and_false false_and or_false false_or not_false_eq_true not_true_eq_false
  eq_self_iff_true ne_eq
  List.forall_mem_cons List.forall_mem_nil List.not_mem_nil false_implies implies_true forall_const
  List.getElem?_map Option.map_eq_some_iff List.getElem?_cons_zero List.getElem?_cons_succ
  List.forall_mem_map List.mem_range List.length_map List.length_range List.length_cons List.length_nil
  Option.isSome_some Option.isSome_none
  if_true if_false le_refl Int.toNat_zero Int.toNat_natCast
  Bool.true_eq_false Bool.false_eq_true beq_iff_eq beq_self_eq_true
  Value.beq_vInt Value.beq_vLong Value.beq_vShort Value.beq_vByte Value.beq_vBigInt Value.beq_vBool
  Value.beq_vGroupElement bytesToVColl_beq_true typeOf SType.beq
  Bool.and_eq_true
  beq_eq_false_iff_ne Int.natCast_inj Int.ofNat_inj

/-- One round of `eval_inv` rewriting (plus the numeral/`if` simprocs it needs). -/
syntax (name := evalSimp) "eval_simp" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| eval_simp $[$loc]?) =>
    `(tactic| simp only [eval_inv, reduceIte, Nat.reduceEqDiff, Nat.reduceSub, Nat.reduceAdd, Int.reduceLE,
        Int.reduceLT, Nat.reduceLeDiff, Int.reduceNeg, Int.reduceToNat, decide_eq_true_eq, Int.natCast_nonneg]
        $[$loc]?)

/-- Loop helpers whose success facts `eval_simp_hyps` leaves alone. -/
def loopHelpers : List Lean.Name :=
  [``forallHelper, ``existsHelper, ``mapHelper, ``filterHelper, ``foldHelper]

open Lean Elab Tactic Meta in
/-- Run `simp only [eval_inv, …, extra]` on every propositional hypothesis,
    leaving the goal alone. Fails if nothing changed. -/
def evalSimpHyps (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (singlePass := false) : TacticM Unit :=
  withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 20000 }) do
  let stx ← `(tactic| simp (config := { maxSteps := 4000000 }) only [eval_inv, reduceIte, Nat.reduceEqDiff, Nat.reduceSub, Nat.reduceAdd,
      Int.reduceLE, Int.reduceLT, Nat.reduceLeDiff, Int.reduceEq, Int.reduceNe, Int.reduceAdd, Int.reduceSub, Int.reduceNeg, Int.reduceToNat, decide_eq_true_eq,
      Int.natCast_nonneg, $extra,*])
  let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let ctx ← ctx.setConfig { ctx.config with singlePass }
  withMainContext do
    let fvarIds ← (← getLCtx).getFVarIds.filterM fun fv => do
      let d ← fv.getDecl
      if d.isImplementationDetail || !(← isProp d.type) then return false
      -- Folded loop facts (`forallHelper … = .ok _` etc.) carry a whole loop
      -- body; nothing in `eval_inv` rewrites them, so skip re-traversing
      -- (unless extra lemmas were given, e.g. `forallHelper_true_iff`).
      let t ← instantiateMVars d.type
      if let some (_, lhs, _) := t.eq? then
        if extra.isEmpty && loopHelpers.any (lhs.isAppOf ·) then return false
      return true
    -- All hypotheses in one `simpGoal` call; if that fails (e.g. one
    -- hypothesis hits `maxSteps`), fall back to one hypothesis at a time so
    -- the others still make progress.
    let g ← getMainGoal
    let batch ← observing? <| dischargeWrapper.with fun discharge? =>
      simpGoal g ctx simprocs discharge? (simplifyTarget := false) (fvarIdsToSimp := fvarIds)
    if let some (r, _) := batch then
      match r with
      | none => replaceMainGoal []; return
      | some (_, g') =>
        if g' == g then throwError "eval_simp_hyps: no progress"
        replaceMainGoal [g']; return
    let mut progress := false
    for fv in fvarIds do
      let g ← getMainGoal
      unless (← g.getDecl).lctx.contains fv do continue
      let r ← observing? <| dischargeWrapper.with fun discharge? =>
        simpGoal g ctx simprocs discharge? (simplifyTarget := false) (fvarIdsToSimp := #[fv])
      match r with
      | some (none, _) => replaceMainGoal []; return
      | some (some (_, g'), _) =>
        if g' != g then progress := true
        replaceMainGoal [g']
      | none => pure ()
    unless progress do throwError "eval_simp_hyps: no progress"

/-- `eval_simp` on every propositional hypothesis, leaving the goal alone
    (so a statement being proved is never rewritten). Extra simp lemmas can be
    given in brackets. Fails if nothing changed. -/
syntax "eval_simp_hyps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
elab_rules : tactic
  | `(tactic| eval_simp_hyps) => evalSimpHyps #[]
  | `(tactic| eval_simp_hyps [$extra,*]) => evalSimpHyps extra.getElems

/-- `eval_simp_hyps` with simp's `singlePass`: each call descends only one
    rewrite round, so `eval_sym'` interleaves splitting/substitution with
    unfolding (keeps terms small on large trees). -/
syntax "eval_simp_hyps1" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
elab_rules : tactic
  | `(tactic| eval_simp_hyps1) => evalSimpHyps #[] true
  | `(tactic| eval_simp_hyps1 [$extra,*]) => evalSimpHyps extra.getElems true

open Lean Elab Tactic Meta in
/-- For two hypotheses `h₁ : e = some a` and `h₂ : e = some b` with the same
    `e` (e.g. a register read twice by the script), replace `h₂` by
    `some a = some b`, which `eval_simp` then turns into `a = b`. Fails if
    there is no such pair. -/
elab "merge_some_eqs" : tactic => withMainContext do
  let hyps ← getLocalHyps
  for h1 in hyps do
    for h2 in hyps do
      if h1 == h2 then continue
      let t1 ← instantiateMVars (← inferType h1)
      let t2 ← instantiateMVars (← inferType h2)
      let some (_, l1, r1) := t1.eq? | continue
      let some (_, l2, r2) := t2.eq? | continue
      unless r1.isAppOfArity ``Option.some 2 && r2.isAppOfArity ``Option.some 2 do continue
      unless l1 == l2 && r1 != r2 do continue
      let pf ← mkEqTrans (← mkEqSymm h1) h2
      let g ← getMainGoal
      let (_, g) ← g.note `hmerge pf
      let g ← g.clear h2.fvarId!
      replaceMainGoal [g]
      return
  throwError "merge_some_eqs: nothing to merge"

/-- Symbolic execution loop: split `∧`/`∃` hypotheses, `subst_vars`,
    `eval_simp_hyps`, `merge_some_eqs`, until none makes progress.
    `eval_sym [lemmas]` adds simp lemmas, e.g. `forallHelper_true_iff` to
    expand collection loops under their binders. -/
syntax "eval_sym" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| eval_sym) => `(tactic| eval_sym [])
  | `(tactic| eval_sym [$extra,*]) => `(tactic| (
    repeat (first
      | (casesm _ ∧ _, ∃ _, _); (casesm* _ ∧ _, ∃ _, _); (try subst_vars)
      | fail_if_no_progress subst_vars
      | eval_simp_hyps [$extra,*]
      | merge_some_eqs)))

/-- `eval_sym` driven by single-pass simp rounds (for large trees). -/
syntax "eval_sym'" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| eval_sym') => `(tactic| eval_sym' [])
  | `(tactic| eval_sym' [$extra,*]) => `(tactic| (
    repeat (first
      | (casesm _ ∧ _, ∃ _, _); (casesm* _ ∧ _, ∃ _, _); (try subst_vars)
      | fail_if_no_progress subst_vars
      | merge_some_eqs
      | eval_simp_hyps1 [$extra,*])))

/-- Closes `inlineFuns t = some t` for a (unfolded) literal tree `t` with no
    `ValDef`-bound lambdas; use as `(by unfold myTree; inline_funs_id)`. -/
macro "inline_funs_id" : tactic =>
  `(tactic| simp [inlineFuns, rewriteExpr, rewriteDefs, rewriteExprList, isFuncValue])

end ErgoTreeLean
