/-
`sell-order`'s theorems re-proved with `eval_sym` (`Tactics/EvalSym.lean`), as
a small worked example of the tooling. Same statements as in `SellOrder.lean`,
where they are proved from two hand-derived evaluation lemmas
(`eval_outputs_nil`/`eval_outputs_cons`); here `eval_sym` executes the tree.
-/
import ErgoTreeLean.Contracts.SellOrder
import ErgoTreeLean.Tactics.EvalSym

namespace ErgoTreeLean.Contracts.SellOrder

open ErgoTreeLean

/-- `seller_paid`, via `eval_sym`: `sigmaOr` is split with
    `EvalHolds_sigmaOr_imp`; in the seller's branch `eval_sym` derives
    `pk ∈ signers` and the contradiction with `hnotSigner`, in the other it
    leaves the payment facts. -/
theorem seller_paid' (pk prop : List UInt8) (price : Int) (ctx : Context) (signers : List PK)
    (hspend : spendable (consts pk prop price) ctx signers sellOrderTree) (hnotSigner : pk ∉ signers) :
    ∃ o, ctx.outputs.head? = some o ∧ o.propositionBytes = prop ∧ o.value ≥ price := by
  have h := spendable_of_inlineFuns_eq inlineFuns_sellOrderTree hspend
  unfold sellOrderTree consts at h
  eval_sym
  obtain ⟨e, he, hh⟩ := EvalHolds_sigmaOr_imp (h := ‹EvalHolds _ _ _ _ (.sigmaOr _)›) ..
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> eval_sym [hnotSigner]
  exact ⟨_, by rw [List.head?_eq_getElem?]; assumption, ‹_›, ‹_›⟩

/-- `no_outputs_unspendable`, via `eval_sym`: `OUTPUTS(0)` has no value. -/
theorem no_outputs_unspendable' (pk prop : List UInt8) (price : Int) (ctx : Context) (signers : List PK)
    (houts : ctx.outputs = []) :
    ¬ spendable (consts pk prop price) ctx signers sellOrderTree := by
  intro hspend
  have h := spendable_of_inlineFuns_eq inlineFuns_sellOrderTree hspend
  unfold sellOrderTree consts at h
  eval_sym [houts]

end ErgoTreeLean.Contracts.SellOrder

#print axioms ErgoTreeLean.Contracts.SellOrder.seller_paid'
#print axioms ErgoTreeLean.Contracts.SellOrder.no_outputs_unspendable'
