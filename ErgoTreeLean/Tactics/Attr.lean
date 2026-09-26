/-
Simp sets used by the symbolic-evaluation tooling (`ErgoTreeLean/Lemmas/EvalInv.lean`).

* `eval_inv`: rewrites a success equation `eval consts ctx env e = .ok v` for a
  concrete node `e` into a statement about `e`'s children, with every runtime
  pattern match already resolved. Running `simp only [eval_inv] at h` on a
  success hypothesis about a whole contract tree symbolically executes it.
-/
import Lean

register_simp_attr eval_inv
