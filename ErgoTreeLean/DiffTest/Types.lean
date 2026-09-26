/-
Shared types for the differential-testing harness (`difftest/` on the Rust
side, `lake exe difftest` on the Lean side — see `README.md`). A `Case` is
one `(EIP-5 constants, spending Context)` pair together with what
sigma-rust's real `ergotree-interpreter 0.28.0` reducer (`reduce_to_crypto`)
says the outcome is; the `difftest` case generator emits these as JSON
(one array file per contract family, e.g.
`ErgoTreeLean/DiffTest/sell-order-cases.json`), decoded back into these
exact constructors by `Decode.lean`.
-/
import ErgoTreeLean.Syntax
import ErgoTreeLean.Context

namespace ErgoTreeLean.DiffTest

/-- One differential-test case. `expected := none` means sigma-rust's
    `reduce_to_crypto` itself errored (an evaluation error, in the task
    brief's sense — the error *message* is deliberately not recorded/
    compared, only the ok/error outcome and, when `ok`, the resulting
    `SigmaBoolean`, after sigma-rust's own `Cand`/`Cor` normalization —
    see `Eval.lean`'s `normalizeCand`/`normalizeCor`, which mirror it). -/
structure Case where
  id : Nat
  consts : List Value
  ctx : Context
  expected : Option SigmaBoolean
deriving Repr

end ErgoTreeLean.DiffTest
