import ErgoTreeLean.Syntax
import ErgoTreeLean.Numeric
import ErgoTreeLean.Context
import ErgoTreeLean.Eval
import ErgoTreeLean.InlineFuns
import ErgoTreeLean.Sigma
import ErgoTreeLean.Deserialize
import ErgoTreeLean.Contracts.SellOrder
import ErgoTreeLean.Contracts.SellOrder.Exported
import ErgoTreeLean.Contracts.SellOrder.CrossCheck
-- Symbolic-evaluation tactic tooling (pulls in Lemmas/EvalInv.lean,
-- Lemmas/EvalHolds.lean, Lemmas/SigmaHolds.lean, Lemmas/Beq.lean,
-- Tactics/Attr.lean transitively). The only modules in this library that
-- import Mathlib.
import ErgoTreeLean.Tactics.EvalSym
-- `sell-order`'s theorems re-proved with `eval_sym` (a worked example).
import ErgoTreeLean.Contracts.SellOrder.EvalSym
-- Note: the differential-testing library (`ErgoTreeLean.DiffTest.Types`/
-- `.Decode`, exposing `Case`/`loadCases`/`checkCase`/`runCases`/`Tally`)
-- is *not* imported here — `Decode.lean` itself imports this whole root,
-- so importing it back would be a cycle. A `lean_exe`'s own root module
-- (this repo's `ErgoTreeLean/DiffTest/Main.lean`, or a downstream
-- package's equivalent) imports `ErgoTreeLean` plus
-- `ErgoTreeLean.DiffTest.Types`/`.Decode` directly; see README.md's
-- "Difftest library usage".
