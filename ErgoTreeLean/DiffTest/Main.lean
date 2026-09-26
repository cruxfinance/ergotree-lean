/-
`lake exe difftest`: loads the JSON case file `difftest/` generated from
sigma-rust's real `ergotree-interpreter 0.28.0` reducer
(`ErgoTreeLean/DiffTest/sell-order-cases.json` — see `make difftest`/
`README.md`), decodes it (`Decode.lean`) into `ErgoTreeLean`'s own
`Value`/`Box`/`Context`/`Case`/`SigmaBoolean`, and runs `Runner.lean`'s
`runCases` (`inlineFuns` + `eval` on each case, compared against
sigma-rust's recorded outcome). Prints mismatches and the outcome
distribution; exits nonzero on any mismatch.

This repo's own root module is intentionally thin — the reusable
run-and-compare logic lives in `Runner.lean` (a library module a
downstream package's own `lean_exe` root imports instead of this file,
since two packages both declaring a top-level `main` in the same build
would clash) — see README.md's "Difftest library usage".
-/
import ErgoTreeLean.DiffTest.Decode
import ErgoTreeLean.DiffTest.Runner

namespace ErgoTreeLean.DiffTest

def runMain : IO UInt32 := do
  let sellOrderCases ← loadCases "ErgoTreeLean/DiffTest/sell-order-cases.json"
  let m1 ← runCases "sell-order" ErgoTreeLean.Contracts.SellOrder.sellOrderTree sellOrderCases
  if m1 == 0 then
    IO.println "difftest: 0 mismatches"
    pure 0
  else
    IO.println s!"difftest: {m1} mismatches"
    pure 1

end ErgoTreeLean.DiffTest

/-- `lean_exe` targets need a top-level (not namespaced) `main`. -/
def main : IO UInt32 := ErgoTreeLean.DiffTest.runMain
