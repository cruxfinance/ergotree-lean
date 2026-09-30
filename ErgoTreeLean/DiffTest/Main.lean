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
  -- `box-fields`: R0-R3/`ExtractCreationInfo` on SELF/INPUTS/OUTPUTS (a
  -- hand-written synthetic tree) plus the real mainnet timelock tree
  -- (`ExtractCreationInfo` via `SigmaAnd`) — two trees, reported together
  -- as one family since both cover the same new coverage — see
  -- `ErgoTreeLean/Contracts/BoxFields.lean`/`Contracts/Timelock/Exported.lean`.
  let boxFieldsCases ← loadCases "ErgoTreeLean/DiffTest/box-fields-cases.json"
  let m2 ← runCases "box-fields" ErgoTreeLean.Contracts.boxFieldsTree boxFieldsCases
  let timelockCases ← loadCases "ErgoTreeLean/DiffTest/timelock-cases.json"
  let m3 ← runCases "box-fields (timelock)" ErgoTreeLean.Contracts.Timelock.Exported.timelockTree timelockCases
  -- `sigma-prop-bytes`: `SigmaPropBytes` (`somePk.propBytes`) on a
  -- per-case `SigmaProp` constant of every `SigmaBoolean` shape — see
  -- `ErgoTreeLean/Contracts/SigmaPropBytes.lean`.
  let sigmaPropBytesCases ← loadCases "ErgoTreeLean/DiffTest/sigma-prop-bytes-cases.json"
  let m4 ← runCases "sigma-prop-bytes" ErgoTreeLean.Contracts.sigmaPropBytesTree sigmaPropBytesCases
  -- `coll-indexof`: `SCollection.indexOf` (`type_id=12`, `method_id=26`) on
  -- `INPUTS`/`SELF`, the `MethodCall` node this family added a case for —
  -- see `ErgoTreeLean/Contracts/CollIndexOf.lean`.
  let collIndexOfCases ← loadCases "ErgoTreeLean/DiffTest/coll-indexof-cases.json"
  let m5 ← runCases "coll-indexof" ErgoTreeLean.Contracts.collIndexOfTree collIndexOfCases
  let total := m1 + m2 + m3 + m4 + m5
  if total == 0 then
    IO.println "difftest: 0 mismatches"
    pure 0
  else
    IO.println s!"difftest: {total} mismatches"
    pure 1

end ErgoTreeLean.DiffTest

/-- `lean_exe` targets need a top-level (not namespaced) `main`. -/
def main : IO UInt32 := ErgoTreeLean.DiffTest.runMain
