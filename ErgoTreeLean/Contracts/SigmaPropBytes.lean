/-
The `sigma-prop-bytes` difftest family's tree: a hand-written, purpose-built
`Expr` (no compiled contract behind it — same spirit as `BoxFields.lean`)
that exercises `SigmaPropBytes` (ErgoScript `somePk.propBytes`).

ErgoScript-shaped reading:

```
sigmaProp(OUTPUTS(0).propositionBytes == CONST.propBytes)
```

`CONST` (constant index 0) is a per-case `SigmaProp` value — every
constructor `SigmaBoolean` has (`trivial`/`proveDlog`/`cor`/`cand`/
`cthreshold`), including nested and larger shapes, all built by
`difftest/src/sigma_prop_bytes.rs`'s generator using sigma-rust's own
normalizing constructors (`Cand::normalized`/`Cor::normalized`/
`Cthreshold::reduce`), never a hand-assembled shape sigma-rust itself
couldn't produce. `OUTPUTS(0)`'s box carries a script whose
`propositionBytes` is either exactly `CONST`'s real
`SigmaProp::prop_bytes()` output, or a deliberately different byte string
(a one-byte mutation, a truncation, or a different shape/key's real
bytes) — so the only two success outcomes are `trivial true`/`trivial
false` (a plain `Coll[Byte]` comparison, never a real proof obligation on
`CONST` itself), plus one error path: `OUTPUTS` empty, on which
`ByIndex(OUTPUTS, 0)` fails.

Mirrors `difftest/src/sigma_prop_bytes.rs`'s `build_tree` node-for-node —
that file builds the identical tree directly against `ergotree-ir`'s real
MIR types, run through sigma-rust's real reducer for the differential
test; this is the Lean side `runCases` evaluates the same generated cases
against.
-/
import ErgoTreeLean.Syntax
import ErgoTreeLean.Context
import ErgoTreeLean.Eval
import ErgoTreeLean.InlineFuns

namespace ErgoTreeLean.Contracts

open ErgoTreeLean

def sigmaPropBytesTree : Expr :=
  .boolToSigmaProp
    (.binOp (.relation .eq)
      (.extractScriptBytes (.byIndex .outputs (.const (.vInt 0)) none))
      (.sigmaPropBytes (.constPlaceholder 0 .sSigmaProp)))

end ErgoTreeLean.Contracts
