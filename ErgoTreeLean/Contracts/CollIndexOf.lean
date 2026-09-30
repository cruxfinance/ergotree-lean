/-
The `coll-indexof` difftest family's tree: a hand-written, purpose-built
`Expr` (no compiled contract behind it, exactly like `BoxFields.lean` —
see that file's own docstring) exercising `SCollection.indexOf`
(`type_id=12`, `method_id=26`), the `MethodCall` node `Eval.lean` had *no*
case for at all before this family was added (every `MethodCall` was a
hard `.error`). The motivating case is `dexy-stable`'s
`contracts/bank/update/ballot.es`: `val index = INPUTS.indexOf(SELF, 0)`.

ErgoScript-shaped reading:

```
sigmaProp(INPUTS.indexOf(SELF, fromConst) == targetConst)
```

Mirrors `difftest/src/coll_indexof.rs`'s `build_tree_hex` node-for-node —
that file builds the identical tree (serialized, then re-instantiated per
case via `build_ergo_tree`, exactly like `sell_order.rs`'s
`SELL_ORDER_HEX`) against `ergotree-ir`'s real MIR types, run through
sigma-rust's real reducer for the differential test; this is the Lean side
`runCases` evaluates the same generated cases against. `fromConst`/
`targetConst` are EIP-5-style template constants (`ConstantPlaceholder`
ids 0/1, both `SInt`) — see that file's module docstring for what varying
them (and which boxes go into `INPUTS`) covers: found at index 0, found
later, not found, duplicates (first match at-or-after `from`), `from`
negative, and `from` at/past `INPUTS.size`.
-/
import ErgoTreeLean.Syntax
import ErgoTreeLean.Context
import ErgoTreeLean.Eval
import ErgoTreeLean.InlineFuns

namespace ErgoTreeLean.Contracts

open ErgoTreeLean

def collIndexOfTree : Expr :=
  .boolToSigmaProp
    (.binOp (.relation .eq)
      (.methodCall .inputs 12 26 [.selfBox, .constPlaceholder 0 .sInt])
      (.constPlaceholder 1 .sInt))

end ErgoTreeLean.Contracts
