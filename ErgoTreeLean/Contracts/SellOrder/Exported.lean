/-
GENERATED FILE. Do not hand-edit.

Produced by the Rust exporter (`exporter/`) from the EIP-5
`expressionTree` bytes:

  d801d601b2a5040000eb02cd7300d1ed93c27201730192c172017302

Regenerate with:

  cd exporter && cargo run --release -- <path-to-eip5.json> \
      --lean-name exportedTree --namespace ErgoTreeLean.Contracts.SellOrder.Exported -o <output path>
-/
import ErgoTreeLean.Syntax

namespace ErgoTreeLean.Contracts.SellOrder.Exported

open ErgoTreeLean

def exportedTree : Expr :=
.blockValue [(1, (.byIndex .outputs (.const (Value.vInt 0)) none))] (.sigmaOr [.createProveDlog (.constPlaceholder 0 SType.sGroupElement), .boolToSigmaProp (.binOp (BinOpKind.logical LogicalOp.and) (.binOp (BinOpKind.relation RelationOp.eq) (.extractScriptBytes (.valUse 1 SType.sBox)) (.constPlaceholder 1 (SType.sColl SType.sByte))) (.binOp (BinOpKind.relation RelationOp.ge) (.extractAmount (.valUse 1 SType.sBox)) (.constPlaceholder 2 SType.sLong)))])

end ErgoTreeLean.Contracts.SellOrder.Exported
