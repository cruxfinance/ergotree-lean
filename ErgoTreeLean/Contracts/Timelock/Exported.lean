/-
GENERATED FILE. Do not hand-edit.

Produced by the Rust exporter (`exporter/`) from the full
on-chain ErgoTree bytes (header + constants + expression):

  100204a00b08cd020e814ace36202c238f6e2ce66d69a1036cb3a6a3318afcecd5af64a5b66fd274ea02d192a39a8cc7a70173007301

Regenerate with:

  cd exporter && cargo run --release -- --ergotree <hex-or-@file> \
      --lean-name timelockTree --namespace ErgoTreeLean.Contracts.Timelock.Exported -o <output path>
-/
import ErgoTreeLean.Syntax

namespace ErgoTreeLean.Contracts.Timelock.Exported

open ErgoTreeLean

def timelockTree : Expr :=
.sigmaAnd [.boolToSigmaProp (.binOp (BinOpKind.relation RelationOp.ge) .height (.binOp (BinOpKind.arith ArithOp.plus) (.selectField (.extractCreationInfo .selfBox) 1) (.constPlaceholder 0 SType.sInt))), .constPlaceholder 1 SType.sSigmaProp]

def timelockTreeConsts : List Value := [(Value.vInt 720), (Value.vSigmaProp (SigmaBoolean.proveDlog [2, 14, 129, 74, 206, 54, 32, 44, 35, 143, 110, 44, 230, 109, 105, 161, 3, 108, 179, 166, 163, 49, 138, 252, 236, 213, 175, 100, 165, 182, 111, 210, 116]))]

end ErgoTreeLean.Contracts.Timelock.Exported
