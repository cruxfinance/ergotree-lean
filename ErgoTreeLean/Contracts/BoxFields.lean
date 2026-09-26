/-
The `box-fields` difftest family's tree: a hand-written, purpose-built
`Expr` (no compiled contract behind it — there's no ErgoScript source,
just a direct MIR construction, exactly the way `sell_order.rs`'s
`dummy_tree` builds a bare `Expr::Const` node directly in Rust) that
exercises `ExtractCreationInfo` and `ExtractRegisterAs` on the mandatory
registers R0-R3 of `SELF`, `INPUTS(0)` and `OUTPUTS(0)`.

ErgoScript-shaped reading:

```
sigmaProp(
  HEIGHT >= SELF.creationInfo._1 &&
  SELF.R0[Long].get == SELF.value &&
  SELF.R1[Coll[Byte]].get == SELF.propositionBytes &&
  INPUTS(0).R3[(Int, Coll[Byte])].get == INPUTS(0).creationInfo &&
  OUTPUTS(0).R2[Coll[(Coll[Byte], Long)]].get == OUTPUTS(0).tokens
)
```

Mirrors `difftest/src/box_fields.rs`'s `build_tree` node-for-node — that
file builds the identical tree directly against `ergotree-ir`'s real MIR
types, run through sigma-rust's real reducer for the differential test;
this is the Lean side `runCases` evaluates the same generated cases
against. No template constants (every operand is a `GlobalVars`/
literal-index lookup), so `box-fields` cases always have `consts = []`.
-/
import ErgoTreeLean.Syntax
import ErgoTreeLean.Context
import ErgoTreeLean.Eval
import ErgoTreeLean.InlineFuns

namespace ErgoTreeLean.Contracts

open ErgoTreeLean

def boxFieldsTree : Expr :=
  .boolToSigmaProp
    (.binOp (.logical .and)
      (.binOp (.relation .ge) .height (.selectField (.extractCreationInfo .selfBox) 1))
      (.binOp (.logical .and)
        (.binOp (.relation .eq)
          (.optionGet (.extractRegisterAs .selfBox 0 .sLong))
          (.extractAmount .selfBox))
        (.binOp (.logical .and)
          (.binOp (.relation .eq)
            (.optionGet (.extractRegisterAs .selfBox 1 (.sColl .sByte)))
            (.extractScriptBytes .selfBox))
          (.binOp (.logical .and)
            (.binOp (.relation .eq)
              (.optionGet
                (.extractRegisterAs (.byIndex .inputs (.const (.vInt 0)) none) 3
                  (.sTuple [.sInt, .sColl .sByte])))
              (.extractCreationInfo (.byIndex .inputs (.const (.vInt 0)) none)))
            (.binOp (.relation .eq)
              (.optionGet
                (.extractRegisterAs (.byIndex .outputs (.const (.vInt 0)) none) 2
                  (.sColl (.sTuple [.sColl .sByte, .sLong]))))
              (.propertyCall (.byIndex .outputs (.const (.vInt 0)) none) 99 8))))))

end ErgoTreeLean.Contracts
