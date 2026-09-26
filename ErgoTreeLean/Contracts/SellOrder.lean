/-
The `sellOrder` contract (see `contracts/sell-order.es`):

```
proveDlog(sellerPk) || sigmaProp(
  OUTPUTS(0).propositionBytes == sellerProp && OUTPUTS(0).value >= price
)
```

with EIP-5 template constants `sellerPk : GroupElement` (index 0),
`sellerProp : Coll[Byte]` (index 1), `price : Long` (index 2).
-/
import ErgoTreeLean.Syntax
import ErgoTreeLean.Context
import ErgoTreeLean.Eval
import ErgoTreeLean.InlineFuns
import ErgoTreeLean.Sigma
import ErgoTreeLean.Deserialize

namespace ErgoTreeLean.Contracts.SellOrder

open ErgoTreeLean

/-- Hex encoding of `sellOrder`'s compiled `expressionTree`, exactly as
    produced by the real Scala compiler (see `contracts/sell-order-eip5.json`). -/
def sellOrderHex : String :=
  "d801d601b2a5040000eb02cd7300d1ed93c27201730192c172017302"

/-- The EIP-5 template's `constTypes`, in `constantIndex` order:
    `sellerPk : GroupElement`, `sellerProp : Coll[Byte]`, `price : Long`
    (see `contracts/sell-order-eip5.json`). -/
def sellOrderConstTypes : List SType :=
  [.sGroupElement, .sColl .sByte, .sLong]

/-- `sellOrder`'s body, hand-transcribed from the opcode breakdown in the
    task brief. Constructor spelling follows the MIR-mirroring `Expr`
    redesign in `Syntax.lean` (`.constInt`/`.eq`/`.ge`/`.binAnd` ↦
    `.const (.vInt _)`/`.binOp (.relation .eq)`/`.binOp (.relation .ge)`/
    `.binOp (.logical .and)`); the tree itself is unchanged from phase 1. -/
def sellOrderTree : Expr :=
  .blockValue [(1, .byIndex .outputs (.const (.vInt 0)) none)]
    (.sigmaOr
      [ .createProveDlog (.constPlaceholder 0 .sGroupElement)
      , .boolToSigmaProp
          (.binOp (.logical .and)
            (.binOp (.relation .eq) (.extractScriptBytes (.valUse 1 .sBox)) (.constPlaceholder 1 (.sColl .sByte)))
            (.binOp (.relation .ge) (.extractAmount (.valUse 1 .sBox)) (.constPlaceholder 2 .sLong)))
      ])

/-- The compiled bytes parse to exactly the hand-transcribed tree above.
    This is the check that the rest of the development covers the real
    compiler's output, not a tree we made up. -/
theorem parse_matches : parseExprHex sellOrderHex sellOrderConstTypes = some sellOrderTree := by
  rfl

/-- `sellOrderTree` has no `FuncValue`-bound `ValDef`s at all, so
    `inlineFuns` is a no-op on it (still required to state `spendable`,
    per `Sigma.lean`'s design). Proved via `simp` (unfolding `inlineFuns`'s
    and its helpers' equation lemmas), not `rfl`: `inlineFuns`/`eval`/etc.
    are compiled via well-founded recursion (an explicit `termination_by`
    measure — see `Eval.lean`/`InlineFuns.lean`), which the kernel doesn't
    reduce through definitionally the way plain structural recursion does;
    only the equation-lemma-driven `simp` unfolding does. -/
theorem inlineFuns_sellOrderTree : inlineFuns sellOrderTree = some sellOrderTree := by
  simp [inlineFuns, sellOrderTree, rewriteExpr, rewriteDefs, rewriteExprList, isFuncValue]

/-- The EIP-5 template constants, in `constantIndex` order. `sellerProp`
    is lifted into the `Value` world via `bytesToVColl` (Coll[Byte] is
    `vColl .sByte [...]`, not a dedicated byte-string constructor — see
    `Syntax.lean`'s module docstring). -/
def consts (pk : List UInt8) (prop : List UInt8) (price : Int) : List Value :=
  [.vGroupElement pk, bytesToVColl prop, .vLong price]

/-! ### Two small `Value.beq` lemmas `eval_outputs_cons` needs

`extractScriptBytes`/the `sellerProp` constant are both lifted through
`bytesToVColl` (see `consts` above), so the tree's `Coll[Byte]` equality
check reduces through `Value.beq`'s `vColl` case (comparing `elemTpe` and
an element-wise `List.map (vByte ∘ signedByteVal)` equality), not a direct
`List UInt8` comparison the way phase 1's dedicated `vBytes` did. These
two lemmas bridge back to plain `List UInt8` equality: `signedByteVal` is
injective (`Coll[Byte]`'s signed-byte encoding is a bijection on `UInt8`),
so `bytesToVColl` is too. -/

private theorem signedByteVal_beq (a b : UInt8) : (signedByteVal a == signedByteVal b) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  unfold signedByteVal
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  by_cases hA : a.toNat ≥ 128 <;> by_cases hB : b.toNat ≥ 128 <;>
    simp only [hA, hB, if_true, if_false] <;>
    constructor <;> intro h <;>
    first
      | (apply UInt8.toNat.inj; omega)
      | (subst h; omega)
      | omega

private theorem bytesToVColl_beq (a b : List UInt8) :
    Value.beq (bytesToVColl a) (bytesToVColl b) = (a == b) := by
  unfold bytesToVColl
  simp only [Value.beq, SType.beq, Bool.true_and]
  induction a generalizing b with
  | nil => cases b <;> simp [Value.beqList]
  | cons x xs ih =>
    cases b with
    | nil => simp [Value.beqList]
    | cons y ys =>
      simp only [List.map_cons, Value.beqList, Value.beq, signedByteVal_beq, ih ys,
        List.cons_beq_cons]

/-! ### Evaluation, reduced

Two lemmas pinning down `eval` on `sellOrderTree`, one per shape of
`ctx.outputs` (the only field of `ctx` the tree inspects — `sellOrderTree`
never reads `SELF`/`HEIGHT`/`CONTEXT`, so every other `Context` field is
left universally quantified). Everything below is proved from these two.

`eval_outputs_cons`'s conclusion is an `if`-`then`-`else`, not the raw
`cor [proveDlog pk, trivial b]` phase 1 had: `SigmaOr`'s evaluator now
normalizes (`Cand.normalized`/`Cor.normalized`, mirroring sigma-rust
exactly — see `Eval.lean`'s `normalizeCor`), and a 2-item `cor` where the
second item is `trivial true` collapses to `trivial true` outright, while
`trivial false` gets dropped, leaving the bare `proveDlog pk` (not wrapped
in a `cor` at all). This is expected per the phase-2 brief, not a bug. -/

/-- With no outputs, `OUTPUTS(0)` is out of bounds and (since it is bound
    eagerly by the enclosing `BlockValue`, before either disjunct of the
    `||` is inspected) evaluation fails outright — see `no_outputs_unspendable`. -/
theorem eval_outputs_nil (pk prop : List UInt8) (price : Int) (ctx : Context)
    (houts : ctx.outputs = []) :
    eval (consts pk prop price) ctx [] sellOrderTree =
      Except.error (.error "byIndex: index out of bounds and no default") := by
  simp [eval, evalDefs, sellOrderTree, consts, houts, Except.bind, bind, pure, Pure.pure, Except.pure]

/-- With at least one output `o`, `sellOrderTree` reduces to the expected
    sigma-proposition, normalized (see module docstring). -/
theorem eval_outputs_cons (pk prop : List UInt8) (price : Int) (o : Box) (rest : List Box)
    (ctx : Context) (houts : ctx.outputs = o :: rest) :
    eval (consts pk prop price) ctx [] sellOrderTree =
      Except.ok (.vSigmaProp
        (if o.propositionBytes == prop && decide (o.value ≥ price) then
           SigmaBoolean.trivial true
         else
           SigmaBoolean.proveDlog pk)) := by
  simp [eval, evalDefs, evalList, sellOrderTree, consts, houts, List.map_cons,
    List.getElem?_cons_zero, sameKindRaw, Value.numKind,
    Except.bind, bind, pure, Pure.pure, Except.pure]
  rw [bytesToVColl_beq]
  cases hb : (o.propositionBytes == prop) <;> cases hv : decide (price ≤ o.value) <;>
    simp_all [toSigmaProps, normalizeCor, isTrivial, Except.bind, bind, pure, Pure.pure, Except.pure]

/-! ### Headline theorems -/

/-- If the contract is spendable and the seller did *not* sign, then it must
    be because the "pay the seller" branch held: the first output really
    does pay `sellerProp` at least `price`. -/
theorem seller_paid (pk prop : List UInt8) (price : Int) (ctx : Context) (signers : List PK)
    (hspend : spendable (consts pk prop price) ctx signers sellOrderTree) (hnotSigner : pk ∉ signers) :
    ∃ o, ctx.outputs.head? = some o ∧ o.propositionBytes = prop ∧ o.value ≥ price := by
  obtain ⟨t, sb, hinline, heval, hholds⟩ := hspend
  rw [inlineFuns_sellOrderTree] at hinline
  injection hinline with hinline
  subst hinline
  cases houts : ctx.outputs with
  | nil => rw [eval_outputs_nil _ _ _ ctx houts] at heval; cases heval
  | cons o rest =>
    rw [eval_outputs_cons _ _ _ _ _ ctx houts] at heval
    injection heval with heval
    injection heval with heval
    subst heval
    by_cases hb : o.propositionBytes == prop && decide (o.value ≥ price)
    · simp only [hb, if_true] at hholds
      rw [Bool.and_eq_true] at hb
      exact ⟨o, by simp, eq_of_beq hb.1, of_decide_eq_true hb.2⟩
    · simp only [hb, holds] at hholds
      exact absurd hholds hnotSigner

/-- Anyone can spend by paying the seller: knowing no secrets at all
    (`signers = []`) suffices once the output actually pays `sellerProp`
    at least `price`. -/
theorem anyone_can_fill (pk prop : List UInt8) (price : Int) (ctx : Context) (o : Box)
    (hhead : ctx.outputs.head? = some o) (hprop : o.propositionBytes = prop) (hval : o.value ≥ price) :
    spendable (consts pk prop price) ctx [] sellOrderTree := by
  cases houts : ctx.outputs with
  | nil => rw [houts] at hhead; simp at hhead
  | cons o' rest =>
    rw [houts] at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    -- hhead : o' = o
    refine ⟨sellOrderTree, .trivial true, inlineFuns_sellOrderTree, ?_, ?_⟩
    · rw [eval_outputs_cons _ _ _ _ _ ctx houts]
      have hb : o'.propositionBytes == prop && decide (o'.value ≥ price) := by
        rw [hhead]; simp [hprop, hval]
      simp [hb]
    · simp [holds]

/-- The seller can always cancel by signing, as long as there is at least
    one output for `OUTPUTS(0)` to resolve to (see `no_outputs_unspendable`
    for why that side condition is genuinely needed). -/
theorem seller_can_cancel (pk prop : List UInt8) (price : Int) (ctx : Context) (signers : List PK)
    (houtsNe : ctx.outputs ≠ []) (hsigner : pk ∈ signers) :
    spendable (consts pk prop price) ctx signers sellOrderTree := by
  cases houts : ctx.outputs with
  | nil => exact absurd houts houtsNe
  | cons o rest =>
    by_cases hb : o.propositionBytes == prop && decide (o.value ≥ price)
    · refine ⟨sellOrderTree, .trivial true, inlineFuns_sellOrderTree, ?_, ?_⟩
      · rw [eval_outputs_cons _ _ _ _ _ ctx houts]; simp [hb]
      · simp [holds]
    · refine ⟨sellOrderTree, .proveDlog pk, inlineFuns_sellOrderTree, ?_, ?_⟩
      · rw [eval_outputs_cons _ _ _ _ _ ctx houts]; simp [hb]
      · simp [holds, hsigner]

/-- A somewhat surprising consequence of eager `ValDef` evaluation: with no
    outputs at all, the contract is unspendable *even by the seller*,
    because `OUTPUTS(0)` fails before either disjunct of the `||` is ever
    considered. -/
theorem no_outputs_unspendable (pk prop : List UInt8) (price : Int) (ctx : Context) (signers : List PK)
    (houts : ctx.outputs = []) :
    ¬ spendable (consts pk prop price) ctx signers sellOrderTree := by
  rintro ⟨t, sb, hinline, heval, -⟩
  rw [inlineFuns_sellOrderTree] at hinline
  injection hinline with hinline
  subst hinline
  rw [eval_outputs_nil _ _ _ ctx houts] at heval
  cases heval

/-! ### Examples -/

private def examplePk : List UInt8 := [0x02, 0xAA]
private def exampleProp : List UInt8 := [0xDE, 0xAD, 0xBE, 0xEF]
private def examplePrice : Int := 1000000000

private def exampleSelf : Box := { id := [], value := 0, propositionBytes := [], tokens := [], registers := [] }

private def mkCtx (outputs : List Box) : Context :=
  { selfBox := exampleSelf, inputs := [], outputs := outputs, dataInputs := [], height := 0, extension := [] }

-- A context that pays the seller enough: the "anyone can fill" branch.
#eval eval (consts examplePk exampleProp examplePrice)
  (mkCtx [{ id := [], value := 2000000000, propositionBytes := exampleProp, tokens := [], registers := [] }]) [] sellOrderTree

-- A context that pays the wrong party: only a seller signature could
-- spend this (which `eval` alone cannot show — that is `holds`'s job).
#eval eval (consts examplePk exampleProp examplePrice)
  (mkCtx [{ id := [], value := 2000000000, propositionBytes := [0x00], tokens := [], registers := [] }]) [] sellOrderTree

-- No outputs: unspendable regardless of signatures.
#eval eval (consts examplePk exampleProp examplePrice) (mkCtx []) [] sellOrderTree

end ErgoTreeLean.Contracts.SellOrder
