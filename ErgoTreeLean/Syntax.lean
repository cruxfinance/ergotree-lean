/-
Deep-embedded syntax for ErgoTree, designed to mirror sigma-rust's MIR
(`ergotree_ir::mir::expr::Expr`, crate `ergotree-ir 0.28`) as closely as
practical: same node granularity, same field order, constructor names are
the lowerCamelCase spelling of the MIR type/variant names. This makes the
Rust exporter (`exporter/`) a close-to-trivial structural map from MIR to
this `Expr`, and keeps the two easy to audit against each other.

Two deliberate, documented departures from a literal 1:1 mirror:

1. `BlockValue.items : Vec<Expr>` holds a list of `Expr::ValDef` nodes in
   MIR; here `blockValue` takes `List (Nat × Expr)` directly (an id/rhs
   pair per `ValDef`) rather than a separate `valDef` constructor wrapped
   in a list. This was already the shape used by the hand-written
   `sellOrderTree`/parser and keeps `eval`'s environment-threading simple;
   every `BlockValue` produced by the real compiler has exactly this shape
   (ValDefs only), so nothing is lost.
2. MIR's `Expr::GlobalVars(GlobalVars)` (an inner enum with `Inputs`,
   `Outputs`, `Height`, `SelfBox`, `MinerPubKey`, `GroupGenerator`) is
   flattened into dedicated leaf constructors (`outputs`, `height`,
   `selfBox`) for the cases this development actually uses, rather than a
   `globalVar (gv : GlobalVars)` wrapper — this is what the original
   sell-order `Expr` already did for `outputs`.

A note on `&&`/`allOf`: sigma-rust does **not** have a dedicated "BinAnd"
MIR node. `&&` between two `SBoolean` expressions compiles to
`Expr::BinOp(BinOp { kind: BinOpKind::Logical(LogicalOp::And), .. })` —
the same node family as `==`/`>=`/etc, just with a `Logical` kind instead
of `Relation`. The *separate* `Expr::And`/`Expr::Or` MIR nodes (from
sigma-rust's `mir::and`/`mir::or`) are for the n-ary `allOf(coll)`/
`anyOf(coll)` builtins over a `Coll[Boolean]`, mirrored here as `andOf`/
`orOf`.

**`SigmaProp && SigmaProp` / `SigmaProp || SigmaProp`.** ErgoScript's `&&`/
`||` between two `SigmaProp`-typed operands (e.g. `sigmaProp(bool) &&
someProof` in a contract with a sigma-proposition guard) is *not* lowered
to `BinOp(Logical, ...)` — the compiler lowers it directly to the
dedicated `SigmaAnd`/`SigmaOr` MIR nodes (`sigma_and.rs`/`sigma_or.rs`;
`BinOp`'s `Logical` kind only ever sees `SBoolean` operands in practice —
`bin_op.rs`'s `LogicalOp::And`/`Or` call `try_extract_into::<bool>()`,
which would error on a `SigmaProp` operand). So a downstream contract's
`sigmaAnd [boolToSigmaProp (...), createProveDlog (...)]` for
`sigmaProp(...) && someProof` is exactly what the real compiler emits.

## Numeric semantics, `Box`/`Context`/`Value`

`Long`/`Int`/etc are checked, fixed-width arithmetic, not unbounded `Int`,
and `Box` carries registers/tokens — see `Numeric.lean` for
the fixed-width-checked-arithmetic helpers `Eval.lean`'s `BinOp`/`Upcast`/
`Downcast`/`Negation` cases use; `Value`'s numeric constructors still carry
a plain Lean `Int` (there's no dependent `Fin`/`BitVec` doing double duty
as both value and type tag), but `eval`'s own arithmetic cannot
*produce* an out-of-range numeric `Value` — every arithmetic case
range-checks its result before returning it, exactly like sigma-rust's
`checked_add`/`checked_sub`/... erroring on `None`.

**No dedicated `Coll[Byte]` representation.** sigma-rust's own `Value`
special-cases `Coll[Byte]` as `CollKind::NativeColl` (vs. `WrappedColl` for
every other element type) purely as a storage optimization — semantically
inert, since every construction site (`CollKind::from_collection`, et al.)
routes `SByte` into `NativeColl` *unconditionally*, so within a single
correct evaluator a `Coll[Byte]` is *always* represented the same way, and
comparing two of them never actually exercises the "different Rust enum
variant" case that would make `#[derive(PartialEq)]` on `CollKind` see them
as unequal. This development has only one representation to begin with
(`vColl .sByte [.vByte _, ...]`), so that invariant holds trivially — no
separate `vBytes` constructor is needed. `Box.propositionBytes`/`Box.id`/
`Box.tokens`' token-id component stay raw `List UInt8` (matching `Box`'s
own field types below), converted to `vColl .sByte [...]` only when
`Eval.lean` extracts them into the `Value` world (`ExtractScriptBytes`,
`ExtractId`, `PropertyCall Box.tokens`); this conversion must sign-extend
each byte as sigma-rust's `i8` does (`Coll[Byte]`'s elements are *signed* —
see `Numeric.lean`'s `signedByteVal`), not treat them as unsigned `0..255`.

**`Box` and `Value` are mutually recursive** (a register can hold any
`Value`, including a nested `Box` — a downstream contract's `R5 : Box`,
for example), so they're declared together in one `mutual ... end` block. Lean 4's
`structure` command *can* participate in a `mutual` block (tested
separately), so `Box` stays an ordinary `structure` with real field
projections, not a hand-rolled single-constructor `inductive`.

**Manual, non-`partial`, structurally-recursive `beq`.** `SType`/
`SigmaBoolean`/`Value`/`Box` all get a hand-written `beq` via `mutual`
blocks with an explicit list-recursion helper (`Type.beqList`) alongside
the scalar one, mirroring how `Eval.lean` itself already avoids routing
recursion through `List.map`/`List.all`/`List.zip` (`evalDefs`/`evalList`
are dedicated helpers, not `List.map eval`). This isn't just style: a
`partial def` doesn't get the equation lemmas `simp`/`rfl` need to unfold
it inside a proof (this repo's theorems, including
`SellOrder.lean`'s, unfold `eval`/`Value.beq` via `simp`), and deriving
`DecidableEq` automatically fails outright on `SType`/`Value` (both have a
constructor holding `List <the type itself>`, which the derive handler
doesn't support) — confirmed by trying it. Two derived-`PartialEq`
subtleties from sigma-rust's real `Value`/`CollKind` are mirrored exactly:
`vColl`'s `beq` compares `elemTpe` too (not just elements — `CollKind::
WrappedColl` derives `PartialEq` over both fields), while `vOption`'s does
*not* compare `elemTpe` (sigma-rust's actual runtime `Value::Opt` carries no
element-type field at all, unlike `CollKind`; `elemTpe` here exists only
for `GetVar`/`ExtractRegisterAs`-style typing, see `typeOf` below). -/

namespace ErgoTreeLean

/-- Mirrors `ergotree_ir::types::stype::SType`. Only the cases that occur
    in the contracts this development covers are given real shape (nested
    `SColl`/`SOption`/`STuple`/`SFunc` are still modelled structurally so
    that e.g. `Coll[(Coll[Byte], Long)]` round-trips faithfully). -/
inductive SType where
  | sBoolean
  | sByte
  | sShort
  | sInt
  | sLong
  | sBigInt
  | sGroupElement
  | sSigmaProp
  | sBox
  | sAvlTree
  | sContext
  | sHeader
  | sPreHeader
  | sGlobal
  | sUnit
  | sAny
  | sOption (t : SType)
  | sColl (t : SType)
  | sTuple (ts : List SType)
  | sFunc (dom : List SType) (range : SType)
deriving Repr

mutual
/-- Structural equality on `SType` (`deriving DecidableEq` fails on this
    type — it has a constructor, `sTuple`/`sFunc`, holding `List SType` —
    so this is hand-written via an explicit list-recursion helper; see
    module docstring). Needed by `Value.beq`'s `vColl`/`vOption` cases. -/
def SType.beq : SType → SType → Bool
  | .sBoolean, .sBoolean => true
  | .sByte, .sByte => true
  | .sShort, .sShort => true
  | .sInt, .sInt => true
  | .sLong, .sLong => true
  | .sBigInt, .sBigInt => true
  | .sGroupElement, .sGroupElement => true
  | .sSigmaProp, .sSigmaProp => true
  | .sBox, .sBox => true
  | .sAvlTree, .sAvlTree => true
  | .sContext, .sContext => true
  | .sHeader, .sHeader => true
  | .sPreHeader, .sPreHeader => true
  | .sGlobal, .sGlobal => true
  | .sUnit, .sUnit => true
  | .sAny, .sAny => true
  | .sOption a, .sOption b => SType.beq a b
  | .sColl a, .sColl b => SType.beq a b
  | .sTuple as, .sTuple bs => SType.beqList as bs
  | .sFunc ds1 r1, .sFunc ds2 r2 => SType.beqList ds1 ds2 && SType.beq r1 r2
  | _, _ => false

def SType.beqList : List SType → List SType → Bool
  | [], [] => true
  | x :: xs, y :: ys => SType.beq x y && SType.beqList xs ys
  | _, _ => false
end

instance : BEq SType := ⟨SType.beq⟩

/-- A sigma-proposition, i.e. the reduced form of a sigma-expression after
    evaluation. Represents *what must be proved*, not a proof itself.
    Mirrors `ergotree_ir::sigma_protocol::sigma_boolean::SigmaBoolean`
    restricted to the variants this development's contracts produce
    (`TrivialProp`, `ProveDlog`, and `SigmaConjecture::{Cand,Cor}`). -/
inductive SigmaBoolean where
  /-- A statically-known truth value (from `BoolToSigmaProp` on a plain
      bool, or from `Cand.normalized`/`Cor.normalized` collapsing to a
      constant — see `Eval.lean`). -/
  | trivial (b : Bool)
  /-- `proveDlog pk`: knowledge of the discrete log of `pk`.
      `GroupElement` is modelled opaquely as its encoded bytes. -/
  | proveDlog (pk : List UInt8)
  /-- `SigmaOr`/`COR`: satisfied if any child is satisfied. `Eval.lean`
      only ever constructs this *normalized* (`Cor.normalized`): a real
      `cor` never holds 0/1 items or a `trivial` item — see `cor.rs`. -/
  | cor (items : List SigmaBoolean)
  /-- `SigmaAnd`/`CAND`: satisfied if every child is satisfied. Likewise
      only ever constructed normalized (`Cand.normalized`). -/
  | cand (items : List SigmaBoolean)
  /-- `SigmaConjecture::Cthreshold` / ErgoScript's `atLeast(k, items)`: a
      k-of-n threshold — satisfied iff at least `k` of `items` are
      satisfied. Mirrors `ergotree-ir`'s `Cthreshold { k : u8, children }`
      (`Eval.lean`'s `cthresholdReduce` builds this only in the
      exact normalized shape `Cthreshold::reduce` would — see there). -/
  | cthreshold (k : Nat) (items : List SigmaBoolean)
deriving Repr

mutual
/-- Structural equality mirroring `SigmaBoolean`'s derived `PartialEq`
    (order-sensitive list comparison, no re-normalization — two
    *unnormalized* but logically-equivalent `SigmaBoolean`s are not `beq`,
    exactly like Rust's derived `PartialEq`; not currently exercised by any
    contract's `==`/`!=`, kept for completeness of `Value.beq`). -/
def SigmaBoolean.beq : SigmaBoolean → SigmaBoolean → Bool
  | .trivial a, .trivial b => a == b
  | .proveDlog a, .proveDlog b => a == b
  | .cor xs, .cor ys => SigmaBoolean.beqList xs ys
  | .cand xs, .cand ys => SigmaBoolean.beqList xs ys
  | .cthreshold k1 xs, .cthreshold k2 ys => k1 == k2 && SigmaBoolean.beqList xs ys
  | _, _ => false

def SigmaBoolean.beqList : List SigmaBoolean → List SigmaBoolean → Bool
  | [], [] => true
  | x :: xs, y :: ys => SigmaBoolean.beq x y && SigmaBoolean.beqList xs ys
  | _, _ => false
end

instance : BEq SigmaBoolean := ⟨SigmaBoolean.beq⟩

/-- VLQ-encode a value already known to be a `u16` (top-bit-continuation,
    low 7 bits per byte, least-significant group first) — mirrors
    `sigma-ser`'s `WriteSigmaVlqExt::put_u16` (`vlq_encode.rs`:
    `put_u16(v) = put_u64(v as u64)`, the same base-128 VLQ
    `Deserialize.lean`'s `readVLQ` decodes, just unsigned and with no
    zigzag step). `n % 65536` mirrors the `as u16` truncation every
    call site below performs before encoding (`Cand`/`Cor`'s
    `items.len() as u16`, `Cthreshold`'s `k as u16`/`children.len() as
    u16` — `sigmaboolean.rs`), so this is total and needs no fuel: a
    `u16` value is at most 65535, which needs at most 3 VLQ bytes
    (⌈16/7⌉ = 3), so the three cases below (1, 2 or 3 bytes) are
    exhaustive and there is no further recursive case to write. -/
def vlqEncodeU16 (n : Nat) : List UInt8 :=
  let n := n % 65536
  if n < 128 then
    [UInt8.ofNat n]
  else
    let b0 := UInt8.ofNat (n % 128 + 128)
    let n1 := n / 128
    if n1 < 128 then
      [b0, UInt8.ofNat n1]
    else
      let b1 := UInt8.ofNat (n1 % 128 + 128)
      let n2 := n1 / 128
      -- `n ≤ 65535 ⇒ n1 = n / 128 ≤ 511 ⇒ n2 = n1 / 128 ≤ 3 < 128`, so
      -- this is always the last byte (no fourth VLQ byte is ever
      -- needed for a `u16`).
      [b0, b1, UInt8.ofNat n2]

mutual
/-- `SigmaBoolean`'s real wire encoding, i.e. everything `sigmaboolean.rs`'s
    `impl SigmaSerializable for SigmaBoolean` writes for one node: a 1-byte
    op code (`self.op_code()`) followed by that constructor's payload.
    Used by `propBytes` below (`SigmaProp::prop_bytes()`,
    `sigma_boolean.rs:302`, always serializes the *whole* `SigmaBoolean`
    this way, header and type code aside). Op codes are
    `LAST_CONSTANT_CODE (112) + shift` (`op_code.rs`'s `new_op_code`):
    `ProveDlog` shift 93 ↦ 205 = `0xcd`; `Cand`/`And` shift 38 ↦ 150 =
    `0x96`; `Cor`/`Or` shift 39 ↦ 151 = `0x97`; `Cthreshold`/`Atleast`
    shift 40 ↦ 152 = `0x98`; `TrivialProp` has no `new_op_code` entry of
    its own — `TRIVIAL_PROP_FALSE`/`_TRUE` are literal `OpCode::new(210)`/
    `new(211)` (`0xd2`/`0xd3`) in `op_code.rs`, besides which `TrivialProp`
    writes no further bytes. `ProveDlog`'s payload is `pk` exactly as
    stored (an `EcPoint`'s `sigma_serialize` writes its 33-byte SEC1
    compressed encoding with no length prefix — `ec_point.rs`'s
    `scorex_serialize`/`GROUP_SIZE`; this model's `GroupElement` is
    already exactly those 33 bytes, see `Syntax.lean`'s `proveDlog`
    docstring, so no encoding step is needed here beyond appending it).
    `Cand`/`Cor`'s payload is `put_u16(items.len())` (a VLQ, *not* 2 raw
    bytes — see `vlqEncodeU16`) followed by each item serialized in
    order; `Cthreshold`'s is `put_u16(k)` then `put_u16(children.len())`
    then each child. -/
def SigmaBoolean.serialize : SigmaBoolean → List UInt8
  | .trivial false => [0xd2]
  | .trivial true => [0xd3]
  | .proveDlog pk => (0xcd : UInt8) :: pk
  | .cor items => (0x97 : UInt8) :: vlqEncodeU16 items.length ++ SigmaBoolean.serializeList items
  | .cand items => (0x96 : UInt8) :: vlqEncodeU16 items.length ++ SigmaBoolean.serializeList items
  | .cthreshold k items =>
      (0x98 : UInt8) :: vlqEncodeU16 k ++ vlqEncodeU16 items.length ++ SigmaBoolean.serializeList items

def SigmaBoolean.serializeList : List SigmaBoolean → List UInt8
  | [] => []
  | sb :: rest => SigmaBoolean.serialize sb ++ SigmaBoolean.serializeList rest
end

/-- `somePk.propBytes` (`SigmaPropBytes`'s result, `Eval.lean`): the exact
    bytes `SigmaProp::prop_bytes()` produces (`sigma_boolean.rs:302`) —
    the `SigmaBoolean` wrapped as an `ErgoTree`'s sole root expression
    (`Constant { tpe: SSigmaProp, .. }`) and serialized whole. Traced
    through `ErgoTree::try_from(Expr)` (`ergo_tree.rs`): a bare
    `Expr::Const` of type `SSigmaProp` gets header `ErgoTreeHeader::v0(false)`
    — version 0, *no* constant segregation, *no* size flag, i.e. a single
    header byte `0x00` — so `ErgoTree::sigma_serialize` writes just that
    byte (no constants segment, `has_size` false) followed by the root
    `Expr::Const`'s own serialization with no constant store installed
    (`expr.rs`'s `Expr::Const` case, `None` branch: writes the `Constant`
    directly, not a placeholder). A `Constant`'s serialization
    (`constant.rs`) is its `SType` (a single type-code byte —
    `SSigmaProp`'s is `8 = 0x08`, `types.rs`) followed by
    `DataSerializer::sigma_serialize`, which for `Literal::SigmaProp(sp)`
    is exactly `sp.value().sigma_serialize(w)` (`data.rs`) — i.e.
    `SigmaBoolean.serialize` above, with no extra framing. Net layout:
    `0x00 ++ 0x08 ++ <SigmaBoolean.serialize sb>` — e.g. `proveDlog pk`
    is `[0x00, 0x08, 0xcd] ++ pk`.

    **Never errors for any shape this model can build.** `prop_bytes()`
    returns `Result<Vec<u8>, ErgoTreeError>`, but every step on this path
    is infallible for a bare `Const(SSigmaProp)` root: `ErgoTree::new`
    with `is_constant_segregation = false` just wraps the expression
    (`ergo_tree.rs`'s `else` branch — no serialize/parse round-trip, so
    no parse error is possible), and every `sigma_serialize` call from
    there down writes to an in-memory `Vec<u8>` (`io::Write` on a `Vec`
    never fails) with no VLQ/count encoding step that can itself fail —
    `put_u16` casts its `usize`/`u8` argument to `u16` with Rust's `as`
    (silent truncation, never a panic), which `vlqEncodeU16`'s `n % 65536`
    mirrors exactly. So this function is total and needs no `Except`. -/
def SigmaBoolean.propBytes (sb : SigmaBoolean) : List UInt8 :=
  (0x00 : UInt8) :: (0x08 : UInt8) :: sb.serialize

/-- Mirrors `ergotree_ir::mir::bin_op::ArithOp`. -/
inductive ArithOp where
  | plus | minus | multiply | divide | modulo | max | min
deriving Repr

/-- Mirrors `ergotree_ir::mir::bin_op::RelationOp`. -/
inductive RelationOp where
  | eq | neq | ge | gt | le | lt
deriving Repr

/-- Mirrors `ergotree_ir::mir::bin_op::LogicalOp`. -/
inductive LogicalOp where
  | and | or | xor
deriving Repr

/-- Mirrors `ergotree_ir::mir::bin_op::BitOp`. -/
inductive BitOp where
  | bitOr | bitAnd | bitXor
deriving Repr

/-- Mirrors `ergotree_ir::mir::bin_op::BinOpKind`. -/
inductive BinOpKind where
  | arith (op : ArithOp)
  | relation (op : RelationOp)
  | logical (op : LogicalOp)
  | bit (op : BitOp)
deriving Repr

mutual

/-- `Box` and `Value` are mutually recursive: a register (`Box.registers`)
    can hold any `Value`, including a `vBox` (a downstream contract's
    `R5 : Box` register, for example). Lean 4's `structure` command can
    participate in a `mutual`
    block, so `Box` stays a real `structure` (ordinary `{ field := v, ... }`
    construction and `b.field` projections), not a hand-rolled
    single-constructor `inductive`.

    Runtime values, mirroring `ergotree_ir::mir::value::Value` restricted to
    the variants this development's contracts produce. See the module
    docstring for the numeric-width and "no dedicated `Coll[Byte]`" design. -/
inductive Value where
  | vUnit
  | vBool (b : Bool)
  | vByte (v : Int)
  | vShort (v : Int)
  | vInt (v : Int)
  | vLong (v : Int)
  | vBigInt (v : Int)
  /-- `GroupElement`, modelled opaquely as its encoded bytes. -/
  | vGroupElement (g : List UInt8)
  | vSigmaProp (sb : SigmaBoolean)
  | vBox (b : Box)
  /-- A collection (including `Coll[Byte]`, as `vColl .sByte [.vByte _,
      ...]` — see module docstring). Carries its element `SType` so that an
      empty collection is still well-typed, matching `CollKind::
      WrappedColl`'s `elem_tpe` field in sigma-rust. -/
  | vColl (elemTpe : SType) (vs : List Value)
  | vTuple (vs : List Value)
  /-- `Value::Opt` in sigma-rust carries *no* element-type field at
      runtime; `elemTpe` here is kept only so `GetVar`/`ExtractRegisterAs`
      have something to report as the result's `SOption T` type — `beq`
      does not compare it (see module docstring). -/
  | vOption (elemTpe : SType) (v : Option Value)
deriving Repr

/-- A box, mirroring the fields of `ergotree_ir::chain::ergo_box::ErgoBox`
    that the contracts this development covers inspect. `id` is an opaque
    field
    (`blake2b256` hashing of the box's serialized bytes is not modelled;
    sigma-rust computes it once at box-*construction* time, never inside
    `eval` — `ExtractId` just projects this field back out, matching
    `extract_id.rs`). `registers` holds the **non-mandatory** registers
    R4..R9 only, keyed by numeric index; absent = not present. Mirrors
    `get_register`/`extract_reg_as.rs`: **no type-check against a
    register's declared `elemTpe` is performed** — a register can hold any
    `Value`, and a mismatch only surfaces later, when that `Value` is used
    somewhere requiring a specific shape. This is a deliberate, faithful
    mirror of sigma-rust (`extract_reg_as.rs` does `Value::from(c.v)` with
    no type comparison), not a shortcut. -/
structure Box where
  id : List UInt8
  value : Int
  propositionBytes : List UInt8
  tokens : List (List UInt8 × Int)
  registers : List (Nat × Value)
  /-- Mirrors `ErgoBox.creation_height : u32` (`chain/ergo_box.rs`): the
      height, as declared by the box's creator, of the transaction that
      created it. Read back as an `SInt` by R3/`ExtractCreationInfo`
      (`creation_info()`'s `self.creation_height as i32`) — like `value`
      above, this model stores the field as a plain `Int` and does not
      range-check it (a real chain's height never approaches 2^31, so the
      `u32`→`i32` two's-complement wraparound `as i32` can in principle
      trigger is not modelled). Default `0` keeps every `{ id := …, value
      := …, … }` literal predating creation info compiling unchanged. -/
  creationHeight : Int := 0
  /-- Mirrors `ErgoBox.transaction_id : TxId` (`chain/tx_id.rs`), the id of
      the transaction that created this box — a `Digest32`, i.e. exactly
      32 bytes. Default: 32 zero bytes, mirroring `TxId::zero()`. -/
  transactionId : List UInt8 := List.replicate 32 (0 : UInt8)
  /-- Mirrors `ErgoBox.index : u16` (`chain/ergo_box.rs`): this box's
      output index (0..65535) in the transaction that created it. Default
      `0`. No range check (see `creationHeight`'s docstring). -/
  index : Int := 0
deriving Repr

end

/-- Big-endian encoding of a `u16` (`Box.index`), matching Rust's
    `u16::to_be_bytes()` — the tail of `creation_info()`'s byte layout
    (`Eval.lean`'s `Box.register`, R3/`ExtractCreationInfo`:
    `transactionId ++ indexBEBytes index`). Truncates to 16 bits via
    `% 65536` (two's-complement `u16` wraparound); `index` is never
    actually outside `0..65535` in a well-formed box. -/
def Box.indexBEBytes (idx : Int) : List UInt8 :=
  let n := idx.toNat % 65536
  [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- Expression AST, mirroring `ergotree_ir::mir::expr::Expr` (see module
    docstring for the departures from a literal 1:1 mirror). Only the MIR
    node kinds that occur in the contracts covered by this repo (e.g.
    `sell-order`) are given constructors; the exporter fails loudly on
    anything else rather than emitting an approximation.
    Declared after `Value`/`Box` (rather than before, or inside their
    `mutual` block) since `Expr.const` needs `Value` but nothing in
    `Value`/`Box` needs `Expr` back — a one-directional dependency, not a
    mutual one. -/
inductive Expr where
  /-- `Const`: an inline literal constant. -/
  | const (v : Value)
  /-- `ConstPlaceholder`: an EIP-5 template constant, supplied out-of-band
      at spend time (never inlined by the exporter). -/
  | constPlaceholder (id : Nat) (tpe : SType)
  /-- `BlockValue`: evaluate each `ValDef` in order, extending the
      environment, then evaluate `result` (see module docstring). -/
  | blockValue (defs : List (Nat × Expr)) (result : Expr)
  /-- `ValUse`: look up a previously bound `ValDef`/`FuncArg` by id. -/
  | valUse (id : Nat) (tpe : SType)
  /-- `GlobalVars::Outputs`: the transaction's output boxes. -/
  | outputs
  /-- `GlobalVars::Height`: the current blockchain height (an `SInt` in
      sigma-rust — see `eval/global_vars.rs`: `ctx.height as i32`). -/
  | height
  /-- `GlobalVars::SelfBox`: the box currently being spent. -/
  | selfBox
  /-- `GlobalVars::Inputs`: the transaction's input boxes
      (`eval/global_vars.rs`'s `GlobalVars::Inputs` arm). -/
  | inputs
  /-- `Expr::Context` (bare `CONTEXT` global, type `SContext`).
      Has no sensible standalone evaluation in this model — it only ever
      appears as the receiver of `PropertyCall(101.1 dataInputs)`, which
      `Eval.lean` matches on the *syntax* `.propertyCall .context 101 1`
      directly (mirroring `scontext.rs`'s `DATA_INPUTS_EVAL_FN`) without
      ever evaluating a bare `.context` to a `Value` — see `Eval.lean`. -/
  | context
  /-- `ByIndex`: index into a collection, with an optional default on
      out-of-bounds access. -/
  | byIndex (coll idx : Expr) (default : Option Expr)
  /-- `SigmaOr`: eager sigma-disjunction of two or more sigma-propositions
      (also how ErgoScript's `SigmaProp || SigmaProp` compiles). -/
  | sigmaOr (items : List Expr)
  /-- `SigmaAnd`: eager sigma-conjunction of two or more sigma-propositions
      (also how ErgoScript's `SigmaProp && SigmaProp` compiles). -/
  | sigmaAnd (items : List Expr)
  /-- `CreateProveDlog`: build a `proveDlog` sigma-proposition from a
      `GroupElement`. -/
  | createProveDlog (e : Expr)
  /-- `BoolToSigmaProp`: lift a boolean into a (trivial) sigma-proposition. -/
  | boolToSigmaProp (e : Expr)
  /-- `SigmaPropBytes`: `somePk.propBytes` — the serialized bytes of a
      `SigmaProp` value. Mirrors `mir/sigma_prop_bytes.rs`; see
      `SigmaBoolean.propBytes` for the exact byte layout, which
      `Eval.lean`'s case for this node reads straight off the evaluated
      `SigmaProp`'s `SigmaBoolean`. -/
  | sigmaPropBytes (e : Expr)
  /-- `BinOp`: arithmetic/relational/logical/bitwise binary operation. -/
  | binOp (kind : BinOpKind) (l r : Expr)
  /-- `And`: `allOf` — n-ary AND over a `Coll[Boolean]`. -/
  | andOf (input : Expr)
  /-- `Or`: `anyOf` — n-ary OR over a `Coll[Boolean]`. -/
  | orOf (input : Expr)
  /-- `LogicalNot`. -/
  | logicalNot (e : Expr)
  /-- `If`: lazy — only the taken branch is evaluated (`if_op.rs`). -/
  | ifExpr (cond thenE elseE : Expr)
  /-- `ExtractScriptBytes`: a box's `propositionBytes`. -/
  | extractScriptBytes (e : Expr)
  /-- `ExtractAmount`: a box's nanoERG value. -/
  | extractAmount (e : Expr)
  /-- `ExtractId`: a box's id (opaque bytes — hashing not modelled, see
      `Box.id`). -/
  | extractId (e : Expr)
  /-- `ExtractCreationInfo`: `box.creationInfo`, i.e. `(SInt, Coll[Byte])` —
      the height the box's creating transaction declared, paired with that
      transaction's id concatenated with this box's output index
      (big-endian `u16`). Mirrors `mir/extract_creation_info.rs`'s
      `ExtractCreationInfo`; see `Eval.lean`'s `Box.register`, which
      derives the identical tuple for R3. -/
  | extractCreationInfo (e : Expr)
  /-- `ExtractRegisterAs`: `box.RX[T]`, result type `SOption T`. No
      type-check against `elemTpe` is performed (`extract_reg_as.rs`
      returns whatever `Value` is stored, untyped) — see `Eval.lean`. -/
  | extractRegisterAs (input : Expr) (registerId : Int) (elemTpe : SType)
  /-- `OptionGet`: `.get` — errors if `none`. -/
  | optionGet (e : Expr)
  /-- `OptionIsDefined`: `.isDefined`. -/
  | optionIsDefined (e : Expr)
  /-- `OptionGetOrElse`: `.getOrElse(default)`. -/
  | optionGetOrElse (e default : Expr)
  /-- `GetVar`: `getVar[T](id)`, result type `SOption T`. Absent variable →
      `none` (no error); present but wrong dynamic type → error (mirrors
      `get_var.rs`) — see `Eval.lean`. -/
  | getVar (varId : Nat) (varTpe : SType)
  /-- `Collection`: a `Coll[T]` literal built from expressions. -/
  | collection (elemTpe : SType) (items : List Expr)
  /-- `Tuple`. -/
  | tuple (items : List Expr)
  /-- `SelectField`: 1-based tuple field access (`t._1` ↦ `fieldIndex = 1`;
      mirrors `TupleFieldIndex`, `mir/select_field.rs`:
      `zero_based_index() = self.0 - 1`). -/
  | selectField (input : Expr) (fieldIndex : Nat)
  /-- `SizeOf`: `.size` / `.length`. -/
  | sizeOf (e : Expr)
  /-- `Slice`. -/
  | sliceOf (input fromE untilE : Expr)
  /-- `Filter`. -/
  | filterOf (input cond : Expr) (elemTpe : SType)
  /-- `Exists`. -/
  | existsOf (input cond : Expr) (elemTpe : SType)
  /-- `ForAll`. -/
  | forAllOf (input cond : Expr) (elemTpe : SType)
  /-- `Fold`. -/
  | foldOf (input zero foldOp : Expr)
  /-- `Append`. -/
  | appendOf (input col2 : Expr)
  /-- `FuncValue`: an anonymous lambda (only ever appears — after
      `inlineFuns` — as the argument to `apply` or a higher-order op like
      `Filter`/`Exists`/`ForAll`/`Fold`; ErgoTree has no named top-level
      functions — local Scala `def`s compile to a `ValDef` binding a
      `FuncValue`, referenced via `Apply(ValUse f, ...)` — see
      `Eval.lean`'s `inlineFuns`). -/
  | funcValue (args : List (Nat × SType)) (body : Expr)
  /-- `Apply`: function application. After `inlineFuns`, `func` is always
      syntactically a literal `funcValue`. -/
  | apply (func : Expr) (args : List Expr)
  /-- `MethodCall`: carries the numeric `type_id`/`method_id` (see the
      exported file's comment for the human method name). -/
  | methodCall (obj : Expr) (typeId methodId : Nat) (args : List Expr)
  /-- `PropertyCall`: like `methodCall` but zero-argument. -/
  | propertyCall (obj : Expr) (typeId methodId : Nat)
  /-- `Upcast`: numeric widening (e.g. `Long.toBigInt`). -/
  | upcast (e : Expr) (tpe : SType)
  /-- `Downcast`: numeric narrowing. -/
  | downcast (e : Expr) (tpe : SType)
  /-- `Negation`: unary numeric negation (checked — overflows on negating
      the minimum value of the type, see `negation.rs`). -/
  | negation (e : Expr)
  /-- `ByteArrayToBigInt`. -/
  | byteArrayToBigInt (e : Expr)
  /-- `ByteArrayToLong`. -/
  | byteArrayToLong (e : Expr)
  /-- `CalcBlake2b256`: hash a `Coll[Byte]`. Evaluated via
      `ctx.oracle.blake2b256` (`Context.lean`'s `Oracle`) — proofs never
      compute a real blake2b hash; see `Eval.lean` and the README's "What is modelled". -/
  | calcBlake2b256 (e : Expr)
  /-- `DeserializeContext`: `getVar[Coll[Byte]](varId)`,
      deserialize-then-evaluate in place, result type `tpe`. Evaluated via
      `ctx.oracle.deserialize` (`Context.lean`'s `Oracle`) — see
      `Eval.lean` and the README's "What is modelled" for why the oracle's return type is
      `Option Value` (the already-evaluated result), not `Option Expr`:
      sigma-rust's real `deserialize_context.rs` deserializes *and
      evaluates* the resulting `Expr` inline
      (`Expr::sigma_parse_bytes(bytes)?.eval(env, ctx)`), and mirroring
      that literally (deserialize to an `Expr`, then recursively call
      `eval` on it) would recurse into an `Expr` with no size relationship
      to the original `DeserializeContext` node, breaking `eval`'s
      structural/well-founded termination measure — folding
      "deserialize + evaluate" into one atomic, opaque oracle call (like
      `blake2b256`) sidesteps that without weakening anything actually
      *verified*: this node's semantics are abstracted behind a trusted
      oracle either way, exactly like the crypto hash. -/
  | deserializeContext (varId : Nat) (tpe : SType)
  /-- `Atleast` (ErgoScript's `atLeast(bound, items)`): a k-of-n
      sigma-threshold. `bound`/`input` are both `Expr` (the bound is a
      genuine `SInt`-typed sub-expression, not baked in as a `Nat`) —
      mirrors `ergotree_ir::mir::atleast::Atleast { bound, input }`. -/
  | atLeast (bound input : Expr)
  /-- `Map`: `coll.map(mapper)`. `elemTpe` is the *output*
      collection's element type (`Map::out_elem_tpe`, i.e.
      `mapper_sfunc.t_range`) — mirrors `filterOf`'s `elemTpe` field
      exactly (also the output-collection type, not the input's). -/
  | mapOf (input mapper : Expr) (elemTpe : SType)
deriving Repr

mutual
/-- Structural equality on `Value`/`Box`, matching sigma-rust's derived
    `PartialEq` on `ergotree_ir::mir::value::Value`/`ErgoBox` (used by
    `BinOp`'s `Eq`/`NEq` — see module docstring for the `vColl`/`vOption`
    subtlety, and for why this is hand-written rather than `deriving
    DecidableEq`/`partial def`). Total (never fails) — a type mismatch
    between the two `Value`s being compared is simply `false`, not an
    error, exactly like sigma-rust's plain `lv == rv` (only
    *arithmetic*/*ordering* relations error on a type mismatch, via
    `try_extract_into` — see `Eval.lean`). -/
def Value.beq : Value → Value → Bool
  | .vUnit, .vUnit => true
  | .vBool a, .vBool b => a == b
  | .vByte a, .vByte b => a == b
  | .vShort a, .vShort b => a == b
  | .vInt a, .vInt b => a == b
  | .vLong a, .vLong b => a == b
  | .vBigInt a, .vBigInt b => a == b
  | .vGroupElement a, .vGroupElement b => a == b
  | .vSigmaProp a, .vSigmaProp b => SigmaBoolean.beq a b
  | .vBox a, .vBox b => Box.beq a b
  | .vColl te1 vs1, .vColl te2 vs2 => SType.beq te1 te2 && Value.beqList vs1 vs2
  | .vTuple vs1, .vTuple vs2 => Value.beqList vs1 vs2
  | .vOption _ o1, .vOption _ o2 =>
      match o1, o2 with
      | none, none => true
      | some x, some y => Value.beq x y
      | _, _ => false
  | _, _ => false

def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => Value.beq x y && Value.beqList xs ys
  | _, _ => false

/-- Full structural `Box` equality (id, value, propositionBytes, tokens,
    registers, creationHeight, transactionId, index) — mirrors `ErgoBox`'s
    derived `PartialEq` in sigma-rust (which also compares `box_id`,
    `value`, `ergo_tree`, `tokens`, `additional_registers`,
    `creation_height`, `transaction_id`, `index` — the same eight fields).
    No contract in this repo compares two `Box`es directly with `==`
    (only specific projected fields); included for completeness/fidelity. -/
def Box.beq : Box → Box → Bool
  | ⟨id1, v1, p1, t1, r1, ch1, tx1, ix1⟩, ⟨id2, v2, p2, t2, r2, ch2, tx2, ix2⟩ =>
      id1 == id2 && v1 == v2 && p1 == p2 && Box.beqTokens t1 t2 && Box.beqRegisters r1 r2
        && ch1 == ch2 && tx1 == tx2 && ix1 == ix2

def Box.beqTokens : List (List UInt8 × Int) → List (List UInt8 × Int) → Bool
  | [], [] => true
  | (tid1, amt1) :: xs, (tid2, amt2) :: ys => tid1 == tid2 && amt1 == amt2 && Box.beqTokens xs ys
  | _, _ => false

def Box.beqRegisters : List (Nat × Value) → List (Nat × Value) → Bool
  | [], [] => true
  | (i1, v1) :: xs, (i2, v2) :: ys => i1 == i2 && Value.beq v1 v2 && Box.beqRegisters xs ys
  | _, _ => false
end

instance : BEq Value := ⟨Value.beq⟩
instance : BEq Box := ⟨Box.beq⟩

mutual
/-- Reconstruct the `SType` a `Value` was built at. Used by `GetVar`'s
    dynamic type check (`get_var.rs`: `v.tpe == self.var_tpe`) and nothing
    else — `eval` never needs a full type-checker beyond this. Manual
    `mutual` recursion for the same reason as `beq` above (no `partial`,
    no routing through `List.map`). -/
def typeOf : Value → SType
  | .vUnit => .sUnit
  | .vBool _ => .sBoolean
  | .vByte _ => .sByte
  | .vShort _ => .sShort
  | .vInt _ => .sInt
  | .vLong _ => .sLong
  | .vBigInt _ => .sBigInt
  | .vGroupElement _ => .sGroupElement
  | .vSigmaProp _ => .sSigmaProp
  | .vBox _ => .sBox
  | .vColl t _ => .sColl t
  | .vTuple vs => .sTuple (typeOfList vs)
  | .vOption t _ => .sOption t

def typeOfList : List Value → List SType
  | [] => []
  | v :: vs => typeOf v :: typeOfList vs
end

end ErgoTreeLean
