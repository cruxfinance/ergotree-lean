/-
A parser for exactly the ErgoTree opcode subset used by `sell-order.es`'s
compiled `expressionTree`. Anything outside this subset fails to parse
(`none`), rather than being silently misinterpreted.

Recursion uses an explicit `fuel : Nat` parameter (initialised to the byte
length of the input, which is always enough since every recursive descent
consumes at least one byte) so that every function here is *structurally*
recursive on `fuel`, keeping `parseExprHex` reducible by `rfl`/`decide`.
-/
import ErgoTreeLean.Syntax

namespace ErgoTreeLean

/-- Decode a single hex digit (`0-9a-fA-F`). -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (c.toNat - 'A'.toNat + 10)
  else
    none

/-- Decode a list of hex-digit characters, two at a time, into bytes. -/
def hexChars : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | c1 :: c2 :: rest => do
      let d1 ← hexDigit c1
      let d2 ← hexDigit c2
      let bs ← hexChars rest
      pure (UInt8.ofNat (d1 * 16 + d2) :: bs)

/-- Decode a hex string (no `0x` prefix, e.g. `"d801..."`) into bytes. -/
def hexStringToBytes (s : String) : Option (List UInt8) :=
  hexChars s.toList

/-- Read a base-128 VLQ-encoded unsigned integer (protobuf-style varint:
    low 7 bits are data, the high bit signals "more bytes follow"). Returns
    the decoded value and the remaining, unconsumed bytes. -/
def readVLQ : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
      let low7 := b.toNat % 128
      if b.toNat < 128 then
        some (low7, rest)
      else
        match readVLQ rest with
        | some (hi, rest') => some (low7 + 128 * hi, rest')
        | none => none

/-- Zigzag-decode a VLQ-read magnitude into a signed integer, matching
    Sigma's `SInt` constant encoding. -/
def zigzagDecode (z : Nat) : Int :=
  if z % 2 == 0 then (z / 2 : Int) else -((z / 2 : Int) + 1)

/-- A best-effort, non-recursive-descent-independent type reconstruction
    for the handful of `Expr` shapes this hand parser itself can produce,
    used only to populate the `tpe` field on `ValUse` nodes (looked up via
    a val-def type store threaded through parsing, mirroring sigma-rust's
    real `ValDefTypeStore`) while parsing `BlockValue`s. Falls back to
    `.sAny` for anything not covered — `eval` never inspects a `ValUse`'s
    `tpe` field, so this loses no precision that matters to any theorem
    here; the real type-checker this loosely stands in for is out of scope
    for a hand-written single-contract parser. -/
def exprTpe : Expr → SType
  | .const (.vInt _) => .sInt
  | .const (.vLong _) => .sLong
  | .const (.vBool _) => .sBoolean
  | .const (.vColl .sByte _) => .sColl .sByte
  | .const (.vGroupElement _) => .sGroupElement
  | .const _ => .sAny
  | .valUse _ tpe => tpe
  | .constPlaceholder _ tpe => tpe
  | .outputs => .sColl .sBox
  | .byIndex coll _ _ => match exprTpe coll with
      | .sColl t => t
      | _ => .sAny
  | .sigmaOr _ => .sSigmaProp
  | .createProveDlog _ => .sSigmaProp
  | .boolToSigmaProp _ => .sSigmaProp
  | .binOp (.relation _) _ _ => .sBoolean
  | .binOp (.logical _) _ _ => .sBoolean
  | .extractScriptBytes _ => .sColl .sByte
  | .extractAmount _ => .sLong
  | .blockValue _ result => exprTpe result
  | _ => .sAny

/-- Val-def type store: `(id, tpe)` pairs for every `ValDef` parsed so far
    (in the enclosing `BlockValue`s), used to type `ValUse` nodes. -/
abbrev ValStore := List (Nat × SType)

mutual

/-- Parse one `Expr` from the front of `bytes`, returning it together with
    whatever bytes remain. `fuel` bounds recursion depth (see module
    docstring); `store` types `ValUse`; `constTypes` types
    `ConstantPlaceholder` (its `constantIndex`-ordered EIP-5 template
    types — sigma-rust's real parser gets these the same way, from the
    ErgoTree's constant-segregation constants). -/
def parseExpr : Nat → ValStore → List SType → List UInt8 → Option (Expr × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, store, constTypes, b :: bytes =>
      if b == 0x04 then do
        -- Inline SInt constant: type byte 0x04 already consumed, followed
        -- by a zigzag-VLQ value.
        let (z, bytes1) ← readVLQ bytes
        some (.const (.vInt (zigzagDecode z)), bytes1)
      else if b == 0x72 then do
        let (id, bytes1) ← readVLQ bytes
        let tpe := (store.find? (fun p => p.1 == id)).map Prod.snd |>.getD .sAny
        some (.valUse id tpe, bytes1)
      else if b == 0x73 then do
        let (id, bytes1) ← readVLQ bytes
        let tpe := constTypes[id]?.getD .sAny
        some (.constPlaceholder id tpe, bytes1)
      else if b == 0xa5 then
        some (.outputs, bytes)
      else if b == 0xb2 then do
        let (coll, bytes1) ← parseExpr fuel store constTypes bytes
        let (idx, bytes2) ← parseExpr fuel store constTypes bytes1
        match bytes2 with
        | tag :: bytes3 =>
            if tag == 0x00 then
              some (.byIndex coll idx none, bytes3)
            else if tag == 0x01 then do
              let (dflt, bytes4) ← parseExpr fuel store constTypes bytes3
              some (.byIndex coll idx (some dflt), bytes4)
            else
              none
        | [] => none
      else if b == 0x92 then do
        let (l, bytes1) ← parseExpr fuel store constTypes bytes
        let (r, bytes2) ← parseExpr fuel store constTypes bytes1
        some (.binOp (.relation .ge) l r, bytes2)
      else if b == 0x93 then do
        let (l, bytes1) ← parseExpr fuel store constTypes bytes
        let (r, bytes2) ← parseExpr fuel store constTypes bytes1
        some (.binOp (.relation .eq) l r, bytes2)
      else if b == 0xc1 then do
        let (e, bytes1) ← parseExpr fuel store constTypes bytes
        some (.extractAmount e, bytes1)
      else if b == 0xc2 then do
        let (e, bytes1) ← parseExpr fuel store constTypes bytes
        some (.extractScriptBytes e, bytes1)
      else if b == 0xcd then do
        let (e, bytes1) ← parseExpr fuel store constTypes bytes
        some (.createProveDlog e, bytes1)
      else if b == 0xd1 then do
        let (e, bytes1) ← parseExpr fuel store constTypes bytes
        some (.boolToSigmaProp e, bytes1)
      else if b == 0xd8 then do
        let (n, bytes1) ← readVLQ bytes
        let (defs, store', bytes2) ← parseValDefs fuel store constTypes n bytes1
        let (result, bytes3) ← parseExpr fuel store' constTypes bytes2
        some (.blockValue defs result, bytes3)
      else if b == 0xeb then do
        let (n, bytes1) ← readVLQ bytes
        let (items, bytes2) ← parseExprList fuel store constTypes n bytes1
        some (.sigmaOr items, bytes2)
      else if b == 0xed then do
        let (l, bytes1) ← parseExpr fuel store constTypes bytes
        let (r, bytes2) ← parseExpr fuel store constTypes bytes1
        some (.binOp (.logical .and) l r, bytes2)
      else
        none

/-- Parse `n` `ValDef`s (each `0xd6, <VLQ id>, <Expr rhs>`) in order,
    returning the accumulated val-def type store alongside them (so the
    enclosing `BlockValue`'s `result` — and later `ValDef`s — can type
    `ValUse`s that refer back to them). -/
def parseValDefs : Nat → ValStore → List SType → Nat → List UInt8 →
    Option (List (Nat × Expr) × ValStore × List UInt8)
  | _, store, _, 0, bytes => some ([], store, bytes)
  | 0, _, _, _ + 1, _ => none
  | _ + 1, _, _, _ + 1, [] => none
  | fuel + 1, store, constTypes, n + 1, b :: bytes =>
      if b == 0xd6 then do
        let (id, bytes1) ← readVLQ bytes
        let (rhs, bytes2) ← parseExpr fuel store constTypes bytes1
        let store' := (id, exprTpe rhs) :: store
        let (rest, store'', bytes3) ← parseValDefs fuel store' constTypes n bytes2
        some ((id, rhs) :: rest, store'', bytes3)
      else
        none

/-- Parse `n` `Expr`s in order (used for `SigmaOr`'s items). -/
def parseExprList : Nat → ValStore → List SType → Nat → List UInt8 → Option (List Expr × List UInt8)
  | _, _, _, 0, bytes => some ([], bytes)
  | 0, _, _, _ + 1, _ => none
  | fuel + 1, store, constTypes, n + 1, bytes => do
      let (e, bytes1) ← parseExpr fuel store constTypes bytes
      let (rest, bytes2) ← parseExprList fuel store constTypes n bytes1
      some (e :: rest, bytes2)

end

/-- Parse a full hex-encoded `expressionTree`: it must decode to exactly one
    `Expr` with no leftover bytes. `constTypes` is the EIP-5 template's
    `constTypes` array (in `constantIndex` order), needed to type
    `ConstantPlaceholder` nodes — exactly the "build a constant store to
    type placeholders" step the task brief calls for on the Rust exporter
    side too. -/
def parseExprHex (s : String) (constTypes : List SType) : Option Expr := do
  let bytes ← hexStringToBytes s
  let (e, rest) ← parseExpr bytes.length [] constTypes bytes
  if rest.isEmpty then some e else none

end ErgoTreeLean
