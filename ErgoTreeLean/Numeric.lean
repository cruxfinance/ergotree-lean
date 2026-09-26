/-
Fixed-width and `BigInt256` numeric semantics, mirroring sigma-rust
`ergotree-interpreter-0.28.0/src/eval/bin_op.rs`, `upcast.rs`,
`downcast.rs`, `negation.rs`, `byte_array_to_bigint.rs`,
`byte_array_to_long.rs`, and `ergotree-ir-0.28.0/src/bigint256.rs`. `Int`
here is always an *unbounded* Lean integer used as the carrier for a
fixed-width value — `Value.vByte`/`vShort`/`vInt`/`vLong`/`vBigInt` all
carry a plain `Int` (see `Syntax.lean`); the functions in this file are
what enforce the width, not the `Value` constructor itself.
-/
import ErgoTreeLean.Syntax

namespace ErgoTreeLean

/-- Which of the five ErgoTree numeric types a value belongs to. -/
inductive NumKind where
  | byte | short | int | long | bigint
deriving Repr, DecidableEq

/-- `(min, max)` inclusive bounds for `k`, matching `i8`/`i16`/`i32`/`i64`'s
    range and `BigInt256`'s `[-2^255, 2^255 - 1]` range
    (`ergotree-ir::bigint256::BigInt256`'s `TryFrom<BigInt>`, which rejects
    anything smaller than `-2^255` or larger than `2^255 - 1`). -/
def NumKind.bounds : NumKind → Int × Int
  | .byte => (-128, 127)
  | .short => (-32768, 32767)
  | .int => (-2147483648, 2147483647)
  | .long => (-9223372036854775808, 9223372036854775807)
  | .bigint => (-(2 ^ 255 : Int), 2 ^ 255 - 1)

def NumKind.inRange (k : NumKind) (v : Int) : Bool :=
  k.bounds.1 ≤ v && v ≤ k.bounds.2

/-- Widening rank (`Byte < Short < Int < Long < BigInt`), used by `Upcast`
    (only ever widens or is a same-kind no-op — see `upcastValue`). -/
def NumKind.rank : NumKind → Nat
  | .byte => 0 | .short => 1 | .int => 2 | .long => 3 | .bigint => 4

/-- Bit width used by the two's-complement bitwise helpers below. -/
def NumKind.bits : NumKind → Nat
  | .byte => 8 | .short => 16 | .int => 32 | .long => 64 | .bigint => 256

/-- Extract the `(kind, raw Int)` of a numeric `Value`, or `none` for a
    non-numeric one. Used to dispatch `BinOp`/`Negation`/`Upcast`/
    `Downcast`, and to wrap a checked-arithmetic result back into the same
    `Value` constructor it came from. -/
def Value.numKind : Value → Option (NumKind × Int)
  | .vByte v => some (.byte, v)
  | .vShort v => some (.short, v)
  | .vInt v => some (.int, v)
  | .vLong v => some (.long, v)
  | .vBigInt v => some (.bigint, v)
  | _ => none

/-- Wrap a raw `Int` back into the `Value` constructor for `k`. -/
def NumKind.wrap (k : NumKind) (v : Int) : Value :=
  match k with
  | .byte => .vByte v | .short => .vShort v | .int => .vInt v
  | .long => .vLong v | .bigint => .vBigInt v

/-- The `NumKind` a numeric `SType` denotes, or `none` for a non-numeric
    type. Used by `Upcast`/`Downcast`'s `tpe` field in `Eval.lean`. -/
def sTypeToNumKind? : SType → Option NumKind
  | .sByte => some .byte
  | .sShort => some .short
  | .sInt => some .int
  | .sLong => some .long
  | .sBigInt => some .bigint
  | _ => none

/-- The raw `Int` of `rv`, but only if `rv` is *the same numeric kind* as
    `lv` — mirrors `eval_ge`/`eval_gt`/`eval_lt`/`eval_le` and the
    `eval_plus`/`eval_minus`/... generic helpers in `bin_op.rs`, which all
    extract the right operand via `rv.try_extract_into::<T>()` for the
    exact Rust type `T` determined by the left operand's variant — a
    `Byte` left operand and a `Long` right operand is a hard
    `TryExtractFromError`, not a coercion (this is the "fix the old
    permissive `GE`" the phase-2 brief calls for). -/
def sameKindRaw (lv rv : Value) : Option (NumKind × Int × Int) :=
  match lv.numKind, rv.numKind with
  | some (k1, a), some (k2, b) => if k1 == k2 then some (k1, a, b) else none
  | _, _ => none

/-- Truncating (toward-zero) division, matching Rust's `/` on signed
    integers — **not** Lean's default `Int./`, which is Euclidean
    (`(-7 : Int) / 2 = -4` in Lean, but `-3` in Rust; confirmed directly
    with `#eval`). Mirrors `bin_op.rs::eval_div`'s `checked_div` for
    Byte/Short/Int/Long; `BigInt256`'s `Div` impl over `Int256` is
    likewise truncating (`bin_op.rs`'s `test_bigint_extremes`:
    `(min()+1) / (-1) = max()`). -/
def tdiv (a b : Int) : Int :=
  let q : Int := (a.natAbs / b.natAbs : Nat)
  if (a < 0) == (b < 0) then q else -q

/-- Truncating remainder (sign follows the dividend), matching Rust's `%`
    on `i8`/`i16`/`i32`/`i64` (`bin_op.rs::eval_mod`'s `checked_rem`).
    **Not** what `BigInt256`'s `%` does — see `checkedRemBigInt` below, a
    genuinely different (floor-mod, positive-divisor-only) rule. -/
def trem (a b : Int) : Int := a - b * tdiv a b

/-- `checked_add`/`checked_sub`/`checked_mul`/`max`/`min`: compute over
    unbounded `Int`, then range-check against `k`'s bounds (`none` on
    overflow, mirroring `EvalError::ArithmeticException` on `None` from
    `checked_add`/etc. in `bin_op.rs`). Also used for `max`/`min` (never
    actually overflows — the result is one of the two in-range inputs —
    but the check is harmless). -/
def checkedArith (k : NumKind) (op : Int → Int → Int) (a b : Int) : Option Int :=
  let r := op a b
  if k.inRange r then some r else none

/-- `checked_div`, for all five kinds (division itself is truncating for
    Byte/Short/Int/Long *and* BigInt — `bin_op.rs::eval_div`); errors on
    division by zero and on the one case where truncating division itself
    overflows the type (`MIN / -1`), matching `i64::checked_div`. -/
def checkedDiv (k : NumKind) (a b : Int) : Option Int :=
  if b == 0 then none
  else if a == k.bounds.1 && b == -1 then none
  else some (tdiv a b)

/-- `checked_rem` for Byte/Short/Int/Long: truncating remainder
    (`bin_op.rs::eval_mod`), erroring on division by zero and on the same
    `MIN % -1` overflow case `i64::checked_rem` reports (even though the
    mathematical result, `0`, would fit — Rust's `checked_rem` fails
    whenever the *division* would overflow). -/
def checkedRemFixed (k : NumKind) (a b : Int) : Option Int :=
  if b == 0 then none
  else if a == k.bounds.1 && b == -1 then none
  else some (trem a b)

/-- `checked_rem` for **BigInt** — genuinely different from the
    fixed-width rule above (`ergotree-ir::bigint256::BigInt256`'s
    `CheckedRem` impl, confirmed against `bin_op.rs`'s
    `test_bigint_extremes`: `20 % -1` and `20 % 0` both error, not just
    `%0`): the divisor must be *strictly positive*, and the result is
    **floor**-mod, not truncating (always in `[0, b)` for positive `b`).
    Deliberately *not* "fixed" to match the other four kinds — this is a
    real sigma-rust asymmetry, not a bug to paper over; see `Eval.lean`. -/
def checkedRemBigInt (a b : Int) : Option Int :=
  if b ≤ 0 then none
  else
    let r := trem a b
    some (if r < 0 then r + b else r)

/-- `checked_neg`: negation overflows only at each type's minimum (e.g.
    `Long.MIN.negate()`), matching `negation.rs`. -/
def checkedNeg (k : NumKind) (a : Int) : Option Int :=
  let r := -a
  if k.inRange r then some r else none

/-! ### Bitwise ops

`BitOp` (`&`/`|`/`^`), matching `bin_op.rs::eval_bit_op`: plain
two's-complement bitwise ops on the raw fixed-width/`BigInt256` value
(never overflows, so no range check on the way out). -/

/-- Two's-complement encoding of `a` (assumed in-range for `bits`) as a
    `bits`-wide unsigned magnitude. -/
def toTwos (bits : Nat) (a : Int) : Nat :=
  if a ≥ 0 then a.toNat else (a + (2 ^ bits : Int)).toNat

/-- Inverse of `toTwos`. -/
def ofTwos (bits : Nat) (n : Nat) : Int :=
  if n < 2 ^ (bits - 1) then (n : Int) else (n : Int) - (2 ^ bits : Int)

def bitOpOn (k : NumKind) (op : Nat → Nat → Nat) (a b : Int) : Int :=
  ofTwos k.bits (op (toTwos k.bits a) (toTwos k.bits b))

/-! ### Upcast / Downcast

Mirrors `eval/upcast.rs` / `eval/downcast.rs`: both are keyed off the
*source* kind (`Upcast`) or handle every source kind explicitly
(`Downcast`), never a generic "coerce". -/

/-- `Upcast`: only ever widens (same-kind is a no-op; the other direction —
    `upcast_to_byte` on a `Short`, say — errors, it never silently
    narrows). No range check needed: a narrower value is always in the
    wider target's range. -/
def upcastValue (src : NumKind) (srcV : Int) (tgt : NumKind) : Option Int :=
  if src == tgt || tgt.rank > src.rank then some srcV else none

/-- `Downcast`: an explicit table, **not** a generic "widen-or-range-check"
    rule — `downcast.rs`'s five `downcast_to_*` functions each hand-list
    the source kinds they accept, and two real asymmetries fall out of
    that (mirrored here, not "fixed"):
    1. Nothing can be `Downcast`ed *from* `BigInt` — every `downcast_to_*`
       function's `match` omits a `BigInt` arm (falls to `_ => Err`),
       including `downcast_to_bigint` itself (`BigInt → BigInt` errors,
       it's *not* a no-op).
    2. `downcast_to_short` has no `Byte` arm — `Downcast(byteExpr, SShort)`
       errors, even though it's a widening a real compiler would emit as
       `Upcast` (so this path is presumably just never hit by compiled
       code) — while `downcast_to_int`/`_long`/`_bigint` all *do* widen
       from `Byte` explicitly.
    Same-kind (except BigInt) and every other widening is a no-op;
    narrowing range-checks the target (`i8`/`i16`/`i32::try_from`),
    erroring "overflow" out of range. -/
def downcastValue (src : NumKind) (srcV : Int) (tgt : NumKind) : Option Int :=
  match tgt with
  | .bigint =>
      match src with
      | .byte | .short | .int | .long => some srcV
      | .bigint => none
  | .long =>
      match src with
      | .byte | .short | .int | .long => some srcV
      | .bigint => none
  | .int =>
      match src with
      | .byte | .short | .int => some srcV
      | .long => if tgt.inRange srcV then some srcV else none
      | .bigint => none
  | .short =>
      match src with
      | .short => some srcV
      | .int | .long => if tgt.inRange srcV then some srcV else none
      | .byte | .bigint => none
  | .byte =>
      match src with
      | .byte => some srcV
      | .short | .int | .long => if tgt.inRange srcV then some srcV else none
      | .bigint => none

/-! ### `ByteArrayToBigInt` / `ByteArrayToLong`

Mirrors `eval/byte_array_to_bigint.rs` / `eval/byte_array_to_long.rs`.
Both treat the input `Coll[Byte]` as raw signed bytes (`i8`). Neither node
occurs in `sell-order`'s compiled tree, but both are implemented here for
completeness/fidelity to the phase-2 brief. -/

/-- A raw byte's value as sigma-rust's `i8` (two's-complement,
    `[-128,127]`), matching how `Coll[Byte]`'s elements are actually
    signed in ErgoTree. -/
def signedByteVal (b : UInt8) : Int :=
  if b.toNat ≥ 128 then (b.toNat : Int) - 256 else (b.toNat : Int)

/-- `ByteArrayToBigInt`: big-endian two's complement decode of the *whole*
    (arbitrary-length) byte string (`BigInt::from_signed_bytes_be`), then
    range-checked against `[-2^255, 2^255-1]` (`BigInt256::try_from`).
    Errors on an empty input or a decoded value outside that range
    (sign-extended leading bytes don't push the value out of range merely
    by being long; only the *value* matters). -/
def byteArrayToBigInt (bs : List UInt8) : Option Int :=
  match bs with
  | [] => none
  | b0 :: _ =>
      let n := bs.length
      let mag : Int := bs.foldl (fun acc b => acc * 256 + (b.toNat : Int)) 0
      let v := if b0.toNat ≥ 128 then mag - (2 ^ (n * 8) : Int) else mag
      if NumKind.bigint.inRange v then some v else none

/-- `ByteArrayToLong`: needs at least 8 bytes (else errors); takes
    *exactly* the first 8 (later bytes ignored — no error). Reproduces the
    Rust source bit-for-bit rather than a "clean" big-endian decode: each
    of the first 8 bytes is sign-extended to a 64-bit `i64` *before* being
    shifted into position and OR'ed together
    (`(input[0] as i64) << 56 | (input[1] as i64) << 48 | ...`). Because OR
    (not addition) combines the terms, a *negative* non-leading byte's
    sign-extension bits can leak into more-significant bit positions than
    its own byte — exactly what the real evaluator computes (cross-checked
    against the Scala reference in `byte_array_to_long.rs`'s
    `test_equivalence`), reproduced here via the same 64-bit
    two's-complement shift-then-OR rather than a textbook decode (which
    would disagree whenever a non-leading byte is negative). -/
def byteArrayToLong (bs : List UInt8) : Option Int :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
      let mask64 : Nat := 2 ^ 64
      let term (b : UInt8) (shift : Nat) : Nat :=
        (toTwos 64 (signedByteVal b) * 2 ^ shift) % mask64
      let combined :=
        Nat.lor (term b0 56) (Nat.lor (term b1 48) (Nat.lor (term b2 40) (Nat.lor (term b3 32)
          (Nat.lor (term b4 24) (Nat.lor (term b5 16) (Nat.lor (term b6 8) (term b7 0)))))))
      some (ofTwos 64 combined)
  | _ => none

end ErgoTreeLean
