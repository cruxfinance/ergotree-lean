/-
Decodes the JSON emitted by `difftest/src/leanval.rs` back into
`ErgoTreeLean`'s own `Value`/`Box`/`Context`/`Case`/`SigmaBoolean`
constructors — see that file's module docstring for *why* this is JSON
decoded at run time rather than a generated `.lean` literal (elaborating a
literal `List Case` with more than a couple hundred cases was empirically
too slow — confirmed, not assumed).

These `partial def`s are test-support code, not proofs: the "no `sorry`,
no `native_decide`, no new `axiom`" rule (and the "no `partial def` in
`Eval.lean`/`InlineFuns.lean`, because it can't be `simp`-unfolded inside a
proof" reasoning) is about the trusted evaluator/proof base, not about
this executable. `Main.lean`'s comparison uses the *compiled* `eval`/
`inlineFuns` (also fine to run compiled outside a proof), so decoding
being `partial` costs nothing here — correctness of this whole harness is
checked empirically (0 mismatches on real sigma-rust-generated cases), not
by kernel proof.

## JSON schema (must match `difftest/src/leanval.rs` exactly)

- `SType`: `{"tag": "sByte"}`, `{"tag": "sOption", "inner": SType}`,
  `{"tag": "sColl", "inner": SType}`, `{"tag": "sTuple", "items": [SType]}`,
  one no-argument object per other constructor.
- `Value`: `{"tag": "vUnit"}`, `{"tag": "vBool", "v": Bool}`,
  `{"tag": "vByte"/"vShort"/"vInt", "v": Int}` (JSON number),
  `{"tag": "vLong"/"vBigInt", "v": String}` (decimal, possibly negative —
  stringified since the value can exceed what's safe to round-trip as a
  bare JSON number), `{"tag": "vGroupElement", "hex": String}`,
  `{"tag": "collByte", "hex": String}` (→ `bytesToVColl`, `Coll[Byte]`),
  `{"tag": "wrapped", "elem": SType, "items": [Value]}` (→ `Value.vColl`),
  `{"tag": "vOption", "v": null | Value}`, `{"tag": "vTuple", "items":
  [Value]}`, `{"tag": "vBox", "box": Box}`.
- `Box`: `{"id": hex, "value": String, "propositionBytes": hex, "tokens":
  [[hex, String]], "registers": [[Nat, Value]]}`.
- `Context` (embedded in `Case.ctx`): `{"selfBox": Box, "inputs": [Box],
  "outputs": [Box], "dataInputs": [Box], "height": Nat, "extension":
  [[Nat, Value]], "blake2b": [[hex, hex]]?, "deserialize": [[hex,
  Value]]?}` — the last two (phase 4) are per-case oracle tables, optional
  (absent = empty = `Oracle.default`); see `decodeContext`.
- `SigmaBoolean`: `{"tag": "trivial", "v": Bool}`, `{"tag": "proveDlog",
  "hex": String}`, `{"tag": "cor"/"cand", "items": [SigmaBoolean]}`,
  `{"tag": "cthreshold", "k": Nat, "items": [SigmaBoolean]}` (phase 4).
- `Case`: `{"id": Nat, "consts": [Value], "ctx": Context, "expected": null
  | SigmaBoolean}`. The top-level file is a JSON array of `Case`.
-/
import ErgoTreeLean
import ErgoTreeLean.DiffTest.Types
import Lean.Data.Json

namespace ErgoTreeLean.DiffTest

open Lean (Json)

/-- Decode a hex string into `List UInt8`, failing (rather than silently
    returning `[]`) on malformed hex — unlike `Eval.lean`'s internal use of
    `hexStringToBytes`, a decode failure here is a real bug in this file or
    in `difftest/src/leanval.rs`, not an expected "absent" case. -/
def decodeHex (s : String) : Except String (List UInt8) :=
  match hexStringToBytes s with
  | some bs => .ok bs
  | none => .error s!"decodeHex: malformed hex string {s}"

/-- Parse an optionally-negative decimal string into `Int` (used for
    `Long`/`BigInt`/box-value/token-amount fields, stringified on the Rust
    side to avoid relying on JSON-number precision for values near
    `Int64`/`BigInt256` range). -/
def parseInt (s : String) : Except String Int :=
  if s.startsWith "-" then
    match (s.drop 1).toNat? with
    | some n => .ok (-(n : Int))
    | none => .error s!"parseInt: malformed integer {s}"
  else
    match s.toNat? with
    | some n => .ok (n : Int)
    | none => .error s!"parseInt: malformed integer {s}"

def getTag (j : Json) : Except String String := do
  (← j.getObjVal? "tag").getStr?

/-- Total array indexing into `Except`, used for the small fixed-size
    `[hex, amount]`/`[regId, value]`/`[varId, value]` pair arrays below. -/
def arrGet (arr : Array Json) (i : Nat) : Except String Json :=
  match arr[i]? with
  | some j => .ok j
  | none => .error s!"arrGet: index {i} out of bounds (array has {arr.size} elements)"

partial def decodeSType (j : Json) : Except String SType := do
  let tag ← getTag j
  match tag with
  | "sBoolean" => pure .sBoolean
  | "sByte" => pure .sByte
  | "sShort" => pure .sShort
  | "sInt" => pure .sInt
  | "sLong" => pure .sLong
  | "sBigInt" => pure .sBigInt
  | "sGroupElement" => pure .sGroupElement
  | "sSigmaProp" => pure .sSigmaProp
  | "sBox" => pure .sBox
  | "sUnit" => pure .sUnit
  | "sAny" => pure .sAny
  | "sOption" => do
      let inner ← decodeSType (← j.getObjVal? "inner")
      pure (.sOption inner)
  | "sColl" => do
      let inner ← decodeSType (← j.getObjVal? "inner")
      pure (.sColl inner)
  | "sTuple" => do
      let items ← (← j.getObjVal? "items").getArr?
      let items' ← items.toList.mapM decodeSType
      pure (.sTuple items')
  | other => .error s!"decodeSType: unknown tag {other}"

mutual
partial def decodeValue (j : Json) : Except String Value := do
  let tag ← getTag j
  match tag with
  | "vUnit" => pure .vUnit
  | "vBool" => do
      let v ← (← j.getObjVal? "v").getBool?
      pure (.vBool v)
  | "vByte" => do
      let v ← (← j.getObjVal? "v").getInt?
      pure (.vByte v)
  | "vShort" => do
      let v ← (← j.getObjVal? "v").getInt?
      pure (.vShort v)
  | "vInt" => do
      let v ← (← j.getObjVal? "v").getInt?
      pure (.vInt v)
  | "vLong" => do
      let v ← parseInt (← (← j.getObjVal? "v").getStr?)
      pure (.vLong v)
  | "vBigInt" => do
      let v ← parseInt (← (← j.getObjVal? "v").getStr?)
      pure (.vBigInt v)
  | "vGroupElement" => do
      let bs ← decodeHex (← (← j.getObjVal? "hex").getStr?)
      pure (.vGroupElement bs)
  | "collByte" => do
      let bs ← decodeHex (← (← j.getObjVal? "hex").getStr?)
      pure (bytesToVColl bs)
  | "wrapped" => do
      let elem ← decodeSType (← j.getObjVal? "elem")
      let items ← (← j.getObjVal? "items").getArr?
      let items' ← items.toList.mapM decodeValue
      pure (.vColl elem items')
  | "vOption" => do
      let v := j.getObjValD "v"
      if v.isNull then pure (.vOption .sAny none)
      else do
        let v' ← decodeValue v
        pure (.vOption .sAny (some v'))
  | "vTuple" => do
      let items ← (← j.getObjVal? "items").getArr?
      let items' ← items.toList.mapM decodeValue
      pure (.vTuple items')
  | "vBox" => do
      let b ← decodeBox (← j.getObjVal? "box")
      pure (.vBox b)
  -- Phase 4: the "deserialize" oracle table's answer is an already
  -- evaluated `Value` — for a downstream contract's
  -- `executeFromVar[SigmaProp]`, that's always a `vSigmaProp`, which
  -- `literal_to_json`'s original callers (register/constant literals)
  -- never needed to produce. See `difftest/src/leanval.rs`'s matching
  -- `Literal::SigmaProp` case.
  | "vSigmaProp" => do
      let sb ← decodeSigmaBoolean (← j.getObjVal? "sb")
      pure (.vSigmaProp sb)
  | other => .error s!"decodeValue: unknown tag {other}"

partial def decodeBox (j : Json) : Except String Box := do
  let id ← decodeHex (← (← j.getObjVal? "id").getStr?)
  let value ← parseInt (← (← j.getObjVal? "value").getStr?)
  let propBytes ← decodeHex (← (← j.getObjVal? "propositionBytes").getStr?)
  let tokensJ ← (← j.getObjVal? "tokens").getArr?
  let tokens ← tokensJ.toList.mapM (fun tj => do
    let arr ← tj.getArr?
    let tid ← decodeHex (← (← arrGet arr 0).getStr?)
    let amt ← parseInt (← (← arrGet arr 1).getStr?)
    pure (tid, amt))
  let regsJ ← (← j.getObjVal? "registers").getArr?
  let regs ← regsJ.toList.mapM (fun rj => do
    let arr ← rj.getArr?
    let idx ← (← arrGet arr 0).getNat?
    let v ← decodeValue (← arrGet arr 1)
    pure (idx, v))
  pure (Box.mk id value propBytes tokens regs)

-- In the same `mutual` block as `decodeValue`/`decodeBox` (rather than
-- after them, as in an earlier version of this file) because `decodeValue`'s
-- `"vSigmaProp"` case (phase 4, the `deserialize` oracle table's answers —
-- see that case's comment) now calls it.
partial def decodeSigmaBoolean (j : Json) : Except String SigmaBoolean := do
  let tag ← getTag j
  match tag with
  | "trivial" => do
      let v ← (← j.getObjVal? "v").getBool?
      pure (.trivial v)
  | "proveDlog" => do
      let bs ← decodeHex (← (← j.getObjVal? "hex").getStr?)
      pure (.proveDlog bs)
  | "cor" => do
      let itemsJ ← (← j.getObjVal? "items").getArr?
      let items ← itemsJ.toList.mapM decodeSigmaBoolean
      pure (.cor items)
  | "cand" => do
      let itemsJ ← (← j.getObjVal? "items").getArr?
      let items ← itemsJ.toList.mapM decodeSigmaBoolean
      pure (.cand items)
  | "cthreshold" => do
      let k ← (← j.getObjVal? "k").getNat?
      let itemsJ ← (← j.getObjVal? "items").getArr?
      let items ← itemsJ.toList.mapM decodeSigmaBoolean
      pure (.cthreshold k items)
  | other => .error s!"decodeSigmaBoolean: unknown tag {other}"
end

partial def decodeContext (j : Json) : Except String Context := do
  let selfBox ← decodeBox (← j.getObjVal? "selfBox")
  let inputsJ ← (← j.getObjVal? "inputs").getArr?
  let inputs ← inputsJ.toList.mapM decodeBox
  let outputsJ ← (← j.getObjVal? "outputs").getArr?
  let outputs ← outputsJ.toList.mapM decodeBox
  let dataInputsJ ← (← j.getObjVal? "dataInputs").getArr?
  let dataInputs ← dataInputsJ.toList.mapM decodeBox
  let height ← (← j.getObjVal? "height").getNat?
  let extJ ← (← j.getObjVal? "extension").getArr?
  let ext ← extJ.toList.mapM (fun ej => do
    let arr ← ej.getArr?
    let idx ← (← arrGet arr 0).getNat?
    let v ← decodeValue (← arrGet arr 1)
    pure (idx, v))
  -- Phase 4: per-case oracle tables (`"blake2b"`/`"deserialize"`, both
  -- optional — absent, as in every pre-phase-4 case file, means "empty
  -- table", i.e. `Oracle.default`). `difftest/src/cl_common.rs` emits
  -- these as `[[hexInput, hexHash], ...]` / `[[hexInput, Value], ...]`
  -- respectively — the *real* blake2b256 hash of the bytes this case
  -- actually feeds `CalcBlake2b256`, and the already-evaluated `Value`
  -- sigma-rust's `DeserializeContext` would produce for the bytes this
  -- case actually feeds it (see `Context.lean`'s `Oracle` docstring for
  -- why `deserialize` returns a `Value`, not an `Expr`). Any bytes not
  -- listed simply aren't queried by the case they came with — a genuine
  -- lookup miss would be a generator bug, not an expected "absent" case,
  -- so a miss here falls back to `[]`/`none` rather than failing decode.
  let blake2bJ := j.getObjValD "blake2b"
  let blake2bTable ← if blake2bJ.isNull then pure ([] : List (List UInt8 × List UInt8)) else do
    let arr ← blake2bJ.getArr?
    arr.toList.mapM (fun pj => do
      let parr ← pj.getArr?
      let inBs ← decodeHex (← (← arrGet parr 0).getStr?)
      let outBs ← decodeHex (← (← arrGet parr 1).getStr?)
      pure (inBs, outBs))
  let deserJ := j.getObjValD "deserialize"
  let deserTable ← if deserJ.isNull then pure ([] : List (List UInt8 × Value)) else do
    let arr ← deserJ.getArr?
    arr.toList.mapM (fun pj => do
      let parr ← pj.getArr?
      let inBs ← decodeHex (← (← arrGet parr 0).getStr?)
      let v ← decodeValue (← arrGet parr 1)
      pure (inBs, v))
  let oracle : Oracle :=
    { blake2b256 := fun bs => ((blake2bTable.find? (fun p => p.1 == bs)).map Prod.snd).getD []
      deserialize := fun bs => (deserTable.find? (fun p => p.1 == bs)).map Prod.snd }
  pure (Context.mk selfBox inputs outputs dataInputs height ext oracle)

def decodeCase (j : Json) : Except String Case := do
  let id ← (← j.getObjVal? "id").getNat?
  let constsJ ← (← j.getObjVal? "consts").getArr?
  let consts ← constsJ.toList.mapM decodeValue
  let ctx ← decodeContext (← j.getObjVal? "ctx")
  let expectedJ := j.getObjValD "expected"
  let expected ← if expectedJ.isNull then pure none else do
    let sb ← decodeSigmaBoolean expectedJ
    pure (some sb)
  pure (Case.mk id consts ctx expected)

/-- Read and decode a whole cases file (a JSON array of `Case`, as emitted
    by `difftest --out <path>`). -/
def loadCases (path : System.FilePath) : IO (List Case) := do
  let text ← IO.FS.readFile path
  match Json.parse text with
  | .error e => throw (IO.userError s!"loadCases: JSON parse error in {path}: {e}")
  | .ok j =>
      match j.getArr? with
      | .error e => throw (IO.userError s!"loadCases: {path}: {e}")
      | .ok arr =>
          match arr.toList.mapM decodeCase with
          | .error e => throw (IO.userError s!"loadCases: {path}: {e}")
          | .ok cases => pure cases

end ErgoTreeLean.DiffTest
