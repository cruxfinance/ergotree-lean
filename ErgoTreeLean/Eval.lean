/-
Reference-interpreter-faithful evaluator, mirroring
`ergotree-interpreter-0.28.0`'s `eval/*.rs`. Every case below carries a
`-- mirrors: eval/<file>.rs` comment naming the Rust source it was read
against.

## Design note: no closures, higher-order ops match `funcValue` syntactically

sigma-rust's evaluator produces a genuine `Value::Lambda` closure when it
evaluates a bare `FuncValue`, and `Apply`/`Filter`/`Exists`/`ForAll`/`Fold`
all evaluate their function-valued sub-expression first and then
pattern-match the *resulting `Value`* on `Value::Lambda`. Reproducing that
faithfully would need a `Value` constructor closing over an `Env`, which
breaks `eval`'s structural recursion — the whole point of `eval`/
`inlineFuns` in this repo (see `InlineFuns.lean`'s docstring).

Instead, every higher-order case here matches the *syntax* of its
function-valued sub-expression directly against `.funcValue params body`,
without ever calling `eval` on it. This is equivalent to sigma-rust
whenever the sub-expression *is* syntactically a `FuncValue` — true for
every `Filter`/`Exists`/`ForAll`/`Fold`/`Apply` node that reaches `eval`
after `inlineFuns` has run (`InlineFuns.lean`'s `inlineFuns` pass
eliminates exactly the `ValUse`-of-a-`FuncValue`-`ValDef` indirection that
would otherwise require a real closure; by the time `eval` sees an
`apply`/`filterOf`/etc. node, its function argument is always already a
literal `.funcValue`). A standalone `funcValue` reached via plain
recursive `eval` (not one of these special cases) has no sensible result
and is a hard error.
-/
import ErgoTreeLean.Syntax
import ErgoTreeLean.Context
import ErgoTreeLean.Numeric

namespace ErgoTreeLean

/-- Evaluation failures. A real interpreter would carry more structure; a
    single opaque reason string is enough for this development (we only
    ever pattern-match on `Except.ok` / `Except.error`, never on the
    message — the difftest harness compares *outcomes*, not messages). -/
inductive EvalError where
  | error (msg : String)
deriving Repr, DecidableEq

/-- Environment: `ValDef`/`FuncArg` bindings, most-recently bound first. -/
abbrev Env := List (Nat × Value)

/-! ### `SigmaAnd`/`SigmaOr` normalization

-- mirrors: ergotree-ir-0.28.0/src/sigma_protocol/sigma_boolean/{cand,cor}.rs

`Cand::normalized`/`Cor::normalized` (called by `sigma_and.rs`/
`sigma_or.rs`'s `eval` on the fully-evaluated `Vec<SigmaBoolean>`, *after*
every item has been evaluated — normalization never skips evaluating an
item):
- `Cand`: any `TrivialProp(false)` item collapses the whole thing to
  `TrivialProp(false)`; `TrivialProp(true)` items are dropped; 0 survivors
  → `TrivialProp(true)`; 1 survivor → that item, unwrapped; else → `Cand`
  of the survivors.
- `Cor`: symmetric (`true` absorbs, `false` is dropped). -/

def isTrivial (b : Bool) : SigmaBoolean → Bool
  | .trivial b' => b' == b
  | _ => false

/-- mirrors: `Cand::normalized` (`sigma_protocol/sigma_boolean/cand.rs`). -/
def normalizeCand (items : List SigmaBoolean) : SigmaBoolean :=
  if items.any (isTrivial false) then .trivial false
  else
    match items.filter (fun sb => !isTrivial true sb) with
    | [] => .trivial true
    | [x] => x
    | xs => .cand xs

/-- mirrors: `Cor::normalized` (`sigma_protocol/sigma_boolean/cor.rs`). -/
def normalizeCor (items : List SigmaBoolean) : SigmaBoolean :=
  if items.any (isTrivial true) then .trivial true
  else
    match items.filter (fun sb => !isTrivial false sb) with
    | [] => .trivial false
    | [x] => x
    | xs => .cor xs

/-! ### `Atleast` / `Cthreshold` normalization

-- mirrors: ergotree-ir-0.28.0/src/sigma_protocol/sigma_boolean/cthreshold.rs
   (`Cthreshold::reduce`)

Sigma-rust's real loop (`Cthreshold::reduce`) walks `children` left to
right, threading two counters — `curr_k` (bound remaining to satisfy) and
`children_left` (size of the "pool" still in play: every already-kept
non-trivial item plus every not-yet-processed item) — and checks, *before*
processing each item, whether `curr_k == 1` (then the *whole remaining
pool*, item included, reduces to a `Cor`) or `curr_k == children_left`
(then the whole remaining pool reduces to a `Cand`); otherwise a
`TrivialProp(true)` item is consumed (both counters drop), a
`TrivialProp(false)` item is dropped (`children_left` drops), and any
other item is kept in `res` (neither counter changes). If the loop
finishes without ever early-returning, it performs that *same* two-way
check one final time against the post-loop counters and `res` alone,
falling back to a genuine `Cthreshold` if neither holds.

`cthresholdGo` mirrors this as one recursive function over `remaining`
(the not-yet-processed suffix): checking the two conditions *before*
matching `remaining` unifies the loop body and its post-loop fallback
into a single shape — the base case `remaining = []` naturally reproduces
the "loop finished, do the final check" step, since `res ++ [] = res`. -/
def cthresholdGo (currK childrenLeft : Nat) (res : List SigmaBoolean) :
    List SigmaBoolean → SigmaBoolean
  | [] =>
      if currK == 1 then normalizeCor res
      else if currK == childrenLeft then normalizeCand res
      else .cthreshold currK res
  | sb :: rest =>
      if currK == 1 then normalizeCor (res ++ sb :: rest)
      else if currK == childrenLeft then normalizeCand (res ++ sb :: rest)
      else
        match sb with
        | .trivial true => cthresholdGo (currK - 1) (childrenLeft - 1) res rest
        | .trivial false => cthresholdGo currK (childrenLeft - 1) res rest
        | other => cthresholdGo currK childrenLeft (res ++ [other]) rest

/-- mirrors: `Cthreshold::reduce`'s own entry checks (`k == 0` → trivially
    true; `k > children.len()` → trivially false — the latter is dead code
    reached from `Atleast`'s own `eval` below, which already rejects
    `bound > input.len()` before ever calling this, but is kept for
    fidelity to the reusable Rust function). -/
def cthresholdReduce (k : Nat) (children : List SigmaBoolean) : SigmaBoolean :=
  if k == 0 then .trivial true
  else if k > children.length then .trivial false
  else cthresholdGo k children.length [] children

/-- Coerce a list of `Value`s (the results of `SigmaOr`/`SigmaAnd`'s items)
    into a list of `SigmaBoolean`s, failing if any item is not a
    sigma-proposition. -- mirrors: eval/sigma_and.rs, eval/sigma_or.rs
    (`try_extract_into::<SigmaProp>`). -/
def toSigmaProps : List Value → Except EvalError (List SigmaBoolean)
  | [] => pure []
  | .vSigmaProp sb :: rest => do
      let sbs ← toSigmaProps rest
      pure (sb :: sbs)
  | _ :: _ => .error (.error "sigmaOr/sigmaAnd: item is not a SigmaProp")

/-- `Coll[Byte]` element → `Value`, sign-extended (`Coll[Byte]`'s elements
    are signed `i8` in sigma-rust — see `Numeric.lean`'s `signedByteVal`).
    Used whenever a raw `List UInt8` field on `Box`
    (`propositionBytes`/`id`/a token id) is lifted into the `Value` world. -/
def bytesToVColl (bs : List UInt8) : Value :=
  .vColl .sByte (bs.map (fun b => .vByte (signedByteVal b)))

/-- Extract a `Coll[Byte]`'s raw bytes back out (inverse of
    `bytesToVColl`'s sign-extension), used by `ByteArrayToBigInt`/
    `ByteArrayToLong`. -/
def vsToBytes : List Value → Except EvalError (List UInt8)
  | [] => pure []
  | .vByte v :: rest => do
      let bs ← vsToBytes rest
      let raw : Int := if v < 0 then v + 256 else v
      pure (UInt8.ofNat raw.toNat :: bs)
  | _ :: _ => .error (.error "expected Coll[Byte] element to be a Byte")

/-- Extract a `Coll[Boolean]`'s elements as plain `Bool`s, used by
    `andOf`/`orOf`. -- mirrors: eval/and.rs, eval/or.rs (which fully
    materialize the `Vec<bool>` before `.all()`/`.any()`). -/
def toBoolList : List Value → Except EvalError (List Bool)
  | [] => pure []
  | .vBool b :: rest => do
      let bs ← toBoolList rest
      pure (b :: bs)
  | _ :: _ => .error (.error "expected Coll[Boolean] element to be a Bool")

/-- The tuple `Box.register`'s R3 case and `.extractCreationInfo` both
    produce: `(creationHeight, transactionId ++ indexBEBytes index)`.
    -- mirrors: chain/ergo_box.rs (`ErgoBox::creation_info`). -/
def Box.creationInfoValue (b : Box) : Value :=
  .vTuple [.vInt b.creationHeight, bytesToVColl (b.transactionId ++ Box.indexBEBytes b.index)]

/-- Read a single register by index: the four mandatory registers (0..3),
    *derived* from the box's other fields, and the six non-mandatory
    registers (4..9), a plain lookup in `registers`. Used by
    `ExtractRegisterAs` below.
    -- mirrors: chain/ergo_box.rs (`ErgoBox::get_register`, ~line 154):
    `R0 ↦ Some(value.into())` (`SLong`), `R1 ↦ Some(script_bytes().into())`
    (`Coll[Byte]` — this model's `propositionBytes` is already exactly
    `script_bytes()`, see `Syntax.lean`), `R2 ↦ Some(tokens_raw().into())`
    (`Coll[(Coll[Byte], Long)]`, matching the `Box.tokens` PropertyCall
    case below byte for byte), `R3 ↦ Some(creation_info().into())`
    (`Box.creationInfoValue` above); 4..9 ↦
    `additional_registers.get_constant`, i.e. the `Box.registers` lookup
    this function used to be (before mandatory registers were derived).
    Unlike sigma-rust's `Result<Option<Constant>, RegisterValueError>`
    (which can fail on an unparseable *stored* register value), this model
    has no "unparseable" `Value` to represent, so every mandatory register
    is always `some` — matching the success path `get_register`/
    `extract_reg_as.rs` take for every `Box` this model can construct. -/
def Box.register (b : Box) (idx : Int) : Option Value :=
  if idx == 0 then some (.vLong b.value)
  else if idx == 1 then some (bytesToVColl b.propositionBytes)
  else if idx == 2 then
    some (.vColl (.sTuple [.sColl .sByte, .sLong])
      (b.tokens.map (fun (tid, amt) => .vTuple [bytesToVColl tid, .vLong amt])))
  else if idx == 3 then some b.creationInfoValue
  else (b.registers.find? (fun p => (p.1 : Int) == idx)).map Prod.snd

/-- `Coll.indexOf(elem, from)`'s per-element search, walking `vs` left to
    right while threading `i`, the *absolute* index of `vs`'s head in the
    original (undropped) collection — see `Value.indexOf` below, which
    seeds `i` at the already-clamped `from` and passes it `vs.drop from`.
    First element equal to `elem` under `Value.beq` wins; `[]` (search ran
    off the end) → `-1`. -- mirrors: `eval/scoll.rs`'s `INDEX_OF_EVAL_FN`,
    the `.position(|it| it == target_element)` step. -/
def indexOfGo (elem : Value) : Int → List Value → Int
  | _, [] => -1
  | i, v :: vs => if Value.beq v elem then i else indexOfGo elem (i + 1) vs

/-- `SCollection.indexOf` (`type_id=12`, `method_id=26`): the index of the
    first element of `vs` equal to `elem` (`Value.beq` — the same total
    structural equality `BinOp`'s `Eq`/`NEq` use; for a `Coll[Box]` this is
    `Box.beq`'s full eight-field structural comparison, matching `ErgoBox`'s
    derived `PartialEq` in sigma-rust — no divergence found), searching only
    from index `from` onward; `-1` if none matches (including when `from` is
    at or past `vs.length`). -- mirrors: `ergotree-interpreter-0.28.0`'s
    `eval/scoll.rs`, `INDEX_OF_EVAL_FN` exactly:
    `args.get(1)…try_extract_into::<i32>()?.max(0)` clamps a *negative*
    `from` to `0` (never "from the end", and never an error) before
    `.skip(from as usize).position(|it| it == target_element).map(|idx| idx
    as i32 + from).unwrap_or(-1)` — `from` past the collection's length just
    makes `.skip` produce an empty iterator, so that case is `-1` too, not
    an error. No known Scala-node divergence for this method. -/
def Value.indexOf (vs : List Value) (elem : Value) (fromArg : Int) : Int :=
  let from' := max fromArg 0
  indexOfGo elem from' (vs.drop from'.toNat)

/-- Bind a `FuncValue`'s parameter list to a list of already-evaluated
    argument values, in order; `none` on an arity mismatch. -/
def bindArgs (env : Env) : List (Nat × SType) → List Value → Option Env
  | [], [] => some env
  | (id, _) :: ps, v :: vs => bindArgs ((id, v) :: env) ps vs
  | _, _ => none

mutual

/-- Evaluate a single expression under `consts` (EIP-5 template constants),
    `ctx` (the spending context) and `env` (local `ValDef`/`FuncArg`
    bindings). Every case names the sigma-rust `eval/*.rs` file it
    mirrors. -/
def eval (consts : List Value) (ctx : Context) (env : Env) : Expr → Except EvalError Value
  -- mirrors: eval/expr.rs (Const is a no-op at eval time)
  | .const v => pure v
  -- mirrors: eval/subst_const.rs / the exporter's `ConstantPlaceholder` handling
  | .constPlaceholder id _tpe =>
      match consts[id]? with
      | some v => pure v
      | none => .error (.error s!"constPlaceholder: index {id} out of range")
  -- mirrors: eval/block.rs
  | .blockValue defs result => do
      let env' ← evalDefs consts ctx env defs
      eval consts ctx env' result
  -- mirrors: eval/val_use.rs
  | .valUse id _tpe =>
      match env.find? (fun p => p.1 == id) with
      | some (_, v) => pure v
      | none => .error (.error s!"valUse: unbound id {id}")
  -- mirrors: eval/global_vars.rs (GlobalVars::Outputs)
  | .outputs => pure (.vColl .sBox (ctx.outputs.map .vBox))
  -- mirrors: eval/global_vars.rs (GlobalVars::Height — `ctx.height as i32`, an SInt not SLong)
  | .height => pure (.vInt (ctx.height : Int))
  -- mirrors: eval/global_vars.rs (GlobalVars::SelfBox)
  | .selfBox => pure (.vBox ctx.selfBox)
  -- mirrors: eval/global_vars.rs (GlobalVars::Inputs)
  | .inputs => pure (.vColl .sBox (ctx.inputs.map .vBox))
  -- mirrors: eval/expr.rs's `Expr::Context` — a bare `CONTEXT`
  -- has no standalone evaluation in this model (sigma-rust's own
  -- `Value::Context` is likewise just a dataless marker property-call
  -- eval-fns check against, never produced from evaluating anything);
  -- the one property this development supports (`dataInputs`) is matched
  -- syntactically at `.propertyCall .context 101 1` below instead of
  -- going through this case at all.
  | .context =>
      .error (.error "context: standalone CONTEXT value has no defined evaluation \
        (should only appear as PropertyCall's receiver)")
  -- mirrors: eval/coll_by_index.rs (`ByIndex`'s index is always SInt)
  | .byIndex coll idx default => do
      let cv ← eval consts ctx env coll
      match cv with
      | .vColl _ vs => do
          let iv ← eval consts ctx env idx
          match iv with
          | .vInt i =>
              if i < 0 then
                match default with
                | some d => eval consts ctx env d
                | none => .error (.error "byIndex: index out of bounds and no default")
              else
                match vs[i.toNat]? with
                | some v => pure v
                | none =>
                    match default with
                    | some d => eval consts ctx env d
                    | none => .error (.error "byIndex: index out of bounds and no default")
          | _ => .error (.error "byIndex: index is not an Int")
      | _ => .error (.error "byIndex: not a collection")
  -- mirrors: eval/atleast.rs + sigma_protocol/sigma_boolean/cthreshold.rs
  -- (`Atleast` — ErgoScript's `atLeast(bound, items)`). Order
  -- matches the real `eval`: bound must fit a `u8` (`0..=255`) *before*
  -- the `bound > input size` check is even reached (a negative bound is
  -- therefore always an error, not "vacuously true" — that would be
  -- `cthresholdReduce`'s own `k == 0` case, only reachable for `bound = 0`
  -- exactly, since `-1..` all fail the `u8` conversion first).
  | .atLeast boundE inputE => do
      let bv ← eval consts ctx env boundE
      let iv ← eval consts ctx env inputE
      match bv, iv with
      | .vInt bound, .vColl _ vs => do
          let sbs ← toSigmaProps vs
          if bound < 0 || bound > 255 then
            .error (.error s!"atLeast: bound {bound} does not fit a u8 (0..=255)")
          else if bound > (sbs.length : Int) then
            .error (.error s!"atLeast: bound {bound} > input size {sbs.length}")
          -- `input.try_into()` into `SigmaConjectureItems` (`BoundedVec<_, 1,
          -- 255>`) fails on an empty input, so `atLeast(0, [])` is an error,
          -- not `trivial true`.
          else if sbs.isEmpty then
            .error (.error "atLeast: empty input")
          else
            pure (.vSigmaProp (cthresholdReduce bound.toNat sbs))
      | _, _ => .error (.error "atLeast: bad operand types (expected Int bound, Coll[SigmaProp] input)")
  -- mirrors: eval/calc_blake2b256.rs, via `ctx.oracle.blake2b256`
  -- — see `Context.lean`'s `Oracle`; never computes a real hash here.
  | .calcBlake2b256 e => do
      let v ← eval consts ctx env e
      match v with
      | .vColl .sByte vs => do
          let bs ← vsToBytes vs
          pure (bytesToVColl (ctx.oracle.blake2b256 bs))
      | _ => .error (.error "calcBlake2b256: not a Coll[Byte]")
  -- mirrors: eval/deserialize_context.rs, via `ctx.oracle.deserialize`
  -- — see `Syntax.lean`'s `deserializeContext` docstring for
  -- why the oracle returns the already-*evaluated* `Value`, not an
  -- `Expr` to recurse into.
  | .deserializeContext varId tpe => do
      match ctx.getVar varId with
      | none =>
          .error (.error s!"deserializeContext: no value with id {varId} in context extension map")
      | some v =>
          match v with
          | .vColl .sByte vs => do
              let bs ← vsToBytes vs
              match ctx.oracle.deserialize bs with
              | none =>
                  .error (.error "deserializeContext: sigma-rust would fail to deserialize/evaluate these bytes")
              | some result =>
                  if SType.beq (typeOf result) tpe then pure result
                  else .error (.error "deserializeContext: deserialized result has the wrong type")
          | _ => .error (.error "deserializeContext: stored context-extension value is not Coll[Byte]")
  -- mirrors: eval/sigma_or.rs + sigma_boolean/cor.rs's `Cor::normalized`
  | .sigmaOr items => do
      let vs ← evalList consts ctx env items
      let sbs ← toSigmaProps vs
      pure (.vSigmaProp (normalizeCor sbs))
  -- mirrors: eval/sigma_and.rs + sigma_boolean/cand.rs's `Cand::normalized`
  | .sigmaAnd items => do
      let vs ← evalList consts ctx env items
      let sbs ← toSigmaProps vs
      pure (.vSigmaProp (normalizeCand sbs))
  -- mirrors: eval/create_provedlog.rs
  | .createProveDlog e => do
      let v ← eval consts ctx env e
      match v with
      | .vGroupElement g => pure (.vSigmaProp (.proveDlog g))
      | _ => .error (.error "createProveDlog: not a GroupElement")
  -- mirrors: eval/bool_to_sigma.rs
  | .boolToSigmaProp e => do
      let v ← eval consts ctx env e
      match v with
      | .vBool b => pure (.vSigmaProp (.trivial b))
      | _ => .error (.error "boolToSigmaProp: not a Bool")
  -- mirrors: eval/sigma_prop_bytes.rs (`Value::SigmaProp(sp) => sp.prop_bytes()`,
  -- any other value an error; see `Syntax.lean`'s `SigmaBoolean.propBytes`
  -- for the exact byte layout and why `prop_bytes()` itself never errors
  -- for a shape this model can build)
  | .sigmaPropBytes e => do
      let v ← eval consts ctx env e
      match v with
      | .vSigmaProp sb => pure (bytesToVColl sb.propBytes)
      | _ => .error (.error "sigmaPropBytes: not a SigmaProp")
  -- mirrors: eval/bin_op.rs (`LogicalOp::And` — lazy: rhs only evaluated if lhs is true)
  | .binOp (.logical .and) l r => do
      let lv ← eval consts ctx env l
      match lv with
      | .vBool false => pure (.vBool false)
      | .vBool true => do
          let rv ← eval consts ctx env r
          match rv with
          | .vBool b => pure (.vBool b)
          | _ => .error (.error "binOp and: rhs is not a Bool")
      | _ => .error (.error "binOp and: lhs is not a Bool")
  -- mirrors: eval/bin_op.rs (`LogicalOp::Or` — lazy: rhs only evaluated if lhs is false)
  | .binOp (.logical .or) l r => do
      let lv ← eval consts ctx env l
      match lv with
      | .vBool true => pure (.vBool true)
      | .vBool false => do
          let rv ← eval consts ctx env r
          match rv with
          | .vBool b => pure (.vBool b)
          | _ => .error (.error "binOp or: rhs is not a Bool")
      | _ => .error (.error "binOp or: lhs is not a Bool")
  -- mirrors: eval/bin_op.rs (`LogicalOp::Xor` — always evaluates both sides)
  | .binOp (.logical .xor) l r => do
      let lv ← eval consts ctx env l
      let rv ← eval consts ctx env r
      match lv, rv with
      | .vBool a, .vBool b => pure (.vBool (Bool.xor a b))
      | _, _ => .error (.error "binOp xor: operand is not a Bool")
  -- mirrors: eval/bin_op.rs (`RelationOp`: Eq/NEq are total `Value.beq`;
  -- Ge/Gt/Le/Lt dispatch on the left operand's numeric kind and require
  -- the right operand to be the exact same kind — a type mismatch is a
  -- hard error, not a coercion)
  | .binOp (.relation op) l r => do
      let lv ← eval consts ctx env l
      let rv ← eval consts ctx env r
      match op with
      | .eq => pure (.vBool (Value.beq lv rv))
      | .neq => pure (.vBool (!Value.beq lv rv))
      | .ge | .gt | .le | .lt =>
          match sameKindRaw lv rv with
          | none => .error (.error "binOp relation: mismatched or non-numeric operand types")
          | some (_, a, b) =>
              pure (.vBool
                (match op with
                  | .ge => a ≥ b
                  | .gt => a > b
                  | .le => a ≤ b
                  | .lt => a < b
                  | .eq | .neq => false))
  -- mirrors: eval/bin_op.rs (`ArithOp`: checked per-width; BigInt modulo
  -- uses the positive-divisor-only floor-mod rule — see `Numeric.lean`)
  | .binOp (.arith op) l r => do
      let lv ← eval consts ctx env l
      let rv ← eval consts ctx env r
      match sameKindRaw lv rv with
      | none => .error (.error "binOp arith: mismatched or non-numeric operand types")
      | some (k, a, b) =>
          let res : Option Int :=
            match op with
            | .plus => checkedArith k (· + ·) a b
            | .minus => checkedArith k (· - ·) a b
            | .multiply => checkedArith k (· * ·) a b
            | .divide => checkedDiv k a b
            | .modulo => if k == .bigint then checkedRemBigInt a b else checkedRemFixed k a b
            | .max => some (max a b)
            | .min => some (min a b)
          match res with
          | some v => pure (k.wrap v)
          | none => .error (.error "binOp arith: overflow or arithmetic error")
  -- mirrors: eval/bin_op.rs (`BitOp`: plain two's-complement, never overflows)
  | .binOp (.bit op) l r => do
      let lv ← eval consts ctx env l
      let rv ← eval consts ctx env r
      match sameKindRaw lv rv with
      | none => .error (.error "binOp bit: mismatched or non-numeric operand types")
      | some (k, a, b) =>
          let f : Nat → Nat → Nat :=
            match op with
            | .bitAnd => Nat.land
            | .bitOr => Nat.lor
            | .bitXor => Nat.xor
          pure (k.wrap (bitOpOn k f a b))
  -- mirrors: eval/and.rs (`allOf` — the whole `Coll[Boolean]` is
  -- materialized eagerly, then `.all()`; no short-circuit of evaluation)
  | .andOf input => do
      let v ← eval consts ctx env input
      match v with
      | .vColl .sBoolean vs => do
          let bs ← toBoolList vs
          pure (.vBool (bs.all id))
      | _ => .error (.error "andOf: not a Coll[Boolean]")
  -- mirrors: eval/or.rs (`anyOf`)
  | .orOf input => do
      let v ← eval consts ctx env input
      match v with
      | .vColl .sBoolean vs => do
          let bs ← toBoolList vs
          pure (.vBool (bs.any id))
      | _ => .error (.error "orOf: not a Coll[Boolean]")
  -- mirrors: eval/logical_not.rs
  | .logicalNot e => do
      let v ← eval consts ctx env e
      match v with
      | .vBool b => pure (.vBool (!b))
      | _ => .error (.error "logicalNot: not a Bool")
  -- mirrors: eval/if_op.rs (lazy — only the taken branch is evaluated)
  | .ifExpr cond thenE elseE => do
      let cv ← eval consts ctx env cond
      match cv with
      | .vBool true => eval consts ctx env thenE
      | .vBool false => eval consts ctx env elseE
      | _ => .error (.error "ifExpr: condition is not a Bool")
  -- mirrors: eval/extract_script_bytes.rs
  | .extractScriptBytes e => do
      let v ← eval consts ctx env e
      match v with
      | .vBox b => pure (bytesToVColl b.propositionBytes)
      | _ => .error (.error "extractScriptBytes: not a Box")
  -- mirrors: eval/extract_amount.rs
  | .extractAmount e => do
      let v ← eval consts ctx env e
      match v with
      | .vBox b => pure (.vLong b.value)
      | _ => .error (.error "extractAmount: not a Box")
  -- mirrors: eval/extract_id.rs (a field read, not a hash computation — see `Box.id`)
  | .extractId e => do
      let v ← eval consts ctx env e
      match v with
      | .vBox b => pure (bytesToVColl b.id)
      | _ => .error (.error "extractId: not a Box")
  -- mirrors: eval/extract_creation_info.rs
  | .extractCreationInfo e => do
      let v ← eval consts ctx env e
      match v with
      | .vBox b => pure b.creationInfoValue
      | _ => .error (.error "extractCreationInfo: not a Box")
  -- mirrors: eval/extract_reg_as.rs (no type-check against `elemTpe` —
  -- a mismatch only surfaces later, when the `Value` is used)
  | .extractRegisterAs input registerId _elemTpe => do
      let v ← eval consts ctx env input
      match v with
      | .vBox b => pure (.vOption _elemTpe (b.register registerId))
      | _ => .error (.error "extractRegisterAs: not a Box")
  -- mirrors: eval/option_get.rs
  | .optionGet e => do
      let v ← eval consts ctx env e
      match v with
      | .vOption _ (some x) => pure x
      | .vOption _ none => .error (.error "optionGet: None")
      | _ => .error (.error "optionGet: not an Option")
  -- mirrors: eval/option_is_defined.rs
  | .optionIsDefined e => do
      let v ← eval consts ctx env e
      match v with
      | .vOption _ o => pure (.vBool o.isSome)
      | _ => .error (.error "optionIsDefined: not an Option")
  -- mirrors: eval/option_get_or_else.rs
  | .optionGetOrElse e default => do
      let v ← eval consts ctx env e
      match v with
      | .vOption _ (some x) => pure x
      | .vOption _ none => eval consts ctx env default
      | _ => .error (.error "optionGetOrElse: not an Option")
  -- mirrors: eval/get_var.rs (absent id → `none`, no error; present but
  -- wrong dynamic type → error — the opposite asymmetry from
  -- `ExtractRegisterAs`, which never type-checks)
  | .getVar varId varTpe => do
      match ctx.getVar varId with
      | none => pure (.vOption varTpe none)
      | some v =>
          if SType.beq (typeOf v) varTpe then pure (.vOption varTpe (some v))
          else .error (.error "getVar: stored value has the wrong dynamic type")
  -- mirrors: eval/collection.rs (left-to-right, no special-casing for
  -- `Coll[Byte]` — see module docstring on the uniform `vColl` representation)
  | .collection elemTpe items => do
      let vs ← evalList consts ctx env items
      pure (.vColl elemTpe vs)
  -- mirrors: eval/tuple.rs
  | .tuple items => do
      let vs ← evalList consts ctx env items
      pure (.vTuple vs)
  -- mirrors: eval/select_field.rs (`field_index` is 1-based;
  -- `zero_based_index() = self.0 - 1`)
  | .selectField input fieldIndex => do
      let v ← eval consts ctx env input
      match v with
      | .vTuple vs =>
          if fieldIndex ≥ 1 then
            match vs[fieldIndex - 1]? with
            | some x => pure x
            | none => .error (.error "selectField: index out of bounds")
          else .error (.error "selectField: index must be ≥ 1")
      | _ => .error (.error "selectField: not a Tuple")
  -- mirrors: eval/coll_size.rs
  | .sizeOf e => do
      let v ← eval consts ctx env e
      match v with
      | .vColl _ vs => pure (.vInt (vs.length : Int))
      | _ => .error (.error "sizeOf: not a collection")
  -- mirrors: eval/coll_slice.rs (clamped to `[0, len]`, never errors on an
  -- out-of-range bound — not exercised by `sell-order`, which never
  -- calls `.slice`; kept for completeness)
  | .sliceOf input fromE untilE => do
      let v ← eval consts ctx env input
      let fv ← eval consts ctx env fromE
      let uv ← eval consts ctx env untilE
      match v, fv, uv with
      | .vColl t vs, .vInt f, .vInt u =>
          let len : Int := (vs.length : Int)
          let clamp (x : Int) : Nat := (max 0 (min x len)).toNat
          let f' := clamp f
          let u' := clamp u
          pure (.vColl t ((vs.drop f').take (u' - f')))
      | _, _, _ => .error (.error "sliceOf: bad operand types")
  -- mirrors: eval/coll_filter.rs (left-to-right; see `filterHelper`)
  | .filterOf input (.funcValue [(argId, _)] body) elemTpe => do
      let v ← eval consts ctx env input
      match v with
      | .vColl _ vs => do
          let vs' ← filterHelper consts ctx env argId body vs
          pure (.vColl elemTpe vs')
      | _ => .error (.error "filterOf: not a collection")
  | .filterOf _ _ _ =>
      .error (.error "filterOf: condition is not a single-argument literal funcValue")
  -- mirrors: eval/coll_map.rs (left-to-right; see `mapHelper`)
  | .mapOf input (.funcValue [(argId, _)] body) elemTpe => do
      let v ← eval consts ctx env input
      match v with
      | .vColl _ vs => do
          let vs' ← mapHelper consts ctx env argId body vs
          pure (.vColl elemTpe vs')
      | _ => .error (.error "mapOf: not a collection")
  | .mapOf _ _ _ =>
      .error (.error "mapOf: mapper is not a single-argument literal funcValue")
  -- mirrors: eval/coll_exists.rs (short-circuits on the first `true`)
  | .existsOf input (.funcValue [(argId, _)] body) _ => do
      let v ← eval consts ctx env input
      match v with
      | .vColl _ vs => do
          let b ← existsHelper consts ctx env argId body vs
          pure (.vBool b)
      | _ => .error (.error "existsOf: not a collection")
  | .existsOf _ _ _ =>
      .error (.error "existsOf: condition is not a single-argument literal funcValue")
  -- mirrors: eval/coll_forall.rs (short-circuits on the first `false`)
  | .forAllOf input (.funcValue [(argId, _)] body) _ => do
      let v ← eval consts ctx env input
      match v with
      | .vColl _ vs => do
          let b ← forallHelper consts ctx env argId body vs
          pure (.vBool b)
      | _ => .error (.error "forAllOf: not a collection")
  | .forAllOf _ _ _ =>
      .error (.error "forAllOf: condition is not a single-argument literal funcValue")
  -- mirrors: eval/coll_fold.rs (left fold; `fold_op`'s single argument is
  -- the `(acc, elem)` pair, mirrored here as a 2-tuple bound to the
  -- funcValue's one parameter — not exercised by `sell-order`, which
  -- never calls `.fold`; kept for completeness)
  | .foldOf input zero (.funcValue [(argId, _)] body) => do
      let v ← eval consts ctx env input
      let z ← eval consts ctx env zero
      match v with
      | .vColl _ vs => foldHelper consts ctx env argId body z vs
      | _ => .error (.error "foldOf: not a collection")
  | .foldOf _ _ _ =>
      .error (.error "foldOf: fold_op is not a single-argument literal funcValue")
  -- mirrors: eval/coll_append.rs
  | .appendOf input col2 => do
      let v1 ← eval consts ctx env input
      let v2 ← eval consts ctx env col2
      match v1, v2 with
      | .vColl t1 vs1, .vColl _ vs2 => pure (.vColl t1 (vs1 ++ vs2))
      | _, _ => .error (.error "appendOf: not collections")
  -- mirrors: eval/func_value.rs — see the "no closures" module docstring:
  -- a *standalone* funcValue (not caught by apply/filterOf/existsOf/
  -- forAllOf/foldOf's dedicated cases above) has no defined evaluation here.
  | .funcValue _ _ =>
      .error (.error "funcValue: standalone lambda has no defined evaluation \
        (should only appear as the direct argument to apply/filterOf/existsOf/\
        forAllOf/foldOf, after inlineFuns)")
  -- mirrors: eval/apply.rs (evaluate the function operand, then all
  -- arguments left-to-right, then bind and evaluate the body — see the
  -- "no closures" module docstring for why `func` must already be a
  -- literal funcValue here, post-`inlineFuns`)
  | .apply (.funcValue params body) args => do
      let avs ← evalList consts ctx env args
      match bindArgs env params avs with
      | some env' => eval consts ctx env' body
      | none => .error (.error "apply: argument count mismatch")
  | .apply _ _ =>
      .error (.error "apply: function operand is not a literal funcValue (inlineFuns should have produced one)")
  -- mirrors: eval/scontext.rs's `DATA_INPUTS_EVAL_FN`. Matched
  -- syntactically on the receiver being the literal `.context` node
  -- (never evaluating it to a `Value` first — see `.context`'s own case/
  -- docstring above: there is no `Value` constructor for `CONTEXT` in
  -- this model, mirroring sigma-rust's dataless `Value::Context` marker).
  | .propertyCall .context 101 1 => pure (.vColl .sBox (ctx.dataInputs.map .vBox))
  -- mirrors: eval/property_call.rs's generic `SCollection.indices`
  -- (`type_id=12`, `method_id=14`) — the `0 ..< size` index list of any
  -- collection (used by some downstream contracts).
  | .propertyCall obj 12 14 => do
      let v ← eval consts ctx env obj
      match v with
      | .vColl _ vs => pure (.vColl .sInt ((List.range vs.length).map (fun (i : Nat) => Value.vInt (i : Int))))
      | _ => .error (.error "propertyCall indices: not a collection")
  -- mirrors: eval/property_call.rs + eval/sbox.rs (`Box.tokens`, the only
  -- PropertyCall/MethodCall either covered contract emits: type_id=99
  -- (SBox), method_id=8)
  | .propertyCall obj 99 8 => do
      let v ← eval consts ctx env obj
      match v with
      | .vBox b =>
          pure (.vColl (.sTuple [.sColl .sByte, .sLong])
            (b.tokens.map (fun (tid, amt) => .vTuple [bytesToVColl tid, .vLong amt])))
      | _ => .error (.error "propertyCall Box.tokens: not a Box")
  | .propertyCall _ typeId methodId =>
      .error (.error s!"propertyCall: unsupported method {typeId}.{methodId}")
  -- mirrors: eval/method_call.rs (obj, then args left to right, eagerly)
  -- + eval/scoll.rs's `INDEX_OF_EVAL_FN` (`SCollection.indexOf`,
  -- `type_id=12`, `method_id=26`) — see `Value.indexOf`'s docstring for the
  -- exact semantics (`from` clamped to ≥ 0, `-1` when not found).
  | .methodCall obj 12 26 [elemE, fromE] => do
      let v ← eval consts ctx env obj
      let ev ← eval consts ctx env elemE
      let fv ← eval consts ctx env fromE
      match v, fv with
      | .vColl _ vs, .vInt f => pure (.vInt (Value.indexOf vs ev f))
      | .vColl _ _, _ => .error (.error "methodCall indexOf: from is not an Int")
      | _, _ => .error (.error "methodCall indexOf: not a collection")
  | .methodCall _ typeId methodId _ =>
      .error (.error s!"methodCall: unsupported method {typeId}.{methodId}")
  -- mirrors: eval/upcast.rs (only ever widens; same-kind is a no-op)
  | .upcast e tpe => do
      let v ← eval consts ctx env e
      match v.numKind, sTypeToNumKind? tpe with
      | some (src, raw), some tgt =>
          match upcastValue src raw tgt with
          | some r => pure (tgt.wrap r)
          | none => .error (.error "upcast: source is not narrower than (or equal to) the target")
      | _, _ => .error (.error "upcast: not a numeric value/type")
  -- mirrors: eval/downcast.rs (an explicit, non-uniform table — see `Numeric.lean`)
  | .downcast e tpe => do
      let v ← eval consts ctx env e
      match v.numKind, sTypeToNumKind? tpe with
      | some (src, raw), some tgt =>
          match downcastValue src raw tgt with
          | some r => pure (tgt.wrap r)
          | none => .error (.error "downcast: overflow or unsupported source/target pair")
      | _, _ => .error (.error "downcast: not a numeric value/type")
  -- mirrors: eval/negation.rs (checked — overflows only at each type's minimum)
  | .negation e => do
      let v ← eval consts ctx env e
      match v.numKind with
      | some (k, raw) =>
          match checkedNeg k raw with
          | some r => pure (k.wrap r)
          | none => .error (.error "negation: overflow")
      | none => .error (.error "negation: not a numeric value")
  -- mirrors: eval/byte_array_to_bigint.rs
  | .byteArrayToBigInt e => do
      let v ← eval consts ctx env e
      match v with
      | .vColl .sByte vs => do
          let bs ← vsToBytes vs
          match byteArrayToBigInt bs with
          | some r => pure (.vBigInt r)
          | none => .error (.error "byteArrayToBigInt: empty input or value out of BigInt256 range")
      | _ => .error (.error "byteArrayToBigInt: not a Coll[Byte]")
  -- mirrors: eval/byte_array_to_long.rs
  | .byteArrayToLong e => do
      let v ← eval consts ctx env e
      match v with
      | .vColl .sByte vs => do
          let bs ← vsToBytes vs
          match byteArrayToLong bs with
          | some r => pure (.vLong r)
          | none => .error (.error "byteArrayToLong: fewer than 8 bytes")
      | _ => .error (.error "byteArrayToLong: not a Coll[Byte]")
termination_by e => (sizeOf e, 0)

/-- Evaluate a `BlockValue`'s `ValDef` list in order, threading the growing
    environment (a failing `ValDef` fails evaluation of the whole block). -/
def evalDefs (consts : List Value) (ctx : Context) (env : Env) : List (Nat × Expr) → Except EvalError Env
  | [] => pure env
  | (id, e) :: rest => do
      let v ← eval consts ctx env e
      evalDefs consts ctx ((id, v) :: env) rest
termination_by defs => (sizeOf defs, 0)

/-- Evaluate a list of expressions in order (used by `SigmaOr`/`SigmaAnd`/
    `Collection`/`Tuple`/`Apply`'s arguments; all items are evaluated
    eagerly, unlike `BinOp`'s short-circuiting logical `and`/`or`). -/
def evalList (consts : List Value) (ctx : Context) (env : Env) : List Expr → Except EvalError (List Value)
  | [] => pure []
  | e :: rest => do
      let v ← eval consts ctx env e
      let vs ← evalList consts ctx env rest
      pure (v :: vs)
termination_by items => (sizeOf items, 0)

/-- `Filter`'s per-element loop: no short-circuit (every element's
    predicate is evaluated, left to right; the first predicate *error*
    still aborts the whole filter, since `Except`'s `do` is strict).

    ### Termination note (applies to this and the three helpers below)

    `eval`/`evalDefs`/`evalList` alone are plain structural recursion on an
    `Expr`/list-of-`Expr` that shrinks on every call — Lean's equation
    compiler finds that automatically. These four helpers break that: they
    recurse on a *runtime* `List Value` (e.g. a box's token list) whose
    length has no relationship to any `Expr`'s AST size, while also calling
    back into `eval` on `body` — the *same* `Expr`, unchanged, on every
    iteration. Neither "the `Expr` shrinks" nor "the list shrinks" alone
    describes the whole mutual clique, so each function here gets an
    explicit two-part `termination_by (sizeOf key_expr, list_length)`
    measure, compared lexicographically:
    - Self-recursion (e.g. `filterHelper … vs` from `v :: vs`): `body` is
      unchanged (first component ties), but the list strictly shrinks
      (second component strictly decreases) — decreases lexicographically.
    - The call into `eval … body`: `eval`'s measure there is
      `(sizeOf body, 0)`, strictly less than this function's own measure
      `(sizeOf body, 1 + (v :: vs).length)` at the call site, since the
      first components are *equal* and `0 < 1 + (v :: vs).length` —
      decreases lexicographically.
    - The call *into* one of these helpers from `eval` (e.g. `eval`
      processing `.filterOf input (.funcValue [(argId,_)] body) elemTpe`,
      calling `filterHelper … body vs`): `body` is a strict subterm of the
      `.filterOf …` expression `eval` was processing, so the first
      component alone (`sizeOf body < sizeOf (.filterOf …)`) already gives
      a strict decrease, regardless of the list. -/
def filterHelper (consts : List Value) (ctx : Context) (env : Env) (argId : Nat) (body : Expr) :
    List Value → Except EvalError (List Value)
  | [] => pure []
  | v :: vs => do
      let bv ← eval consts ctx ((argId, v) :: env) body
      match bv with
      | .vBool b => do
          let rest ← filterHelper consts ctx env argId body vs
          pure (if b then v :: rest else rest)
      | _ => .error (.error "filter: predicate is not a Bool")
termination_by l => (sizeOf body, 1 + l.length)

/-- `Exists`'s per-element loop: stops (returns `true`) at the first
    element whose predicate is `true`, *without* evaluating the predicate
    on any later element (`eval/coll_exists.rs`). See `filterHelper`'s
    docstring for the termination measure. -/
def existsHelper (consts : List Value) (ctx : Context) (env : Env) (argId : Nat) (body : Expr) :
    List Value → Except EvalError Bool
  | [] => pure false
  | v :: vs => do
      let bv ← eval consts ctx ((argId, v) :: env) body
      match bv with
      | .vBool true => pure true
      | .vBool false => existsHelper consts ctx env argId body vs
      | _ => .error (.error "exists: predicate is not a Bool")
termination_by l => (sizeOf body, 1 + l.length)

/-- `ForAll`'s per-element loop: stops (returns `false`) at the first
    element whose predicate is `false` (`eval/coll_forall.rs`). See
    `filterHelper`'s docstring for the termination measure. -/
def forallHelper (consts : List Value) (ctx : Context) (env : Env) (argId : Nat) (body : Expr) :
    List Value → Except EvalError Bool
  | [] => pure true
  | v :: vs => do
      let bv ← eval consts ctx ((argId, v) :: env) body
      match bv with
      | .vBool false => pure false
      | .vBool true => forallHelper consts ctx env argId body vs
      | _ => .error (.error "forall: predicate is not a Bool")
termination_by l => (sizeOf body, 1 + l.length)

/-- `Map`'s per-element loop: applies `body` to every element, in order,
    building the result list (`eval/coll_map.rs`). See
    `filterHelper`'s docstring for the termination measure. -/
def mapHelper (consts : List Value) (ctx : Context) (env : Env) (argId : Nat) (body : Expr) :
    List Value → Except EvalError (List Value)
  | [] => pure []
  | v :: vs => do
      let bv ← eval consts ctx ((argId, v) :: env) body
      let rest ← mapHelper consts ctx env argId body vs
      pure (bv :: rest)
termination_by l => (sizeOf body, 1 + l.length)

/-- `Fold`'s left fold: `fold_op`'s single parameter is bound to the
    `(accumulator, element)` pair at each step (`eval/coll_fold.rs`). See
    `filterHelper`'s docstring for the termination measure. -/
def foldHelper (consts : List Value) (ctx : Context) (env : Env) (argId : Nat) (body : Expr) (acc : Value) :
    List Value → Except EvalError Value
  | [] => pure acc
  | v :: vs => do
      let acc' ← eval consts ctx ((argId, .vTuple [acc, v]) :: env) body
      foldHelper consts ctx env argId body acc' vs
termination_by l => (sizeOf body, 1 + l.length)

end

end ErgoTreeLean
