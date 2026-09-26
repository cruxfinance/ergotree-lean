/-
Transaction-evaluation context: the parts of the spending transaction the
contract can observe. `Box`/`Value` live in `Syntax.lean` (they're
mutually recursive with each other, not with `Context`).

Mirrors `ergotree_interpreter::eval::context::Context` (`eval/context.rs`):
`self_box`/`inputs` are non-optional there (a spending transaction always
has at least one input, itself), `data_inputs` is `Option<TxIoVec<..>>`
(modelled here as a possibly-empty list rather than `Option (List Box)` —
"no data inputs" and "empty data inputs list" are observationally
identical to every node a contract that never reads `CONTEXT.dataInputs`
(e.g. `sell-order`) uses).
-/
import ErgoTreeLean.Syntax

namespace ErgoTreeLean

/-- An abstract oracle for the two operations `Eval.lean` must
    never compute directly — cryptographic hashing and script
    deserialization (see the module docstring on `Expr.calcBlake2b256`/
    `Expr.deserializeContext` in `Syntax.lean` and the README's "What is modelled"
    section). `deserialize` returns the *already-evaluated* `Value` a real
    `DeserializeContext` would produce (deserialize-then-eval folded into
    one atomic call — see `Syntax.lean`'s `deserializeContext` docstring
    for why, a termination argument, not a semantic shortcut), `none`
    exactly when sigma-rust would fail (either to parse the bytes as an
    `Expr`, or to evaluate/type-check the result).

    No proof in this repo computes a real blake2b hash or parses bytes
    into an `Expr`: theorems about a tree using either node take `oracle`
    as a hypothesis (e.g. an assumed collision-freeness fact at the
    specific bytes involved), never inspect its definition. The
    differential-testing harness (`difftest/`) supplies a *real*,
    per-case oracle (an exact hash/deserialization table the Rust
    generator emits, checked against sigma-rust's own real behaviour —
    see `README.md`), so `eval`'s outcome is still checked against
    sigma-rust empirically, end to end. -/
structure Oracle where
  blake2b256 : List UInt8 → List UInt8
  deserialize : List UInt8 → Option Value

/-- The default oracle (never exercised by `sell-order`, which uses
    neither node) — this is what lets `Context`'s `oracle` field carry a
    default value so a `{ selfBox := ..., ... }` construction that omits
    it still compiles. -/
def Oracle.default : Oracle where
  blake2b256 := fun _ => []
  deserialize := fun _ => none

instance : Inhabited Oracle := ⟨Oracle.default⟩

/-- `Oracle` holds plain functions, which have no derivable `Repr`; this
    opaque placeholder instance exists only so `Context`'s `deriving Repr`
    (used for debug printing, e.g. by `difftest`'s error messages) still
    elaborates — nothing meaningful is ever printed here, and no proof
    inspects it. -/
instance : Repr Oracle := ⟨fun _ _ => "Oracle.default"⟩

/-- The evaluation context. `extension` is the prover-supplied
    `getVar[T](id)` map (`ContextExtension` in sigma-rust) for the input
    currently being evaluated. `oracle` is the crypto/deserialize
    abstraction (see `Oracle` above); it defaults to `Oracle.default` so
    a `Context` literal that omits it still compiles. -/
structure Context where
  selfBox : Box
  inputs : List Box
  outputs : List Box
  dataInputs : List Box
  height : Nat
  extension : List (Nat × Value)
  oracle : Oracle := Oracle.default
deriving Repr

/-- Read a single context-extension variable by id, or `none` if absent.
    Used by `GetVar` in `Eval.lean`. -/
def Context.getVar (ctx : Context) (varId : Nat) : Option Value :=
  (ctx.extension.find? (fun p => p.1 == varId)).map Prod.snd

end ErgoTreeLean
