/-
A transaction, and the evaluation context of each of its inputs.

`Context` (`Context.lean`) is what one script sees: its own input (`SELF`),
the transaction's inputs, outputs and data inputs, the height, its own context
extension, and the oracle. A node evaluates every input's script in such a
context, and the transaction is valid only if every script accepts. Statements
about several inputs of one transaction (one script relying on another input's
script having run, as in a contract split into a guard and a payload) need
that shared structure: `Tx` holds it, `Tx.ctxAt tx i` is input `i`'s context,
and `Tx.Valid` says every input is spendable in its own context.

Two things are left to the user of this model, as hypotheses:

* **Which tree an input runs.** A box stores its script as serialized bytes
  (`propositionBytes`); this model does not parse them (`Deserialize.lean`
  covers one contract's opcodes only). `Tx.Valid` takes the parsing as a
  function `script : List UInt8 → Option (List Value × Expr)` (constants and
  expression tree); a theorem about a contract assumes `script bytes = some
  (consts, tree)` for that contract's bytes.
* **Distinct inputs.** The protocol never spends a box twice, so the inputs'
  ids are distinct. `Tx.Valid` states it directly (`ids_nodup`); ids are not
  modelled as hashes of the box contents.

Each input has its own `Oracle`: `Oracle.deserialize` returns the value of
evaluating the deserialized expression, and that evaluation happens in the
context of the input that runs it, so it can differ between inputs.
`blake2b256` is meant to be the same function for every input, but nothing
here needs that.
-/
import ErgoTreeLean.Sigma

namespace ErgoTreeLean

/-- A transaction. `extensions i` and `oracles i` are input `i`'s context
    extension and oracle. -/
structure Tx where
  inputs : List Box
  dataInputs : List Box
  outputs : List Box
  height : Nat
  extensions : Nat → List (Nat × Value)
  oracles : Nat → Oracle

/-- A box with no id, value, script, tokens or registers: the `SELF` of
    `Tx.ctxAt` at an index that is not an input (never used by a statement
    about an actual input). -/
def Box.empty : Box := { id := [], value := 0, propositionBytes := [], tokens := [], registers := [] }

/-- Input `i`'s evaluation context: `SELF` is input `i`, with input `i`'s own
    context extension and oracle. -/
def Tx.ctxAt (tx : Tx) (i : Nat) : Context where
  selfBox := tx.inputs.getD i Box.empty
  inputs := tx.inputs
  outputs := tx.outputs
  dataInputs := tx.dataInputs
  height := tx.height
  extension := tx.extensions i
  oracle := tx.oracles i

/-- The transaction is valid for spenders knowing `signers`, with scripts
    parsed by `script`: the inputs' ids are distinct, and every input's
    script parses and is spendable in that input's own context. -/
structure Tx.Valid (tx : Tx) (script : List UInt8 → Option (List Value × Expr)) (signers : List PK) :
    Prop where
  ids_nodup : (tx.inputs.map Box.id).Nodup
  spendable : ∀ i b, tx.inputs[i]? = some b →
    ∃ consts tree, script b.propositionBytes = some (consts, tree) ∧ spendable consts (tx.ctxAt i) signers tree

namespace Tx

variable (tx : Tx) (i : Nat)

@[simp] theorem ctxAt_inputs : (tx.ctxAt i).inputs = tx.inputs := rfl
@[simp] theorem ctxAt_outputs : (tx.ctxAt i).outputs = tx.outputs := rfl
@[simp] theorem ctxAt_dataInputs : (tx.ctxAt i).dataInputs = tx.dataInputs := rfl
@[simp] theorem ctxAt_height : (tx.ctxAt i).height = tx.height := rfl
@[simp] theorem ctxAt_extension : (tx.ctxAt i).extension = tx.extensions i := rfl
@[simp] theorem ctxAt_oracle : (tx.ctxAt i).oracle = tx.oracles i := rfl

theorem ctxAt_selfBox {i : Nat} {b : Box} (h : tx.inputs[i]? = some b) : (tx.ctxAt i).selfBox = b := by
  simp [ctxAt, List.getD_eq_getElem?_getD, h]

/-- With distinct ids, an input is determined by its id. -/
theorem eq_of_id_eq {script signers} (hv : tx.Valid script signers) {i j : Nat} {b c : Box}
    (hi : tx.inputs[i]? = some b) (hj : tx.inputs[j]? = some c) (h : b.id = c.id) : i = j := by
  obtain ⟨hil, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  have hn := List.pairwise_iff_getElem.mp hv.ids_nodup
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have := hn i j (by simpa using hil) (by simpa using hjl) hij
    simp only [List.getElem_map] at this
    exact absurd h this
  · exact hij
  · have := hn j i (by simpa using hjl) (by simpa using hil) hij
    simp only [List.getElem_map] at this
    exact absurd h.symm this

end Tx

end ErgoTreeLean
