/-
Sigma-protocol semantics, abstracted at the level of "who can produce a
valid proof".

**Crypto assumption (not proved here):** we assume the completeness and
soundness of the underlying sigma-protocols (Schnorr proveDlog, and the
OR/AND composition of Cramer-Damgård-Schoenmakers), i.e.:

  a valid non-interactive proof for a `SigmaBoolean` exists
  iff
  `holds signers sb` holds, where `signers` is the set of secret keys
  (identified by their public keys) the prover knows.

This file only formalizes the right-hand side, `holds`; it does not attempt
to model proof transcripts, Fiat–Shamir, or the discrete-log assumption.
-/
import ErgoTreeLean.Syntax
import ErgoTreeLean.Context
import ErgoTreeLean.Eval
import ErgoTreeLean.InlineFuns

namespace ErgoTreeLean

/-- A public key, encoded the same way as `SigmaBoolean.proveDlog`'s
    `GroupElement` bytes. -/
abbrev PK := List UInt8

mutual
/-- Whether a spender who knows the secrets behind `signers` can satisfy
    sigma-proposition `sb`. See the module docstring for the crypto
    assumption this abstracts away.

    `holdsAny`/`holdsAll` are mutually-recursive helpers for the `cor`/`cand`
    list cases — writing them as plain structural recursion (rather than
    `∃ sb ∈ items, ...` / `∀ sb ∈ items, ...`) keeps this reducible by
    `simp`/`decide` and lets Lean's termination checker see the recursion
    on `SigmaBoolean` directly. -/
def holds (signers : List PK) : SigmaBoolean → Prop
  | .trivial b => b = true
  | .proveDlog pk => pk ∈ signers
  | .cor items => holdsAny signers items
  | .cand items => holdsAll signers items
  | .cthreshold k items => holdsAtLeast signers k items

def holdsAny (signers : List PK) : List SigmaBoolean → Prop
  | [] => False
  | sb :: rest => holds signers sb ∨ holdsAny signers rest

def holdsAll (signers : List PK) : List SigmaBoolean → Prop
  | [] => True
  | sb :: rest => holds signers sb ∧ holdsAll signers rest

/-- `atLeast(k, items)` (`SigmaBoolean.cthreshold`): a spender knowing
    `signers` can satisfy it iff *some* sub-collection of `items`, of size
    at least `k`, is one every member of which they can independently
    satisfy — the standard k-of-n threshold reading, and the natural
    generalization of `holdsAny`/`holdsAll` (`k = 1`/`k = items.length`
    are the two extremes). Recursive on the list, exactly like
    `holdsAny`/`holdsAll`: `k = 0` is vacuously satisfiable (matches
    `cthresholdReduce`'s `k == 0 → trivial true`); an empty list can only
    satisfy `k = 0`; otherwise, either the head holds and it counts toward
    the threshold (`k - 1` more needed from the rest), or the head is
    skipped entirely and the full `k` is still needed from the rest. -/
def holdsAtLeast (signers : List PK) : Nat → List SigmaBoolean → Prop
  | 0, _ => True
  | _ + 1, [] => False
  | k + 1, sb :: rest => (holds signers sb ∧ holdsAtLeast signers k rest) ∨ holdsAtLeast signers (k + 1) rest
end

/-- A tree is spendable in context `ctx` by a spender knowing `signers` iff,
    after `inlineFuns` (`InlineFuns.lean`) eliminates the `ValUse`-of-a-
    `FuncValue`-`ValDef` indirection `eval` can't evaluate on its own,
    evaluation reduces it to some `SigmaBoolean` that `signers` satisfies.

    Requiring `inlineFuns tree = some t` to succeed (rather than treating a
    `none` as vacuously unspendable, say) is deliberate: `inlineFuns`
    failing means the tree violated its own precondition (duplicate
    `ValDef` ids), which never happens for real compiler output — see
    `InlineFuns.lean`'s module docstring for why dropping a `FuncValue`
    `ValDef` this way preserves `eval`'s result whenever the pass *does*
    succeed (evaluating a `FuncValue` can't itself fail or have an
    observable side effect, so inlining it is the same computation `eval`
    would otherwise perform per `Apply` site, just done once, ahead of
    time). Differential testing (`difftest/`) checks this equivalence
    empirically against sigma-rust's real evaluator, on top of that
    argument. -/
def spendable (consts : List Value) (ctx : Context) (signers : List PK) (tree : Expr) : Prop :=
  ∃ t sb, inlineFuns tree = some t ∧
    eval consts ctx [] t = .ok (.vSigmaProp sb) ∧ holds signers sb

end ErgoTreeLean
