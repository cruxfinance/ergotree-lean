/-
The difftest library's run-and-compare logic, shared by this repo's own
`lean_exe difftest` (`Main.lean`, `sell-order` only) and a downstream
package's own `lean_exe` (registering its own contract families) — see
README.md's "Difftest library usage". Kept in its own module, separate
from `Decode.lean` (decoding) and `Main.lean` (this repo's own thin
`main`, which can't be imported elsewhere without a top-level `main`
name clash).

Test code, not a proof: this may use compiled (`#eval`/`IO`) evaluation
freely — the "no `native_decide` in proofs" rule is about kernel proof
terms, not about this executable.
-/
import ErgoTreeLean
import ErgoTreeLean.DiffTest.Types

namespace ErgoTreeLean.DiffTest

/-- One case's verdict: `true` iff the Lean evaluator's outcome agrees with
    `c.expected` (sigma-rust's), after `Value.beq`/`SigmaBoolean.beq`
    structural comparison (which already applies the same `Cand`/`Cor`
    normalization on both sides — see `Eval.lean`). -/
def checkCase (tree : Expr) (c : Case) : Bool × String :=
  match inlineFuns tree with
  | none => (false, s!"case {c.id}: inlineFuns failed (duplicate ValDef ids)")
  | some t =>
      match eval c.consts c.ctx [] t with
      | .ok (.vSigmaProp sb) =>
          match c.expected with
          | some esb =>
              if SigmaBoolean.beq sb esb then (true, "")
              else (false, s!"case {c.id}: MISMATCH lean=ok({reprStr sb}) rust=ok({reprStr esb})")
          | none => (false, s!"case {c.id}: MISMATCH lean=ok({reprStr sb}) rust=error")
      | .ok other => (false, s!"case {c.id}: lean produced a non-SigmaProp value: {reprStr other}")
      | .error e =>
          match c.expected with
          | none => (true, "")
          | some esb => (false, s!"case {c.id}: MISMATCH lean=error({reprStr e}) rust=ok({reprStr esb})")

/-- Outcome-distribution tally, classified purely from `c.expected` (i.e.
    sigma-rust's own answer — what actually happened is what we're
    checking Lean against, so the distribution is reported against the
    ground truth, not against Lean's possibly-wrong answer). -/
structure Tally where
  trivialTrue : Nat := 0
  trivialFalse : Nat := 0
  proveDlog : Nat := 0
  other : Nat := 0
  error : Nat := 0
deriving Repr

def classify (t : Tally) : Option SigmaBoolean → Tally
  | none => { t with error := t.error + 1 }
  | some (.trivial true) => { t with trivialTrue := t.trivialTrue + 1 }
  | some (.trivial false) => { t with trivialFalse := t.trivialFalse + 1 }
  | some (.proveDlog _) => { t with proveDlog := t.proveDlog + 1 }
  | some _ => { t with other := t.other + 1 }

/-- Run every case for `name`/`tree`, printing each mismatch as it's found;
    returns the mismatch count. -/
def runCases (name : String) (tree : Expr) (cases : List Case) : IO Nat := do
  let mut mismatches : Nat := 0
  let mut tally : Tally := {}
  for c in cases do
    tally := classify tally c.expected
    let (ok, msg) := checkCase tree c
    if !ok then
      mismatches := mismatches + 1
      IO.println msg
  IO.println s!"{name}: {cases.length} cases, {mismatches} mismatches — outcome distribution: \
    {tally.trivialTrue} trivial-true, {tally.trivialFalse} trivial-false, \
    {tally.proveDlog} proveDlog, {tally.other} other-sigma, {tally.error} evaluation-error"
  pure mismatches

end ErgoTreeLean.DiffTest
