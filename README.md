# ergotree-lean

A Lean 4 model of ErgoTree evaluation — a deep-embedded semantics for the
smart-contract language of the Ergo blockchain — differentially tested
against `sigma-rust`'s real evaluator (`ergotree-interpreter 0.28.0`, the
exact version this model was hand-ported from). The included example
contract is `sell-order`; the model and tooling here are built to be
reused by downstream packages that add their own contracts and proofs on
top (as a `require` on this package, plus their own generator/proof
files — see "Difftest library usage" and "`eval_sym` tooling" below).

## Trust caveats — read this first

This model is evidence, not a guarantee of on-chain safety, and it is
evidence of a specific, narrower thing than "this contract is correct on
Ergo mainnet":

- **The reference is `sigma-rust`, not the Scala node.** Mainnet consensus
  runs the Scala interpreter, so any divergence between `sigma-rust` and
  Scala carries over into this model unexamined. One known case:
  `sigma-rust`'s `ExtractRegisterAs` returns a register's value even when
  its dynamic type doesn't match the type the script requested (mirrored
  here faithfully, not "fixed"); the Scala `getReg[T]` is believed to
  throw on that mismatch instead. Where Scala fails a script and
  `sigma-rust` doesn't, this model accepts a superset of what mainnet
  accepts — a **safety** theorem ("spendable ⇒ P") proved here still holds
  on mainnet, but a **liveness** theorem ("… ⇒ spendable") may not, since
  mainnet could reject a case this model calls spendable.
- **`executeFromVar`/`DeserializeContext` is lazy, evaluated exactly at
  the node, with no pre-pass** — confirmed directly from `sigma-rust`
  0.28.0's source (`eval/expr.rs` dispatches it in the ordinary per-node
  `match`; `eval/deserialize_context.rs` does the lookup, type check,
  parse and recursive evaluation all inside that one call). An absent or
  wrong-shape context variable is only an error if the node is actually
  reached, exactly like any other lazily-short-circuited node. The Scala
  node differs: on a devnet it was seen to deserialize the context
  variable whenever the variable is present, even on a path that never
  reaches the node. So a transaction carrying a malformed variable on an
  unreached path passes `sigma-rust` and fails on the node. As with the
  register case, safety theorems carry over and liveness theorems may
  not.
- **`atLeast(0, [])` is an evaluation error**, not vacuously true —
  `sigma-rust` converts the threshold's item list into a
  non-empty-bounded vector before `Cthreshold::reduce` ever sees `k = 0`,
  so a threshold of `0` over an empty collection fails rather than
  trivially succeeding. Mirrored as-is.
- **Kernel-checked proofs use only the three standard axioms**
  (`propext`, `Classical.choice`, `Quot.sound` — confirmed per theorem via
  `#print axioms`), no `sorry`, no new `axiom`, and no `native_decide` in
  a proof term (test/generator code is a different matter — see
  "Differential testing" below).
- **The differential test is empirical evidence, not a proof.** 0
  mismatches on a large, seeded, deliberately-varied case set is strong
  evidence this model's `eval` agrees with `sigma-rust`'s real reducer on
  everything those cases exercise — it is not a proof that they agree on
  every input, and it says nothing about the Scala/`sigma-rust` gap above.

## What is modelled

- **Syntax** (`ErgoTreeLean/Syntax.lean`): `SType`, `SigmaBoolean`,
  `Value`, `Box`, `BinOpKind`, and an `Expr` inductive mirroring
  `sigma-rust`'s MIR (`ergotree_ir::mir::expr::Expr`) 1:1 — same node
  granularity, same field order, lowerCamelCase constructor names —
  specifically so the exporter's walk (below) is a near-trivial
  structural map. Only the MIR node kinds that occur in the contracts
  covered by this repo (or a downstream package built on it) are given
  constructors; anything else fails loudly at export time rather than
  being approximated.
- **Numeric semantics** (`ErgoTreeLean/Numeric.lean`): checked, per-width
  arithmetic (`Byte`/`Short`/`Int`/`Long`/`BigInt`, each range-checked
  against its own bound), truncating (not Euclidean) division/modulo,
  `BigInt`'s genuinely different floor-mod rule, and the `Upcast`/
  `Downcast` tables (including their real, unfixed asymmetries — e.g.
  nothing downcasts *from* `BigInt`).
- **Context** (`ErgoTreeLean/Context.lean`): `selfBox`/`inputs`/`outputs`/
  `dataInputs`/`height`/`extension`/`oracle`, mirroring
  `ergotree_interpreter::eval::context::Context`. `oracle` is an abstract
  hook for the two operations `eval` must never compute directly —
  `blake2b256` hashing and script deserialization — so no proof in this
  repo ever computes a real hash or parses bytes into an `Expr`; the
  differential-testing harness supplies a *real* oracle instead (an exact
  hash/deserialization table the Rust generator emits), so `eval`'s
  outcome on those nodes is still checked against `sigma-rust`
  empirically, end to end.
- **Evaluator** (`ErgoTreeLean/Eval.lean`): a strict/eager,
  well-founded-recursive `eval`, faithful to `ergotree-interpreter
  0.28.0` node-for-node — every case carries a `-- mirrors: eval/<file>.rs`
  comment. Highlights: `BlockValue`/`&&`/`||`/`If` are lazy exactly where
  `sigma-rust` is; `SigmaAnd`/`SigmaOr` normalize their `Cand`/`Cor`
  result exactly like `sigma-rust`'s `Cand::normalized`/`Cor::normalized`
  (an absorbing `TrivialProp` collapses the whole thing, other
  `TrivialProp` items are dropped, 1 survivor unwraps to a bare item); no
  closures (`Apply`/`Filter`/`Exists`/`ForAll`/`Fold`'s function operand
  is matched syntactically against a literal `funcValue`, never evaluated
  to a `Value` first — see `inlineFuns` below for what makes this work).
- **`inlineFuns`** (`ErgoTreeLean/InlineFuns.lean`): a syntactic pre-pass
  that substitutes every `ValDef`-bound `FuncValue` at its `ValUse` sites
  and drops the `ValDef`, so that by the time `eval` runs, every `Apply`'s
  function operand is already a literal `funcValue` — the pass a contract
  compiling a multiply-used local `def` to a `ValDef`/`Apply(ValUse, ...)`
  pair needs (see the file's own docstring for the id-shadowing subtlety
  this has to get right, found by checking against a real compiled tree).
- **Sigma semantics** (`ErgoTreeLean/Sigma.lean`): `holds signers sb`, the
  logical (not cryptographic) statement of who can satisfy a
  `SigmaBoolean`, and `spendable` built on top of `inlineFuns` + `eval` +
  `holds`.
- **Deserializer** (`ErgoTreeLean/Deserialize.lean`): a from-scratch,
  independent Lean byte parser (hex → bytes → VLQ/zigzag decoding → a
  14-opcode `Expr` parser) for exactly `sell-order`'s compiled tree, kept
  as a cross-check against the Rust exporter below.
- **`sell-order`** (`ErgoTreeLean/Contracts/SellOrder.lean`): a
  hand-transcribed tree, a proof it matches the real compiler's bytes,
  and five theorems (who can spend it, when it's unspendable, and why).
  `Exported.lean`/`CrossCheck.lean`: the same contract independently
  exported by the Rust exporter agrees with the hand-transcribed tree,
  by `rfl`.

## Architecture: exporter → Lean `Expr`

Two ways an ErgoTree gets into this development's `Expr` type:

1. **Hand-written parser** (`ErgoTreeLean/Deserialize.lean`) — an
   independent check, but only covers the 14 opcodes `sell-order` uses.
2. **Rust exporter** (`exporter/`) — a `sigma-rust`-based CLI that parses
   an EIP-5 template's `expressionTree` with the real `ergotree-ir` crate
   (crates.io, `0.28`) and walks the resulting MIR to emit a Lean `Expr`
   term. This is what scales past a 14-opcode hand parser to real,
   larger contracts.

`sell-order` is run through *both* pipelines, and
`ErgoTreeLean/Contracts/SellOrder/CrossCheck.lean` proves they agree by
`rfl` — evidence that neither parser has a matching blind spot.

## Building

```
lake exe cache get      # fetch prebuilt Mathlib .olean's (skips a from-source build)
make check               # everything: cargo build/clippy + lake build + difftest
```

Requires the Lean 4 toolchain pinned in `lean-toolchain`
(`leanprover/lean4:v4.24.0`) via `elan`. `exporter/` and `difftest/` are
ordinary Cargo crates (crates.io `ergotree-ir`/`ergotree-interpreter`/
`ergo-chain-types` `0.28`/`0.28`/`0.15`), separate from the Lean project,
not wired into `lake build` directly — `lake exe difftest` invokes the
*Lean* executable, which reads a JSON case file `difftest`'s Rust binary
already produced (`make difftest-gen`).

```
make regen        # re-run the exporter against contracts/sell-order-eip5.json
make difftest      # regenerate cases + run `lake exe difftest` (0 mismatches required)
```

`exporter --inventory <eip5.json>` prints the sorted set of distinct MIR
node kinds in a tree without emitting Lean — useful before adding a new
contract, to see which nodes (if any) still need an `Expr`/`eval` case.
`exporter --hex <expressionTreeHex> --const-types 07,0e,05` runs on raw
bytes + constant types instead of an EIP-5 JSON file (for a contract with
no EIP-5 wrapper).

## Differential testing

`difftest/` is a Cargo **library** crate: it owns the generic
case-building machinery (`GenCase`, `build_ergo_tree`,
`build_context`/`build_context_with_data_inputs`, the `dummy_*`/
`coll_*_const` builders, `run_reducer`, JSON encoding via `leanval`) and a
reusable CLI driver, `run_cli`, that takes a `&[(&str, Generator)]` table
mapping a family name to its case-generator function. This repo's own
`difftest/src/bin/difftest.rs` is a thin binary that registers only
`sell-order`:

```rust
fn main() -> anyhow::Result<()> {
    difftest::run_cli(&[("sell-order", difftest::sell_order::generate)])
}
```

On the Lean side, `ErgoTreeLean.DiffTest` (`Types.lean`/`Decode.lean`/
`Runner.lean`/`Main.lean`) is a library too: `Types.lean` defines `Case`,
`Decode.lean` defines `loadCases`, and `Runner.lean` defines `checkCase`/
`runCases`/`Tally` — kept in their own module, separate from `Main.lean`
(this repo's own thin `main`), since two packages both declaring a
top-level `main` in the same build would clash. None of this is
re-exported from the package root — `Decode.lean`/`Runner.lean` both
import the whole root themselves (for `bytesToVColl`/`hexStringToBytes`/
`inlineFuns`/`eval`/etc), so a `lean_exe`'s own root module imports
`ErgoTreeLean` plus `ErgoTreeLean.DiffTest.{Types,Decode,Runner}`
directly, exactly as this repo's own `Main.lean` does. This repo's own
`lean_exe difftest` (`ErgoTreeLean/DiffTest/Main.lean`) loads
`sell-order-cases.json`, runs `runCases` against `sellOrderTree`, and
exits nonzero on any mismatch.

**Result, current seed:** `sell-order`: 300 cases, 0 mismatches.

### Difftest library usage (downstream)

A downstream package that adds its own contracts:

1. Depends on this package's `difftest` crate by path
   (`difftest = { path = "../ergotree-lean/difftest" }`), writes its own
   `<family>.rs` generator module(s) (`pub fn generate(rng, count) ->
   Result<Vec<difftest::GenCase>>`, using this crate's `build_ergo_tree`/
   `build_context`/`coll_*_const`/etc.), and its own thin `bin/difftest.rs`
   calling `difftest::run_cli` with its own family table.
2. Depends on this package as a Lean `require`. Its own `lean_exe` root
   module imports `ErgoTreeLean` plus `ErgoTreeLean.DiffTest.Types`/
   `.Decode`/`.Runner` directly (not through the package root — see
   above), loads its own case JSON files (`loadCases`), and calls
   `runCases "<family>" <tree> <cases>` per family, tallying/exiting the
   same way this repo's own `Main.lean` does.

## `eval_sym` tooling and proof automation

`ErgoTreeLean/Lemmas/` + `ErgoTreeLean/Tactics/` are proof-automation
support for writing contract theorems on top of `eval`/`holds`, and are
the only modules in this library that import Mathlib (the core model —
`Syntax`/`Context`/`Eval`/`Numeric`/`InlineFuns`/`Sigma` — and the
difftest library stay Mathlib-free).

- `Lemmas/EvalInv.lean`: one `@[eval_inv]` rewrite rule per `Expr` node
  kind, turning a success equation `eval consts ctx env e = .ok w` into a
  statement about `e`'s children with every runtime pattern match already
  resolved (the intermediate values appear as existentials with their
  constructor shape pinned). `sigmaOr`/`atLeast` only have *forward*
  rules, not `↔`, because only soundness of the `Cor`/`Cthreshold` normal
  forms is proved here — there's no rule that runs the other direction to
  push a goal *into* an `Exists`/`Fold`/`Map` loop shape, so those still
  need to be unfolded and reasoned about by hand once reached.
- `Lemmas/EvalHolds.lean`: the same idea one layer up, for `EvalHolds`
  (the sigma-proposition/`holds` layer). `Lemmas/SigmaHolds.lean`/
  `Lemmas/Beq.lean`: generic facts about `holds` against `eval`'s normal
  forms, and about `Value.beq`'s `Coll[Byte]` encoding, any contract
  proof can reuse.
- `Tactics/EvalSym.lean`: `eval_sym`, which repeatedly (1) rewrites
  hypotheses with the `eval_inv`/`EvalHolds` rules, (2) splits `∧`/`∃`
  into separate hypotheses, and (3) substitutes every equation that
  defines a variable — symbolically executing a concrete contract tree
  inside a proof. What remains after it stops making progress is facts
  about the context, plus `∀`-statements for collection loops and
  unexpanded disjunctions for `||`/`if`, which the proof then handles in
  ordinary Lean. `eval_sym'` is a single-pass-simp variant for larger
  trees; `eval_simp`/`eval_simp_hyps` run one round of the rewrite alone.

**Known limits**, from using this on real contract proofs: it's slow on
large loop bodies, because each round re-simplifies every hypothesis from
scratch rather than running an incremental engine that only touches what
changed; `Value`/`SigmaBoolean` have no `LawfulBEq` instance, so a few
comparisons need manual `Value.beq`-soundness lemmas instead of plain
`decide`/`simp`; and there are no *forward* rules that push a goal into
`Exists`/`Fold`/`Map`'s loop shape, so those still need hand-written
lemmas per contract, the way `sigmaOr`/`atLeast` already do above.

## What's still not modelled / assumed

- **Sigma-protocol cryptography is abstracted away.** `holds` assumes
  completeness/soundness of the underlying sigma-protocols — a valid
  proof for a `SigmaBoolean` exists iff `holds` holds for the secrets the
  prover knows. Standard, not (re-)proved here.
- **Box id / hashing is opaque**, matching `sigma-rust`'s own `eval`-time
  behaviour (hashing happens once, at box construction, never inside
  `eval`) — not a shortcut relative to `sigma-rust`, the same thing it
  does.
- **`ProveDhTuple`/`Cthreshold`'s cousins beyond what's used here** have
  no `SigmaBoolean` constructor; the difftest JSON emission fails loudly
  (not silently) if a case ever produces one that isn't modelled.
- **`Header`/`PreHeader`/`GlobalVars::MinerPubKey`/`GroupGenerator`** are
  not modelled — no contract in this repo reads them; add constructors if
  a downstream contract needs them.

## Layout

```
ErgoTreeLean/            core model, proof tooling, sell-order example
  Contracts/SellOrder*    the sell-order example contract
  Lemmas/, Tactics/        eval_sym proof automation (imports Mathlib)
  DiffTest/                difftest library (Types/Decode/Runner) + this repo's Main
exporter/                 Rust: ErgoTree → Lean Expr exporter
difftest/                 Rust: difftest library + this repo's sell-order bin
contracts/                sell-order.es + its EIP-5 compiled JSON
```

License: TBD.
