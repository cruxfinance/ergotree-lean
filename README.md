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
  and five theorems (who can spend it, when it's unspendable, and why);
  `SellOrder/EvalSym.lean` re-proves two of them with `eval_sym`.
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
no EIP-5 wrapper). `--inventory` works with any input mode.

`exporter --ergotree <ergoTreeHex>` parses a full on-chain ErgoTree
(header byte, optional size, optional constants segment, expression) —
what you get from a box's `ergoTree` field or by decoding a P2S address —
instead of an EIP-5 template. It's mutually exclusive with the positional
JSON input and with `--hex`/`--const-types`. Besides `def <lean-name> :
Expr`, it also emits `def <lean-name>Consts : List Value`, the tree's
actual constant values in `constantIndex` order (the EIP-5/`--hex` routes
never see real constant values, only types, so they emit no such list).
Prefix the hex with `@` to read it from a file instead
(`--ergotree @path/to/tree.hex`, trimmed of surrounding whitespace) —
ErgoTrees are long enough that this beats a shell argument.

## Verifying a new contract

Reviewing a contract you didn't write means getting its tree into this
model, checking the model actually covers it, then difftesting before
trusting any proof.

### 1. Get the compiled tree

For an on-chain contract, get its full ErgoTree hex and pass it to
`exporter --ergotree`:

- **From a box**: its `ergoTree` field, from a node's box-lookup
  endpoints (e.g. `/utxo/byId/{boxId}`) or an explorer API.
- **From a P2S address**: a node's `GET /script/addressToTree/{address}`
  returns `{"tree": "<hex>"}` — the address decoded straight to its
  ErgoTree hex.

Either way you get one hex string covering the header, the constants
segment (if any) and the expression together — no separate constants
list to track by hand, and the exporter also emits the tree's actual
constant values (see "Building" above).

The EIP-5 template route (`{"constTypes": [...], "expressionTree":
"..."}`, see `contracts/sell-order-eip5.json`) stays the way to export a
compiler's own output, which is a template with placeholders rather than
a concrete on-chain instance — it has no real constant values to emit.
`--hex <expressionTreeHex> --const-types ...` covers the same
placeholder-only case when there's no EIP-5 wrapper.

### 2. Check coverage before anything else

Run `exporter --inventory <path-to-eip5.json>` (or `--ergotree ...`, or
`--hex ... --const-types ...`). It prints the sorted set of distinct MIR
node kinds the tree contains, no Lean emitted. This repo's `Expr` (`Syntax.lean`)
only has constructors for the node kinds the contracts covered here
actually use; anything else is deliberately absent, not approximated —
the real export step (`exporter <path> --lean-name ... --namespace ...
-o ...`) fails loudly, naming the unhandled node, rather than silently
emitting something wrong.

**Coverage is limited to what this repo's contracts exercise.** If
`--inventory` turns up a node not already handled in
`Syntax.lean`/`Eval.lean`, extending coverage is a contribution, not a
config change: a new `Expr` constructor in `Syntax.lean` (matching the
MIR node's shape 1:1), a new `eval` case in `Eval.lean` mirroring the
corresponding `ergotree-interpreter 0.28.0` source file (tag it `--
mirrors: eval/<file>.rs`; see `CONTRIBUTING.md`), exporter support (a
case in `exporter/src/emit.rs`, plus `exporter/src/inventory.rs` if you
want `--inventory` to name it), an `eval_inv`/`EvalHolds` rule in
`ErgoTreeLean/Lemmas/` if a proof needs to see through it, and difftest
cases exercising it (step 4) — new coverage with no differential-test
evidence isn't trustworthy no matter how right `eval` looks by eye.

### 3. Export the tree to Lean

- **Reviewing your own contract, in your own package**: `require` this
  repo as a Lean dependency (see "Difftest library usage" below) and
  export into your own package, e.g.:
  ```
  exporter --ergotree @path/to/box-ergotree.hex --lean-name myContractTree \
    --namespace MyPackage.Contracts.MyContract \
    -o MyPackage/Contracts/MyContract/Exported.lean
  ```
  This also gives you `MyPackage.Contracts.MyContract.myContractTreeConsts
  : List Value` — the tree's real constant values, in the order
  `eval`/`spendable` expect. State your property with it directly, no
  hand-transcribing:
  ```
  theorem myContractTree_spendable_iff (ctx : Context) (signers : List PK) :
      spendable myContractTreeConsts ctx signers myContractTree ↔ ... := by
    ...
  ```
  The EIP-5/`--hex` routes have no real constant values to offer, so a
  contract exported that way needs its own hand-written `consts` (see
  `Contracts/SellOrder.lean`'s `consts` for the pattern).
- **Contributing the contract to this repo**: export under
  `ErgoTreeLean/Contracts/`, following the `sell-order` layout
  (`Contracts/SellOrder.lean` for the hand/theorem-carrying tree,
  `Contracts/SellOrder/Exported.lean` + `CrossCheck.lean` for the
  exporter's independent copy and the `rfl` proof the two agree).

The generated file's own header records the exact command and source hex
to regenerate it — never hand-edit a generated file.

### 4. Write difftest coverage before trusting anything

The model is only trustworthy on the node kinds and value shapes the
differential test exercises. Before writing a single theorem:

- Add a Rust generator module under `difftest/src/`, following
  `sell_order.rs`: `pub fn generate(rng: &mut StdRng, count: usize) ->
  Result<Vec<difftest::GenCase>>`, building varied `(consts, Context)`
  cases with `build_ergo_tree`/`build_context`/
  `build_context_with_data_inputs` and the `*_const`/`coll_*_const`/
  `dummy_*` helpers, run through sigma-rust's real reducer with
  `run_reducer`. Register it in your `bin/difftest.rs`'s `run_cli` family
  table.
- Vary everything the tree branches on: values at and around any
  threshold, present vs. absent optional data, wrong-script/wrong-party
  outputs, missing outputs/inputs, and, if the tree uses
  `CalcBlake2b256`/`DeserializeContext`, real oracle-table entries
  (`GenCase.blake2b_table`/`deser_table`).
- On the Lean side, reuse `ErgoTreeLean.DiffTest` directly (inside this
  repo) or `require` it and write a thin runner mirroring
  `ErgoTreeLean/DiffTest/Main.lean`: `loadCases` your case JSON, call
  `runCases "<family>" <tree> <cases>`, check the mismatch count is `0`.
- Run it: `make difftest-gen && lake exe difftest` (or your package's
  equivalent). Anything but "0 mismatches" means the model disagrees
  with sigma-rust on a case you generated — do not proceed to proving
  properties about that tree until it's 0.

### 5. State and prove a property

State the property as a plain Lean proposition over
`spendable`/`holds`/`eval`, not as prose.
`ErgoTreeLean/Contracts/SellOrder/EvalSym.lean` is the minimal worked
example: it re-proves two `SellOrder.lean` theorems with `eval_sym`
(`ErgoTreeLean/Tactics/EvalSym.lean`), which symbolically executes the
`eval`/`EvalHolds` hypotheses about your concrete tree instead of you
hand-deriving evaluation lemmas. Follow its shape for a first proof:
unfold your tree and constants, call `eval_sym`, and use
`EvalHolds_sigmaOr_imp` (or the matching `EvalHolds_*` rule for your
top-level connective) to split on which branch of the guard holds. Once
a proof completes, run `#print axioms <theorem>` and confirm it lists
only `propext`, `Classical.choice`, `Quot.sound` (see `CONTRIBUTING.md`).

### 6. Multi-input properties

A property spanning several inputs of one transaction (e.g. "input 0's
guard relies on input 1 having already been validated") needs `Tx.lean`:
build a `Tx`, use `Tx.ctxAt tx i` for input `i`'s context, and state the
transaction-level hypothesis as `Tx.Valid tx script signers`. Name
`Tx.Valid`'s two hypotheses explicitly rather than assuming them: `script`
(the function from a box's `propositionBytes` to its parsed `(consts,
tree)` — this model does not parse arbitrary bytes, see
`Deserialize.lean`'s scope) and, transitively through `spendable`, any
`executeFromVar`/`Oracle` fact the tree needs.

### 7. What you actually have at the end

A theorem proved this way is exactly as strong as "Trust caveats — read
this first" above says, no stronger: evidence against `sigma-rust`, not
the Scala node; backed by empirical difftest coverage, not a proof `eval`
matches `sigma-rust` on every input; and a "spendable ⇒ property"
(safety) result carries over to mainnet more reliably than a "property ⇒
spendable" (liveness) one. Say explicitly which kind you proved.

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
  constructor shape pinned). The rest of a block after a `ValDef` and the
  branches of an `if` are wrapped in `Later` (a marker equal to its
  argument) so `eval_sym` can decode them in order, below.
- `Lemmas/EvalHolds.lean`: the same idea one layer up, for `EvalHolds`
  (the sigma-proposition/`holds` layer). `sigmaOr`/`atLeast` only have
  forward rules (`EvalHolds_sigmaOr_imp`, `EvalHolds_atLeast_proveDlogs`),
  because only soundness of the `Cor`/`Cthreshold` normal forms is proved.
  `Lemmas/SigmaHolds.lean`/`Lemmas/Beq.lean`: generic facts about `holds`
  against `eval`'s normal forms, and about `Value.beq`'s `Coll[Byte]`
  encoding.
- `Lemmas/Decode.lean`: rules that turn what the inversion leaves into
  plain facts. `SType.beq` is lawful (`LawfulBEq SType`); `typeOf v = .sInt`
  and friends pin a value's constructor; `Value.beq` is equality when one
  side has no `vOption` inside (`Value.beq_eq_true_iff_of_optFree`; not in
  general, because `vOption`'s `beq` ignores the element type as sigma-rust's
  runtime `Opt` has none), a comparison against a partly known value peels
  one constructor at a time (`Value.beq_vColl_right`, …), and
  `Value.beqList_getElem?_of_optFree` transfers a known element across a
  `beqList`; arithmetic results (`arithRes`) become the plain `Int` result
  plus its overflow side-condition as two `Int` bounds; an upcast to
  `BigInt` keeps the payload.
- `Lemmas/Loops.lean`: forward rules for loop facts (`exists`/`forall`
  results, `map` pointwise, `filter` sublist) and invariant rules for `fold`
  (`foldHelper_inv`, and `foldHelper_foldl` to turn a script-level sum into
  `List.foldl`), the building blocks for transaction-level statements.
  `forall` has the exact `forallHelper_true_iff` in `EvalInv.lean`.
- `Tactics/EvalSym.lean`: `eval_sym`, symbolic execution of the `eval`/
  `EvalHolds` hypotheses about a concrete tree. It is a loop, run until
  nothing changes:
  1. `simp` with the `eval_inv` rules, only on hypotheses whose statement
     is not yet in normal form (a statement already simplified, or a part
     of one, is never simplified again unless a new rule can rewrite it),
     split `∧`/`∃` hypotheses, and merge two reads `e = some a`,
     `e = some b` (or `e = .ok a`, `e = .ok b`) into `a = b`;
  2. turn every variable definition `x = t` into a rewrite rule for `x`
     (instead of `subst`); of two variables the one the engine introduced
     is rewritten, so a name given with `obtain ⟨out, h⟩ : ∃ out, … :=
     ⟨_, ‹_›⟩` replaces an anonymous variable on the next `eval_sym` (loop
     facts are rewritten with these definitions too, and nothing else);
  3. when stuck, split the goal on an `if` whose condition is undecided and
     keep the condition as a rewrite rule for that branch, so every later
     `if` on the same condition loses its dead arm without being looked at;
  4. otherwise release the `Later` facts: `simp` stops at a `Later`, so a
     block runs one definition at a time and each continuation is
     simplified once, with the definitions before it decoded.

  The goal is not changed while the engine runs: derived facts live in a
  local context of the engine's own, each with its proof term, and the
  proof is assembled once at the end, in one pass over the term
  (`(fun h => …) pf` substituted for a fact, `Exists.elim` for an
  existential, `Or.elim` at a split). The ordering, arithmetic and cast
  rules bind each operand's kind and payload right where its equation fixes
  it (`∃ k p, eval l = .ok (k.wrap p) ∧ ∃ q, …`), so `simp` drops each
  existential as soon as it is decided.

  What remains is facts about the context (`ctx.outputs[k]? = some out`,
  `out.register 5 = some (.vColl τ vs)`, `vs[0]? = some (.vLong n)`, `Int`
  equations and bounds), disjunctions for `||`, and loop facts
  (`forallHelper … = .ok true` etc., and any `∀`-statement about `eval`,
  such as `mapHelper_getElem?`'s pointwise fact, left folded: instantiate
  one at an element and run `eval_sym` on the result). `eval_sym [lemmas]`
  adds rewrite rules: local hypotheses (tracked by name as the engine
  rewrites them), or a loop lemma such as `forallHelper_true_iff`, which
  makes `eval_sym` expand loops under their binders. `clear_loops` drops
  loop facts not needed any more. `eval_simp` is one plain `simp` round with
  every `Later` released, for a goal or a statement under binders.
  `set_option trace.eval_sym true` logs each `simp` call's time.

  Example: `Contracts/SellOrder/EvalSym.lean` re-proves two `sell-order`
  theorems in a few lines each. On a larger downstream contract (a
  20-definition loop body with value-producing `if`s and `BigInt`
  arithmetic), a per-input safety theorem checks in about 30 s, and one
  that executes three further loops (two `map`s, a `fold` inside a
  `forall`, an `exists`) in about 30 s.

- `Tx.lean` (core model, no Mathlib): a transaction (`Tx`: inputs, data
  inputs, outputs, height, and each input's context extension and oracle),
  `Tx.ctxAt tx i`, input `i`'s evaluation context, and `Tx.Valid`: distinct
  input ids and every input spendable in its own context, with the parsing
  of script bytes into trees passed in as a function. For statements that
  span several inputs of one transaction.

**Known limits.** Most of the check time of a large proof is now `simp`
itself; the largest single call is a long `&&` chain in one step (a few
seconds). `Value`/`SigmaBoolean` have no `LawfulBEq`
instance (it would be false for `vOption`). There are no rules that push a
*goal* into a loop shape (liveness direction).

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
  Tx.lean                  transaction model: per-input contexts, validity
  Contracts/SellOrder*    the sell-order example contract
  Lemmas/, Tactics/        eval_sym proof automation (imports Mathlib)
  DiffTest/                difftest library (Types/Decode/Runner) + this repo's Main
exporter/                 Rust: ErgoTree → Lean Expr exporter
difftest/                 Rust: difftest library + this repo's sell-order bin
contracts/                sell-order.es + its EIP-5 compiled JSON
```

## License

CC0-1.0. See [LICENSE](LICENSE).
