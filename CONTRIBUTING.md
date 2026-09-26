# Contributing

## Running the checks

```
lake exe cache get   # once, to fetch prebuilt Mathlib .olean's
make check            # cargo build/clippy + lake build + difftest, exit 0 required
```

`make check` must print `difftest: 0 mismatches` (see README's "Building"
and "Differential testing"). A PR that doesn't pass it locally won't pass
CI either.

## Proof rules

- No `sorry`, anywhere, in a committed proof.
- No `native_decide` inside a proof term (test/generator code is a
  different matter).
- No new `axiom`. `#print axioms <theorem>` must list only the three
  standard ones: `propext`, `Classical.choice`, `Quot.sound`.
- Every `maxHeartbeats` override must be a finite number, not `0`
  (unlimited) — if a proof needs more than the default budget, raise the
  limit to a specific value, not disable the check.

## Evaluator changes

Any change or addition to `ErgoTreeLean/Eval.lean` must mirror the
corresponding `ergotree-interpreter 0.28.0` Rust source file, tagged with
a `-- mirrors: eval/<file>.rs` comment on the case, and must come with
difftest coverage exercising it (see the README's "Verifying a new
contract", steps 2 and 4) before it's trusted by any proof. A new `Expr`
node needs the matching `Syntax.lean` constructor, exporter support
(`exporter/src/emit.rs`, `exporter/src/inventory.rs`), and, if a
sigma-proposition proof needs to see through it, an `eval_inv`/
`EvalHolds` rule in `ErgoTreeLean/Lemmas/`.

## License

This project is released under CC0-1.0 (see `LICENSE`). By contributing,
you agree your contribution is released under the same license.
