# Convenience targets. Also see README.md.

.PHONY: regen check lean-build cargo-build cargo-test clippy difftest difftest-gen

# Rebuild the exporter and regenerate the exported/generated Lean tree
# files from the EIP-5 template in contracts/.
regen:
	cd exporter && cargo build --release
	cd exporter && cargo run -q --release -- ../contracts/sell-order-eip5.json \
		--lean-name exportedTree \
		--namespace ErgoTreeLean.Contracts.SellOrder.Exported \
		-o ../ErgoTreeLean/Contracts/SellOrder/Exported.lean

cargo-build:
	cd exporter && cargo build
	cd difftest && cargo build

# `exporter/tests/` (the `--ergotree` full-ErgoTree route's coverage).
cargo-test:
	cd exporter && cargo test

lean-build:
	lake build

clippy:
	cd exporter && cargo clippy --all-targets -- -D warnings
	cd difftest && cargo clippy --all-targets -- -D warnings

# Regenerate the differential-test case files (Rust side): runs the real
# sigma-rust `ergotree-interpreter 0.28.0` reducer over generated cases
# for every registered family and emits them as JSON (decoded by
# `ErgoTreeLean/DiffTest/Decode.lean` at `lake exe difftest` run time —
# see `difftest/src/leanval.rs` for why JSON, not a generated .lean
# literal).
difftest-gen:
	cd difftest && cargo build --release
	cd difftest && ./target/release/difftest --contract sell-order --seed 1 --count 300 \
		--out ../ErgoTreeLean/DiffTest/sell-order-cases.json
	cd difftest && ./target/release/difftest --contract box-fields --seed 1 --count 300 \
		--out ../ErgoTreeLean/DiffTest/box-fields-cases.json
	cd difftest && ./target/release/difftest --contract timelock --seed 1 --count 150 \
		--out ../ErgoTreeLean/DiffTest/timelock-cases.json
	cd difftest && ./target/release/difftest --contract sigma-prop-bytes --seed 1 --count 300 \
		--out ../ErgoTreeLean/DiffTest/sigma-prop-bytes-cases.json

# Full differential test: regenerate cases, then run the Lean evaluator
# over all of them via `lake exe difftest` (0 mismatches required).
difftest: difftest-gen
	lake build difftest
	lake exe difftest

# Full verification: exporter + difftest crate build/clippy-clean, the
# exporter's own test suite green, Lean builds (no sorry/errors), and the
# differential test passes with 0 mismatches on the generated cases.
check: cargo-build clippy cargo-test lean-build difftest
