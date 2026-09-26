# Convenience targets. Also see README.md.

.PHONY: regen check lean-build cargo-build clippy difftest difftest-gen

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

lean-build:
	lake build

clippy:
	cd exporter && cargo clippy --all-targets -- -D warnings
	cd difftest && cargo clippy --all-targets -- -D warnings

# Regenerate the differential-test case file (Rust side): runs the real
# sigma-rust `ergotree-interpreter 0.28.0` reducer over 300 generated
# sell-order cases and emits them as JSON (decoded by
# `ErgoTreeLean/DiffTest/Decode.lean` at `lake exe difftest` run time —
# see `difftest/src/leanval.rs` for why JSON, not a generated .lean
# literal).
difftest-gen:
	cd difftest && cargo build --release
	cd difftest && ./target/release/difftest --contract sell-order --seed 1 --count 300 \
		--out ../ErgoTreeLean/DiffTest/sell-order-cases.json

# Full differential test: regenerate cases, then run the Lean evaluator
# over all of them via `lake exe difftest` (0 mismatches required).
difftest: difftest-gen
	lake build difftest
	lake exe difftest

# Full verification: exporter + difftest crate build/clippy-clean, Lean
# builds (no sorry/errors), and the differential test passes with 0
# mismatches on the generated cases.
check: cargo-build clippy lean-build difftest
