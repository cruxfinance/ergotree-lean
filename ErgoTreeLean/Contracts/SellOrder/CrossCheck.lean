/-
Cross-check: the Rust exporter (`exporter/`, driven off sigma-rust's
ErgoTree parser) and the independently hand-written Lean parser
(`Deserialize.lean`'s `parseExpr`, checked against `sellOrderTree` by
`SellOrder.parse_matches`) agree on `sell-order`'s compiled tree.

This is the point of exporting `sell-order` (a contract already covered by
a hand-transcribed tree) through the new Rust exporter pipeline before
trusting it on larger contracts that have no hand-transcribed tree to
compare against: two independently-written parsers — one hand-rolled in
Lean, one sigma-rust's real ErgoTree parser driven from Rust — agreeing on
the same compiled bytes is evidence (not proof) that neither has a
matching blind spot.
-/
import ErgoTreeLean.Contracts.SellOrder
import ErgoTreeLean.Contracts.SellOrder.Exported

namespace ErgoTreeLean.Contracts.SellOrder

open ErgoTreeLean

theorem exported_eq_hand : Exported.exportedTree = sellOrderTree := by
  rfl

end ErgoTreeLean.Contracts.SellOrder
