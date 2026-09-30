//! `coll-indexof` case generator: exercises `SCollection.indexOf`
//! (`type_id=12`, `method_id=26`), the `MethodCall` node
//! `ErgoTreeLean/Eval.lean` had no case for at all before this family was
//! added (`eval` returned `.error` on *every* `MethodCall`) — the
//! motivating example is `dexy-stable`'s `contracts/bank/update/ballot.es`,
//! `val index = INPUTS.indexOf(SELF, 0)`. See
//! `ErgoTreeLean/Contracts/CollIndexOf.lean`'s `collIndexOfTree`, which
//! this generator's `build_tree` mirrors node-for-node.
//!
//! Tree (ErgoScript-shaped):
//!
//! ```text
//! sigmaProp(INPUTS.indexOf(SELF, fromConst) == targetConst)
//! ```
//!
//! `fromConst`/`targetConst` are per-case EIP-5-style template constants
//! (`ConstantPlaceholder` ids 0/1, both `SInt`) substituted into one fixed
//! tree, exactly like `sell_order.rs`'s `SELL_ORDER_HEX` — see
//! `build_ergo_tree`. Varying them (plus which boxes go into `INPUTS`)
//! covers `Value.indexOf`'s whole behaviour (see that function's docstring
//! in `Eval.lean`): found at index 0 (`ballot.es`'s own shape: `SELF` is
//! `INPUTS(0)`), found later, not found (`SELF` absent from `INPUTS`,
//! `-1`), duplicates (two+ inputs structurally equal to `SELF` — the first
//! at-or-after `from` wins), `from` negative (clamped to `0`, never "from
//! the end"), and `from` at/past `INPUTS.size` (`-1`, not an error).
//! `targetConst` is the *actually correct* index for that case's `INPUTS`/
//! `from` (computed here by construction, not by re-deriving sigma-rust's
//! algorithm) most of the time — so the tree checks the real numeric
//! result, not just some inequality — and deliberately wrong on a fifth of
//! cases, for outcome-distribution diversity (sigma-rust's real
//! `reduce_to_crypto` decides `true`/`false` from its own evaluation
//! either way, so a "wrong" guess is still a fully valid, independently
//! meaningful case, not a hand-picked expectation).
use std::collections::HashMap;

use anyhow::{Context as _, Result};
use ergotree_ir::chain::ergo_box::ErgoBox;
use ergotree_ir::mir::bin_op::{BinOp, BinOpKind, RelationOp};
use ergotree_ir::mir::bool_to_sigma::BoolToSigmaProp;
use ergotree_ir::mir::constant::ConstantPlaceholder;
use ergotree_ir::mir::expr::Expr;
use ergotree_ir::mir::global_vars::GlobalVars;
use ergotree_ir::mir::method_call::MethodCall;
use ergotree_ir::mir::unary_op::OneArgOpTryBuild;
use ergotree_ir::serialization::SigmaSerializable;
use ergotree_ir::types::scoll;
use ergotree_ir::types::stype::SType;
use ergotree_ir::types::stype_param::STypeVar;
use rand::rngs::StdRng;
use rand::Rng;

use crate::{build_context, build_ergo_tree, dummy_box_with_tree, dummy_tree, int_const, run_reducer, GenCase, MIN_BOX_VALUE};

fn from_placeholder() -> Expr {
    Expr::ConstPlaceholder(ConstantPlaceholder { id: 0, tpe: SType::SInt })
}
fn target_placeholder() -> Expr {
    Expr::ConstPlaceholder(ConstantPlaceholder { id: 1, tpe: SType::SInt })
}

/// Builds the `coll-indexof` family's tree — see this module's docstring
/// and `ErgoTreeLean/Contracts/CollIndexOf.lean`'s `collIndexOfTree`, which
/// this mirrors 1:1. Returned as raw (unsegregated) `Expr` bytes, hex
/// encoded, exactly what `build_ergo_tree` expects as its
/// `expression_tree_hex` (matching `SELL_ORDER_HEX` in `sell_order.rs` —
/// that hex came from a real compiler, this one comes from serializing
/// this hand-built `Expr` directly, since `INPUTS.indexOf(SELF, ...)` is
/// simple enough not to need a round trip through scalac).
pub fn build_tree_hex() -> Result<String> {
    let index_of_method = scoll::INDEX_OF_METHOD
        .clone()
        .with_concrete_types(&[(STypeVar::t(), SType::SBox)].into_iter().collect::<HashMap<_, _>>());
    let index_of = Expr::MethodCall(
        MethodCall::new(
            Expr::GlobalVars(GlobalVars::Inputs),
            index_of_method,
            vec![Expr::GlobalVars(GlobalVars::SelfBox), from_placeholder()],
        )
        .map_err(|e| anyhow::anyhow!("MethodCall::new: {e:?}"))?
        .into(),
    );
    let eq = Expr::BinOp(
        BinOp {
            kind: BinOpKind::Relation(RelationOp::Eq),
            left: Box::new(index_of),
            right: Box::new(target_placeholder()),
        }
        .into(),
    );
    let tree: Expr = Expr::BoolToSigmaProp(BoolToSigmaProp::try_build(eq)?);
    let body = SigmaSerializable::sigma_serialize_bytes(&tree).context("serializing coll-indexof body")?;
    Ok(hex::encode(body))
}

/// A box with some deterministically-varied script/value, distinct from
/// `SELF` (a different `tag` than `self_tag` guarantees a different
/// `propositionBytes`, hence never structurally equal to `SELF` —
/// `Box.beq`/`ErgoBox`'s `PartialEq` compare the script too).
fn other_box(rng: &mut StdRng, tag: i64) -> Result<ErgoBox> {
    let value = rng.gen_range(MIN_BOX_VALUE..1_000_000_000u64);
    dummy_box_with_tree(value, dummy_tree(tag)?)
}

pub fn generate(rng: &mut StdRng, count: usize) -> Result<Vec<GenCase>> {
    let body_hex = build_tree_hex()?;
    let mut cases = Vec::with_capacity(count);
    for i in 0..count {
        let height: u32 = rng.gen_range(0..2_000_000);
        // A fresh SELF per case (own tag `-1`, distinct from every `other_box` tag
        // below, all `>= 0`), so no case's SELF is accidentally structurally
        // equal to a same-case `other_box`.
        let self_box = other_box(rng, -1)?;
        let mode = i % 9;
        let (inputs, from, correct_idx): (Vec<ErgoBox>, i32, i32) = match mode {
            // Found at 0 — `ballot.es`'s own shape: `SELF` is `INPUTS(0)`.
            0 => (vec![self_box.clone(), other_box(rng, 0)?], 0, 0),
            // Found later: two distinct boxes before `SELF`.
            1 => (vec![other_box(rng, 0)?, other_box(rng, 1)?, self_box.clone()], 0, 2),
            // Not found: `SELF` entirely absent from `INPUTS`.
            2 => (vec![other_box(rng, 0)?, other_box(rng, 1)?], 0, -1),
            // Duplicates, `from = 0`: two inputs structurally equal to `SELF`
            // (both clones) — the *first* match (index 1) wins.
            3 => (vec![other_box(rng, 0)?, self_box.clone(), self_box.clone()], 0, 1),
            // Same duplicates, but `from` = the first match's own index: the
            // search is inclusive of `from`, so it still finds that same
            // first match, not the second.
            4 => (vec![other_box(rng, 0)?, self_box.clone(), self_box.clone()], 1, 1),
            // Same duplicates, `from` = one past the first match: skips it,
            // finds the second ("first match >= from").
            5 => (vec![other_box(rng, 0)?, self_box.clone(), self_box.clone()], 2, 2),
            // `from` negative: clamped to `0`, never "from the end" — same
            // expected index as the plain `from = 0` found-later case.
            6 => (vec![other_box(rng, 0)?, other_box(rng, 1)?, self_box.clone()], -7, 2),
            // `from` at/past `INPUTS.size`: `-1`, not an error.
            7 => (vec![self_box.clone(), other_box(rng, 0)?], 1000, -1),
            // `from` one past `SELF`'s only occurrence: not found from there on.
            _ => (vec![self_box.clone(), other_box(rng, 0)?], 1, -1),
        };
        // Correct guess 4/5 of the time (checks the real numeric result);
        // deliberately wrong on the rest (outcome-distribution diversity —
        // see module docstring).
        let target = if i % 5 == 4 { correct_idx.wrapping_add(1) } else { correct_idx };
        let consts = vec![int_const(from), int_const(target)];
        let tree = build_ergo_tree(&body_hex, consts.clone())?;
        let input_refs: Vec<&ErgoBox> = inputs.iter().collect();
        let ctx = build_context(&self_box, &input_refs, &[], height, vec![])?;
        let expected = run_reducer(&tree, &ctx);
        cases.push(GenCase {
            consts,
            self_box: self_box.clone(),
            inputs,
            outputs: vec![],
            height,
            extension: vec![],
            data_inputs: vec![],
            blake2b_table: vec![],
            deser_table: vec![],
            expected,
        });
    }
    Ok(cases)
}
