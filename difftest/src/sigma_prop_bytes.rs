//! `sigma-prop-bytes` case generator: exercises `SigmaPropBytes`
//! (ErgoScript `somePk.propBytes`) against real sigma-rust serialization —
//! see `ErgoTreeLean/Contracts/SigmaPropBytes.lean`'s `sigmaPropBytesTree`,
//! which this generator's `build_tree` mirrors node-for-node.
//!
//! The tree (ErgoScript-shaped, for reference):
//!
//! ```text
//! sigmaProp(OUTPUTS(0).propositionBytes == CONST.propBytes)
//! ```
//!
//! `CONST` (constant index 0) is a per-case `SigmaProp` value, built with
//! the *real* sigma-rust normalizing constructors (`Cand::normalized`/
//! `Cor::normalized`/`Cthreshold::reduce`, never a hand-rolled
//! `SigmaBoolean` literal), so every shape this generator emits is one
//! sigma-rust itself would actually produce — see `build_sb`. `OUTPUTS(0)`'s
//! box carries a script whose `propositionBytes` is either exactly
//! `CONST`'s real `SigmaProp::prop_bytes()` (an equality case), or a
//! deliberately different byte string (a one-byte mutation, a truncation,
//! or a wholly different shape/key) — an inequality case. Both sides of
//! `==` therefore always compare two `Coll[Byte]`s and the tree's root is
//! a plain `BinOp(Eq)` wrapped in `BoolToSigmaProp`, so the only possible
//! outcomes are `trivial true`, `trivial false`, or (when `OUTPUTS` is
//! empty, `ByIndex`'s one error path here) an evaluation error — no
//! `ProveDlog`/conjecture outcome, since `CONST` is never itself proved,
//! only serialized.

use anyhow::{Context as _, Result};
use ergotree_ir::chain::ergo_box::ErgoBox;
use ergotree_ir::ergo_tree::ErgoTree;
use ergotree_ir::mir::bin_op::{BinOp, BinOpKind, RelationOp};
use ergotree_ir::mir::bool_to_sigma::BoolToSigmaProp;
use ergotree_ir::mir::coll_by_index::ByIndex;
use ergotree_ir::mir::constant::{Constant, ConstantPlaceholder, Literal};
use ergotree_ir::mir::expr::Expr;
use ergotree_ir::mir::extract_script_bytes::ExtractScriptBytes;
use ergotree_ir::mir::global_vars::GlobalVars;
use ergotree_ir::mir::sigma_prop_bytes::SigmaPropBytes;
use ergotree_ir::mir::unary_op::OneArgOpTryBuild;
use ergotree_ir::serialization::SigmaSerializable;
use ergotree_ir::sigma_protocol::sigma_boolean::cand::Cand;
use ergotree_ir::sigma_protocol::sigma_boolean::cor::Cor;
use ergotree_ir::sigma_protocol::sigma_boolean::cthreshold::Cthreshold;
use ergotree_ir::sigma_protocol::sigma_boolean::{ProveDlog, SigmaBoolean, SigmaProp};
use ergotree_ir::types::stype::SType;
use rand::rngs::StdRng;
use rand::Rng;

use crate::{build_context, build_ergo_tree, dummy_box_with_tree, dummy_tree, rand_ec_point, run_reducer, GenCase, MIN_BOX_VALUE};

fn int_lit(v: i32) -> Expr {
    Expr::Const(Constant { tpe: SType::SInt, v: Literal::Int(v) })
}
fn outputs_expr() -> Expr {
    Expr::GlobalVars(GlobalVars::Outputs)
}
fn by_index0(coll: Expr) -> Result<Expr> {
    Ok(Expr::ByIndex(ByIndex::new(coll, int_lit(0), None)?.into()))
}

/// Builds the `sigma-prop-bytes` family's tree — see this module's
/// docstring and `ErgoTreeLean/Contracts/SigmaPropBytes.lean`'s
/// `sigmaPropBytesTree`, which this mirrors 1:1. Returns the bare `Expr`
/// (not yet a full `ErgoTree`); `generate` serializes it once and prepends
/// a fresh header + this case's one constant per case via
/// `build_ergo_tree` (the same "template + real constants" pattern
/// `sell_order.rs`/`timelock.rs` use).
fn build_tree() -> Result<Expr> {
    let out_prop_bytes = Expr::ExtractScriptBytes(ExtractScriptBytes::try_build(by_index0(outputs_expr())?)?);
    let const_placeholder = Expr::ConstPlaceholder(ConstantPlaceholder { id: 0, tpe: SType::SSigmaProp });
    let const_prop_bytes = Expr::SigmaPropBytes(SigmaPropBytes::try_build(const_placeholder)?);
    let eq = Expr::BinOp(
        BinOp {
            kind: BinOpKind::Relation(RelationOp::Eq),
            left: Box::new(out_prop_bytes),
            right: Box::new(const_prop_bytes),
        }
        .into(),
    );
    Ok(Expr::BoolToSigmaProp(BoolToSigmaProp::try_build(eq)?))
}

fn prove_dlog_sb(rng: &mut StdRng) -> SigmaBoolean {
    SigmaBoolean::from(ProveDlog::new(rand_ec_point(rng)))
}

fn cand_sb(items: Vec<SigmaBoolean>) -> SigmaBoolean {
    #[allow(clippy::unwrap_used)]
    Cand::normalized(items.try_into().unwrap())
}
fn cor_sb(items: Vec<SigmaBoolean>) -> SigmaBoolean {
    #[allow(clippy::unwrap_used)]
    Cor::normalized(items.try_into().unwrap())
}
fn cthreshold_sb(k: u8, items: Vec<SigmaBoolean>) -> SigmaBoolean {
    #[allow(clippy::unwrap_used)]
    Cthreshold::reduce(k, items.try_into().unwrap())
}

/// This case's `CONST` `SigmaBoolean` shape. Every shape is built through
/// sigma-rust's own normalizing constructors (`Cand::normalized`/
/// `Cor::normalized`/`Cthreshold::reduce`), so whatever comes out —
/// including a `Cthreshold::reduce` call collapsing to a bare `Cor`/`Cand`
/// at an extreme `k` — is a shape sigma-rust itself would actually
/// produce, never a hand-assembled "impossible" `SigmaBoolean`. Cycles
/// through 16 shapes: a lone `ProveDlog`; `TrivialProp(true)`/`(false)`;
/// small (2-item) and larger (5-6 item) `Cand`/`Cor`; a genuine
/// (non-collapsing) `Cthreshold` at a small and a larger child count;
/// `Cthreshold` at the boundary `k` values that collapse to `Cor` (`k=1`),
/// `Cand` (`k=n`), `true` (`k=0`) and `false` (`k>n`); `Cthreshold` with a
/// `TrivialProp` mixed into its children (exercises `reduce`'s
/// trivial-folding loop); and two nested shapes (`Cand` containing a
/// `Cor`, `Cor` containing a `Cand`).
fn build_sb(rng: &mut StdRng, idx: usize) -> SigmaBoolean {
    match idx % 16 {
        0 => prove_dlog_sb(rng),
        1 => true.into(),
        2 => false.into(),
        3 => cand_sb(vec![prove_dlog_sb(rng), prove_dlog_sb(rng)]),
        4 => cor_sb(vec![prove_dlog_sb(rng), prove_dlog_sb(rng)]),
        5 => cand_sb((0..6).map(|_| prove_dlog_sb(rng)).collect()),
        6 => cor_sb((0..6).map(|_| prove_dlog_sb(rng)).collect()),
        7 => cthreshold_sb(2, (0..4).map(|_| prove_dlog_sb(rng)).collect()),
        8 => cthreshold_sb(4, (0..7).map(|_| prove_dlog_sb(rng)).collect()),
        9 => cthreshold_sb(1, (0..3).map(|_| prove_dlog_sb(rng)).collect()), // reduce() -> Cor
        10 => cthreshold_sb(3, (0..3).map(|_| prove_dlog_sb(rng)).collect()), // reduce() -> Cand
        11 => cthreshold_sb(0, (0..3).map(|_| prove_dlog_sb(rng)).collect()), // reduce() -> true
        12 => cthreshold_sb(9, (0..3).map(|_| prove_dlog_sb(rng)).collect()), // reduce() -> false (k > n)
        13 => {
            let items = vec![true.into(), prove_dlog_sb(rng), prove_dlog_sb(rng), prove_dlog_sb(rng), prove_dlog_sb(rng)];
            cthreshold_sb(3, items) // one trivial-true child folded into k during `reduce`
        }
        14 => cand_sb(vec![prove_dlog_sb(rng), cor_sb(vec![prove_dlog_sb(rng), prove_dlog_sb(rng)])]),
        _ => cor_sb(vec![prove_dlog_sb(rng), cand_sb(vec![prove_dlog_sb(rng), prove_dlog_sb(rng), prove_dlog_sb(rng)])]),
    }
}

fn mutate_one_byte(rng: &mut StdRng, bytes: &[u8]) -> Vec<u8> {
    let mut out = bytes.to_vec();
    if !out.is_empty() {
        let idx = rng.gen_range(0..out.len());
        out[idx] ^= 0xFF;
    }
    out
}

fn truncate(rng: &mut StdRng, bytes: &[u8]) -> Vec<u8> {
    if bytes.is_empty() {
        return vec![];
    }
    let len = rng.gen_range(0..bytes.len());
    bytes[..len].to_vec()
}

/// A box whose script is exactly the `ErgoTree` `bytes` decode to —
/// `ErgoTree::sigma_parse_bytes` never hard-errors on arbitrary bytes (a
/// malformed/truncated input falls back to `ErgoTree::Unparsed`, which
/// re-serializes to exactly the bytes it was given — see `ergo_tree.rs`),
/// so this box's `propositionBytes` (`b.ergo_tree.sigma_serialize_bytes()`,
/// what `ExtractScriptBytes`/`extract_script_bytes.rs` reads) is always
/// exactly `bytes`, whether or not `bytes` happens to parse as a valid
/// `SigmaProp` constant.
fn box_with_bytes(rng: &mut StdRng, bytes: &[u8]) -> Result<ErgoBox> {
    let tree = ErgoTree::sigma_parse_bytes(bytes).context("parsing case bytes into ErgoTree")?;
    let value: u64 = rng.gen_range(MIN_BOX_VALUE..1_000_000_000u64);
    dummy_box_with_tree(value, tree)
}

fn gen_one(rng: &mut StdRng, i: usize, body_hex: &str) -> Result<GenCase> {
    let height: u32 = rng.gen_range(0..2_000_000);

    let sb = build_sb(rng, i);
    let sb_const = Constant { tpe: SType::SSigmaProp, v: Literal::SigmaProp(Box::new(SigmaProp::new(sb.clone()))) };
    let tree = build_ergo_tree(body_hex, vec![sb_const.clone()])?;

    // The real bytes `CONST.propBytes` evaluates to, computed by
    // sigma-rust's own `SigmaProp::prop_bytes()` — never hand-encoded.
    let real_bytes = SigmaProp::new(sb).prop_bytes().context("SigmaProp::prop_bytes")?;

    // Outcome kind from `i / 16`, not `i`: `build_sb` picks the shape by
    // `i % 16`, and reusing `i % 6` here would pair the exact-match outcome
    // with even shapes only.
    let outputs: Vec<ErgoBox> = match (i / 16) % 6 {
        // Exact match: OUTPUTS(0)'s propositionBytes is exactly CONST.propBytes -> trivial true.
        0 => vec![box_with_bytes(rng, &real_bytes)?],
        // One-byte mutation -> trivial false.
        1 => {
            let mutated = mutate_one_byte(rng, &real_bytes);
            vec![box_with_bytes(rng, &mutated)?]
        }
        // Truncation -> trivial false.
        2 => {
            let truncated = truncate(rng, &real_bytes);
            vec![box_with_bytes(rng, &truncated)?]
        }
        // A wholly different shape/key's real bytes -> trivial false.
        3 => {
            let other_sb = build_sb(rng, i.wrapping_add(7919));
            let other_bytes = SigmaProp::new(other_sb).prop_bytes().context("SigmaProp::prop_bytes (other)")?;
            vec![box_with_bytes(rng, &other_bytes)?]
        }
        // OUTPUTS empty -> ByIndex(OUTPUTS, 0) errors -> the tree's one error path.
        4 => vec![],
        // Two outputs, OUTPUTS(0) itself mismatching (OUTPUTS(1) would
        // match, confirming the tree really reads index 0, not "any
        // output") -> trivial false.
        _ => {
            let mutated = mutate_one_byte(rng, &real_bytes);
            let b0 = box_with_bytes(rng, &mutated)?;
            let b1 = box_with_bytes(rng, &real_bytes)?;
            vec![b0, b1]
        }
    };

    let self_tree = dummy_tree(0)?;
    let self_box = dummy_box_with_tree(MIN_BOX_VALUE, self_tree)?;
    let inputs = [&self_box];
    let ctx = build_context(&self_box, &inputs, &outputs, height, vec![])?;
    let expected = run_reducer(&tree, &ctx);

    Ok(GenCase {
        consts: vec![sb_const],
        self_box: self_box.clone(),
        inputs: vec![self_box],
        outputs,
        height,
        extension: vec![],
        data_inputs: vec![],
        blake2b_table: vec![],
        deser_table: vec![],
        expected,
    })
}

pub fn generate(rng: &mut StdRng, count: usize) -> Result<Vec<GenCase>> {
    let body_hex = hex::encode(build_tree()?.sigma_serialize_bytes().context("serializing sigma-prop-bytes tree body")?);
    let mut cases = Vec::with_capacity(count);
    let mut i = 0usize;
    while cases.len() < count {
        i += 1;
        cases.push(gen_one(rng, i, &body_hex).with_context(|| format!("sigma-prop-bytes case {i}"))?);
    }
    Ok(cases)
}
