//! `box-fields` case generator: exercises `ExtractCreationInfo` and
//! `ExtractRegisterAs` on the mandatory registers R0-R3 of `SELF`,
//! `INPUTS(0)` and `OUTPUTS(0)`, across boxes with varied creation
//! heights (relative to `HEIGHT`), transaction ids and output indices —
//! see `ErgoTreeLean/Contracts/BoxFields.lean`'s `boxFieldsTree`, which
//! this generator's `build_tree` mirrors node-for-node (no template
//! constants: every operand is a `GlobalVars`/literal-index lookup, so
//! `GenCase::consts` is always empty for this family).
//!
//! The tree (ErgoScript-shaped, for reference):
//!
//! ```text
//! sigmaProp(
//!   HEIGHT >= SELF.creationInfo._1 &&
//!   SELF.R0[Long].get == SELF.value &&
//!   SELF.R1[Coll[Byte]].get == SELF.propositionBytes &&
//!   INPUTS(0).R3[(Int, Coll[Byte])].get == INPUTS(0).creationInfo &&
//!   OUTPUTS(0).R2[Coll[(Coll[Byte], Long)]].get == OUTPUTS(0).tokens
//! )
//! ```
//!
//! `INPUTS(0)` never errors (a spending transaction always has at least
//! one input — `build_context`'s `TxIoVec` is non-empty by construction),
//! so the only error path this tree can take is `OUTPUTS(0)` on an empty
//! `outputs` list; the R0/R1/R3/R2 identities always hold once evaluation
//! gets that far (each reads a box's own mandatory register straight back
//! against the same box's own field), so the only outcome split besides
//! that error path is the `HEIGHT >= SELF.creationInfo._1` boundary.
//!
//! Every box built here (`varied_box`) also carries 0-3 tokens (random
//! ids, amounts spanning `TokenAmount`'s full range, including the `1`
//! and near-`i64::MAX` boundaries) and 0-2 non-mandatory registers
//! (R4/R5, plain `Long`/`Int` constants) — R2 (`Box.tokens`) is computed
//! by a separate code path from R0/R1/R3 (`Eval.lean`'s `Box.register`
//! duplicates, rather than reuses, the `propertyCall … 99 8` tokens
//! mapping — see that function's docstring), so it needs its own
//! populated-list coverage, not just the empty-list case; R4/R5 confirm
//! R0-R3's derivation doesn't disturb the plain `Box.registers` lookup
//! real non-mandatory entries still go through.

use std::sync::Arc;

use anyhow::{anyhow, Context as _, Result};
use ergo_chain_types::blake2b256_hash;
use ergotree_ir::chain::ergo_box::box_value::BoxValue;
use ergotree_ir::chain::ergo_box::{BoxTokens, ErgoBox, NonMandatoryRegisters};
use ergotree_ir::chain::token::{Token, TokenAmount, TokenId};
use ergotree_ir::chain::tx_id::TxId;
use ergotree_ir::ergo_tree::ErgoTree;
use ergotree_ir::mir::bin_op::{BinOp, BinOpKind, LogicalOp, RelationOp};
use ergotree_ir::mir::bool_to_sigma::BoolToSigmaProp;
use ergotree_ir::mir::coll_by_index::ByIndex;
use ergotree_ir::mir::constant::{Constant, Literal};
use ergotree_ir::mir::expr::Expr;
use ergotree_ir::mir::extract_amount::ExtractAmount;
use ergotree_ir::mir::extract_creation_info::ExtractCreationInfo;
use ergotree_ir::mir::extract_reg_as::ExtractRegisterAs;
use ergotree_ir::mir::extract_script_bytes::ExtractScriptBytes;
use ergotree_ir::mir::global_vars::GlobalVars;
use ergotree_ir::mir::option_get::OptionGet;
use ergotree_ir::mir::property_call::PropertyCall;
use ergotree_ir::mir::select_field::{SelectField, TupleFieldIndex};
use ergotree_ir::mir::unary_op::OneArgOpTryBuild;
use ergotree_ir::types::sbox;
use ergotree_ir::types::stuple::STuple;
use ergotree_ir::types::stype::SType;
use rand::rngs::StdRng;
use rand::Rng;

use crate::{build_context, dummy_tree, int_const, long_const, run_reducer, GenCase, MIN_BOX_VALUE};

fn self_box_expr() -> Expr {
    Expr::GlobalVars(GlobalVars::SelfBox)
}
fn inputs_expr() -> Expr {
    Expr::GlobalVars(GlobalVars::Inputs)
}
fn outputs_expr() -> Expr {
    Expr::GlobalVars(GlobalVars::Outputs)
}
fn int_lit(v: i32) -> Expr {
    Expr::Const(Constant { tpe: SType::SInt, v: Literal::Int(v) })
}
fn by_index0(coll: Expr) -> Result<Expr> {
    Ok(Expr::ByIndex(ByIndex::new(coll, int_lit(0), None)?.into()))
}
fn extract_reg(input: Expr, reg: i8, elem_tpe: SType) -> Result<Expr> {
    Ok(Expr::ExtractRegisterAs(
        ExtractRegisterAs::new(input, reg, SType::SOption(Arc::new(elem_tpe)))?.into(),
    ))
}
fn option_get(input: Expr) -> Result<Expr> {
    Ok(Expr::OptionGet(OptionGet::try_build(input)?.into()))
}
fn creation_info(input: Expr) -> Result<Expr> {
    Ok(Expr::ExtractCreationInfo(ExtractCreationInfo::try_build(input)?))
}
fn creation_height(input: Expr) -> Result<Expr> {
    let ci = creation_info(input)?;
    let idx = TupleFieldIndex::try_from(1u8).map_err(|_| anyhow!("bad TupleFieldIndex"))?;
    Ok(Expr::SelectField(SelectField::new(ci, idx)?.into()))
}
fn tokens_call(obj: Expr) -> Result<Expr> {
    Ok(Expr::PropertyCall(PropertyCall::new(obj, sbox::TOKENS_METHOD.clone())?.into()))
}
fn eq_expr(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp { kind: BinOpKind::Relation(RelationOp::Eq), left: Box::new(l), right: Box::new(r) }.into())
}
fn ge_expr(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp { kind: BinOpKind::Relation(RelationOp::Ge), left: Box::new(l), right: Box::new(r) }.into())
}
fn and_expr(l: Expr, r: Expr) -> Expr {
    Expr::BinOp(BinOp { kind: BinOpKind::Logical(LogicalOp::And), left: Box::new(l), right: Box::new(r) }.into())
}

/// Builds the `box-fields` family's tree — see this module's docstring
/// and `ErgoTreeLean/Contracts/BoxFields.lean`'s `boxFieldsTree`, which
/// this mirrors 1:1.
pub fn build_tree() -> Result<Expr> {
    let height_ge = ge_expr(Expr::GlobalVars(GlobalVars::Height), creation_height(self_box_expr())?);
    let r0_eq = eq_expr(
        option_get(extract_reg(self_box_expr(), 0, SType::SLong)?)?,
        Expr::ExtractAmount(ExtractAmount::try_build(self_box_expr())?),
    );
    let r1_eq = eq_expr(
        option_get(extract_reg(self_box_expr(), 1, SType::SColl(Arc::new(SType::SByte)))?)?,
        Expr::ExtractScriptBytes(ExtractScriptBytes::try_build(self_box_expr())?),
    );
    let r3_eq = eq_expr(
        option_get(extract_reg(
            by_index0(inputs_expr())?,
            3,
            SType::STuple(STuple::pair(SType::SInt, SType::SColl(Arc::new(SType::SByte)))),
        )?)?,
        creation_info(by_index0(inputs_expr())?)?,
    );
    let r2_eq = eq_expr(
        option_get(extract_reg(
            by_index0(outputs_expr())?,
            2,
            SType::SColl(Arc::new(SType::STuple(STuple::pair(
                SType::SColl(Arc::new(SType::SByte)),
                SType::SLong,
            )))),
        )?)?,
        tokens_call(by_index0(outputs_expr())?)?,
    );
    let conj = and_expr(height_ge, and_expr(r0_eq, and_expr(r1_eq, and_expr(r3_eq, r2_eq))));
    Ok(Expr::BoolToSigmaProp(BoolToSigmaProp::try_build(conj)?))
}

/// A box with a deterministically-varied tree/tx-id/index/tokens/
/// non-mandatory-registers and the given creation height. See this
/// module's docstring for why tokens and R4/R5 are populated (not just
/// the box-identity fields R0/R1/R3/`creationInfo` already vary).
fn varied_box(rng: &mut StdRng, tag: i64, creation_height: u32) -> Result<ErgoBox> {
    let tree = dummy_tree(tag)?;
    let seed: [u8; 32] = rng.gen();
    let tx_id = TxId(blake2b256_hash(&seed));
    let index: u16 = rng.gen_range(0..5);
    let value = rng.gen_range(MIN_BOX_VALUE..1_000_000_000u64);
    let bv = BoxValue::try_from(value).context("BoxValue::try_from")?;

    // 0-3 tokens, random ids, amounts spanning `TokenAmount`'s full range
    // (`1`, near-`i64::MAX`, and uniform in between).
    let ntok = rng.gen_range(0..4usize);
    let mut toks = Vec::with_capacity(ntok);
    for j in 0..ntok {
        let tok_seed: [u8; 32] = rng.gen();
        let token_id = TokenId::from(blake2b256_hash(&tok_seed));
        let amount = match j % 3 {
            0 => TokenAmount::MIN,
            1 => TokenAmount::try_from(TokenAmount::MAX_RAW).context("TokenAmount::try_from MAX_RAW")?,
            _ => TokenAmount::try_from(rng.gen_range(TokenAmount::MIN_RAW..=TokenAmount::MAX_RAW))
                .context("TokenAmount::try_from")?,
        };
        toks.push(Token { token_id, amount });
    }
    let tokens = if toks.is_empty() {
        None
    } else {
        Some(BoxTokens::try_from(toks).map_err(|e| anyhow!("BoxTokens::try_from: {e:?}"))?)
    };

    // 0-2 non-mandatory registers (R4, then R5), plain Long/Int constants
    // — R0-R3's derivation must leave the real `Box.registers` lookup for
    // 4..9 untouched.
    let nregs = rng.gen_range(0..3usize);
    let mut regs: Vec<Constant> = Vec::with_capacity(nregs);
    if nregs >= 1 {
        regs.push(long_const(rng.gen::<i64>()));
    }
    if nregs >= 2 {
        regs.push(int_const(rng.gen::<i32>()));
    }
    let registers = if regs.is_empty() {
        NonMandatoryRegisters::empty()
    } else {
        NonMandatoryRegisters::try_from(regs).map_err(|e| anyhow!("NonMandatoryRegisters::try_from: {e:?}"))?
    };

    ErgoBox::new(bv, tree, tokens, registers, creation_height, tx_id, index)
        .map_err(|e| anyhow!("ErgoBox::new: {e:?}"))
}

pub fn generate(rng: &mut StdRng, count: usize) -> Result<Vec<GenCase>> {
    let tree = ErgoTree::try_from(build_tree()?).context("building box-fields ErgoTree")?;
    let mut cases = Vec::with_capacity(count);
    for i in 0..count {
        let height: u32 = rng.gen_range(0..2_000_000);
        // Vary SELF's creation height strictly below / exactly at / above
        // HEIGHT, splitting the `HEIGHT >= SELF.creationInfo._1` outcome.
        let self_height = match i % 3 {
            0 => height.saturating_sub(rng.gen_range(1..1000)),
            1 => height,
            _ => height + rng.gen_range(1..1000),
        };
        let self_box = varied_box(rng, (i as i64) % 40, self_height)?;
        let input1 = varied_box(rng, (i as i64) % 40 + 1, height)?;
        let inputs = [&self_box, &input1];
        // Vary OUTPUTS: empty (the tree's one error path, via
        // ByIndex(OUTPUTS, 0)) vs. one or two boxes.
        let outputs = match i % 4 {
            0 => vec![],
            1 => vec![varied_box(rng, 99, height)?],
            _ => vec![varied_box(rng, 100, height)?, varied_box(rng, 101, height)?],
        };
        let ctx = build_context(&self_box, &inputs, &outputs, height, vec![])?;
        let expected = run_reducer(&tree, &ctx);
        cases.push(GenCase {
            consts: vec![],
            self_box: self_box.clone(),
            inputs: vec![self_box, input1],
            outputs,
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
