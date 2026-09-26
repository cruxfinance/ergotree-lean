//! `timelock` case generator: the real mainnet
//! `sigmaProp(HEIGHT >= SELF.creationInfo._1 + 720) && PK("...")` tree
//! (same hex `exporter/tests/ergotree_input.rs`'s `TIMELOCK_WITH_PK` uses,
//! and what `ErgoTreeLean/Contracts/Timelock/Exported.lean` was exported
//! from), varying `SELF`'s creation height around the `HEIGHT - 720`
//! boundary. A second, real-world complement to the synthetic
//! `box-fields` family: this tree exercises `ExtractCreationInfo` (via
//! `SigmaAnd`/`Cand` normalization) rather than R0-R3, and is a tree this
//! model didn't support at all before this change (see
//! `exporter/tests/ergotree_input.rs`).
//!
//! `SELF.creationInfo` never fails to evaluate (always defined), so this
//! family has no error outcome — only `trivial false` (the height check
//! fails, so `Cand::normalized` collapses to `TrivialProp(false)`) and
//! `proveDlog` (the height check passes, so the `TrivialProp(true)` guard
//! drops out of the `Cand`, leaving the bare `ProveDlog`).

use anyhow::{Context as _, Result};
use ergo_chain_types::blake2b256_hash;
use ergotree_ir::chain::ergo_box::box_value::BoxValue;
use ergotree_ir::chain::ergo_box::{ErgoBox, NonMandatoryRegisters};
use ergotree_ir::chain::tx_id::TxId;
use ergotree_ir::ergo_tree::ErgoTree;
use ergotree_ir::serialization::SigmaSerializable;
use rand::rngs::StdRng;
use rand::Rng;

use crate::{build_context, dummy_tree, run_reducer, GenCase, MIN_BOX_VALUE};

/// Same hex as `exporter/tests/ergotree_input.rs`'s `TIMELOCK_WITH_PK`.
const TIMELOCK_HEX: &str =
    "100204a00b08cd020e814ace36202c238f6e2ce66d69a1036cb3a6a3318afcecd5af64a5b66fd274ea02d192a39a8cc7a70173007301";

fn tree() -> Result<ErgoTree> {
    let bytes = hex::decode(TIMELOCK_HEX).context("decoding TIMELOCK_HEX")?;
    ErgoTree::sigma_parse_bytes(&bytes).context("parsing the real timelock tree")
}

fn varied_box(rng: &mut StdRng, creation_height: u32) -> Result<ErgoBox> {
    let self_tree = dummy_tree(0)?;
    let seed: [u8; 32] = rng.gen();
    let tx_id = TxId(blake2b256_hash(&seed));
    let index: u16 = rng.gen_range(0..5);
    let bv = BoxValue::try_from(MIN_BOX_VALUE).context("BoxValue::try_from")?;
    ErgoBox::new(bv, self_tree, None, NonMandatoryRegisters::empty(), creation_height, tx_id, index)
        .map_err(|e| anyhow::anyhow!("ErgoBox::new: {e:?}"))
}

pub fn generate(rng: &mut StdRng, count: usize) -> Result<Vec<GenCase>> {
    let t = tree()?;
    let consts = t.get_constants().map_err(|e| anyhow::anyhow!("get_constants: {e:?}"))?;
    let mut cases = Vec::with_capacity(count);
    for i in 0..count {
        let height: u32 = rng.gen_range(720..2_000_000);
        // Vary SELF.creation_height around the `HEIGHT - 720` boundary:
        // well below (passes), exactly at it (passes, `>=`), and above it
        // (fails).
        let self_height = match i % 3 {
            0 => height.saturating_sub(720).saturating_sub(rng.gen_range(1..500)),
            1 => height.saturating_sub(720),
            _ => height.saturating_sub(720) + rng.gen_range(1..500),
        };
        let self_box = varied_box(rng, self_height)?;
        let inputs = [&self_box];
        let ctx = build_context(&self_box, &inputs, &[], height, vec![])?;
        let expected = run_reducer(&t, &ctx);
        cases.push(GenCase {
            consts: consts.clone(),
            self_box: self_box.clone(),
            inputs: vec![self_box],
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
