//! `sell-order` case generator — a smoke test for the harness itself
//! (`sell-order` is the phase-1 contract with hand-proved theorems; this
//! isn't testing anything new about it, just confirming the difftest
//! plumbing agrees with sigma-rust on a simple, already-trusted contract).

use anyhow::Result;
use ergotree_ir::chain::ergo_box::box_value::BoxValue;
use ergotree_ir::mir::constant::Constant;
use ergotree_ir::types::stype::SType;
use rand::rngs::StdRng;
use rand::Rng;

use crate::{build_context, build_ergo_tree, dummy_box_with_tree, dummy_tree, rand_ec_point, run_reducer, GenCase};

const SELL_ORDER_HEX: &str = "d801d601b2a5040000eb02cd7300d1ed93c27201730192c172017302";
const MIN_BOX_VALUE: i64 = 100_000;

pub fn generate(rng: &mut StdRng, count: usize) -> Result<Vec<GenCase>> {
    let mut cases = Vec::with_capacity(count);
    let mut i = 0usize;
    while cases.len() < count {
        i += 1;
        match gen_one(rng, i) {
            Ok(c) => cases.push(c),
            Err(_) => continue,
        }
    }
    Ok(cases)
}

fn gen_one(rng: &mut StdRng, i: usize) -> Result<GenCase> {
    let self_tree = dummy_tree(0)?;
    let self_box = dummy_box_with_tree(MIN_BOX_VALUE as u64, self_tree)?;

    let seller_pk = rand_ec_point(rng);
    let seller_prop_tag: i64 = rng.gen_range(0..50);
    let seller_prop_tree = dummy_tree(seller_prop_tag)?;
    let seller_prop_bytes = ergotree_ir::serialization::SigmaSerializable::sigma_serialize_bytes(&seller_prop_tree)?;
    let price: i64 = match i % 7 {
        0 => MIN_BOX_VALUE,
        1 => i64::MAX / 2,
        2 => MIN_BOX_VALUE + 1,
        _ => rng.gen_range(MIN_BOX_VALUE..1_000_000_000_000i64),
    };

    let consts: Vec<Constant> = vec![
        Constant { tpe: SType::SGroupElement, v: ergotree_ir::mir::constant::Literal::GroupElement(std::sync::Arc::new(seller_pk)) },
        crate::coll_byte_const(&seller_prop_bytes),
        crate::long_const(price),
    ];
    let tree = build_ergo_tree(SELL_ORDER_HEX, consts.clone())?;

    // Vary: no outputs / output paying enough / output paying too little / output with a
    // different script entirely / output at the price boundary exactly.
    let outputs = match i % 5 {
        0 => vec![],
        1 => {
            let val = if price > BoxValue::MAX_RAW as i64 - 1000 { price } else { price + rng.gen_range(0..1000) };
            vec![dummy_box_with_tree(val as u64, dummy_tree(seller_prop_tag)?)?]
        }
        2 => {
            let val = (price / 2).max(MIN_BOX_VALUE);
            vec![dummy_box_with_tree(val as u64, dummy_tree(seller_prop_tag)?)?]
        }
        3 => vec![dummy_box_with_tree(MIN_BOX_VALUE as u64, dummy_tree(seller_prop_tag + 1)?)?],
        _ => vec![dummy_box_with_tree(price as u64, dummy_tree(seller_prop_tag)?)?], // exact boundary
    };

    let inputs = [&self_box];
    let ctx = build_context(&self_box, &inputs, &outputs, 0, vec![])?;
    let expected = run_reducer(&tree, &ctx);

    Ok(GenCase {
        consts,
        self_box: self_box.clone(),
        inputs: vec![self_box],
        outputs,
        height: 0,
        extension: vec![],
        data_inputs: vec![],
        blake2b_table: vec![],
        deser_table: vec![],
        expected,
    })
}
