//! Differential test-case generator library, driven by the real sigma-rust
//! `ergotree-interpreter 0.28.0` reducer (the exact version
//! `ErgoTreeLean/Eval.lean` was hand-ported from). For each generated
//! `(consts, Context)` pair a family's `generate` function builds:
//!
//! 1. Instantiate the EIP-5 template into a full `ErgoTree` (`build_ergo_tree`).
//! 2. Build a real `ergotree_interpreter::eval::context::Context`
//!    (`build_context`/`build_context_with_data_inputs`).
//! 3. Call `reduce_to_crypto` — sigma-rust's actual evaluator (`run_reducer`).
//! 4. Record the outcome (`Ok(SigmaBoolean)` or `Err`) and emit the whole
//!    case as JSON (`leanval`), into a single array file per contract.
//!
//! `ErgoTreeLean/DiffTest/Decode.lean` decodes that JSON back into
//! `ErgoTreeLean`'s own `Value`/`Box`/`Context`/`Case`/`SigmaBoolean`
//! constructors at `lake exe difftest` run time — see `leanval`'s module
//! docstring for why JSON-plus-a-runtime-decoder, not a generated `.lean`
//! literal (a generated Lean literal doesn't scale past a couple hundred
//! cases).
//!
//! This crate is a **library**: the case-building helpers below
//! (`GenCase`, `build_ergo_tree`, `build_context*`, `dummy_*`, the
//! `coll_*_const`/`*_const` constant builders, `run_reducer`) and the
//! `run_cli` driver are `pub` so a downstream package can register its
//! own contract families (its own `generate` functions) without
//! duplicating any of this. `bin/difftest.rs` is this repo's own thin
//! binary, registering only the `sell-order` family — see README.md's
//! "Difftest library usage" for how a downstream package wires up its
//! own binary against this same library.

pub mod box_fields;
pub mod leanval;
pub mod sell_order;
pub mod sigma_prop_bytes;
pub mod timelock;

use anyhow::{Context as _, Result};
use clap::Parser;
use ergo_chain_types::{ec_point, EcPoint};
use ergotree_interpreter::eval::context::{Context as EvalContext, TxIoVec};
use ergotree_interpreter::eval::reduce_to_crypto;
use ergotree_interpreter::sigma_protocol::prover::ContextExtension;
use ergotree_ir::chain::ergo_box::box_value::BoxValue;
use ergotree_ir::chain::ergo_box::{ErgoBox, NonMandatoryRegisters};
use ergotree_ir::chain::tx_id::TxId;
use ergotree_ir::ergo_tree::{ErgoTree, ErgoTreeHeader};
use ergotree_ir::mir::constant::{Constant, Literal};
use ergotree_ir::mir::value::{CollKind, NativeColl};
use ergotree_ir::serialization::sigma_byte_writer::SigmaByteWriter;
use ergotree_ir::serialization::SigmaSerializable;
use ergotree_ir::sigma_protocol::sigma_boolean::SigmaBoolean;
use ergotree_ir::types::stype::SType;
use indexmap::IndexMap;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::json;
use sigma_ser::vlq_encode::WriteSigmaVlqExt;

use leanval::{box_to_json, hex_of, literal_to_json, sigma_boolean_to_json};

/// One generated differential-test case: the EIP-5 template constants +
/// spending `Context`, plus what sigma-rust's real reducer says about it.
pub struct GenCase {
    pub consts: Vec<Constant>,
    pub self_box: ErgoBox,
    pub inputs: Vec<ErgoBox>,
    pub outputs: Vec<ErgoBox>,
    pub height: u32,
    pub extension: Vec<(u8, Constant)>,
    /// `CONTEXT.dataInputs` — empty for families that never read it.
    pub data_inputs: Vec<ErgoBox>,
    /// The per-case `blake2b256` oracle table this case's evaluation
    /// needs — `(input bytes, real blake2b256 hash)` pairs. Empty for
    /// families that never call `CalcBlake2b256`. See `Decode.lean`'s
    /// module docstring.
    pub blake2b_table: Vec<(Vec<u8>, Vec<u8>)>,
    /// The per-case `deserialize` oracle table — `(context-var bytes,
    /// already-evaluated Value JSON)` pairs, one per
    /// `executeFromVar`-reachable payload this case supplies. See
    /// `Decode.lean`'s module docstring.
    pub deser_table: Vec<(Vec<u8>, serde_json::Value)>,
    pub expected: Option<SigmaBoolean>,
}

impl GenCase {
    /// See `leanval`'s module docstring for the JSON schema and why JSON,
    /// not a generated `.lean` literal.
    pub fn to_json(&self, id: usize) -> Result<serde_json::Value> {
        let consts = self.consts.iter().map(|c| literal_to_json(&c.v)).collect::<Result<Vec<_>>>()?;
        let self_box = box_to_json(&self.self_box)?;
        let inputs = self.inputs.iter().map(box_to_json).collect::<Result<Vec<_>>>()?;
        let outputs = self.outputs.iter().map(box_to_json).collect::<Result<Vec<_>>>()?;
        let data_inputs = self.data_inputs.iter().map(box_to_json).collect::<Result<Vec<_>>>()?;
        let extension = self
            .extension
            .iter()
            .map(|(id, c)| Ok(json!([id, literal_to_json(&c.v)?])))
            .collect::<Result<Vec<_>>>()?;
        let blake2b: Vec<serde_json::Value> = self
            .blake2b_table
            .iter()
            .map(|(inp, out)| json!([hex_of(inp), hex_of(out)]))
            .collect();
        let deserialize: Vec<serde_json::Value> =
            self.deser_table.iter().map(|(inp, v)| json!([hex_of(inp), v])).collect();
        let expected = match &self.expected {
            None => serde_json::Value::Null,
            Some(sb) => sigma_boolean_to_json(sb)?,
        };
        Ok(json!({
            "id": id,
            "consts": consts,
            "ctx": {
                "selfBox": self_box,
                "inputs": inputs,
                "outputs": outputs,
                "dataInputs": data_inputs,
                "height": self.height,
                "extension": extension,
                "blake2b": blake2b,
                "deserialize": deserialize,
            },
            "expected": expected,
        }))
    }
}

/// Build a full `ErgoTree` from an EIP-5 template's raw `expressionTree`
/// hex bytes + real constant values, by prepending a from-scratch
/// header+constants-segment (mirrors what the original compiler's full
/// serialized-ErgoTree bytes look like — the EIP-5 JSON only keeps the
/// body/`expressionTree` segment, so this reconstructs the rest).
pub fn build_ergo_tree(expression_tree_hex: &str, constants: Vec<Constant>) -> Result<ErgoTree> {
    let body = hex::decode(expression_tree_hex).context("decoding expressionTree hex")?;
    let mut data: Vec<u8> = Vec::new();
    {
        let mut w = SigmaByteWriter::new(&mut data, None);
        w.put_u8(ErgoTreeHeader::v0(true).serialized())?;
        w.put_u32(constants.len() as u32)?;
        for c in &constants {
            c.sigma_serialize(&mut w)?;
        }
    }
    data.extend_from_slice(&body);
    ErgoTree::sigma_parse_bytes(&data).context("parsing constructed ErgoTree bytes")
}

/// A trivial, deterministically-varied "some other script" ErgoTree, used
/// for boxes whose exact script doesn't matter except that it's some valid,
/// comparable `propositionBytes` (destination templates, cancel addresses,
/// mismatched continuations, ...). Never evaluated.
pub fn dummy_tree(tag: i64) -> Result<ErgoTree> {
    let expr = ergotree_ir::mir::expr::Expr::Const(Constant {
        tpe: SType::SLong,
        v: Literal::Long(tag),
    });
    ErgoTree::try_from(expr).context("building dummy ErgoTree")
}

/// Minimum safe `BoxValue` this generator ever uses (well above
/// `BoxValue::MIN_RAW`, to leave headroom for `+ rng.gen_range(..)`-style
/// perturbations elsewhere without falling back under the real minimum).
pub const MIN_BOX_VALUE: u64 = 100_000;

pub fn dummy_box_with_tree(value: u64, tree: ErgoTree) -> Result<ErgoBox> {
    let bv = BoxValue::try_from(value.max(MIN_BOX_VALUE)).context("BoxValue::try_from")?;
    ErgoBox::new(bv, tree, None, NonMandatoryRegisters::empty(), 0, TxId::zero(), 0)
        .map_err(|e| anyhow::anyhow!("ErgoBox::new: {e:?}"))
}

pub fn coll_byte_const(bs: &[u8]) -> Constant {
    let signed: Vec<i8> = bs.iter().map(|b| *b as i8).collect();
    Constant {
        tpe: SType::SColl(std::sync::Arc::new(SType::SByte)),
        v: Literal::Coll(CollKind::NativeColl(NativeColl::CollByte(signed.into()))),
    }
}

pub fn coll_long_const(vs: &[i64]) -> Constant {
    Constant {
        tpe: SType::SColl(std::sync::Arc::new(SType::SLong)),
        v: Literal::Coll(CollKind::WrappedColl {
            elem_tpe: SType::SLong,
            items: vs.iter().map(|v| Literal::Long(*v)).collect::<Vec<_>>().into(),
        }),
    }
}

pub fn coll_group_element_const(pks: &[EcPoint]) -> Constant {
    Constant {
        tpe: SType::SColl(std::sync::Arc::new(SType::SGroupElement)),
        v: Literal::Coll(CollKind::WrappedColl {
            elem_tpe: SType::SGroupElement,
            items: pks
                .iter()
                .map(|p| Literal::GroupElement(std::sync::Arc::new(p.clone())))
                .collect::<Vec<_>>()
                .into(),
        }),
    }
}

pub fn coll_coll_byte_const(items: &[Vec<u8>]) -> Constant {
    Constant {
        tpe: SType::SColl(std::sync::Arc::new(SType::SColl(std::sync::Arc::new(SType::SByte)))),
        v: Literal::Coll(CollKind::WrappedColl {
            elem_tpe: SType::SColl(std::sync::Arc::new(SType::SByte)),
            items: items
                .iter()
                .map(|bs| {
                    let signed: Vec<i8> = bs.iter().map(|b| *b as i8).collect();
                    Literal::Coll(CollKind::NativeColl(NativeColl::CollByte(signed.into())))
                })
                .collect::<Vec<_>>()
                .into(),
        }),
    }
}

pub fn box_const(b: &ErgoBox) -> Constant {
    Constant {
        tpe: SType::SBox,
        v: Literal::CBox(ergotree_ir::reference::Ref::Arc(std::sync::Arc::new(b.clone()))),
    }
}

pub fn int_const(v: i32) -> Constant {
    Constant { tpe: SType::SInt, v: Literal::Int(v) }
}
pub fn long_const(v: i64) -> Constant {
    Constant { tpe: SType::SLong, v: Literal::Long(v) }
}

pub fn token_id_from_seed(rng: &mut StdRng) -> Vec<u8> {
    let bytes: [u8; 32] = rng.gen();
    ergo_chain_types::blake2b256_hash(&bytes).into()
}

/// A deterministically-varied `EcPoint`: `n` repeated group additions of
/// the generator to itself (`EcPoint`'s `Mul<&EcPoint>` operator is group
/// addition, not scalar multiplication — see `ec_point.rs`), avoiding a
/// direct dependency on the underlying `k256::Scalar` type. `n = 0` yields
/// the generator itself.
pub fn nth_point(n: u32) -> EcPoint {
    let g = ec_point::generator();
    let mut p = g.clone();
    for _ in 0..n {
        p = p * &g;
    }
    p
}

pub fn rand_ec_point(rng: &mut StdRng) -> EcPoint {
    nth_point(rng.gen_range(0..500))
}

/// Run sigma-rust's real evaluator on a fully-built `(ErgoTree, Context)`
/// pair. `None` means the `.proposition()` substitution or `reduce_to_crypto`
/// itself errored (an evaluation error).
pub fn run_reducer(tree: &ErgoTree, ctx: &EvalContext) -> Option<SigmaBoolean> {
    let expr = tree.proposition().ok()?;
    match reduce_to_crypto(&expr, ctx) {
        Ok(r) => Some(r.sigma_prop),
        Err(e) => {
            if std::env::var("DIFFTEST_DEBUG").is_ok() {
                eprintln!("reduce_to_crypto error: {e:?}");
            }
            None
        }
    }
}

pub fn build_context<'a>(
    self_box: &'a ErgoBox,
    inputs: &'a [&'a ErgoBox],
    outputs: &'a [ErgoBox],
    height: u32,
    extension: Vec<(u8, Constant)>,
) -> Result<EvalContext<'a>> {
    build_context_with_data_inputs(self_box, inputs, outputs, &[], height, extension)
}

/// Like `build_context`, but also wires up `CONTEXT.dataInputs` — a real
/// `Option<TxIoVec<&ErgoBox>>` on sigma-rust's own `Context`, unlike a
/// family that never reads `CONTEXT.dataInputs` and so always passes
/// `&[]` here via the plain `build_context` above (`None`, matching what
/// a real transaction with zero data inputs looks like).
pub fn build_context_with_data_inputs<'a>(
    self_box: &'a ErgoBox,
    inputs: &'a [&'a ErgoBox],
    outputs: &'a [ErgoBox],
    data_inputs: &'a [&'a ErgoBox],
    height: u32,
    extension: Vec<(u8, Constant)>,
) -> Result<EvalContext<'a>> {
    let base = sigma_test_util::force_any_val::<EvalContext<'static>>();
    let inputs_vec: Vec<&'a ErgoBox> = inputs.to_vec();
    let inputs_bv: TxIoVec<&'a ErgoBox> =
        inputs_vec.try_into().map_err(|e| anyhow::anyhow!("inputs TxIoVec: {e:?}"))?;
    let data_inputs_bv: Option<TxIoVec<&'a ErgoBox>> = if data_inputs.is_empty() {
        None
    } else {
        Some(data_inputs.to_vec().try_into().map_err(|e| anyhow::anyhow!("data_inputs TxIoVec: {e:?}"))?)
    };
    let mut ext_map = IndexMap::new();
    for (id, c) in extension {
        ext_map.insert(id, c);
    }
    Ok(EvalContext {
        height,
        self_box,
        outputs,
        data_inputs: data_inputs_bv,
        inputs: inputs_bv,
        pre_header: base.pre_header,
        headers: base.headers,
        extension: ContextExtension { values: ext_map },
    })
}

/// A registered contract family's case generator.
pub type Generator = fn(&mut StdRng, usize) -> Result<Vec<GenCase>>;

#[derive(Parser)]
#[command(name = "difftest", about = "Differential-test case generator")]
struct Cli {
    /// Which registered contract family to generate cases for.
    #[arg(long)]
    contract: String,
    /// PRNG seed (deterministic).
    #[arg(long, default_value_t = 1)]
    seed: u64,
    /// Number of cases to generate.
    #[arg(long, default_value_t = 1200)]
    count: usize,
    /// Output JSON file path (read by `ErgoTreeLean/DiffTest/Decode.lean`).
    #[arg(short, long)]
    out: String,
}

/// The standard difftest CLI (`--contract/--seed/--count/--out`), driven
/// by a name → generator table a downstream binary supplies — this is
/// the "reusable CLI/driver that takes a family name → generator mapping"
/// every `difftest` binary (this repo's own `bin/difftest.rs`, and a
/// downstream package's own binary) is built from, so the case-generation
/// loop, JSON emission and outcome tally live in exactly one place.
pub fn run_cli(families: &[(&str, Generator)]) -> Result<()> {
    let cli = Cli::parse();
    let generate = families
        .iter()
        .find(|(name, _)| *name == cli.contract)
        .map(|(_, g)| *g)
        .ok_or_else(|| {
            let names: Vec<&str> = families.iter().map(|(n, _)| *n).collect();
            anyhow::anyhow!("unknown contract {:?} (known: {})", cli.contract, names.join(", "))
        })?;

    let mut rng = StdRng::seed_from_u64(cli.seed);
    let cases = generate(&mut rng, cli.count)?;

    let mut ok_trivial_true = 0usize;
    let mut ok_trivial_false = 0usize;
    let mut ok_prove_dlog = 0usize;
    let mut ok_other = 0usize;
    let mut errored = 0usize;

    let mut json_cases = Vec::with_capacity(cases.len());
    for (i, case) in cases.iter().enumerate() {
        json_cases.push(case.to_json(i)?);
        match &case.expected {
            Some(SigmaBoolean::TrivialProp(true)) => ok_trivial_true += 1,
            Some(SigmaBoolean::TrivialProp(false)) => ok_trivial_false += 1,
            Some(SigmaBoolean::ProofOfKnowledge(_)) => ok_prove_dlog += 1,
            Some(_) => ok_other += 1,
            None => errored += 1,
        }
    }

    let out = serde_json::to_string(&json_cases)?;
    std::fs::write(&cli.out, out).with_context(|| format!("writing {}", cli.out))?;

    eprintln!(
        "{}: {} cases -> {} (trivial-true={} trivial-false={} proveDlog={} other={} error={})",
        cli.contract,
        cases.len(),
        cli.out,
        ok_trivial_true,
        ok_trivial_false,
        ok_prove_dlog,
        ok_other,
        errored
    );
    Ok(())
}
