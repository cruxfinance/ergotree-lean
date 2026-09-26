//! Exports an EIP-5 ErgoTree template's `expressionTree` to a Lean 4
//! `Expr` term (see `ErgoTreeLean/Syntax.lean` for the target grammar,
//! which is designed to mirror this crate's `ergotree_ir::mir::expr::Expr`
//! 1:1).
//!
//! ConstantPlaceholders are typed (but never inlined) by building a
//! `ConstantStore` of dummy constants, one per `constTypes` entry, and
//! parsing with `substitute_placeholders = false` (the default for
//! `SigmaByteReader::new`) — so parsing yields `Expr::ConstPlaceholder`
//! nodes with the correct `tpe`, never `Expr::Const` values inlined from
//! the dummies. We deliberately parse the raw `expressionTree` bytes with
//! `Expr::sigma_parse` directly (not via `ErgoTree::sigma_parse_bytes` +
//! `.proposition()`), since `.proposition()` performs exactly the
//! placeholder-substitution this exporter must avoid.

use std::io::Cursor;
use std::io::Write as _;
use std::sync::Arc;

use anyhow::{anyhow, bail, Context, Result};
use clap::Parser;
use ergotree_ir::bigint256::BigInt256;
use ergotree_ir::mir::constant::{Constant, Literal};
use ergotree_ir::mir::expr::Expr;
use ergotree_ir::mir::value::CollKind;
use ergotree_ir::serialization::constant_store::ConstantStore;
use ergotree_ir::serialization::sigma_byte_reader::SigmaByteReader;
use ergotree_ir::serialization::SigmaSerializable;
use ergotree_ir::types::stype::SType;

mod eip5;
mod emit;
mod inventory;

use eip5::Eip5Template;

#[derive(Parser)]
#[command(name = "exporter", about = "Export an EIP-5 ErgoTree template to a Lean 4 Expr term")]
struct Cli {
    /// Path to an EIP-5 template JSON file (e.g. contracts/sell-order-eip5.json).
    input: Option<String>,

    /// Lean identifier for the generated `def <ident> : Expr := ...`.
    #[arg(long = "lean-name")]
    lean_name: Option<String>,

    /// Lean namespace the generated module opens with `namespace <ns> ... end <ns>`.
    #[arg(long)]
    namespace: Option<String>,

    /// Write output to this file instead of stdout.
    #[arg(short = 'o', long)]
    output: Option<String>,

    /// Print the sorted set of distinct MIR node kinds in the tree instead of emitting Lean.
    #[arg(long)]
    inventory: bool,

    /// Raw mode: parse this hex-encoded expressionTree instead of reading a JSON file.
    #[arg(long)]
    hex: Option<String>,

    /// Raw mode: comma-separated constType bytes (e.g. "07,0e,05"), matching --hex.
    #[arg(long = "const-types")]
    const_types: Option<String>,

    /// Extra free-text note appended to the generated file's header
    /// docstring (e.g. to record a network-specific baked-in constant a
    /// downstream contract's compiled tree has inlined, which `--hex`
    /// mode has no other way to flag since it has no EIP-5 template
    /// parameters).
    #[arg(long = "extra-doc")]
    extra_doc: Option<String>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    let (expr, hex_used) = if let Some(hex_str) = &cli.hex {
        let const_types_str = cli
            .const_types
            .as_ref()
            .ok_or_else(|| anyhow!("--hex requires --const-types"))?;
        let const_type_codes: Vec<String> = const_types_str
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();
        (parse_expression_tree(hex_str, &const_type_codes)?, hex_str.clone())
    } else {
        let path = cli
            .input
            .clone()
            .unwrap_or_else(|| "contracts/sell-order-eip5.json".to_string());
        let text = std::fs::read_to_string(&path)
            .with_context(|| format!("reading EIP-5 template {path}"))?;
        let template: Eip5Template =
            serde_json::from_str(&text).with_context(|| format!("parsing EIP-5 JSON {path}"))?;
        let expr = parse_expression_tree(&template.expression_tree, &template.const_types)?;
        (expr, template.expression_tree.clone())
    };

    if cli.inventory {
        let mut kinds = std::collections::BTreeSet::new();
        inventory::collect(&expr, &mut kinds);
        for k in kinds {
            println!("{k}");
        }
        return Ok(());
    }

    let lean_name = cli
        .lean_name
        .ok_or_else(|| anyhow!("--lean-name is required unless --inventory is passed"))?;
    let namespace = cli.namespace.unwrap_or_else(|| "ErgoTreeLean.Contracts".to_string());

    let mut body = String::new();
    emit::emit_expr(&expr, 2, &mut body)?;

    let extra_doc_block = match &cli.extra_doc {
        Some(note) => format!("\n{note}\n"),
        None => String::new(),
    };

    let out = format!(
        "/-\n\
         GENERATED FILE. Do not hand-edit.\n\n\
         Produced by the Rust exporter (`exporter/`) from the EIP-5\n\
         `expressionTree` bytes:\n\n  {hex_used}\n{extra_doc_block}\n\
         Regenerate with:\n\n\
         \x20 cd exporter && cargo run --release -- <path-to-eip5.json> \\\n\
         \x20     --lean-name {lean_name} --namespace {namespace} -o <output path>\n\
         -/\n\
         import ErgoTreeLean.Syntax\n\n\
         namespace {namespace}\n\n\
         open ErgoTreeLean\n\n\
         def {lean_name} : Expr :=\n{body}\n\n\
         end {namespace}\n"
    );

    match cli.output {
        Some(path) => {
            let mut f = std::fs::File::create(&path)
                .with_context(|| format!("creating output file {path}"))?;
            f.write_all(out.as_bytes())?;
        }
        None => {
            print!("{out}");
        }
    }

    Ok(())
}

/// Parse a raw hex-encoded `expressionTree` under a dummy constant store
/// built from `const_type_codes` (each a hex-encoded, serialized `SType`
/// byte string, in `constantIndex` order). Returns the parsed `Expr` with
/// `ConstPlaceholder` nodes intact (never substituted).
fn parse_expression_tree(hex_str: &str, const_type_codes: &[String]) -> Result<Expr> {
    let mut constants = Vec::with_capacity(const_type_codes.len());
    for (i, code) in const_type_codes.iter().enumerate() {
        let tpe_bytes = hex::decode(code)
            .with_context(|| format!("decoding constTypes[{i}] = {code:?} as hex"))?;
        let mut r = SigmaByteReader::new(Cursor::new(tpe_bytes), ConstantStore::empty());
        let tpe = SType::sigma_parse(&mut r)
            .with_context(|| format!("parsing constTypes[{i}] = {code:?} as an SType"))?;
        let v = dummy_literal(&tpe)
            .with_context(|| format!("building a dummy constant of type {tpe:?} for constTypes[{i}]"))?;
        constants.push(Constant { tpe, v });
    }

    let tree_bytes = hex::decode(hex_str).context("decoding expressionTree as hex")?;
    let mut r = SigmaByteReader::new(Cursor::new(&tree_bytes[..]), ConstantStore::new(constants));
    // `SigmaByteReader::new` defaults `substitute_placeholders` to `false`
    // — see module docstring.
    let expr = Expr::sigma_parse(&mut r).context("parsing expressionTree bytes as an Expr")?;

    // Confirm every byte was consumed, mirroring `parseExprHex`'s
    // "no leftover bytes" check on the Lean side.
    let mut rest = Vec::new();
    std::io::Read::read_to_end(&mut r, &mut rest).ok();
    if !rest.is_empty() {
        bail!(
            "{} leftover byte(s) after parsing expressionTree (parser stopped early)",
            rest.len()
        );
    }

    Ok(expr)
}

/// Build an arbitrary, never-inlined placeholder value of type `tpe`, used
/// only to type `ConstantPlaceholder` nodes while parsing (see module
/// docstring). Only covers the `SType` shapes that actually occur as
/// EIP-5 template constant types across the contracts this repo covers
/// (`GroupElement`, `Coll[Byte]`, `Long`) plus a few cheap-to-support
/// extras; anything else fails loudly rather than guessing.
fn dummy_literal(tpe: &SType) -> Result<Literal> {
    Ok(match tpe {
        SType::SBoolean => Literal::Boolean(false),
        SType::SByte => Literal::Byte(0),
        SType::SShort => Literal::Short(0),
        SType::SInt => Literal::Int(0),
        SType::SLong => Literal::Long(0),
        SType::SBigInt => Literal::BigInt(BigInt256::from(0i32)),
        SType::SGroupElement => {
            Literal::GroupElement(Arc::new(ergo_chain_types::ec_point::generator()))
        }
        SType::SUnit => Literal::Unit,
        SType::SColl(elem) => match elem.as_ref() {
            SType::SByte => Literal::Coll(CollKind::NativeColl(
                ergotree_ir::mir::value::NativeColl::CollByte(Arc::from(Vec::<i8>::new())),
            )),
            other => Literal::Coll(CollKind::WrappedColl {
                elem_tpe: other.clone(),
                items: Arc::from(Vec::<Literal>::new()),
            }),
        },
        SType::SOption(_) => Literal::Opt(Box::new(None)),
        other => bail!("dummy_literal: unsupported EIP-5 constant type {other:?}"),
    })
}
