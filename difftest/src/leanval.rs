//! Convert sigma-rust runtime types (`Literal`, `ErgoBox`, `SigmaBoolean`)
//! into JSON, decoded back into `ErgoTreeLean`'s own `Value`/`Box`/
//! `SigmaBoolean` Lean constructors by `ErgoTreeLean/DiffTest/Decode.lean`
//! at `lake exe difftest` *run* time.
//!
//! ## Why JSON + a runtime decoder, not a generated `.lean` literal
//!
//! Emitting each case directly as Lean source (`Case.mk 0 [...]
//! (Context.mk ...) ...`), one big `def cases : List Case := [...]` per
//! contract, doesn't scale: elaborating a few hundred cases (even after
//! switching every byte string from a `[n1, n2, ...]` numeral list to a
//! hex string + a `hexStringToBytes` call, and from `{ field := .. }`
//! records to positional `Box.mk`/`Context.mk`/`Case.mk`, both tried
//! first) still took minutes and had to be killed — confirmed
//! empirically, twice, not assumed. The cost is in elaborating one
//! enormous literal `List Case` term itself (thousands of nested
//! applications), not in any one part of it, so no amount of shrinking
//! individual leaves fixes it.
//!
//! `ErgoTreeLean`'s own `Value`/`Box`/`Context`/`Case`/`SigmaBoolean`
//! constructors are still exactly what builds every case — `Decode.lean`
//! calls them, just from ordinary (fast, compiled) Lean code walking a
//! parsed `Lean.Json` tree at `lake exe difftest` startup, instead of
//! from elaborated source text. See `Decode.lean`'s module docstring for
//! the JSON schema this file produces.

use anyhow::{bail, Context as _, Result};
use ergotree_ir::chain::ergo_box::NonMandatoryRegisterId;
use ergotree_ir::chain::ergo_box::{ErgoBox, RegisterId};
use ergotree_ir::mir::constant::Literal;
use ergotree_ir::mir::value::{CollKind, NativeColl};
use ergotree_ir::serialization::SigmaSerializable;
use ergotree_ir::sigma_protocol::sigma_boolean::{SigmaBoolean, SigmaConjecture, SigmaProofOfKnowledgeTree};
use ergotree_ir::types::stype::SType;
use serde_json::{json, Value as Json};
use sigma_ser::ScorexSerializable;

pub fn hex_of(bs: &[u8]) -> String {
    hex::encode(bs)
}

/// Mirrors `Syntax.lean`'s `SType` constructor names (lowerCamelCase),
/// exactly like `exporter/src/emit.rs`'s `stype_to_lean` — `Decode.lean`
/// parses these same tags back into `SType`.
pub fn stype_to_json(t: &SType) -> Result<Json> {
    Ok(match t {
        SType::SBoolean => json!({"tag": "sBoolean"}),
        SType::SByte => json!({"tag": "sByte"}),
        SType::SShort => json!({"tag": "sShort"}),
        SType::SInt => json!({"tag": "sInt"}),
        SType::SLong => json!({"tag": "sLong"}),
        SType::SBigInt => json!({"tag": "sBigInt"}),
        SType::SGroupElement => json!({"tag": "sGroupElement"}),
        SType::SSigmaProp => json!({"tag": "sSigmaProp"}),
        SType::SBox => json!({"tag": "sBox"}),
        SType::SUnit => json!({"tag": "sUnit"}),
        SType::SAny => json!({"tag": "sAny"}),
        SType::SOption(inner) => json!({"tag": "sOption", "inner": stype_to_json(inner)?}),
        SType::SColl(inner) => json!({"tag": "sColl", "inner": stype_to_json(inner)?}),
        SType::STuple(stuple) => {
            let items = stuple.items.iter().map(stype_to_json).collect::<Result<Vec<_>>>()?;
            json!({"tag": "sTuple", "items": items})
        }
        other => bail!("stype_to_json: unsupported SType {other:?}"),
    })
}

fn coll_to_json(ck: &CollKind<Literal>) -> Result<Json> {
    match ck {
        CollKind::NativeColl(NativeColl::CollByte(bytes)) => {
            let bs: Vec<u8> = bytes.iter().map(|b| *b as u8).collect();
            Ok(json!({"tag": "collByte", "hex": hex_of(&bs)}))
        }
        CollKind::WrappedColl { elem_tpe, items } => {
            let elem = stype_to_json(elem_tpe)?;
            let items_j = items.iter().map(literal_to_json).collect::<Result<Vec<_>>>()?;
            Ok(json!({"tag": "wrapped", "elem": elem, "items": items_j}))
        }
    }
}

/// Convert a stored register/constant `Literal` into JSON (see
/// `Decode.lean`'s module docstring for the schema).
pub fn literal_to_json(lit: &Literal) -> Result<Json> {
    Ok(match lit {
        Literal::Unit => json!({"tag": "vUnit"}),
        Literal::Boolean(b) => json!({"tag": "vBool", "v": b}),
        Literal::Byte(v) => json!({"tag": "vByte", "v": v}),
        Literal::Short(v) => json!({"tag": "vShort", "v": v}),
        Literal::Int(v) => json!({"tag": "vInt", "v": v}),
        Literal::Long(v) => json!({"tag": "vLong", "v": v.to_string()}),
        Literal::BigInt(v) => {
            let bi: num_bigint::BigInt = v.clone().into();
            json!({"tag": "vBigInt", "v": bi.to_string()})
        }
        Literal::GroupElement(g) => {
            let bytes = g.scorex_serialize_bytes().context("serializing GroupElement")?;
            json!({"tag": "vGroupElement", "hex": hex_of(&bytes)})
        }
        Literal::Coll(ck) => coll_to_json(ck)?,
        Literal::Opt(o) => match o.as_ref() {
            None => json!({"tag": "vOption", "v": null}),
            Some(inner) => json!({"tag": "vOption", "v": literal_to_json(inner)?}),
        },
        Literal::Tup(items) => {
            let items_j = items.iter().map(literal_to_json).collect::<Result<Vec<_>>>()?;
            json!({"tag": "vTuple", "items": items_j})
        }
        Literal::CBox(b) => json!({"tag": "vBox", "box": box_to_json(b)?}),
        // The oracle answer for `deserialize` is an already
        // evaluated `Value` — for a downstream contract's
        // `executeFromVar[SigmaProp](1)`, that's always a `SigmaProp`, not
        // a register/constant-storable literal (sigma-rust's own
        // `Constant` conversion supports it too, `impl From<SigmaProp> for
        // Constant` — this is a real runtime `Value`, just one
        // register/constant literals never produce). See `Decode.lean`'s
        // matching `"vSigmaProp"` case.
        Literal::SigmaProp(sp) => json!({"tag": "vSigmaProp", "sb": sigma_boolean_to_json(sp.value())?}),
        other => bail!("literal_to_json: unsupported register/constant literal {other:?}"),
    })
}

/// Convert an `ErgoBox` to JSON. `propositionBytes` mirrors
/// `eval/extract_script_bytes.rs`'s `b.script_bytes()` — the box's full
/// serialized `ErgoTree` (header + segregated constants + body), not just
/// the substituted proposition. `creationHeight`/`transactionId`/`index`
/// are the three fields `ErgoBox::creation_info()`/R3 derive from (see
/// `Decode.lean`'s module docstring for the schema) — `creationHeight` is
/// emitted as `creation_height as i32`, the exact cast `creation_info()`
/// itself performs, so this model's `Box.creationHeight` field is always
/// fed the same value R3/`ExtractCreationInfo` would read.
pub fn box_to_json(b: &ErgoBox) -> Result<Json> {
    let id_bytes = b.box_id().sigma_serialize_bytes().context("serializing box id")?;
    let prop_bytes = b.ergo_tree.sigma_serialize_bytes().context("serializing ergo_tree")?;
    let value: i64 = b.value.into();
    let creation_height = b.creation_height as i32;
    let transaction_id_bytes: &[u8] = b.transaction_id.as_ref();
    let tokens: Vec<Json> = b
        .tokens
        .as_ref()
        .map(|ts| ts.iter().cloned().collect::<Vec<_>>())
        .unwrap_or_default()
        .iter()
        .map(|t| {
            let tid: Vec<u8> = t.token_id.into();
            let amt: i64 = t.amount.into();
            json!([hex_of(&tid), amt.to_string()])
        })
        .collect();
    let mut regs: Vec<Json> = Vec::new();
    for (idx, reg_id) in [
        (4u8, RegisterId::NonMandatoryRegisterId(NonMandatoryRegisterId::R4)),
        (5, RegisterId::NonMandatoryRegisterId(NonMandatoryRegisterId::R5)),
        (6, RegisterId::NonMandatoryRegisterId(NonMandatoryRegisterId::R6)),
        (7, RegisterId::NonMandatoryRegisterId(NonMandatoryRegisterId::R7)),
        (8, RegisterId::NonMandatoryRegisterId(NonMandatoryRegisterId::R8)),
        (9, RegisterId::NonMandatoryRegisterId(NonMandatoryRegisterId::R9)),
    ] {
        if let Some(c) = b
            .get_register(reg_id)
            .map_err(|e| anyhow::anyhow!("get_register R{idx}: {e:?}"))?
        {
            regs.push(json!([idx, literal_to_json(&c.v)?]));
        }
    }
    Ok(json!({
        "id": hex_of(&id_bytes),
        "value": value.to_string(),
        "propositionBytes": hex_of(&prop_bytes),
        "tokens": tokens,
        "registers": regs,
        "creationHeight": creation_height,
        "transactionId": hex_of(transaction_id_bytes),
        "index": b.index,
    }))
}

/// Convert a reduced `SigmaBoolean` (sigma-rust's `reduce_to_crypto`
/// result) into JSON.
pub fn sigma_boolean_to_json(sb: &SigmaBoolean) -> Result<Json> {
    Ok(match sb {
        SigmaBoolean::TrivialProp(b) => json!({"tag": "trivial", "v": b}),
        SigmaBoolean::ProofOfKnowledge(SigmaProofOfKnowledgeTree::ProveDlog(pd)) => {
            let bytes = pd.h.scorex_serialize_bytes().context("serializing ProveDlog pk")?;
            json!({"tag": "proveDlog", "hex": hex_of(&bytes)})
        }
        SigmaBoolean::ProofOfKnowledge(SigmaProofOfKnowledgeTree::ProveDhTuple(_)) => {
            bail!("sigma_boolean_to_json: ProveDhTuple not modelled by ErgoTreeLean.SigmaBoolean")
        }
        SigmaBoolean::SigmaConjecture(SigmaConjecture::Cand(c)) => {
            let items = c.items.iter().map(sigma_boolean_to_json).collect::<Result<Vec<_>>>()?;
            json!({"tag": "cand", "items": items})
        }
        SigmaBoolean::SigmaConjecture(SigmaConjecture::Cor(c)) => {
            let items = c.items.iter().map(sigma_boolean_to_json).collect::<Result<Vec<_>>>()?;
            json!({"tag": "cor", "items": items})
        }
        SigmaBoolean::SigmaConjecture(SigmaConjecture::Cthreshold(c)) => {
            let items = c.children.iter().map(sigma_boolean_to_json).collect::<Result<Vec<_>>>()?;
            json!({"tag": "cthreshold", "k": c.k, "items": items})
        }
    })
}
