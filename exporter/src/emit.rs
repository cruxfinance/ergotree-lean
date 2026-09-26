//! Walk a parsed `Expr` and emit the corresponding Lean 4 `ErgoTreeLean.Expr`
//! term (see `ErgoTreeLean/Syntax.lean`). Only the node kinds that occur in
//! the contracts this repo covers are handled; anything else fails loudly
//! (`bail!`) naming the unhandled MIR node, rather than emitting an
//! approximation.

use anyhow::{bail, Context, Result};
use ergotree_ir::mir::bin_op::{ArithOp, BinOpKind, BitOp, LogicalOp, RelationOp};
use ergotree_ir::mir::collection::Collection;
use ergotree_ir::mir::constant::Literal;
use ergotree_ir::mir::expr::Expr;
use ergotree_ir::mir::global_vars::GlobalVars;
use ergotree_ir::mir::value::{CollKind, NativeColl};
use ergotree_ir::types::stype::SType;

/// Wrap `s` in parens if it looks like an application (contains whitespace
/// at the top level) and isn't already parenthesized/bracketed — i.e. make
/// it safe to use as an argument in a Lean application.
fn paren(s: &str) -> String {
    let s = s.trim();
    if s.is_empty() {
        return s.to_string();
    }
    if s.starts_with('(') || s.starts_with('[') || !s.contains(' ') {
        s.to_string()
    } else {
        format!("({s})")
    }
}

fn fmt_int(v: i64) -> String {
    if v < 0 {
        format!("(-{})", -(v as i128))
    } else {
        format!("{v}")
    }
}

/// Same convention as `fmt_int`, for an arbitrary-precision `BigInt256`
/// (some contracts have inline `BigInt` constant
/// literals, e.g. `10000L.toBigInt` — folded by the Scala compiler into a
/// literal `Const(BigInt256(10000))` rather than an `Upcast` at those call
/// sites). `to_str_radix(10)` is a plain decimal string with a leading
/// `-` for negatives (`bigint256.rs`'s `Display` impl).
fn fmt_bigint(v: &ergotree_ir::bigint256::BigInt256) -> String {
    let s = v.to_str_radix(10);
    match s.strip_prefix('-') {
        Some(mag) => format!("(-{mag})"),
        None => s,
    }
}

pub fn stype_to_lean(t: &SType) -> Result<String> {
    Ok(match t {
        SType::SBoolean => "SType.sBoolean".to_string(),
        SType::SByte => "SType.sByte".to_string(),
        SType::SShort => "SType.sShort".to_string(),
        SType::SInt => "SType.sInt".to_string(),
        SType::SLong => "SType.sLong".to_string(),
        SType::SBigInt => "SType.sBigInt".to_string(),
        SType::SGroupElement => "SType.sGroupElement".to_string(),
        SType::SSigmaProp => "SType.sSigmaProp".to_string(),
        SType::SBox => "SType.sBox".to_string(),
        SType::SAvlTree => "SType.sAvlTree".to_string(),
        SType::SContext => "SType.sContext".to_string(),
        SType::SHeader => "SType.sHeader".to_string(),
        SType::SPreHeader => "SType.sPreHeader".to_string(),
        SType::SGlobal => "SType.sGlobal".to_string(),
        SType::SUnit => "SType.sUnit".to_string(),
        SType::SAny => "SType.sAny".to_string(),
        SType::SOption(inner) => format!("(SType.sOption {})", stype_to_lean(inner)?),
        SType::SColl(inner) => format!("(SType.sColl {})", stype_to_lean(inner)?),
        SType::STuple(stuple) => {
            let items = stuple
                .items
                .iter()
                .map(stype_to_lean)
                .collect::<Result<Vec<_>>>()?;
            format!("(SType.sTuple [{}])", items.join(", "))
        }
        SType::SFunc(sfunc) => {
            let dom = sfunc
                .t_dom
                .iter()
                .map(stype_to_lean)
                .collect::<Result<Vec<_>>>()?;
            let range = stype_to_lean(&sfunc.t_range)?;
            format!("(SType.sFunc [{}] {})", dom.join(", "), range)
        }
        other => bail!("stype_to_lean: unsupported SType {other:?}"),
    })
}

fn coll_to_lean(ck: &CollKind<Literal>) -> Result<String> {
    match ck {
        // `Coll[Byte]` has no dedicated Lean `Value` constructor (see
        // `Syntax.lean`'s module docstring) — it's `vColl .sByte [.vByte
        // _, ...]` like any other collection, just always built from
        // `NativeColl` on the sigma-rust side (a storage optimization,
        // not a semantic distinction this exporter needs to preserve).
        CollKind::NativeColl(NativeColl::CollByte(bytes)) => {
            let items: Vec<String> = bytes
                .iter()
                .map(|b| format!("(Value.vByte {})", fmt_int(*b as i64)))
                .collect();
            Ok(format!("(Value.vColl SType.sByte [{}])", items.join(", ")))
        }
        CollKind::WrappedColl { elem_tpe, items } => {
            let elem_s = stype_to_lean(elem_tpe)?;
            let items_s = items
                .iter()
                .map(literal_to_lean)
                .collect::<Result<Vec<_>>>()?;
            Ok(format!(
                "(Value.vColl {} [{}])",
                elem_s,
                items_s.join(", ")
            ))
        }
    }
}

fn literal_to_lean(lit: &Literal) -> Result<String> {
    Ok(match lit {
        Literal::Unit => "Value.vUnit".to_string(),
        Literal::Boolean(b) => format!("(Value.vBool {})", if *b { "true" } else { "false" }),
        Literal::Byte(v) => format!("(Value.vByte {})", fmt_int(*v as i64)),
        Literal::Short(v) => format!("(Value.vShort {})", fmt_int(*v as i64)),
        Literal::Int(v) => format!("(Value.vInt {})", fmt_int(*v as i64)),
        Literal::Long(v) => format!("(Value.vLong {})", fmt_int(*v)),
        Literal::BigInt(v) => format!("(Value.vBigInt {})", fmt_bigint(v)),
        Literal::Coll(ck) => coll_to_lean(ck)?,
        // `Value.vOption` carries an `elemTpe` (see `Syntax.lean`'s module
        // docstring) that a bare `Literal::Opt` doesn't record; `SType.sAny`
        // is a safe placeholder — `eval`'s `Value.beq` never compares a
        // `vOption`'s `elemTpe`, and neither covered contract ever emits an
        // inline `Option` constant (`Literal::Opt` only ever appears here as
        // a dead branch), so this is never exercised.
        Literal::Opt(o) => match o.as_ref() {
            None => "(Value.vOption SType.sAny none)".to_string(),
            Some(inner) => {
                format!("(Value.vOption SType.sAny (some {}))", paren(&literal_to_lean(inner)?))
            }
        },
        Literal::Tup(items) => {
            let items_s = items
                .iter()
                .map(literal_to_lean)
                .collect::<Result<Vec<_>>>()?;
            format!("(Value.vTuple [{}])", items_s.join(", "))
        }
        other => bail!(
            "literal_to_lean: unsupported inline constant literal {other:?} \
             (GroupElement/SigmaProp/AvlTree/Box constants aren't used inline by \
             the contracts this exporter has been run against; only via ConstantPlaceholder \
             — BigInt is supported, see fmt_bigint)"
        ),
    })
}

fn bin_op_kind_to_lean(k: &BinOpKind) -> Result<String> {
    Ok(match k {
        BinOpKind::Arith(op) => format!(
            "(BinOpKind.arith {})",
            match op {
                ArithOp::Plus => "ArithOp.plus",
                ArithOp::Minus => "ArithOp.minus",
                ArithOp::Multiply => "ArithOp.multiply",
                ArithOp::Divide => "ArithOp.divide",
                ArithOp::Max => "ArithOp.max",
                ArithOp::Min => "ArithOp.min",
                ArithOp::Modulo => "ArithOp.modulo",
            }
        ),
        BinOpKind::Relation(op) => format!(
            "(BinOpKind.relation {})",
            match op {
                RelationOp::Eq => "RelationOp.eq",
                RelationOp::NEq => "RelationOp.neq",
                RelationOp::Ge => "RelationOp.ge",
                RelationOp::Gt => "RelationOp.gt",
                RelationOp::Le => "RelationOp.le",
                RelationOp::Lt => "RelationOp.lt",
            }
        ),
        BinOpKind::Logical(op) => format!(
            "(BinOpKind.logical {})",
            match op {
                LogicalOp::And => "LogicalOp.and",
                LogicalOp::Or => "LogicalOp.or",
                LogicalOp::Xor => "LogicalOp.xor",
            }
        ),
        BinOpKind::Bit(op) => format!(
            "(BinOpKind.bit {})",
            match op {
                BitOp::BitOr => "BitOp.bitOr",
                BitOp::BitAnd => "BitOp.bitAnd",
                BitOp::BitXor => "BitOp.bitXor",
            }
        ),
    })
}

/// Emit a `List Expr` Lean literal from MIR `Expr` children.
fn list_of(items: &[Expr]) -> Result<String> {
    let parts = items.iter().map(emit).collect::<Result<Vec<_>>>()?;
    Ok(format!("[{}]", parts.join(", ")))
}

pub fn emit(e: &Expr) -> Result<String> {
    Ok(match e {
        Expr::Const(c) => literal_to_lean(&c.v)
            .map(|v| format!(".const {}", paren(&v)))
            .with_context(|| "emitting Expr::Const")?,
        Expr::ConstPlaceholder(cp) => {
            format!(".constPlaceholder {} {}", cp.id, paren(&stype_to_lean(&cp.tpe)?))
        }
        Expr::BlockValue(sp) => {
            let bv = sp.expr();
            let mut defs = Vec::with_capacity(bv.items.len());
            for item in &bv.items {
                match item {
                    Expr::ValDef(vd) => {
                        let vd = vd.expr();
                        let rhs = emit(&vd.rhs)?;
                        defs.push(format!("({}, {})", vd.id.0, paren(&rhs)));
                    }
                    other => bail!(
                        "emit BlockValue: expected item to be a ValDef, got {other:?} \
                         (BlockValue.items should only ever contain ValDef nodes)"
                    ),
                }
            }
            let result = emit(&bv.result)?;
            format!(".blockValue [{}] {}", defs.join(", "), paren(&result))
        }
        Expr::ValUse(vu) => {
            format!(".valUse {} {}", vu.val_id.0, paren(&stype_to_lean(&vu.tpe)?))
        }
        Expr::GlobalVars(GlobalVars::Outputs) => ".outputs".to_string(),
        Expr::GlobalVars(GlobalVars::Height) => ".height".to_string(),
        Expr::GlobalVars(GlobalVars::SelfBox) => ".selfBox".to_string(),
        Expr::GlobalVars(GlobalVars::Inputs) => ".inputs".to_string(),
        Expr::GlobalVars(other) => bail!("emit: unsupported GlobalVars variant {other:?}"),
        Expr::Context => ".context".to_string(),
        Expr::CalcBlake2b256(v) => format!(".calcBlake2b256 {}", paren(&emit(&v.input)?)),
        Expr::DeserializeContext(dc) => {
            format!(".deserializeContext {} {}", dc.id, paren(&stype_to_lean(&dc.tpe)?))
        }
        Expr::Atleast(a) => format!(
            ".atLeast {} {}",
            paren(&emit(&a.bound)?),
            paren(&emit(&a.input)?)
        ),
        Expr::Map(sp) => {
            let m = sp.expr();
            format!(
                ".mapOf {} {} {}",
                paren(&emit(&m.input)?),
                paren(&emit(&m.mapper)?),
                paren(&stype_to_lean(&m.out_elem_tpe())?)
            )
        }
        Expr::ByIndex(sp) => {
            let bi = sp.expr();
            let coll = emit(&bi.input)?;
            let idx = emit(&bi.index)?;
            let default = match &bi.default {
                None => "none".to_string(),
                Some(d) => format!("(some {})", paren(&emit(d)?)),
            };
            format!(
                ".byIndex {} {} {}",
                paren(&coll),
                paren(&idx),
                paren(&default)
            )
        }
        Expr::SigmaOr(so) => format!(".sigmaOr {}", list_of(so.items.as_slice())?),
        Expr::SigmaAnd(sa) => format!(".sigmaAnd {}", list_of(sa.items.as_slice())?),
        Expr::CreateProveDlog(v) => format!(".createProveDlog {}", paren(&emit(&v.input)?)),
        Expr::BoolToSigmaProp(v) => format!(".boolToSigmaProp {}", paren(&emit(&v.input)?)),
        Expr::BinOp(sp) => {
            let bo = sp.expr();
            let kind = bin_op_kind_to_lean(&bo.kind)?;
            let l = emit(&bo.left)?;
            let r = emit(&bo.right)?;
            format!(".binOp {} {} {}", paren(&kind), paren(&l), paren(&r))
        }
        Expr::And(sp) => format!(".andOf {}", paren(&emit(&sp.expr().input)?)),
        Expr::Or(sp) => format!(".orOf {}", paren(&emit(&sp.expr().input)?)),
        Expr::LogicalNot(sp) => format!(".logicalNot {}", paren(&emit(&sp.expr().input)?)),
        Expr::If(v) => format!(
            ".ifExpr {} {} {}",
            paren(&emit(&v.condition)?),
            paren(&emit(&v.true_branch)?),
            paren(&emit(&v.false_branch)?)
        ),
        Expr::ExtractScriptBytes(v) => format!(".extractScriptBytes {}", paren(&emit(&v.input)?)),
        Expr::ExtractAmount(v) => format!(".extractAmount {}", paren(&emit(&v.input)?)),
        Expr::ExtractId(v) => format!(".extractId {}", paren(&emit(&v.input)?)),
        Expr::ExtractRegisterAs(sp) => {
            let er = sp.expr();
            let input = emit(&er.input)?;
            let elem = stype_to_lean(&er.elem_tpe)?;
            format!(
                ".extractRegisterAs {} {} {}",
                paren(&input),
                fmt_int(er.register_id as i64),
                paren(&elem)
            )
        }
        Expr::OptionGet(sp) => format!(".optionGet {}", paren(&emit(&sp.expr().input)?)),
        Expr::OptionIsDefined(sp) => format!(".optionIsDefined {}", paren(&emit(&sp.expr().input)?)),
        Expr::OptionGetOrElse(sp) => {
            let og = sp.expr();
            format!(
                ".optionGetOrElse {} {}",
                paren(&emit(&og.input)?),
                paren(&emit(&og.default)?)
            )
        }
        Expr::GetVar(sp) => {
            let gv = sp.expr();
            // `GetVar::tpe()` is `SOption(var_tpe)`; we want the inner `var_tpe`.
            let var_tpe = match &gv.tpe() {
                SType::SOption(t) => stype_to_lean(t)?,
                other => bail!("emit GetVar: expected SOption var_tpe wrapper, got {other:?}"),
            };
            format!(".getVar {} {}", gv.var_id, paren(&var_tpe))
        }
        Expr::Collection(c) => match c {
            Collection::BoolConstants(bools) => {
                let items: Vec<String> = bools
                    .iter()
                    .map(|b| format!(".const (Value.vBool {})", if *b { "true" } else { "false" }))
                    .collect();
                format!(".collection SType.sBoolean [{}]", items.join(", "))
            }
            Collection::Exprs { elem_tpe, items } => {
                format!(
                    ".collection {} {}",
                    paren(&stype_to_lean(elem_tpe)?),
                    list_of(items)?
                )
            }
        },
        Expr::Tuple(t) => format!(".tuple {}", list_of(t.items.as_slice())?),
        Expr::SelectField(sp) => {
            let sf = sp.expr();
            format!(
                ".selectField {} {}",
                paren(&emit(&sf.input)?),
                sf.field_index
            )
        }
        Expr::SizeOf(v) => format!(".sizeOf {}", paren(&emit(&v.input)?)),
        Expr::Slice(sp) => {
            let sl = sp.expr();
            format!(
                ".sliceOf {} {} {}",
                paren(&emit(&sl.input)?),
                paren(&emit(&sl.from)?),
                paren(&emit(&sl.until)?)
            )
        }
        Expr::Filter(sp) => {
            let f = sp.expr();
            format!(
                ".filterOf {} {} {}",
                paren(&emit(&f.input)?),
                paren(&emit(&f.condition)?),
                paren(&stype_to_lean(&f.elem_tpe)?)
            )
        }
        Expr::Exists(sp) => {
            let f = sp.expr();
            format!(
                ".existsOf {} {} {}",
                paren(&emit(&f.input)?),
                paren(&emit(&f.condition)?),
                paren(&stype_to_lean(&f.elem_tpe)?)
            )
        }
        Expr::ForAll(sp) => {
            let f = sp.expr();
            format!(
                ".forAllOf {} {} {}",
                paren(&emit(&f.input)?),
                paren(&emit(&f.condition)?),
                paren(&stype_to_lean(&f.elem_tpe)?)
            )
        }
        Expr::Fold(sp) => {
            let f = sp.expr();
            format!(
                ".foldOf {} {} {}",
                paren(&emit(&f.input)?),
                paren(&emit(&f.zero)?),
                paren(&emit(&f.fold_op)?)
            )
        }
        Expr::Append(sp) => {
            let a = sp.expr();
            format!(".appendOf {} {}", paren(&emit(&a.input)?), paren(&emit(&a.col_2)?))
        }
        Expr::FuncValue(f) => {
            let args: Vec<String> = f
                .args()
                .iter()
                .map(|a| Ok(format!("({}, {})", a.idx.0, paren(&stype_to_lean(&a.tpe)?))))
                .collect::<Result<Vec<_>>>()?;
            let body = emit(f.body())?;
            format!(".funcValue [{}] {}", args.join(", "), paren(&body))
        }
        Expr::Apply(a) => {
            let func = emit(&a.func)?;
            format!(".apply {} {}", paren(&func), list_of(&a.args)?)
        }
        Expr::MethodCall(sp) => {
            let mc = sp.expr();
            let obj = emit(&mc.obj)?;
            format!(
                ".methodCall {} {} {} {} /- {}.{} -/",
                paren(&obj),
                mc.method.obj_type.type_code() as u8,
                mc.method.method_id().0,
                list_of(&mc.args)?,
                mc.method.obj_type.type_name(),
                mc.method.name()
            )
        }
        Expr::PropertyCall(sp) => {
            let pc = sp.expr();
            let obj = emit(&pc.obj)?;
            format!(
                ".propertyCall {} {} {} /- {}.{} -/",
                paren(&obj),
                pc.method.obj_type.type_code() as u8,
                pc.method.method_id().0,
                pc.method.obj_type.type_name(),
                pc.method.name()
            )
        }
        Expr::Upcast(v) => format!(
            ".upcast {} {}",
            paren(&emit(&v.input)?),
            paren(&stype_to_lean(&v.tpe())?)
        ),
        Expr::Downcast(v) => format!(
            ".downcast {} {}",
            paren(&emit(&v.input)?),
            paren(&stype_to_lean(&v.tpe())?)
        ),
        Expr::Negation(sp) => format!(".negation {}", paren(&emit(&sp.expr().input)?)),
        Expr::ByteArrayToBigInt(sp) => {
            format!(".byteArrayToBigInt {}", paren(&emit(&sp.expr().input)?))
        }
        Expr::ByteArrayToLong(sp) => format!(".byteArrayToLong {}", paren(&emit(&sp.expr().input)?)),
        other => bail!(
            "emit: unsupported MIR node kind {} — the exporter fails loudly rather than \
             emitting an approximation; extend `emit.rs`/`Syntax.lean` if this node is \
             legitimately needed",
            expr_kind_name(other)
        ),
    })
}

/// Human-readable MIR node kind name, for error messages on unsupported
/// nodes (not used on the happy path).
fn expr_kind_name(e: &Expr) -> &'static str {
    match e {
        Expr::Append(_) => "Append",
        Expr::Const(_) => "Const",
        Expr::ConstPlaceholder(_) => "ConstPlaceholder",
        Expr::SubstConstants(_) => "SubstConstants",
        Expr::ByteArrayToLong(_) => "ByteArrayToLong",
        Expr::ByteArrayToBigInt(_) => "ByteArrayToBigInt",
        Expr::LongToByteArray(_) => "LongToByteArray",
        Expr::Collection(_) => "Collection",
        Expr::Tuple(_) => "Tuple",
        Expr::CalcBlake2b256(_) => "CalcBlake2b256",
        Expr::CalcSha256(_) => "CalcSha256",
        Expr::Context => "Context",
        Expr::Global => "Global",
        Expr::GlobalVars(_) => "GlobalVars",
        Expr::FuncValue(_) => "FuncValue",
        Expr::Apply(_) => "Apply",
        Expr::MethodCall(_) => "MethodCall",
        Expr::PropertyCall(_) => "PropertyCall",
        Expr::BlockValue(_) => "BlockValue",
        Expr::ValDef(_) => "ValDef",
        Expr::ValUse(_) => "ValUse",
        Expr::If(_) => "If",
        Expr::BinOp(_) => "BinOp",
        Expr::And(_) => "And",
        Expr::Or(_) => "Or",
        Expr::Xor(_) => "Xor",
        Expr::Atleast(_) => "Atleast",
        Expr::LogicalNot(_) => "LogicalNot",
        Expr::Negation(_) => "Negation",
        Expr::BitInversion(_) => "BitInversion",
        Expr::OptionGet(_) => "OptionGet",
        Expr::OptionIsDefined(_) => "OptionIsDefined",
        Expr::OptionGetOrElse(_) => "OptionGetOrElse",
        Expr::ExtractAmount(_) => "ExtractAmount",
        Expr::ExtractRegisterAs(_) => "ExtractRegisterAs",
        Expr::ExtractBytes(_) => "ExtractBytes",
        Expr::ExtractBytesWithNoRef(_) => "ExtractBytesWithNoRef",
        Expr::ExtractScriptBytes(_) => "ExtractScriptBytes",
        Expr::ExtractCreationInfo(_) => "ExtractCreationInfo",
        Expr::ExtractId(_) => "ExtractId",
        Expr::ByIndex(_) => "ByIndex",
        Expr::SizeOf(_) => "SizeOf",
        Expr::Slice(_) => "Slice",
        Expr::Fold(_) => "Fold",
        Expr::Map(_) => "Map",
        Expr::Filter(_) => "Filter",
        Expr::Exists(_) => "Exists",
        Expr::ForAll(_) => "ForAll",
        Expr::SelectField(_) => "SelectField",
        Expr::BoolToSigmaProp(_) => "BoolToSigmaProp",
        Expr::Upcast(_) => "Upcast",
        Expr::Downcast(_) => "Downcast",
        Expr::CreateProveDlog(_) => "CreateProveDlog",
        Expr::CreateProveDhTuple(_) => "CreateProveDhTuple",
        Expr::SigmaPropBytes(_) => "SigmaPropBytes",
        Expr::DecodePoint(_) => "DecodePoint",
        Expr::SigmaAnd(_) => "SigmaAnd",
        Expr::SigmaOr(_) => "SigmaOr",
        Expr::GetVar(_) => "GetVar",
        Expr::DeserializeRegister(_) => "DeserializeRegister",
        Expr::DeserializeContext(_) => "DeserializeContext",
        Expr::MultiplyGroup(_) => "MultiplyGroup",
        Expr::Exponentiate(_) => "Exponentiate",
        Expr::XorOf(_) => "XorOf",
        Expr::TreeLookup(_) => "TreeLookup",
        Expr::CreateAvlTree(_) => "CreateAvlTree",
    }
}

/// Entry point used by `main.rs`; `indent` is currently unused (output is
/// not pretty-printed with indentation, just fully parenthesized), kept in
/// the signature in case that changes.
pub fn emit_expr(e: &Expr, _indent: usize, out: &mut String) -> Result<()> {
    out.push_str(&emit(e)?);
    Ok(())
}
