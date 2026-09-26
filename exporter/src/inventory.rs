//! `--inventory`: walk an `Expr` tree and collect the sorted set of
//! distinct MIR node kinds it contains (plus, for `MethodCall`/
//! `PropertyCall`, the `type_id.method_id` + method name). This match is
//! exhaustive over every `Expr` variant in `ergotree-ir 0.28` (not just
//! the ones `emit.rs` supports), so the inventory is trustworthy even for
//! node kinds the emitter would reject.

use std::collections::BTreeSet;

use ergotree_ir::mir::expr::Expr;

pub fn collect(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Append(sp) => {
            out.insert("Append".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().col_2, out);
        }
        Expr::Const(_) => {
            out.insert("Const".into());
        }
        Expr::ConstPlaceholder(_) => {
            out.insert("ConstPlaceholder".into());
        }
        Expr::SubstConstants(sp) => {
            out.insert("SubstConstants".into());
            collect(&sp.expr().script_bytes, out);
            collect(&sp.expr().positions, out);
            collect(&sp.expr().new_values, out);
        }
        Expr::ByteArrayToLong(sp) => {
            out.insert("ByteArrayToLong".into());
            collect(&sp.expr().input, out);
        }
        Expr::ByteArrayToBigInt(sp) => {
            out.insert("ByteArrayToBigInt".into());
            collect(&sp.expr().input, out);
        }
        Expr::LongToByteArray(v) => {
            out.insert("LongToByteArray".into());
            collect(&v.input, out);
        }
        Expr::Collection(c) => {
            out.insert("Collection".into());
            if let ergotree_ir::mir::collection::Collection::Exprs { items, .. } = c {
                for it in items {
                    collect(it, out);
                }
            }
        }
        Expr::Tuple(t) => {
            out.insert("Tuple".into());
            for it in t.items.iter() {
                collect(it, out);
            }
        }
        Expr::CalcBlake2b256(v) => {
            out.insert("CalcBlake2b256".into());
            collect(&v.input, out);
        }
        Expr::CalcSha256(v) => {
            out.insert("CalcSha256".into());
            collect(&v.input, out);
        }
        Expr::Context => {
            out.insert("Context".into());
        }
        Expr::Global => {
            out.insert("Global".into());
        }
        Expr::GlobalVars(gv) => {
            out.insert(format!("GlobalVars::{gv:?}"));
        }
        Expr::FuncValue(f) => {
            out.insert("FuncValue".into());
            collect(f.body(), out);
        }
        Expr::Apply(a) => {
            out.insert("Apply".into());
            collect(&a.func, out);
            for arg in &a.args {
                collect(arg, out);
            }
        }
        Expr::MethodCall(sp) => {
            let mc = sp.expr();
            out.insert(format!(
                "MethodCall({}.{} {})",
                mc.method.obj_type.type_code() as u8,
                mc.method.method_id().0,
                mc.method.name()
            ));
            collect(&mc.obj, out);
            for arg in &mc.args {
                collect(arg, out);
            }
        }
        Expr::PropertyCall(sp) => {
            let pc = sp.expr();
            out.insert(format!(
                "PropertyCall({}.{} {})",
                pc.method.obj_type.type_code() as u8,
                pc.method.method_id().0,
                pc.method.name()
            ));
            collect(&pc.obj, out);
        }
        Expr::BlockValue(sp) => {
            out.insert("BlockValue".into());
            for it in &sp.expr().items {
                collect(it, out);
            }
            collect(&sp.expr().result, out);
        }
        Expr::ValDef(sp) => {
            out.insert("ValDef".into());
            collect(&sp.expr().rhs, out);
        }
        Expr::ValUse(_) => {
            out.insert("ValUse".into());
        }
        Expr::If(v) => {
            out.insert("If".into());
            collect(&v.condition, out);
            collect(&v.true_branch, out);
            collect(&v.false_branch, out);
        }
        Expr::BinOp(sp) => {
            out.insert(format!("BinOp({:?})", sp.expr().kind));
            collect(&sp.expr().left, out);
            collect(&sp.expr().right, out);
        }
        Expr::And(sp) => {
            out.insert("And".into());
            collect(&sp.expr().input, out);
        }
        Expr::Or(sp) => {
            out.insert("Or".into());
            collect(&sp.expr().input, out);
        }
        Expr::Xor(x) => {
            out.insert("Xor".into());
            collect(&x.left, out);
            collect(&x.right, out);
        }
        Expr::Atleast(a) => {
            out.insert("Atleast".into());
            collect(&a.bound, out);
            collect(&a.input, out);
        }
        Expr::LogicalNot(sp) => {
            out.insert("LogicalNot".into());
            collect(&sp.expr().input, out);
        }
        Expr::Negation(sp) => {
            out.insert("Negation".into());
            collect(&sp.expr().input, out);
        }
        Expr::BitInversion(v) => {
            out.insert("BitInversion".into());
            collect(&v.input, out);
        }
        Expr::OptionGet(sp) => {
            out.insert("OptionGet".into());
            collect(&sp.expr().input, out);
        }
        Expr::OptionIsDefined(sp) => {
            out.insert("OptionIsDefined".into());
            collect(&sp.expr().input, out);
        }
        Expr::OptionGetOrElse(sp) => {
            out.insert("OptionGetOrElse".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().default, out);
        }
        Expr::ExtractAmount(v) => {
            out.insert("ExtractAmount".into());
            collect(&v.input, out);
        }
        Expr::ExtractRegisterAs(sp) => {
            out.insert("ExtractRegisterAs".into());
            collect(&sp.expr().input, out);
        }
        Expr::ExtractBytes(v) => {
            out.insert("ExtractBytes".into());
            collect(&v.input, out);
        }
        Expr::ExtractBytesWithNoRef(v) => {
            out.insert("ExtractBytesWithNoRef".into());
            collect(&v.input, out);
        }
        Expr::ExtractScriptBytes(v) => {
            out.insert("ExtractScriptBytes".into());
            collect(&v.input, out);
        }
        Expr::ExtractCreationInfo(v) => {
            out.insert("ExtractCreationInfo".into());
            collect(&v.input, out);
        }
        Expr::ExtractId(v) => {
            out.insert("ExtractId".into());
            collect(&v.input, out);
        }
        Expr::ByIndex(sp) => {
            out.insert("ByIndex".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().index, out);
            if let Some(d) = &sp.expr().default {
                collect(d, out);
            }
        }
        Expr::SizeOf(v) => {
            out.insert("SizeOf".into());
            collect(&v.input, out);
        }
        Expr::Slice(sp) => {
            out.insert("Slice".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().from, out);
            collect(&sp.expr().until, out);
        }
        Expr::Fold(sp) => {
            out.insert("Fold".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().zero, out);
            collect(&sp.expr().fold_op, out);
        }
        Expr::Map(sp) => {
            out.insert("Map".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().mapper, out);
        }
        Expr::Filter(sp) => {
            out.insert("Filter".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().condition, out);
        }
        Expr::Exists(sp) => {
            out.insert("Exists".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().condition, out);
        }
        Expr::ForAll(sp) => {
            out.insert("ForAll".into());
            collect(&sp.expr().input, out);
            collect(&sp.expr().condition, out);
        }
        Expr::SelectField(sp) => {
            out.insert("SelectField".into());
            collect(&sp.expr().input, out);
        }
        Expr::BoolToSigmaProp(v) => {
            out.insert("BoolToSigmaProp".into());
            collect(&v.input, out);
        }
        Expr::Upcast(v) => {
            out.insert("Upcast".into());
            collect(&v.input, out);
        }
        Expr::Downcast(v) => {
            out.insert("Downcast".into());
            collect(&v.input, out);
        }
        Expr::CreateProveDlog(v) => {
            out.insert("CreateProveDlog".into());
            collect(&v.input, out);
        }
        Expr::CreateProveDhTuple(v) => {
            out.insert("CreateProveDhTuple".into());
            collect(&v.g, out);
            collect(&v.h, out);
            collect(&v.u, out);
            collect(&v.v, out);
        }
        Expr::SigmaPropBytes(v) => {
            out.insert("SigmaPropBytes".into());
            collect(&v.input, out);
        }
        Expr::DecodePoint(v) => {
            out.insert("DecodePoint".into());
            collect(&v.input, out);
        }
        Expr::SigmaAnd(sa) => {
            out.insert("SigmaAnd".into());
            for it in sa.items.iter() {
                collect(it, out);
            }
        }
        Expr::SigmaOr(so) => {
            out.insert("SigmaOr".into());
            for it in so.items.iter() {
                collect(it, out);
            }
        }
        Expr::GetVar(sp) => {
            out.insert(format!("GetVar(var_id={})", sp.expr().var_id));
        }
        Expr::DeserializeRegister(v) => {
            out.insert("DeserializeRegister".into());
            if let Some(d) = &v.default {
                collect(d, out);
            }
        }
        Expr::DeserializeContext(_) => {
            out.insert("DeserializeContext".into());
        }
        Expr::MultiplyGroup(v) => {
            out.insert("MultiplyGroup".into());
            collect(&v.left, out);
            collect(&v.right, out);
        }
        Expr::Exponentiate(v) => {
            out.insert("Exponentiate".into());
            collect(&v.left, out);
            collect(&v.right, out);
        }
        Expr::XorOf(v) => {
            out.insert("XorOf".into());
            collect(&v.input, out);
        }
        Expr::TreeLookup(sp) => {
            out.insert("TreeLookup".into());
            collect(&sp.expr().tree, out);
            collect(&sp.expr().key, out);
            collect(&sp.expr().proof, out);
        }
        Expr::CreateAvlTree(v) => {
            out.insert("CreateAvlTree".into());
            collect(&v.flags, out);
            collect(&v.digest, out);
            collect(&v.key_length, out);
            if let Some(vl) = &v.value_length {
                collect(vl, out);
            }
        }
    }
}
