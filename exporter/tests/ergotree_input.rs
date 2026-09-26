//! Integration tests for the `--ergotree` full-ErgoTree input mode
//! (`main.rs`'s `parse_full_ergotree`), run as black-box CLI tests against
//! the built `exporter` binary (`env!("CARGO_BIN_EXE_exporter")`) rather
//! than against internal functions, since this crate only ships a `[[bin]]`
//! target.
//!
//! Covers:
//! - a hand-built, constant-segregated ErgoTree (header + real constants +
//!   `contracts/sell-order-eip5.json`'s own template bytes) exported via
//!   `--ergotree` emits the same `Expr` text as the EIP-5 route exports for
//!   that same template, and its `<name>Consts` list decodes back to the
//!   constant values used to build it;
//! - a non-segregated ErgoTree (no constants segment, no placeholders)
//!   exports its single inlined node and an empty `Consts` list;
//! - `--ergotree` together with `--hex` is rejected at the CLI level;
//! - two real trees pulled from the node's mempool: a bare `sigmaProp(true)`
//!   root (no constants segment) exports end to end, and a `HEIGHT >=
//!   SELF.creationInfo._1 + 720 && PK(...)` timelock (`--inventory`,
//!   constants — an `Int` and a `SigmaProp`/`ProveDlog`) is covered —
//!   see `real_mempool_trees` below, including its full export, now that
//!   `ExtractCreationInfo` support has landed.

use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::Arc;

use ergotree_ir::mir::constant::{Constant, Literal};
use ergotree_ir::mir::constant::ConstantPlaceholder;
use ergotree_ir::mir::expr::Expr;
use ergotree_ir::mir::value::{CollKind, NativeColl};
use ergotree_ir::serialization::SigmaSerializable;
use ergotree_ir::types::stype::SType;
use sigma_ser::ScorexSerializable;

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_exporter"))
        .args(args)
        .current_dir(manifest_dir())
        .output()
        .expect("failed to run exporter binary")
}

/// Run the exporter and return stdout, panicking with stderr on a
/// non-zero exit (for a readable test failure).
fn run_ok(args: &[&str]) -> String {
    let out = run(args);
    assert!(
        out.status.success(),
        "exporter exited non-zero for {args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("exporter stdout was not UTF-8")
}

/// Extract the single-line body following `def <name> : Expr :=` — neither
/// `emit::emit` nor `emit::consts_to_lean` ever insert internal newlines,
/// so the body is always the very next line.
fn extract_expr_body(output: &str, name: &str) -> String {
    let marker = format!("def {name} : Expr :=");
    let lines: Vec<&str> = output.lines().collect();
    let idx = lines
        .iter()
        .position(|l| *l == marker)
        .unwrap_or_else(|| panic!("marker {marker:?} not found in output:\n{output}"));
    lines
        .get(idx + 1)
        .unwrap_or_else(|| panic!("no line after {marker:?} in output:\n{output}"))
        .trim()
        .to_string()
}

/// Extract the `[...]` list literal from `def <name>Consts : List Value := [...]`.
fn extract_consts_list(output: &str, name: &str) -> String {
    let marker = format!("def {name}Consts : List Value := ");
    output
        .lines()
        .find_map(|l| l.strip_prefix(marker.as_str()))
        .unwrap_or_else(|| panic!("marker {marker:?} not found in output:\n{output}"))
        .trim()
        .to_string()
}

fn sell_order_template_bytes() -> Vec<u8> {
    let json_path = manifest_dir().join("../contracts/sell-order-eip5.json");
    let text = std::fs::read_to_string(&json_path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", json_path.display()));
    let json: serde_json::Value = serde_json::from_str(&text).expect("parsing sell-order-eip5.json");
    let hex_str = json["expressionTree"]
        .as_str()
        .expect("sell-order-eip5.json missing expressionTree");
    hex::decode(hex_str).expect("decoding expressionTree hex")
}

/// Concrete constants matching `sell-order-eip5.json`'s `constTypes`
/// (`["07", "0e", "05"]` = `GroupElement`, `Coll[Byte]`, `Long`), in
/// `constantIndex` order.
fn sell_order_constants() -> Vec<Constant> {
    let pk = ergo_chain_types::ec_point::generator();
    let prop_bytes: Vec<i8> = vec![1, 2, 3, 4, 5, 6, 7, 8];
    vec![
        Constant {
            tpe: SType::SGroupElement,
            v: Literal::GroupElement(Arc::new(pk)),
        },
        Constant {
            tpe: SType::SColl(Arc::new(SType::SByte)),
            v: Literal::Coll(CollKind::NativeColl(NativeColl::CollByte(Arc::from(
                prop_bytes.as_slice(),
            )))),
        },
        Constant {
            tpe: SType::SLong,
            v: Literal::Long(123_456_789i64),
        },
    ]
}

/// Hand-assemble a constant-segregated ErgoTree: header byte (v0,
/// constant-segregation flag set, no size flag) + the constants segment
/// (`Vec<Constant>`'s own `SigmaSerializable` impl already writes the VLQ
/// length prefix) + the template's expression bytes.
fn build_segregated_ergotree(constants: &[Constant], template: &[u8]) -> Vec<u8> {
    let mut bytes = vec![0x10u8];
    bytes.extend(
        constants
            .to_vec()
            .sigma_serialize_bytes()
            .expect("serializing constants segment"),
    );
    bytes.extend_from_slice(template);
    bytes
}

#[test]
fn ergotree_route_matches_eip5_route_for_sell_order() {
    let constants = sell_order_constants();
    let template = sell_order_template_bytes();
    let tree_bytes = build_segregated_ergotree(&constants, &template);
    let tree_hex = hex::encode(&tree_bytes);

    let eip5_out = run_ok(&[
        "../contracts/sell-order-eip5.json",
        "--lean-name",
        "eip5Tree",
        "--namespace",
        "Test",
    ]);
    let ergotree_out = run_ok(&[
        "--ergotree",
        &tree_hex,
        "--lean-name",
        "ergoTreeTree",
        "--namespace",
        "Test",
    ]);

    let eip5_body = extract_expr_body(&eip5_out, "eip5Tree");
    let ergotree_body = extract_expr_body(&ergotree_out, "ergoTreeTree");
    assert_eq!(
        eip5_body, ergotree_body,
        "emitted Expr differs between the EIP-5 and --ergotree routes for the same template"
    );

    // The header must record the source hex and be regeneratable.
    assert!(ergotree_out.contains(&tree_hex), "header should record the source ErgoTree hex");
    assert!(
        ergotree_out.contains("--ergotree"),
        "header's regenerate command should mention --ergotree"
    );

    // The emitted constants list decodes the exact values used to build
    // the tree.
    let consts_list = extract_consts_list(&ergotree_out, "ergoTreeTree");

    let pk_bytes = ergo_chain_types::ec_point::generator()
        .scorex_serialize_bytes()
        .expect("serializing generator point");
    let expected_pk = format!(
        "(Value.vGroupElement [{}])",
        pk_bytes.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(", ")
    );
    assert!(
        consts_list.contains(&expected_pk),
        "consts list missing expected GroupElement value: {consts_list}"
    );

    let expected_prop = "(Value.vColl SType.sByte [(Value.vByte 1), (Value.vByte 2), \
                          (Value.vByte 3), (Value.vByte 4), (Value.vByte 5), (Value.vByte 6), \
                          (Value.vByte 7), (Value.vByte 8)])";
    assert!(
        consts_list.contains(expected_prop),
        "consts list missing expected Coll[Byte] value: {consts_list}"
    );

    assert!(
        consts_list.contains("(Value.vLong 123456789)"),
        "consts list missing expected Long value: {consts_list}"
    );
}

#[test]
fn ergotree_route_works_with_inventory() {
    let constants = sell_order_constants();
    let template = sell_order_template_bytes();
    let tree_bytes = build_segregated_ergotree(&constants, &template);
    let tree_hex = hex::encode(&tree_bytes);

    let out = run_ok(&["--ergotree", &tree_hex, "--inventory"]);
    let kinds: Vec<&str> = out.lines().collect();
    assert!(kinds.contains(&"BlockValue"), "inventory output: {out:?}");
    assert!(kinds.contains(&"ConstPlaceholder"), "inventory output: {out:?}");
}

#[test]
fn ergotree_route_reads_hex_from_file() {
    let constants = sell_order_constants();
    let template = sell_order_template_bytes();
    let tree_bytes = build_segregated_ergotree(&constants, &template);
    let tree_hex = hex::encode(&tree_bytes);

    let tmp = std::env::temp_dir().join(format!("ergotree-input-test-{}.hex", std::process::id()));
    std::fs::write(&tmp, format!("  {tree_hex}\n")).expect("writing temp hex file");
    let at_arg = format!("@{}", tmp.display());

    let out = run_ok(&["--ergotree", &at_arg, "--lean-name", "fileTree", "--namespace", "Test"]);
    let _ = std::fs::remove_file(&tmp);

    let body = extract_expr_body(&out, "fileTree");
    assert!(!body.is_empty());
}

#[test]
fn ergotree_route_handles_non_segregated_tree() {
    // No constants segment, no placeholders: header byte 0x00 (v0, no
    // segregation, no size), followed directly by a single inlined
    // `Expr::Const` node.
    let expr = Expr::Const(Constant {
        tpe: SType::SBoolean,
        v: Literal::Boolean(true),
    });
    let template = expr.sigma_serialize_bytes().expect("serializing inline Const expr");
    let mut tree_bytes = vec![0x00u8];
    tree_bytes.extend_from_slice(&template);
    let tree_hex = hex::encode(&tree_bytes);

    let out = run_ok(&["--ergotree", &tree_hex, "--lean-name", "nonSegTree", "--namespace", "Test"]);

    let body = extract_expr_body(&out, "nonSegTree");
    assert_eq!(body, ".const (Value.vBool true)");

    let consts_list = extract_consts_list(&out, "nonSegTree");
    assert_eq!(consts_list, "[]");
}

#[test]
fn ergotree_conflicts_with_hex() {
    let out = run(&["--ergotree", "00", "--hex", "00", "--const-types", "05"]);
    assert!(!out.status.success(), "expected a CLI error, got: {out:?}");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("cannot be used with") || stderr.contains("conflict"),
        "expected a clap conflict error, got: {stderr}"
    );
}

#[test]
fn ergotree_rejects_unsupported_header_version() {
    // Version bits (mask 0x07) > 1 are invalid per `ErgoTreeVersion::parse_version`.
    let out = run(&["--ergotree", "07"]);
    assert!(!out.status.success(), "expected a parse error for an invalid header version");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("unsupported or malformed ErgoTree"),
        "expected a clear header error, got: {stderr}"
    );
}

/// Two real trees, pulled from the node's mempool, that exercise
/// `--ergotree` against non-synthetic input.
mod real_mempool_trees {
    use super::*;

    /// `sigmaProp(true)` at the root: header `00` (v0, no constant
    /// segregation, no size), then `08d3` — a single inlined `Expr::Const`
    /// of type `SigmaProp` (type code `08`), value `TrivialProp(true)`.
    /// Exercises the `Literal::SigmaProp` case added to `literal_to_lean`
    /// via an inline `Expr::Const`, not just via `consts_to_lean`.
    const BARE_SIGMA_PROP_TRUE: &str = "0008d3";

    /// `sigmaProp(HEIGHT >= SELF.creationInfo._1 + 720) && PK("...")` — a
    /// 720-block (~1 day) timelock guarded by a signature, decoded via
    /// `ErgoTree::get_constants()`/`.proposition()`: constant 0 is
    /// `Int(720)`, constant 1 is
    /// `SigmaProp(ProofOfKnowledge(ProveDlog(h = EC:020e814a...fd274)))`.
    const TIMELOCK_WITH_PK: &str = "100204a00b08cd020e814ace36202c238f6e2ce66d69a1036cb3a6a3318afcecd5af64a5b66fd274ea02d192a39a8cc7a70173007301";

    /// The `ProveDlog` constant's public key, as its `scorex_serialize_bytes`
    /// hex — matches `020e814ace36202c238f6e2ce66d69a1036cb3a6a3318afcecd5af64a5b66fd274`
    /// verbatim (33-byte compressed point).
    const TIMELOCK_PK_HEX: &str =
        "020e814ace36202c238f6e2ce66d69a1036cb3a6a3318afcecd5af64a5b66fd274";

    #[test]
    fn bare_sigma_prop_true_exports_end_to_end() {
        let out = run_ok(&[
            "--ergotree",
            BARE_SIGMA_PROP_TRUE,
            "--lean-name",
            "mempoolBareSigmaProp",
            "--namespace",
            "Test",
        ]);
        let body = extract_expr_body(&out, "mempoolBareSigmaProp");
        assert_eq!(body, ".const (Value.vSigmaProp (SigmaBoolean.trivial true))");
        let consts = extract_consts_list(&out, "mempoolBareSigmaProp");
        assert_eq!(consts, "[]", "a non-segregated tree has no constants");
    }

    #[test]
    fn timelock_inventory_succeeds_without_touching_constants() {
        // `--inventory` must not depend on constant emission (it walks the
        // MIR exhaustively via `inventory::collect`, which never calls
        // `literal_to_lean`/`consts_to_lean`) — this tree's constant 1 is a
        // `SigmaProp`, which used to make `--inventory` fail before that
        // emission was deferred past the inventory early-return in `main.rs`.
        let out = run_ok(&["--ergotree", TIMELOCK_WITH_PK, "--inventory"]);
        let kinds: Vec<&str> = out.lines().collect();
        for expected in [
            "ConstPlaceholder",
            "ExtractCreationInfo",
            "SelectField",
            "SigmaAnd",
            "BoolToSigmaProp",
            "GlobalVars::Height",
            "GlobalVars::SelfBox",
        ] {
            assert!(kinds.contains(&expected), "missing {expected:?} in inventory: {kinds:?}");
        }
    }

    #[test]
    fn timelock_full_export_succeeds() {
        // The timelock's expression uses `SELF.creationInfo._1`
        // (`Expr::ExtractCreationInfo`); now that `Syntax.lean`/`Eval.lean`/
        // `emit.rs` all support it, this tree fully exports — flipped from
        // this test's old shape (`timelock_full_export_fails_on_extract_creation_info_not_constants`),
        // which asserted the pre-existing gap.
        let out = run_ok(&[
            "--ergotree",
            TIMELOCK_WITH_PK,
            "--lean-name",
            "mempoolTimelock",
            "--namespace",
            "Test",
        ]);
        let body = extract_expr_body(&out, "mempoolTimelock");
        assert_eq!(
            body,
            ".sigmaAnd [.boolToSigmaProp (.binOp (BinOpKind.relation RelationOp.ge) .height \
             (.binOp (BinOpKind.arith ArithOp.plus) (.selectField (.extractCreationInfo .selfBox) 1) \
             (.constPlaceholder 0 SType.sInt))), .constPlaceholder 1 SType.sSigmaProp]"
        );

        let consts = extract_consts_list(&out, "mempoolTimelock");
        assert!(consts.starts_with("[(Value.vInt 720)"), "expected constant 0 to be Int(720): {consts}");
        assert!(
            consts.contains("(Value.vSigmaProp (SigmaBoolean.proveDlog"),
            "expected constant 1 to be a Value.vSigmaProp/proveDlog: {consts}"
        );
    }

    #[test]
    fn timelock_provedlog_constant_value() {
        // Isolates the timelock's real constants segment from its
        // unsupported expression: re-attach the exact same two constants
        // (`Int(720)` and the `SigmaProp`/`ProveDlog` pk) — read back off
        // the real mempool tree via `ErgoTree::get_constants()` — to a
        // trivially-supported template (`ConstantPlaceholder(1,
        // SSigmaProp)`), so `--ergotree` exports successfully and we can
        // check `consts_to_lean`'s output against the real bytes.
        let bytes = hex::decode(TIMELOCK_WITH_PK).unwrap();
        let tree = ergotree_ir::ergo_tree::ErgoTree::sigma_parse_bytes(&bytes)
            .expect("parsing the real timelock tree");
        let constants = tree.get_constants().expect("reading its constants");
        assert_eq!(constants.len(), 2);
        assert_eq!(constants[0].tpe, SType::SInt, "constant 0 should be the Int(720) timelock delay");
        assert_eq!(constants[1].tpe, SType::SSigmaProp, "constant 1 should be the ProveDlog pk");

        let template = Expr::ConstPlaceholder(ConstantPlaceholder {
            id: 1,
            tpe: SType::SSigmaProp,
        })
        .sigma_serialize_bytes()
        .expect("serializing a bare ConstPlaceholder(1, SSigmaProp) expression");

        let mut rebuilt = vec![0x10u8];
        rebuilt.extend(
            constants
                .sigma_serialize_bytes()
                .expect("serializing the real constants segment"),
        );
        rebuilt.extend_from_slice(&template);
        let rebuilt_hex = hex::encode(&rebuilt);

        let out = run_ok(&[
            "--ergotree",
            &rebuilt_hex,
            "--lean-name",
            "timelockConsts",
            "--namespace",
            "Test",
        ]);
        let consts = extract_consts_list(&out, "timelockConsts");

        let pk_bytes = hex::decode(TIMELOCK_PK_HEX).unwrap();
        let expected_pk = format!(
            "(SigmaBoolean.proveDlog [{}])",
            pk_bytes.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(", ")
        );
        assert!(
            consts.contains(&expected_pk),
            "expected the real ProveDlog pk in the consts list: {consts}"
        );
        assert!(
            consts.contains("(Value.vSigmaProp (SigmaBoolean.proveDlog"),
            "expected constant 1 to be a Value.vSigmaProp: {consts}"
        );
        assert!(consts.starts_with("[(Value.vInt 720)"), "expected constant 0 to be Int(720): {consts}");
    }
}
