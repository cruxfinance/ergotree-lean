//! EIP-5 ("Contract Template") JSON shape, as produced by the Scala
//! ErgoScript compiler and consumed by downstream tooling that compiles
//! contracts (e.g. a `compiled/*.json` artifact from such a build).

use serde::Deserialize;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Eip5Template {
    /// Hex-encoded, serialized `SType` byte string per template constant,
    /// in `constantIndex` order.
    pub const_types: Vec<String>,
    /// Hex-encoded, serialized `Expr` bytes (with `ConstantPlaceholder`
    /// nodes standing in for the template constants).
    pub expression_tree: String,
}
