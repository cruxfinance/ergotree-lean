//! This repo's own `difftest` binary: the standard CLI (`difftest::run_cli`)
//! registered against only the `sell-order` family this repo covers. A
//! downstream package depending on the `difftest` library by path
//! registers its own families the same way, in its own binary — see
//! README.md's "Difftest library usage".

fn main() -> anyhow::Result<()> {
    difftest::run_cli(&[
        ("sell-order", difftest::sell_order::generate),
        ("box-fields", difftest::box_fields::generate),
        ("timelock", difftest::timelock::generate),
        ("sigma-prop-bytes", difftest::sigma_prop_bytes::generate),
        ("coll-indexof", difftest::coll_indexof::generate),
    ])
}
