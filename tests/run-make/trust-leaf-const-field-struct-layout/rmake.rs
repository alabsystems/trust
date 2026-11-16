//! fix11 (L2): a local struct whose field type names an UNEVALUATED constant gets its layout
//! when that constant's whole CTFE closure is leaf, so a body whose signature names it is no
//! longer refused as "signature reaches a layout-less struct".
//!
//! The #48 layout funnel (`trust_mir_extract::ctfe_reentrancy::every_reached_type`) declined
//! every such struct on the alias flag: `layout_of` evaluates the constant, and CTFE from inside
//! `mir_built` is an E0391 risk. In `core` that withheld the layout of every `NonZero<uN>`
//! (through `niche_types::*Inner`, an open `pattern_type!` range) and of `DecimalSeq`. The funnel
//! now evaluates exactly the constants whose closure builds no body but leaf constants
//! (`ctfe_reentrancy::evaluate_leaf_constants`).
//!
//! Measured on the pre-change compiler (stage 1 of `425f2192be`) with these flags: `nz`,
//! `dseq_len` and `arr` were refused as "signature reaches a layout-less struct". `TypeId`'s
//! `16 / size_of::<*const ()>()` (`type_id_like`) lays out too: `size_of`/`align_of` over a
//! primitive, `()` or a pointer to one is the one call a leaf constant may make. The controls pin
//! the declines that keep the argument: a constant that calls a const fn (`call`), `size_of` over
//! an ADT (`size_of_adt`), and a const fn that names the struct it sizes (`cyc`, whose evaluation
//! from inside its own `mir_built` would be a query cycle) stay unevaluated — the producer
//! declines the array length (`Ty(array non-const len)`), or the funnel the struct — and the
//! crate compiles at all (no E0391) — the compile itself is that check.

use run_make_support::{cmd, rfs, rustc_path, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }
    cmd(rustc_path())
        .args([
            "leaf_const_field.rs",
            "--edition=2021",
            "--crate-type=lib",
            "--crate-name=leaf_const_field",
            "--emit=metadata",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-dump=ir:ir",
        ])
        .env("TRUST_COVERAGE_DETAIL_CAP", "0")
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/leaf_const_field.coverage.json")).unwrap();
    let rows = report["bodies"].as_array().unwrap();
    let row = |name: &str| {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "missing/duplicate body {name}");
        found[0].clone()
    };
    const LAYOUT_LESS: &str = "Splice(signature reaches a layout-less struct)";
    for name in ["nz", "dseq_len", "arr", "type_id_like"] {
        let r = row(name);
        assert_ne!(r["splice_refusal"], LAYOUT_LESS, "{name}: {r}");
        assert_eq!(r["spliced"], true, "{name} must splice: {r}");
    }
    // Each control's array length is never evaluated inside `mir_built`: the producer's
    // normalization declines it (`ctfe_reentrancy::non_leaf_constant_if_frozen`), so the body
    // does not lower — before the splice, where the layout funnel declines the same struct.
    for name in ["call", "size_of_adt", "cyc"] {
        let r = row(name);
        assert_eq!(r["spliced"], false, "{name} must not splice: {r}");
        let declined = r["unsupported"]
            .as_array()
            .is_some_and(|tags| tags.iter().any(|t| t[0] == "Ty(array non-const len)"));
        assert!(
            declined || r["splice_refusal"] == LAYOUT_LESS,
            "{name}: its non-leaf array length must stay unevaluated: {r}"
        );
    }
}
