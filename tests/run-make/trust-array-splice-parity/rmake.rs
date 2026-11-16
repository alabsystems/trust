//! The crate-module splice carries exactly what it carried before every fixed-size array became
//! a first-class `Ty::Array` in the THIR producer (2026-09-23) — no body lost, none gained.
//!
//! Under the old spelling an array whose element was not a scalar or a struct/enum was a
//! `Ty::Tuple` of N copies of its element, and the splice admitted it through its tuple arms:
//! a struct field `[[u32; 2]; 2]` or `[(u8, u16); 2]`, a promoted `&[(1, 2), (3, 4)]` or
//! `&[[1, 2], [3, 4]]`. Respelled `Ty::Array`, the struct field names a types entry that is itself
//! an array or a tuple of arrays, and the promoted global is `(Ty::Array, Constant::Array)` over
//! a non-scalar element, and a `fn([(u8, u8); 2]) -> u8` pointer's target signature names an
//! array its body's table alone can read. `def_field_ok`'s element bounds, `global_const_ok`'s
//! per-element arm and `fnptr_target_sig_ok`'s cross-table comparison keep all of them spliced.
//! What the old spelling ALREADY made `Ty::Array` — a promoted `&[S; 2]` of structs (wave-NSA),
//! a `fn([[u8; 2]; 2])` pointer (a nested scalar array) — did not splice, and still does not:
//! the respelling widens nothing.
//!
//! Measured on the pre-change compiler (7bc480faf) with these exact flags: 25 bodies, 24
//! lowered (`take` refuses its element read), 22 spliced — `ps` and `reify_n` the two
//! lowered-not-spliced rows.

use run_make_support::{cmd, rfs, rustc_path, serde_json};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return; // Stock rustc has no Trust-IR artifact interface.
    }
    cmd(rustc_path())
        .args([
            "array_splice.rs",
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=array_splice_parity",
            "--emit=mir",
            "-Coverflow-checks=on",
            "-Copt-level=0",
            "-Zthreads=1",
            "-Ztrust-verify=off",
            "-Ztrust-ir-lower=on",
            "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:splice-ir",
            "-o",
            "splice.mir",
        ])
        .run();
    let report: serde_json::Value =
        serde_json::from_slice(&rfs::read("splice-ir/array_splice_parity.coverage.json")).unwrap();
    let rows = report["bodies"].as_array().unwrap();
    let row = |name: &str| {
        let found: Vec<_> = rows.iter().filter(|r| r["def_path"] == name).collect();
        assert_eq!(found.len(), 1, "missing/duplicate body {name}");
        found[0].clone()
    };
    // Every body but `take` lowers, clean (`take`'s `a[0].0` is an element read the producer
    // refuses for a tuple element, before and after).
    for r in rows {
        let lowers = r["def_path"] != "take";
        assert_eq!(r["lowered"], lowers, "{}", r["def_path"]);
        assert_eq!(r["unsupported"].as_array().unwrap().is_empty(), lowers, "{}", r["def_path"]);
    }
    // The shapes the old tuple spelling spliced keep splicing.
    for name in ["get", "qz", "getp", "pt", "pn", "reify", "take_n"] {
        assert_eq!(row(name)["spliced"], true, "{name} must still splice");
    }
    // What the old spelling already made a first-class array did not splice, and must not start.
    for name in ["ps", "reify_n"] {
        assert_eq!(row(name)["spliced"], false, "`{name}` must not newly splice");
    }
    assert_eq!(report["totals"]["spliced"], 22);
    assert_eq!(report["totals"]["lowered"], 24);
    assert_eq!(report["totals"]["bodies"], 25);
}
