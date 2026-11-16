//! Imported Clean-origin functions remain named `[clean-below-gate]` on F1.
//!
//! The D40 source metadata importer resolves exported Clean-origin identities without MIR;
//! Rust level-R evidence cannot admit a Clean carrier. This keeps the existing off/advisory
//! own-item and caller census cases, and requires the retired upstream-MIR option to fail at
//! argument parsing. Strict source R imports have a separate producer/consumer fixture.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rust_lib_name, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const UP: &str = r#"#![crate_name = "up"]
pub mod m {
    clean {
        def cleanXor (a : UInt64) (b : UInt64) : UInt64 := a ^^^ b
    }
}
#[inline]
pub fn r_inl(x: u64) -> u64 { m::cleanXor(x, 7) }
"#;

/// A Rust caller of the imported Clean def.
const DOWN: &str = r#"#![crate_name = "down"]
pub fn calls_up(x: u64) -> u64 { up::m::cleanXor(x, 7) }
"#;

/// A Rust caller of an upstream Rust body whose MIR inlines the Clean def.
const DOWN_R: &str = r#"#![crate_name = "down_r"]
pub fn calls_r(x: u64) -> u64 { up::r_inl(x) }
"#;

/// The upstream crate, on the default LLVM lane (the exporting side is not under test).
fn up(opt: &str) -> String {
    let out = format!("up-o{opt}");
    rfs::create_dir_all(&out);
    rustc()
        .input("up.rs")
        .crate_type("rlib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg(format!("-Copt-level={opt}"))
        .arg("-Ztrust-verify=off")
        .out_dir(&out)
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    format!("{out}/{}", rust_lib_name("up"))
}

fn f1(input: &str, rlib: &str, lane: &str, extra: &[&str]) -> String {
    let out = format!("out-{}-{lane}", input.trim_end_matches(".rs"));
    rfs::create_dir_all(&out);
    let output = rustc()
        .input(input)
        .crate_type("rlib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .args(extra)
        .extern_("up", rlib)
        .out_dir(&out)
        // A run-make recipe is a new policy boundary: bootstrap's inherited deauthorization
        // override must not decide this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail();
    let stderr = output.stderr_utf8();
    for forbidden in ["internal compiler error", "panicked at", "thread 'rustc'"] {
        assert!(!stderr.contains(forbidden), "{input} {lane}: an ICE (`{forbidden}`):\n{stderr}");
    }
    stderr
}

/// The census line for `class` with `count` rows (the census prints `count (pct%) [class]`).
fn class_count(stderr: &str, class: &str) -> usize {
    stderr
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            let (count, rest) = line.split_once(' ')?;
            rest.trim_end().ends_with(&format!("[{class}]")).then(|| count.parse::<usize>().ok())?
        })
        .sum()
}

const CLASSES: &[&str] = &[
    "upstream-body",
    "synthesized-instance",
    "generic-instance",
    "unsupported-abi",
    "producer-declined",
    "malformed-producer-module",
    "converter-refused",
    "crate-module-unavailable",
    "ungated-body",
    "unlicensed-body",
    "unlicensed-by-producer",
    "not-a-local-item",
    "instance-assembly",
    "elided-drop",
    "unfaithful-panic",
    "effect-not-conserved",
    "clean-below-gate",
];

/// The `[clean-below-gate]` options the census prints once for the class.
const OPTIONS_ONCE: &[&str] = &[
    "No F1 lane admits a Clean-origin Function yet, whatever its tier",
    "Options: (1) build this crate on the MIR lane",
    "owner ruling D38",
    "(3) keep the Clean call outside this trust-ir-frontend unit",
];

fn census(what: &str, stderr: &str, header: &str, rows: &[(&str, usize)], needles: &[&str]) {
    assert!(stderr.contains(header), "{what}: missing `{header}` in:\n{stderr}");
    for class in CLASSES {
        let want = rows.iter().find(|(c, _)| c == class).map_or(0, |(_, n)| *n);
        assert_eq!(class_count(stderr, class), want, "{what}: `[{class}]` rows in:\n{stderr}");
    }
    for needle in needles {
        assert!(stderr.contains(needle), "{what}: missing `{needle}` in:\n{stderr}");
    }
}

fn main() {
    rfs::write("up.rs", UP);
    rfs::write("down.rs", DOWN);
    rfs::write("down_r.rs", DOWN_R);
    let up0 = up("0");
    let up2 = up("2");

    // ── The imported Clean def's own copy, and its Rust caller ─────────────────────────────
    for (lane, extra) in [
        ("off", &["-Ztrust-verify=off"][..]),
        ("advisory", &["-Ztrust-verify=on", "-Ztrust-policy=advisory"][..]),
    ] {
        for (opt, rlib) in [("0", &up0), ("2", &up2)] {
            let what = format!("down {lane} up-o{opt}");
            let stderr = f1("down.rs", rlib, &format!("{lane}-o{opt}"), extra);
            census(
                &what,
                &stderr,
                "0/2 reachable function(s) completed",
                &[("clean-below-gate", 2)],
                &[
                    "the Clean-origin def `up::m::cleanXor` (imported from crate `up`",
                    "reaches the Clean-origin def `up::m::cleanXor` (imported from crate `up`",
                ],
            );
            // The class's options, once (review 2026-10-05: before, no output carried them).
            for needle in OPTIONS_ONCE {
                assert_eq!(stderr.matches(needle).count(), 1, "{what}: `{needle}` in:\n{stderr}");
            }
        }
    }

    // Trust (D40/R-2): the former MIR bridge and its enabling option are retired.
    // Keeping the old spelling must fail at option parsing, before it could read a body.
    let stderr = f1("down_r.rs", &up2, "retired-upstream-mir", &["-Ztrust-verify=off", "-Ztrust-ir-upstream-mir"]);
    assert!(stderr.contains("unknown unstable option")
            && (stderr.contains("trust-ir-upstream-mir") || stderr.contains("trust_ir_upstream_mir")), "retired MIR option must refuse: {stderr}");
}
