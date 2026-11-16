//! The builtin trust-cg MIR frontend must lower blocks in flow order, not MIR numbering.
//!
//! A Trust proof session runs the `-O0` MIR pipeline and refuses `-Zmir-opt-level` (T6), so the
//! inlined shape below is reachable only in a vanilla compile: there an explicit
//! `-Zmir-opt-level=2` at `-Copt-level=2` inlines the Lean `chain2` into its wrapper and leaves
//! core's `wrapping_add` as two calls. MIR then numbers the
//! wrapper `bb0 -> bb2 -> bb1`: the return block `bb1` BEFORE the block `bb2` that writes the
//! return place. The bridge used to lower blocks in numbering order, so `bb1` started from the
//! initial local values and returned a never-defined placeholder, and the compile died in
//! instruction selection ("value Value(1) not defined before use") under every gate value.
//! `crates/trust-cg-bridge` now lowers (and lays out) blocks in reverse postorder.
//!
//! Execution-level on purpose: the observable is the printed value. A reassigned PARAMETER in
//! the same CFG shape would have returned its stale entry value (silent wrong code); the bridge
//! unit tests pin that shape, and this fixture pins the shape rustc's MIR really produces.
//!
//! See docs/issues/2026-09-29-trust-cg-mir-isel-value-not-defined-before-use-inlined-chain.md.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{bin_name, rfs, run, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const SUBJECT: &str = r#"#![crate_name = "block_order_subject"]

clean {
    def chain2 (a : UInt64) (b : UInt64) : UInt64 := (a + b) + a
}

#[unsafe(no_mangle)]
pub extern "C" fn f_chain2(x: u64) -> u64 {
    chain2(x, 1)
}
"#;

const DRIVER: &str = r#"extern crate block_order_subject;

unsafe extern "C" {
    fn f_chain2(x: u64) -> u64;
}

fn main() {
    let row: Vec<String> = [0_u64, 1, 20, 200]
        .iter()
        .map(|&x| unsafe { f_chain2(x) }.to_string())
        .collect();
    println!("{}", row.join(" "));
}
"#;

fn main() {
    rfs::write("block_order_subject.rs", SUBJECT);
    rfs::write("driver.rs", DRIVER);
    rfs::create_dir("out");

    // SUBJECT: an explicit mir-opt-level 2 so the MIR inliner runs, at -O2, through the
    // builtin MIR frontend. Verification is off: a proof session refuses `-Zmir-opt-level`
    // (T6), and this fixture pins the backend's block order, which needs the inlined shape.
    rustc()
        .input("block_order_subject.rs")
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Copt-level=2")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off")
        .arg("-Zmir-opt-level=2")
        .arg("-Ztrust-cg-frontend=mir")
        // A run-make recipe is a new policy boundary: bootstrap's inherited deauthorization
        // override must not decide this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .out_dir("out")
        .run();

    // OBSERVER: built with the default backend, verify-off, like the sibling trust-cg observers.
    rustc()
        .input("driver.rs")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .extern_("block_order_subject", "out/libblock_order_subject.rlib")
        .library_search_path("out")
        .output(bin_name("driver"))
        .run();

    let ran = run("driver");
    // (x + 1) + x, wrapping.
    assert_eq!(
        ran.stdout_utf8().trim(),
        "1 3 41 401",
        "a wrapper whose return block is numbered before its predecessor must return the value \
         its predecessor computed"
    );
}
