//! A crate with NO function bodies compiles through the trust-ir -> trust-cg
//! self-host backend, exactly as it does under LLVM.
//!
//! This is a regression pin for a blanket `!compiled_any` refusal in
//! `rustc_codegen_trust_cg`, which asked "did I compile a function?" and made
//! "no" fatal with
//!
//!     error: rustc_codegen_trust_cg: expected local codegenable MIR, but no
//!            local function body was codegenable
//!
//! Measured 2026-09-14 driving the stage1 `library/std` graph with this backend
//! as the DEFAULT: it failed three ordinary crates that have no function bodies
//! at all — `rustc-std-workspace-core` (whose entire contents are
//! `pub use core::*;`), `cfg-if` (macro_rules only), and `rustc-literal-escaper`
//! as built there. None of those is a codegen problem, and stopping a self-host
//! on one stops it before it reaches anything that is.
//!
//! The three shapes below are the three ways a crate can legitimately hand the
//! backend no function to compile. Each must produce a real rlib.
//!
//! What this test deliberately does NOT assert: that a crate whose functions all
//! FAILED to lower is accepted. That case still fails closed — the net was kept
//! and narrowed, not removed.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

fn main() {
    // 1. A pure re-export facade. This is `rustc-std-workspace-core`'s entire body.
    rfs::write("facade.rs", "#![no_std]\npub use core::*;\n");

    // 2. Macro-only: `macro_rules!` is not a mono item, so nothing reaches codegen.
    rfs::write(
        "macros_only.rs",
        "#![no_std]\n#[macro_export]\nmacro_rules! pick { ($a:expr, $b:expr) => { $a }; }\n",
    );

    // 3. Types and consts only — no callable code, but real items to emit.
    rfs::write(
        "types_only.rs",
        "#![no_std]\npub struct Pair { pub a: u32, pub b: u32 }\n\
         pub enum Side { Left, Right }\npub const LIMIT: u32 = 64;\n",
    );

    for krate in ["facade", "macros_only", "types_only"] {
        rustc()
            .edition("2021")
            .input(format!("{krate}.rs"))
            .crate_type("rlib")
            .crate_name(krate)
            .arg("-Zcodegen-backend=trust-ir-cg")
            // Codegen axis only: the certificate lane is a separate axis (like
            // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
            // certificate yet, so leaving proofs on would refuse every compile here with
            // [TCG-PROOF-465] regardless of what this test measures.
            .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
            // The verifier is a separate axis; this test is about codegen alone.
            .arg("-Ztrust-verify=off")
            .arg("-Cdebuginfo=0")
            .run();

        let rlib = format!("lib{krate}.rlib");
        assert!(
            rfs::metadata(&rlib).len() > 0,
            "{rlib} was not produced, or is empty, by the trust-ir-cg backend",
        );
    }
}
