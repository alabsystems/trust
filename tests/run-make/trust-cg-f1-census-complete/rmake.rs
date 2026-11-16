//! Trust (step 2 increment 5, sub-step 5.4.2; plan
//! `docs/design/2026-10-08-step2-inc5-step4-compiler-lane-plan.md` §2, critique M8): ONE fatal on
//! F1's compiler lane lists every refusal — the frontend's, the codegen module's and trust-cg's
//! own preflight rows over the ADMITTED subset — and trust-cg's rows name every refused function,
//! not only the first.
//!
//! * `merged.rs` (verification on, so its Clean `def` is a Clean-origin row of the crate module):
//!   the codegen module refuses the Clean-origin body `calls_clean` reaches
//!   (`CleanOriginBelowCodegenGate`) and drops `calls_clean` with it. Since plan step 3.4 (owner
//!   ruling D37: the codegen license's leg 4 is per function) the two Rust bodies beside the
//!   Clean row keep their `trust-direct-lane-structural` license, so trust-cg admits them and
//!   its census has no row for them: the fatal is exactly those two rows of four. Before 3.4 a
//!   crate with a Clean row had every body stamped `Ungated` (design 105-109) and trust-cg's
//!   census named BOTH Rust bodies `[trust-cg-refused:Adapter::UngatedBody]`; that was this
//!   fixture's witness that trust-cg's rows name every refused function, not only the first.
//!   After 3.4 no Rust source reaches two trust-cg per-body refusals through this lane
//!   (measured on the step-3.4 landing's stage 1), so that property is pinned where trust-cg's
//!   census is called on a hand-built module:
//!   `crates/trust-cg-bridge/tests/f1_compile.rs::census_reports_every_refused_function_and_skips_compile`.
//! * `tuple.rs`: the frontend and the codegen module admit everything, and trust-cg admits
//!   the module too. This was the module-level refusal below until the 1.101 toolchain:
//!   trust-cg's byte path lays a tuple out in declaration order and admits a declared row
//!   only when it EQUALS that layout (WS7.7), and rustc 1.101 lays a pair out in
//!   declaration order (`(u64, u64)` at offsets `[0, 8]`, measured by the ABI probe of
//!   `trust-cg-f1-abi-legalization` and this fixture's own dump), so the stamped row now
//!   agrees. Capability returned, pinned as success.
//! * `tuple3.rs`: the same shape one field wider still refuses — rustc reorders
//!   `(u8, u64, u8)` (stamped offsets `[8, 0, 9]`), which disagrees with the byte path's
//!   declaration-order layout, so trust-cg refuses the module
//!   (`[trust-cg-refused:Adapter::DeclaredTupleLayoutDisagrees]`), a module-level refusal
//!   attributed to the codegen unit. This is the discriminating sibling that keeps the
//!   pair's admission honest.
//!
//! MEASURED (stage 1 of this branch, trust-cg `7ace0c56b`): these are the two distinct trust-cg
//! refusals reachable from Rust source through today's frontend and the 5.4.2 scalar subset; the
//! plan asked for three in one crate, and none of the other shapes probed reached a trust-cg
//! refusal (floats, `u128` shifts and multiplication, structs, arrays, a dense `match`, `Option`
//! and a borrowed argument all compile). trust-cg's `Compiler::preflight` reports a row only for
//! a license refusal or an adapter refusal of one body: when its adapter census fails for the
//! MODULE (a declared tuple layout here), preflight returns no row for it and the refusal
//! surfaces only as the compile's residual error — on the refusal path, where nothing is
//! compiled, it is not listed (measured: a body with an unresolved `Inst::Drop`, admitted beside
//! a refused drop-glue item, produced no trust-cg row). See docs/DECISION_QUEUE.md, INC5.4-SCOPE.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, rustc};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

fn compiler_lane(input: &str, out: &str, verify: &str) -> run_make_support::Rustc {
    rfs::create_dir(out);
    let mut cmd = rustc();
    cmd.input(input)
        .crate_type("lib")
        .edition("2024")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Coverflow-checks=off")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg(format!("-Ztrust-verify={verify}"))
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-cg-f1-backend=compiler")
        .arg("-Ztrust-cg-output-gate=allow-unknown")
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

/// The census sample lines (`e.g. …`) of a fatal.
fn samples(stderr: &str) -> Vec<&str> {
    stderr.lines().filter(|l| l.trim_start().starts_with("e.g.")).collect()
}

fn main() {
    // ── merged: the frontend's, the codegen module's and trust-cg's rows in ONE fatal ───────
    let stderr = compiler_lane("merged.rs", "out-merged", "on").run_fail().stderr_utf8();
    assert!(!stderr.contains("internal compiler error"), "{stderr}");
    assert_eq!(
        stderr.matches("this frontend never falls back to the MIR path").count(),
        1,
        "ONE fatal:\n{stderr}"
    );
    assert!(stderr.contains("the census below counts refusal ROWS"), "{stderr}");
    let lines = samples(&stderr);
    let has = |needles: &[&str]| lines.iter().any(|l| needles.iter().all(|n| l.contains(n)));
    assert!(
        has(&["cleanWsum", "CleanOriginBelowCodegenGate"]),
        "the codegen module names the Clean-origin body:\n{stderr}"
    );
    assert!(has(&["calls_clean", "which is refused"]), "and drops its caller:\n{stderr}");
    // Plan step 3.4: the Rust bodies keep their license, so nothing else is refused.
    assert!(stderr.contains("refused 2 of 4 reachable function(s)"), "{stderr}");
    for function in ["rust_only", "rust_also"] {
        assert!(
            !lines.iter().any(|l| l.contains(function)),
            "3.4: `{function}` keeps its license and is not refused:\n{stderr}"
        );
    }
    assert!(!stderr.contains("[trust-cg-refused:Adapter::UngatedBody]"), "{stderr}");
    assert!(!std::path::Path::new("out-merged/libcensus_merged.rlib").exists());

    // ── tuple: admitted end to end since 1.101 (see the header) ────────────────────────────
    let stderr = compiler_lane("tuple.rs", "out-tuple", "off").run().stderr_utf8();
    assert!(!stderr.contains("internal compiler error"), "{stderr}");
    assert!(
        stderr.contains(
            "1/1 reachable function(s) completed source -> trust_ir_of -> codegen_module"
        ),
        "the frontend and the codegen module admitted the crate:\n{stderr}"
    );
    assert!(
        stderr.contains("compiled 1 function(s) in 1 module(s)"),
        "trust-cg admitted the pair's agreeing declared layout:\n{stderr}"
    );
    assert!(std::path::Path::new("out-tuple/libcensus_tuple.rlib").exists());

    // ── tuple3: a module-level trust-cg refusal, attributed to the codegen unit ────────────
    let stderr = compiler_lane("tuple3.rs", "out-tuple3", "off").run_fail().stderr_utf8();
    assert!(!stderr.contains("internal compiler error"), "{stderr}");
    assert!(
        stderr.contains(
            "1/1 reachable function(s) completed source -> trust_ir_of -> codegen_module"
        ),
        "the frontend and the codegen module admitted the crate:\n{stderr}"
    );
    assert!(
        samples(&stderr).iter().any(|l| l.contains("<module census_tuple3.codegen_unit.0>")
            && l.contains("[trust-cg-refused:Adapter::DeclaredTupleLayoutDisagrees]")),
        "trust-cg's module-level refusal is named and attributed to the unit:\n{stderr}"
    );
    assert!(!std::path::Path::new("out-tuple3/libcensus_tuple3.rlib").exists());
}
