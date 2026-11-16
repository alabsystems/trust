//@ needs-trust-verify
//@ edition: 2021
//@ revisions: o0 o1 o2 o3 os oz o2_off
//@ compile-flags: --crate-type lib
//@[o0] compile-flags: -Ztrust-verify=on -Copt-level=0
//@[o1] compile-flags: -Ztrust-verify=on -Copt-level=1
//@[o2] compile-flags: -Ztrust-verify=on -Copt-level=2
//@[o3] compile-flags: -Ztrust-verify=on -Copt-level=3
//@[os] compile-flags: -Ztrust-verify=on -Copt-level=s
//@[oz] compile-flags: -Ztrust-verify=on -Copt-level=z
//@[o2_off] compile-flags: -Ztrust-verify=off -Copt-level=2
//@[o0] check-pass
//@[o1] check-pass
//@[o2] check-pass
//@[o3] check-pass
//@[os] check-pass
//@[oz] check-pass
//@[o2_off] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Trust (-O parity, 2026-09-25): A PROGRAM THAT VERIFIES AT `-O0` VERIFIES AT
//! EVERY `-Copt-level`.
//!
//! `TrustVerify` is the last MIR pass, so it verifies whatever the passes before
//! it produced. Until this change a verifying session at `-O` ran
//! `-Zmir-opt-level=2`: the MIR inliner and GVN dissolved `slice::Iter::next`
//! into `RawPtr -> NonNull` casts and `PtrOffset`, which the verifier does not
//! model. `m` below was measured on `0.10.0+g16f58bb7a`: rc=0 at `-O0`, rc=1 at
//! `-O` (6x ``unsupported MIR `Rvalue::Cast` ``, 3x `Rvalue::PtrOffset`); the
//! ordinary-Rust sweep verified 73/80 at `-O0` and 43/80 at `-O`.
//!
//! Now a verifying session runs the `-O0` MIR pipeline at every opt-level
//! (`rustc_session::trust_default_mir_opt_level_by_flags`), so `o0`..`oz` must
//! all verify. LLVM's `-Copt-level` is untouched. Since T6 (2026-10-09) the
//! pipeline is not a default but the rule: a proof session refuses
//! `-Zmir-opt-level`, `-Zinline-mir` and every other MIR-pipeline option by name
//! (`proof_session_refuses_mir_pipeline_options.rs`), so the `-O` session that
//! refused `m` cannot be asked for.
//!
//! * `o2_off` pins that the vanilla lane is untouched (it never refused anything).
//! * The negative control — that an optimized pipeline's MIR still reaches no
//!   verified body — is the dependency channel's:
//!   `tests/run-make/trust-proof-session-dependency-mir` builds a dependency at
//!   `-Copt-level=0` and `2` inside a proof session (identical rows in the
//!   verified dependent) and in the vanilla lane at `-Copt-level=2`, whose MIR
//!   the dependent declines to bundle, by name.

pub fn m(a: &[u32]) -> u32 {
    let mut n = 0u32;
    for &v in a {
        n = n.max(v);
    }
    n
}
