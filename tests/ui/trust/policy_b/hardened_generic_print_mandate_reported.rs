//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ revisions: default certify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-profile=hardened -Copt-level=0
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[certify] check-fail
//[certify]~? RAW Trust
//! The platform-agnostic `hardened` profile assumes no Unix semantics, so it
//! declares no process-signal policy and the `process_semantics` mandate on
//! `_print` stays minted — an OPAQUE design requirement (`Bool(true)`, the shape
//! the transport marks `design_mandate: true`). Since 2026-09-16 the default
//! policy REPORTS such a mandate instead of failing the build: targo partitions
//! it as `mandated` and grades `conditional-pass`, the compiler's refusal note
//! still names the fix (`unix_hardened`, or an explicit `-Zon-broken-pipe`), and
//! `-Ztrust-policy=certify` (the `certify` revision) demands full discharge and
//! refuses it. Before, `std::env::args` alone made every ordinary program fatal
//! under `targo trust build`'s default profile with no fix path (v7/D3).
fn main() {
    println!("hello");
}
