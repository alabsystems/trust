//@ revisions: mir_opt_level mir_opt_level_one inline_mir inline_mir_no inline_threshold
//@ revisions: inline_hint inline_forwarder enable_passes bisect preserve_ub strip_debuginfo
//@ revisions: session_dependency vanilla
//@ needs-trust-verify
//@[mir_opt_level] compile-flags: -Ztrust-verify=on -Zmir-opt-level=2
//@[mir_opt_level_one] compile-flags: -Ztrust-verify=on -Zmir-opt-level=1
//@[inline_mir] compile-flags: -Ztrust-verify=on -Zinline-mir=yes
//@[inline_mir_no] compile-flags: -Ztrust-verify=on -Zinline-mir=no
//@[inline_threshold] compile-flags: -Ztrust-verify=on -Zinline-mir-threshold=5
//@[inline_hint] compile-flags: -Ztrust-verify=on -Zinline-mir-hint-threshold=5
//@[inline_forwarder] compile-flags: -Ztrust-verify=on -Zinline-mir-forwarder-threshold=5
//@[enable_passes] compile-flags: -Ztrust-verify=on -Zmir-enable-passes=+GVN
//@[bisect] compile-flags: -Ztrust-verify=on -Zmir-opt-bisect-limit=0
//@[preserve_ub] compile-flags: -Ztrust-verify=on -Zmir-preserve-ub
//@[strip_debuginfo] compile-flags: -Ztrust-verify=on -Zmir-strip-debuginfo=all-locals
//@[session_dependency] compile-flags: -Ztrust-verify=off -Ztrust-verify-session=ui-proof-session
//@[session_dependency] compile-flags: -Zmir-opt-level=2
//@[vanilla] compile-flags: -Ztrust-verify=off -Zmir-opt-level=2
//@[mir_opt_level] check-fail
//@[mir_opt_level_one] check-fail
//@[inline_mir] check-fail
//@[inline_mir_no] check-fail
//@[inline_threshold] check-fail
//@[inline_hint] check-fail
//@[inline_forwarder] check-fail
//@[enable_passes] check-fail
//@[bisect] check-fail
//@[preserve_ub] check-fail
//@[strip_debuginfo] check-fail
//@[session_dependency] check-fail
//@[vanilla] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//[mir_opt_level]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-opt-level would
//[mir_opt_level_one]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-opt-level would
//[inline_mir]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zinline-mir would
//[inline_mir_no]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zinline-mir would
//[inline_threshold]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zinline-mir-threshold would
//[inline_hint]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zinline-mir-hint-threshold would
//[inline_forwarder]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zinline-mir-forwarder-threshold would
//[enable_passes]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-enable-passes would
//[bisect]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-opt-bisect-limit would
//[preserve_ub]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-preserve-ub would
//[strip_debuginfo]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-strip-debuginfo would
//[session_dependency]~? ERROR a Trust proof session runs the -O0 MIR pipeline for every unit; -Zmir-opt-level would

//! Work item T6: every unit of a Trust proof session runs the `-O0` MIR
//! pipeline at every `-Copt-level`, so the verified MIR — and every verdict —
//! is a function of the program, not of the caller's MIR options. Each option
//! that would change which MIR passes run is refused BY NAME in a verifying
//! session, and in a verification-off unit carrying `-Ztrust-verify-session`
//! (a dependency whose encoded MIR a verified dependent re-derives). There is
//! no opt-out: even `-Zmir-opt-level=1`, the level the session runs anyway, and
//! `-Zinline-mir=no` are refused, because the rule is about who chooses the
//! pipeline. The vanilla lane (no verification, no proof session) keeps
//! upstream's options.

pub fn max_of(a: &[u32]) -> u32 {
    let mut n = 0;
    for &v in a {
        n = n.max(v);
    }
    n
}

fn main() {
    let _ = max_of(&[1, 2, 3]);
}
