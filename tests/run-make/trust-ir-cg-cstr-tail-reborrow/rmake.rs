//! A `&CStr` — a `#[repr(transparent)]` UNSIZED wrapper over `[c_char]` — is the
//! `{ data, len }` fat pointer it wraps, and a reborrow of its tail field keeps
//! both lanes.
//!
//! Regression pin for the refusal that stopped the stage1 `library/std` build at
//! `std_detect`:
//!
//!     error: [TCG-MIR-UNSUPPORTED] ... cannot compile required function ...
//!         - ..std_detect6detect2os15detect_features ..: Ty::[i8]
//!
//! raised for the darwin aarch64 `_sysctlbyname(c"hw.optional.…")` probes,
//! MIR-inlined into `detect_features`. The MIR shape is
//!
//!     _4  = const Slice { alloc_id: alloc1, meta: 26 }: &CStr;
//!     _11 = &raw const ((*_4).0: [i8]);        // CStr::as_ptr's `self.inner.as_ptr()`
//!     _10 = copy _11 as *const i8 (PtrToPtr);
//!
//! Every fat-pointer decision in the bridge keyed on a SYNTACTIC `[T]` / `str`
//! pointee, so `&CStr` read as a THIN reference to an aggregate; the pointee
//! flattener descended into the struct and met the unsized tail `[i8]`, which
//! has no scalar type. The fix teaches the one predicate the whole fat-pointer
//! surface shares (`is_slice_reference_ty`) that a non-generic
//! `repr(transparent)` unsized wrapper IS its slice (layout-identical, tail at
//! offset 0, same metadata), and admits the tail-field reborrow
//! (`&raw const (*c).inner` / `&(*c).inner`) as the identity on the pair.
//!
//! The program is compiled TWICE: at the default -O0, where `probe` and
//! `CStr::as_ptr` are real calls and the `&CStr` crosses parameter / const-arg
//! boundaries, and at -O3, where everything inlines into `main` and the caller
//! holds the const and reborrows its tail in place (the std_detect shape).
//!
//! This test RUNS the result rather than only compiling it: the hazard class is
//! a fat pointer with its length dropped, so both the bytes behind the data
//! pointer (`strlen`) and the length lane (`count_bytes` -> `PtrMetadata`) are
//! asserted.

//@ needs-trust-ir-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, rustc};

const FIXTURE: &str = r#"
use std::ffi::CStr;

unsafe extern "C" {
    fn strlen(s: *const std::ffi::c_char) -> usize;
}

// The `std_detect::detect::os::detect_features` shape (darwin aarch64): an
// `#[inline]` probe over `c"…"` literals. At -O3 rustc MIR-inlines it, so the
// CALLER holds `_4 = const Slice {..}: &CStr` and reborrows the wrapper's tail
// in place — `_10 = &raw const ((*_4).0: [i8]); _9 = copy _10 as *const i8` —
// which is the exact statement the stage1 std build refused. At -O0 nothing
// inlines, so the same program instead crosses `&CStr` CALL boundaries (a
// parameter, a const argument) and calls `CStr::as_ptr` for real, whose own body
// is the `Rvalue::Ref` twin of the reborrow (`_2 = &((*_1).0: [i8])`).
#[inline]
fn probe(name: &CStr) -> usize {
    unsafe { strlen(name.as_ptr()) }
}

#[inline(never)]
fn probe_noinline(name: &CStr) -> usize {
    unsafe { strlen(name.as_ptr()) }
}

// The LENGTH lane must survive the tail reborrow, not just the data pointer:
// `count_bytes` is `self.inner.len() - 1`, a `PtrMetadata` of the reborrowed
// `[c_char]` (at -O3: `_3 = &((*_1).0: [i8]); _2 = PtrMetadata(copy _3)`).
#[inline(never)]
fn nul_len(name: &CStr) -> usize {
    name.count_bytes()
}

fn main() {
    // `strlen` reads the bytes behind the DATA pointer: a wrong pointer cannot
    // return these lengths, and a truncated fat pointer cannot compile at all
    // (every consumer of the pair fails closed rather than drop the length).
    assert_eq!(probe(c"hw.optional.floatingpoint"), 25);
    assert_eq!(probe(c""), 0);
    assert_eq!(probe_noinline(c"hw.optional.arm.FEAT_AES"), 24);
    // ... and the LENGTH lane, read independently of the bytes.
    assert_eq!(nul_len(c"abc"), 3);
    assert_eq!(nul_len(c""), 0);
    assert_eq!(nul_len(c"hw.optional.floatingpoint"), 25);
    println!("cstr tail reborrow ok");
}
"#;

fn main() {
    // One source, two binaries: the -O0 (boundary-crossing) and -O3 (inlined,
    // std_detect) shapes are different MIR and exercise different arms.
    rfs::write("cstr_tail_o0.rs", FIXTURE);
    rfs::write("cstr_tail_o3.rs", FIXTURE);

    rustc()
        .edition("2021")
        .input("cstr_tail_o0.rs")
        .crate_type("bin")
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
    run("cstr_tail_o0").assert_stdout_contains("cstr tail reborrow ok");

    rustc()
        .edition("2021")
        .input("cstr_tail_o3.rs")
        .crate_type("bin")
        .opt_level("3")
        .arg("-Zcodegen-backend=trust-ir-cg")
        // Codegen axis only: the certificate lane is a separate axis (like
        // `-Ztrust-verify=off` above). AArch64 pair opcodes have no checker-accepted
        // certificate yet, so leaving proofs on would refuse every compile here with
        // [TCG-PROOF-465] regardless of what this test measures.
        .arg("-Ztrust-ir-cg-args=no-proof-certs=1")
        .arg("-Ztrust-verify=off")
        .arg("-Cdebuginfo=0")
        .run();
    run("cstr_tail_o3").assert_stdout_contains("cstr tail reborrow ok");
}
