//@ needs-trust-verify
//@ edition: 2021
//@ revisions: impostor resident
//@[impostor] aux-crate: core=fmtwrite_impostor/core.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[impostor] check-fail
//@[resident] check-pass
//@[impostor] forbid-output: is a call through its own `Formatter`'s writer
//! THE PLANTED REFUTATION for the WRITER-RELATIVE class
//! (`trust_verify/fmt_writer_relative.rs`) identifying core's formatting
//! machinery from SOURCE-DECLARABLE anchors only: the `Debug`/`Display`,
//! `Formatter` and `FmtWrite` diagnostic items.
//!
//! `impostor`: `core` is a whole-`core` substitute
//! (`auxiliary/fmtwrite_impostor/core.rs`, crate name `core`, verify-off,
//! `--extern core=`) that owns all four diagnostic items. Nothing contests them,
//! because the real `core` is never loaded. `formatting_impl_root` took the impl
//! below for a formatting root, `callee_is_virtual_writer_edge` took its
//! `<dyn fmt::Write>::write_str` for the writer edge and exempted it from the
//! masked-source scan, and the impl compiled as the writer-relative CONDITIONAL
//! pass under `strict`, with the note whose body the `forbid-output` names (a
//! phrase chosen so that no source snippet a diagnostic echoes contains it).
//! That pass is the disclosed conditional one, never "proved" (`certify`
//! refuses every writer-relative row), but its premise ("the writer is core's
//! `Formatter` writer, discharged where std supplies it") is about a crate that
//! is not in this graph. The fix anchors
//! every identity of the class on AUTHENTIC core (`crate_is_authentic_core`:
//! owner of `Sized` AND resident in this compiler's own sysroot). The spawn
//! census (design 2026-09-29-spawn-census-by-construction P2) also refuses the
//! impostor's call: its `dyn Write` writer only enters as `fmt`'s argument and
//! no code the census walks mints one (the impostor is no sysroot crate), so
//! the principal is open and the call UNKNOWN — a second error.
//!
//! `resident`: the HONEST CONTROL. The same impl on this compiler's own `core`
//! (through `Formatter::write_str`, since the real `Formatter`'s writer is
//! private) keeps its conditional pass and its note.
//!
//! MEASURED: see the commit that adds this file. Fix the compiler, not this file.
#![no_std]

pub struct S;

impl core::fmt::Display for S {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        //[resident]~^ NOTE panic-free relative to its `Formatter`'s writer
        //[impostor]~^^ ERROR Trust strict verification failed for `<fmt_writer_relative_fmtwrite_core_substitution_impostor_refuted::S as core::fmt::Display>::fmt`
        //[impostor]~| ERROR Trust Level 0 safety verification incomplete for `<fmt_writer_relative_fmtwrite_core_substitution_impostor_refuted::S as core::fmt::Display>::fmt`
        #[cfg(impostor)]
        return f.buf.write_str("x");
        #[cfg(resident)]
        return f.write_str("x");
    }
}
