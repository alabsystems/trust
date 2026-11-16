//@ trust-ladder: verifies
//@ trust-ladder-row: panic-free relative to its
//! FLIPPED DELIBERATELY by D1 increment 1 (2026-09-25), from `refuses` (needle
//! `<dyn core::fmt::Write as core::fmt::Write>::write_str`, measured on the
//! stage-1 snapshot `4e9fe36bf`) to `verifies` as a CONDITIONAL pass: the impl
//! is panic-free RELATIVE TO its `Formatter`'s writer (the writer-relative
//! class, `trust_verify/fmt_writer_relative.rs`). Its writer row is still
//! unproved and `runtime-checked`, and `-Ztrust-policy=certify` still refuses
//! it; the needle is the writer-relative disclosure, so a green for any other
//! reason diverges. The `dyn` site itself is still NOT discharged (C-FLOW and
//! C-UNIVERSAL decline exactly as the text below says).
//! THE WHOLE FAILURE, MINIMALLY. A hand-written `Debug` impl whose entire body
//! is one `Formatter::write_str`. No derive, no formatting machinery, no user
//! type in any type argument. Compare g2: the same trait method at a concrete
//! receiver verifies.
use core::fmt;
pub struct S(pub u32);
impl fmt::Debug for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("S") }
}
