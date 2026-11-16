//@ trust-ladder: verifies
//@ trust-ladder-row: panic-free relative to its
//! FLIPPED DELIBERATELY by D1 increment 2 (2026-09-25), from `refuses` (needle
//! `<dyn core::fmt::Write as core::fmt::Write>::write_str`, re-measured on the
//! stage-1 snapshot `43b8fe6ab`) to `verifies` as a CONDITIONAL pass: the derived
//! impl is panic-free RELATIVE TO its `Formatter`'s writer — its writer edges and
//! its nested formatter (`<dyn core::fmt::Debug>::fmt` inside core's
//! `DebugTuple`, whose only target is core's `<&u32 as Debug>::fmt`) are
//! excused, never proved (`trust_verify/fmt_writer_relative.rs`, "Increment 2").
//! `-Ztrust-policy=certify` still refuses it; the needle is the writer-relative
//! disclosure, so a green for any other reason diverges. AFTER is PREDICTED until
//! the lead's build records it.
//! The most common construct in Rust, refused on the same single row as f3.
#[derive(Debug)]
pub struct P(pub u32);
