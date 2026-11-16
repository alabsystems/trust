//@ trust-ladder: verifies
//@ trust-ladder-row: panic-free relative to its
//! FLIPPED DELIBERATELY by D1 increment 2 (2026-09-25), from `refuses` (needle
//! `<dyn core::fmt::Write as core::fmt::Write>::write_str`, re-measured on the
//! stage-1 snapshot `43b8fe6ab`) to `verifies` as a CONDITIONAL pass — see `d2`.
//! The unit arm is a plain writer edge (`f.write_str("A")`); the tuple arm is
//! `debug_tuple_field1_finish` with a nested formatter over `&u32`. AFTER is
//! PREDICTED until the lead's build records it.
#[derive(Debug)]
pub enum E { A, B(u32) }
