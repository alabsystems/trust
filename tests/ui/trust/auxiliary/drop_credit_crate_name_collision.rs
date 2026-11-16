//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir -C metadata=aux
//@ no-prefer-dynamic
//! DROP-NAME-COLLIDE-1: a verify-off dependency that SHARES ITS CRATE NAME with
//! the crate that uses it. Its file stem is the consumer's, so both crates are
//! named `drop_credit_crate_name_collision` — what Cargo's bin+lib layout does to
//! every bin (the bin and its own lib are both `foo`) and what two semver
//! versions of one crate do to each other. `-C metadata=aux` gives it a
//! `StableCrateId` of its own, as Cargo's per-unit metadata hash does, so rustc
//! accepts the pair (E0519 needs equal ids).
//!
//! Compiled the way `targo` compiles every dependency unit (`-Ztrust-verify=off`,
//! `-Zalways-encode-mir`). The lie also reproduced with the aux built WITHOUT
//! `-Zalways-encode-mir` (measured by the wave-15 scout).
//!
//! `Conn` renders to the SAME path as the consumer's own `Conn`. Its `drop`
//! PANICS on 7 — that is the assertion. Do not make it total. Consumed by
//! `drop_credit_crate_name_collision.rs` and `drop_credit_crate_name_collision_run.rs`.
pub struct Conn(pub u8);

impl Drop for Conn {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("dependency Conn dropped with 7");
        }
    }
}
