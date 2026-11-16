//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir -C metadata=aux
//@ no-prefer-dynamic
//! DROP-NAME-COLLIDE-1, the capability half: a verify-off dependency that SHARES
//! ITS CRATE NAME with the crate that uses it (its file stem is the consumer's,
//! as Cargo's bin+lib layout makes every bin's own lib) but has NO type of any
//! path the consumer drops. `-C metadata=aux` gives it a `StableCrateId` of its
//! own, as Cargo's per-unit metadata hash does, so rustc accepts the pair.
//!
//! Do not add a `Cfg` or a `Holder` here: the consumer's types must have no
//! namesake anywhere in the graph. Consumed by
//! `drop_credit_crate_name_shared_stamp_kept.rs`.
pub struct Unit;

pub fn greet() -> u8 {
    1
}
