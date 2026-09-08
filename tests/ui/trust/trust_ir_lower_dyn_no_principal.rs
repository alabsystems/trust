//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-DNP): a PRINCIPAL-LESS trait object (`dyn Send`, `dyn Send +
//! Sync`) is identified by its AUTO-TRAIT SET.
//!
//! `faithful_principal_key` is the ONE shared renderer — the THIR producer's
//! `trait_object_id` and the extractor's `TyKind::Dynamic` arm both call it, and
//! the bridge only hashes the string it is handed. Giving the principal-less
//! case an EMPTY base plus the existing sorted `+auto` tail therefore moves
//! both sides together by construction, which is the property that made the old
//! blanket refusal necessary in the first place.
//!
//! Injectivity rests on two things the surrounding code already guarantees: a
//! principal-ful key always begins with a def-path character and a
//! principal-less one always begins with `+` (the auto set is non-empty or the
//! renderer refuses), so the families cannot collide; and the auto set is
//! sorted and sysroot-stamped, so `dyn Send + Sync` and `dyn Sync + Send` are
//! ONE key while an impersonating `Send` is not the real one.

pub fn hold(b: Box<dyn Send>) -> usize {
    core::mem::size_of_val(&b)
}

pub fn hold2(b: Box<dyn Send + Sync>) -> usize {
    core::mem::size_of_val(&b)
}

fn main() {
    let a: Box<dyn Send> = Box::new(7u32);
    let b: Box<dyn Send + Sync> = Box::new(9u64);
    assert_eq!(hold(a), core::mem::size_of::<usize>() * 2);
    assert_eq!(hold2(b), core::mem::size_of::<usize>() * 2);
}
