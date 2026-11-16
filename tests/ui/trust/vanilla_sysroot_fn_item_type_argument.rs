//@ needs-trust-verify
//@ revisions: last count
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[last] check-pass
//@[count] check-pass
#![crate_type = "lib"]
//! A sysroot function ITEM reified as a type argument keeps the call inside the
//! tolerated vanilla-sysroot class.
//!
//! MEASURED OVER-REFUSAL, 2026-09-18. `s.split(char::is_whitespace)` lowers to
//! `core::str::<impl str>::split::<fn(char)->bool {char::is_whitespace}>`, whose
//! type argument is a `ty::FnDef`. `ty_is_foundational` had no `FnDef` arm, so
//! it fell through `_ => false` and the whole call left the vanilla class.
//!
//! How it was located: `v.sort()` and `v.sort_unstable()` produced IDENTICAL
//! verification reports — one `[assert] runtime-checked` row out of one
//! obligation, same summary line — and OPPOSITE exit codes. Nothing about the
//! obligations differed, so nothing about proof was deciding it; the difference
//! was entirely in whether a comparator had been reified into a type argument.
//!
//! The admitted condition is exactly the one the caller applies to a callee —
//! sysroot code, instantiated at foundational types, foundational parameters —
//! so the item can dispatch into no user code. A closure is `ty::Closure`, a
//! trait object `ty::Dynamic`, a fn pointer `ty::FnPtr`; none is a `FnDef`, and
//! a user function's item type is a `FnDef` outside the sysroot.
//!
//! This is a POLICY tolerance, not a proof: the row stays runtime-checked and
//! `-Ztrust-policy=certify` still demands full static discharge and still fails
//! it. This fixture pins the default lane only, which is the lane the change
//! moved.
//!
//! Trust (2026-09-29): two revisions. `last` consumes the `Split` with `.last()`,
//! which bundles no member the admission lane refuses, so it pins exactly the
//! property above: the `split::<fn(char) -> bool {is_whitespace}>` call is a
//! tolerated vanilla-sysroot row. `count` is the file's original `.count()`, now
//! REFUSED by the bundled std-member fix (it was admitted through the
//! lowering-failure tolerance on a bundle discarded for `count`'s core member with
//! an inherited `Overflow(Add)` Assert). The kept bundle evicts core's
//! `Split::fold::<usize, {count's closure}>` and the ledger does not classify that
//! call site — a capability loss recorded in docs/KNOWN_HAZARDS.md ("CLOSED
//! 2026-09-29 — the bundled std-member tolerance …"); the split call itself is
//! still classified vanilla there too.
//!
//! Trust (W4 ITER-HOF, 2026-10-01): `count` is ADMITTED again, as a reported
//! (not counted-verified) function. That `fold` is no longer absent: the bridge's
//! closure-consumer classifier reads the `->` of `fn(char) -> bool {is_whitespace}`
//! as text (`arrow_neutral`), so the call takes the closure-consumer arm that the
//! same `fold` over an arrow-free receiver (`Split<'_, char>`) always took, instead
//! of the fatal absent-callee arm, and the only unproved row is core's count
//! closure's inherited `Overflow(Add)` Assert, published `runtime_checked`
//! (the advisory pinned below; `certify` refuses it).

#[cfg(last)]
pub fn splits_on_a_reified_sysroot_predicate(s: &str) -> bool {
    s.split(char::is_whitespace).last().is_some()
}

#[cfg(count)]
pub fn splits_on_a_reified_sysroot_predicate(s: &str) -> usize {
    // Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(d)): no advisory; see
    // `callable_handed_to_sysroot_is_charged.rs#split`. The call stays inside the vanilla
    // class this file is about, and is now decided total outright.
    s.split(char::is_whitespace).count()
}

pub fn trims_matches_on_a_reified_sysroot_predicate(s: &str) -> &str {
    s.trim_matches(char::is_numeric)
}

/// The control that was already green and must stay green: the same family of
/// call with no function item among its type arguments.
pub fn sorts_unstably(v: &mut Vec<u32>) {
    v.sort_unstable();
}
