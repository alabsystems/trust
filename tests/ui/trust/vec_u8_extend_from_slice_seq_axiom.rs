//@ edition: 2021
//@ needs-trust-verify
//@ revisions: pinned hook
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[pinned] check-pass
//@[hook] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! **`Vec<u8>::extend_from_slice` on the `Ty::Seq` rendering, under the
//! MAX_LIVE_ALLOC_BYTES axiom, keyed on the pinned instance identity.**
//!
//! The verifier lane renders the real std `Vec<u8>` receiver as `&mut Seq<u8>`:
//! no allocator, no `len` field. The bridge's grow summary used to require the
//! structural `alloc::vec::Vec` ADT with a 64-bit `len`, so on this rendering it
//! always declined and every `extend_from_slice` kept an undischargeable
//! `[trust-absent-callee-assumption] … may panic` row (6 ALab rows: astream
//! wire, kafka and term). It now admits the Seq rendering when the call's
//! compiler-stamped instance identity equals the compiler's pinned identity of
//! `<Vec<u8, Global>>::extend_from_slice` (`trust_verify/vec_grow_pins.rs`),
//! minted only on a 64-bit target and only when no crate of the graph can
//! install an allocation-error hook (the oom gate). The obligation is the same
//! axiom-named conditional row (`old_len + buf.len() > isize::MAX`), discharged
//! under MAX_LIVE_ALLOC_BYTES.
//!
//! `pinned`: certify accepts it (MEASURED: the stage 1 before this change refuses
//! `grow` with one runtime-checked row). `hook`: this crate NAMES
//! `std::alloc::set_alloc_error_hook`, whose hook "may choose to panic", so a
//! failed allocation can unwind: the grow summary declines (the row stays
//! runtime-checked), and the existing global-allocator contract refuses the body
//! too. The instance-identity negatives are
//! `vec_extend_from_slice_seq_unpinned_keeps_row.rs`.

#![cfg_attr(hook, feature(alloc_error_hook))]

pub fn grow(v: &mut Vec<u8>, s: &[u8]) {
    //[pinned]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 2
    //[hook]~^^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 2
    //[hook]~| ERROR Trust Level 0 safety verification incomplete
    //[hook]~| ERROR the `contract:global-alloc-dealloc-panic-free` caller contract is refused
    //[hook]~| ERROR Trust strict verification failed
    v.extend_from_slice(s)
}

#[cfg(hook)]
pub fn install() {
    std::alloc::set_alloc_error_hook(|_| panic!("oom"));
    //[hook]~^ ERROR Trust Level 0 safety verification incomplete
    //[hook]~| ERROR Trust strict verification failed
}
