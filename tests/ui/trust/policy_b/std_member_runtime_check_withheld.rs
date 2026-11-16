//@ needs-trust-verify
//@ aux-build: std_member_withheld_dep.rs
//@ revisions: dyn_iter_count dyn_iter_count_only ioerror_drop waker_drop
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! The bundled std-member runtime-checked disposition stands in for std's OWN
//! runtime check only; code in a verify-off dependency that the function reaches
//! THROUGH std withholds it (2026-09-29).
//!
//! Each revision bundles a core member the admission lane refuses as a
//! completeness gap (`Iterator::count::{closure#0}` or `<usize as
//! Sum>::sum::{closure#0}`, an inherited `Overflow(Add)`) and reaches dependency
//! code the kept bundle's rows do not refuse on their own: the whole-function
//! panic-freedom aggregate folds a dispatch that happens INSIDE a bundled std
//! member, and the default lane reports that aggregate as runtime-checked.
//!
//! * `dyn_iter_count`, `dyn_iter_count_only`: `it.count()` on a `&mut dyn
//!   Iterator` — the dyn `next` runs inside core's `count`/`fold` (with and
//!   without a `filter().count()` beside it);
//! * `ioerror_drop`: `filter().count()`, then `drop(e)` of a `std::io::Error` whose
//!   payload is the dependency's `DropBomb` (its glue runs `DropBomb::drop`);
//! * `waker_drop`: the same with `drop(w)` of a `Waker` built on the dependency's
//!   vtable.
//!
//! MEASURED on stage-1 with the disposition but WITHOUT this withholding
//! (`runtime_checked_std_member_withheld`), release-like std and m3's debug std,
//! strict: every revision built exit 0 (not counted verified), and a verify-off
//! `main` passing `dep::It(9)` to the `dyn_iter` shapes panicked in the
//! dependency's `next` (exit 101). On origin/main `f6773df328e` all four were
//! refused on the lowering-failure path (the old tolerance's
//! `!masked_fail_closed_source` conjunct). Now each is refused by the masked-source
//! check, by name. Without `count()` the `io::Error`/`Waker` drops were a separate
//! hole, CLOSED 2026-09-29 (docs/KNOWN_HAZARDS.md, "sysroot drop glue that runs
//! code the dropped VALUE chose …"; `sysroot_drop_reaches_dependency_code.rs`);
//! these revisions pin only that the disposition does not widen it.
// The values a caller passes: `dep::It`, `dep::drop_err`, `dep::waker`.
extern crate std_member_withheld_dep as dep;

pub enum Tag {
    A,
    B,
}

#[cfg(dyn_iter_count)]
pub fn p(t: Tag, v: &[u32; 3], it: &mut dyn Iterator<Item = u32>) -> usize {
    let k = v.iter().filter(|x| **x > 1).count();
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if k == 7 {
        return b;
    }
    it.count()
}

#[cfg(dyn_iter_count_only)]
pub fn p(t: Tag, it: &mut dyn Iterator<Item = u32>) -> usize {
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if b == 7 {
        return b;
    }
    it.count()
}

#[cfg(ioerror_drop)]
pub fn p(t: Tag, v: &[u32; 3], e: std::io::Error) -> usize {
    let k = v.iter().filter(|x| **x > 1).count();
    let c = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if k == 7 {
        return c;
    }
    drop(e);
    c
}

#[cfg(waker_drop)]
pub fn p(t: Tag, v: &[u32; 3], w: std::task::Waker) -> u32 {
    let k = v.iter().filter(|x| **x > 1).count();
    let b = match t {
        Tag::A => 1,
        Tag::B => 2,
    };
    if k == 7 {
        return b;
    }
    drop(w);
    b
}

//[dyn_iter_count,dyn_iter_count_only]~? RAW error: Trust full verification failed for `std_member_runtime_check_withheld::p`: a bundled std/core/alloc member's internal Assert was kept as a runtime check, and this function also reaches code that carries no verdict
// Re-pinned 2026-10-15 (the merge of 2026-10-14): in `ioerror_drop` and `waker_drop` the
// counted panic-freedom aggregate now carries the member's Assert (one `runtime_checked`
// row) and no member is recorded under the runtime-checked disposition, so its named
// refusal does not fire. `p` is still refused, by the drop of the dependency-chosen value
// itself: the fail-closed drop-glue row the default policy never tolerates.
//[ioerror_drop]~? RAW error: Trust strict verification failed for `std_member_runtime_check_withheld::p`
//[ioerror_drop]~? RAW drop glue for `core::io::error::Error` has unproven panic-freedom
//[waker_drop]~? RAW error: Trust strict verification failed for `std_member_runtime_check_withheld::p`
//[waker_drop]~? RAW drop glue for `core::task::wake::Waker` has unproven panic-freedom
