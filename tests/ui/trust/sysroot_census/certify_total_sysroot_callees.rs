//@ needs-trust-verify
//@ revisions: census no_census
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@[no_census] rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[census] check-pass
//@[census] ignore-std-debug-assertions (measured with a release-like std only: a std built with debug assertions keeps `debug_assert!`s, e.g. `OnceLock::get_unchecked`'s, which the census reaches as sites)
//@[no_census] check-fail
//! Trust (2026-09-26, std-absent-callee): a call into a std/core/alloc routine
//! whose OWN MIR reaches no panic site certifies — including from `main`.
//!
//! Before: every function below was refused by `-Ztrust-policy=certify` with one
//! `[trust-absent-callee-assumption] call to absent callee … may panic` row. The
//! bridge models every std callee no lane bundled as "may panic, unconditionally",
//! and `certify` admits no unproved row, so a program could not call these at all.
//! None of them can panic: the sysroot panic census
//! (`trust_verify/sysroot_panic_census.rs`) walks each one's real, instantiated MIR
//! — through its sysroot callees, drop glue, non-unwinding intrinsics and C imports
//! — and reaches no panic site, so the call is discharged on the compiler-total
//! channel by derivation. Nothing here is admitted by name.
//!
//! Two of them show a panic precondition INSIDE std being provably excluded:
//! `OnceLock::get` reaches `atomic_load`, whose `Release`/`AcqRel` arms panic, with
//! the constant `Acquire` — the walk takes only that arm; and `split_at_checked`
//! reaches `split_at_unchecked`, whose `assert_unsafe_precondition!` fires only on
//! undefined behaviour (the census's one premise, docs/TCB.md).
//!
//! The negative twins: `certify_sysroot_callee_reaching_panic_refused.rs` (a std
//! routine that CAN panic stays refused, with the site named) and
//! `certify_println_refused_names_the_std_panic.rs`.
//!
//! The `no_census` revision is the controlled pair on ONE binary:
//! `TRUST_NO_SYSROOT_CENSUS=1` withholds every census grant (it can only remove
//! proof), and the same file is then refused exactly as before the census existed.
//! It keeps the `census` revision's green from being vacuous — if `no_census` ever
//! passes, something other than the census discharged these calls and this file no
//! longer measures it.
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Duration;

// `atomic_add` maps all five orderings onto `atomic_xadd`: no ordering panics.
pub fn fetch_add(a: &AtomicUsize) -> usize {
    //[no_census]~^ ERROR Trust strict verification failed
    a.fetch_add(1, Ordering::Relaxed)
}

// Likewise `atomic_swap`.
pub fn swap_flag(a: &AtomicBool) -> bool {
    a.swap(true, Ordering::SeqCst)
}

// The derived `PartialEq` of `Option<usize>`: a discriminant and a `usize` compare.
pub fn option_eq(a: Option<usize>, b: Option<usize>) -> bool {
    a == b
}

// A length compare and `bcmp` (a non-unwinding C import).
pub fn string_eq(s: &String) -> bool {
    *s == "a"
}

// The same compare, once per element.
pub fn contains_a(xs: &[&str]) -> bool {
    xs.contains(&"a")
}

// `is_completed()` is an `Acquire` load of the once state.
pub fn once_get(cell: &OnceLock<u32>) -> Option<&u32> {
    cell.get()
}

// `Occupied` hands back its slot; `Vacant` is `insert_no_grow` into the capacity
// `HashMap::entry` reserved before it returned the entry: no panic site.
pub fn entry_or_insert(e: std::collections::hash_map::Entry<'_, String, u32>) -> u32 {
    *e.or_insert(0)
}

// Bounds are checked first; the unchecked split behind it carries only a UB check.
pub fn prefix_len(v: &[u8]) -> usize {
    match v.split_at_checked(2) {
        Some((head, _)) => head.len(),
        None => 0,
    }
}

// `u128` arithmetic on a `Duration`'s fields: no overflow is possible.
pub fn millis(d: Duration) -> u128 {
    d.as_millis()
}

// A std routine instantiated at a USER type certifies when it runs none of that
// type's code: `Vec<Quiet>`'s `Deref` and counting its slice iterator never touch
// a `Quiet`, so its destructor is never reached. (`Vec::clear`, which does run it,
// is in the negative twin with a destructor that panics.)
pub struct Quiet(pub u32);
impl Drop for Quiet {
    fn drop(&mut self) {}
}

pub fn count_user(v: &Vec<Quiet>) -> usize {
    v.iter().count()
}

// A PROGRAM that calls std certifies too: `certify` builds this binary.
static COUNTER: AtomicUsize = AtomicUsize::new(0);
static FLAG: AtomicBool = AtomicBool::new(false);

fn main() {
    //[no_census]~^ ERROR Trust strict verification failed
    let _ = COUNTER.fetch_add(1, Ordering::Relaxed);
    let _ = FLAG.swap(true, Ordering::SeqCst);
    let x: Option<usize> = Some(3);
    let _ = x == Some(3);
    let _ = Duration::from_secs(2).as_millis();
}
