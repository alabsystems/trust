//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: index out of bounds: the len is 11 but the index is 1001
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//! The runtime WITNESS for `range_contains_name_is_not_a_bound.rs`: the user
//! `RangeInclusive::contains` answers `true`, so `victim(1001)` indexes an 11-element
//! array at 1001 and panics, as vanilla Rust does. The bounds check is never elided
//! (only overflow checks are), so the program panics BEFORE and AFTER; what the fix
//! changes is the verdict on `victim`.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`, this file's flags,
//! 2026-10-04): `victim`'s bounds row was proved, so the build printed one warning
//! (on `main`), the `victim` annotation below did not fire, and the program panicked
//! with the message above (exit 101).
//!
//! AFTER (predicted, then measured): `victim`'s bounds row is refuted, a warning under
//! advisory. Derived on the same stage 1 from a twin with the type renamed `RngIncl`
//! (the old name test then cannot match): it built with exactly the two warnings
//! annotated here, and the binary panicked with that message, exit 101.
//! Measured on the stage 1 of `4463aeeb6d` (2026-10-04): the build prints the annotated
//! warnings and the run panics `index out of bounds: the len is 11 but the index is 1001`
//! (exit 101).

pub struct RangeInclusive<T>(pub T, pub T);

impl RangeInclusive<u32> {
    #[inline(never)]
    pub fn contains(&self, _x: &u32) -> bool {
        true
    }
}

const R: RangeInclusive<u32> = RangeInclusive(0, 10);

fn victim(x: u32) -> u8 {
    //~^ WARN Trust Level 0 safety verification incomplete for `range_contains_name_is_not_a_bound_run::victim`: 1 obligation(s) were not proved
    let arr = [7u8; 11];
    if R.contains(&x) { arr[x as usize] } else { 0 }
}

fn main() {
    //~^ WARN Trust Level 0 safety verification incomplete for `range_contains_name_is_not_a_bound_run::main`: 1 obligation(s) were not proved
    println!("{}", victim(std::hint::black_box(1001)));
}
