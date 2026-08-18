//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! FAIL-OPEN GUARD for the drop-glue bundling rule. A user `Drop` impl that
//! PANICS, reached through a container's glue, must keep its obligation.
//!
//! ## THE PANICKING `Drop` IS THE ASSERTION — DO NOT MAKE IT TOTAL
//!
//! Admitting drop glue as a bundle callee CREDITS glue that was previously
//! refused, so it is the fail-OPEN direction. This file is the planted
//! violation: if it ever passes, the rule is crediting a body that can panic and
//! `has_dtor`'s cut in `collect_structural_drop_adts` has been wrongly weakened.
//! Fix the rule, never this file.
pub struct Boom;
impl Drop for Boom {
    fn drop(&mut self) {
        panic!("boom");
    }
}
pub fn drops_a_panicker() -> usize {
    let v: Vec<Boom> = vec![Boom];
    v.len()
    //~^^^ ERROR Trust strict verification failed
}
