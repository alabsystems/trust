//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! NEGATIVE CONTROL for `memory_safe/reject_closure_driving_consumer_dep_reach.rs`.
//! A closure-driving consumer over foundational types reaches no user code, so under
//! the default policy its (now counted) may-panic row stays a REPORTED gap and the
//! crate keeps building. Measured on stage-1 436c9eb6d0 (before the carrier) and after.
pub fn count_slice(v: &[u32]) -> usize {
    v.iter().count()
}

pub fn default_u32(o: Option<u32>) -> u32 {
    o.unwrap_or_default()
}

pub fn map_local_closure_collect(v: &[u32]) -> Vec<u64> {
    v.iter().map(|x| *x as u64).collect()
}
