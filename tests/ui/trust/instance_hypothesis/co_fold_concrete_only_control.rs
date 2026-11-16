//~ NOTE "proved":0,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":1,"cached":0,"total":2}
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! Control for `co_fold_open_dispatch_stays_failed.rs`: the per-fold-site decision
//! adds a refutation only where an open dispatch is co-folded. A body whose only
//! absent callee is the concrete `Vec::<u32>::push` keeps its `runtime_checked`
//! row (stage-1 `fbe76cb938`, unchanged by the fix).
pub fn concrete_only(v: &mut Vec<u32>) {
    v.push(1);
}
