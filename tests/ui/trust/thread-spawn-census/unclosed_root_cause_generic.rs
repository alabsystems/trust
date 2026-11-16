//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:UnmodeledThreadSpawnEffect
//@ forbid-output:pools unclosed because
//@ forbid-output:root cause (SC-8)
//! SC-8 (c), docs/DECISION_QUEUE.md (2026-10-11): the generic twin of
//! `unclosed_root_cause_named.rs`. With `impl Fn(u32) -> bool` (R1/SC-3, the
//! remedy the root-cause note names) no `dyn` principal enters from out of sight,
//! the pools close, and the formatting path is QUIET: no row, no root-cause text.

#![allow(dead_code)]

pub fn any_alive(pids: &[u32], pid_alive: impl Fn(u32) -> bool) -> bool {
    pids.iter().any(|p| pid_alive(*p))
}

pub fn render(n: u32) -> String { format!("{n}") }
