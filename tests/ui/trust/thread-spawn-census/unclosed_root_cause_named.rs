//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SC-8 (c), docs/DECISION_QUEUE.md (2026-10-11): disclosure only. A `pub fn` taking
//! `&dyn Fn(u32) -> bool` names a principal whose values only ENTER from out of sight
//! (a downstream caller's argument) and that no vtable here joins, so it is open; one
//! open principal leaves every pool unclosed (SC-5 (b)), and every function that
//! reaches an indirect call (here, `format!`'s `dyn fmt::Write`) is UNKNOWN. The rows
//! stay UNKNOWN; each one the unclosed flag decides now names the principal and the
//! node that first named it, and refers to the one crate-level root-cause note.
//! Shape: a3d-wire `sock::stale_instance_files(.., pid_alive: &dyn Fn(u32) -> bool)`.
//! Twin: `unclosed_root_cause_generic.rs` (`impl Fn`, the pool closes).

#![allow(dead_code)]

pub fn any_alive(pids: &[u32], pid_alive: &dyn Fn(u32) -> bool) -> bool {
    //~^ NOTE [pools unclosed because: open principal `dyn std::ops::Fn(u32) -> bool` @ any_alive, its values entering from out of sight; see the crate's SC-8 root-cause note]
    pids.iter().any(|p| pid_alive(*p))
}

pub fn render(n: u32) -> String { format!("{n}") }
//~^ NOTE an indirect call whose pool is not closed) [pools unclosed because: open principal `dyn std::ops::Fn(u32) -> bool` @ any_alive, its values entering from out of sight; see the crate's SC-8 root-cause note]

//~? NOTE spawn census root cause (SC-8): pools unclosed because: open principal `dyn std::ops::Fn(u32) -> bool` @ any_alive, its values entering from out of sight. Every indirect call's pool stays open while any of these holds (SC-5 (b))
