//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ edition: 2024
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! The MUTANT of `tool_attr_matches_native.rs`: aterm's grid wedge with the
//! reset deleted (`abort_reflow_offload` without
//! `scrollback_detached_for_reflow = false`), stated once natively and once
//! on the `trust` tool surface. Neither may prove, and the two must agree.
//! Without `-Ztrust-policy=advisory` both fail the build.
//!
//! Both are REFUTED: trust-mc's counterexample (entry `detached = true`) now reaches
//! the report. Until the typed-CHC grounding counted a `&mut` pointee's entry value
//! as a function input (`typed_chc_entry_input_names`,
//! `compiler/rustc_mir_transform/src/trust_verify.rs`), the refutation was demoted
//! and both rows read `0 proved, 0 failed, 2 unknown` (measured on seal `321aaeda7`
//! and on main, 2026-09-29).
//!
//! Each exit arm now publishes its own postcondition row: the early-return arm — taken
//! only when `detached` is already false, so the postcondition already holds — proves
//! (kernel-certified), while the fallthrough and whole-function rows still refute. The
//! counts therefore read `1 proved, 2 failed`; neither function proves.

pub struct Storage {
    pub detached: bool,
}

pub struct Window {
    pub storage: Storage,
}

impl Window {
    pub fn abort_native(&mut self) //~ NOTE Trust verification: 1 proved, 2 failed, 0 unknown
        ensures !self.storage.detached
    {
        if !self.storage.detached {
            return;
        }
        // MUTANT: `self.storage.detached = false;` deleted.
    }

    #[trust::ensures(!self.storage.detached)]
    pub fn abort_tool(&mut self) { //~ NOTE Trust verification: 1 proved, 2 failed, 0 unknown
        if !self.storage.detached {
            return;
        }
        // MUTANT: `self.storage.detached = false;` deleted.
    }
}
