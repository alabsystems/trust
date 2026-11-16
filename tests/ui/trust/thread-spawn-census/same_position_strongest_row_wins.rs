//@ revisions: spawning handoff quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[spawning] forbid-output:(via unmeasured_chain
//@[handoff] forbid-output:unmodeled (via unmeasured_taker
//! Spawn census: sites starting at the same source position are one row, and
//! the STRONGEST evidence wins (design 2026-09-29-spawn-census-by-construction
//! §5.5). Before W11 round 3 the dedupe kept whichever row came first, so a
//! position could say "no spawn was found" while its caller was told it
//! "transitively spawns" (review probes n4.rs / mask.rs, 2026-09-29).
//!
//! The UNKNOWN comes from `unmeasured`: polymorphic recursion makes its
//! instance set infinite, so an instance nested deeper than `recursion_limit`
//! is a sink (`polymorphic_recursion_is_unknown.rs`). Until P2 (2026-10-01) it
//! came from a drop glue walk that ran out of budget; the census has no budget
//! now.
//!
//! * `spawning`: in `unmeasured_chain().go()` the call `unmeasured_chain()` is
//!   an UNKNOWN and `.go()`, which starts at the same position, certainly runs
//!   a spawning method (S2): the position is one SPAWNS row, and the UNKNOWN
//!   row citing `unmeasured_chain` never appears there.
//! * `handoff`: `hand_off` hands a spawning fn item to a callee that never
//!   calls it and reaches the sink, so it is an UNKNOWN, never a spawn claim
//!   through `unmeasured_taker`. `masked` hands it to `helper`, which calls it:
//!   `helper::<fn() {launch}>` certainly runs `launch` (S2), so `masked` is a
//!   SPAWNS row. Until P2 a callable handed to a generic callee was an UNKNOWN
//!   whatever the callee did with it.
//! * `quiet` (a spawn-free `launch`): every UNKNOWN row stands.

#![allow(dead_code)]

#[cfg(not(quiet))]
fn launch() { //[spawning,handoff]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

fn unmeasured<T>(n: u32, t: T) { //~ NOTE not enumerated (no spawn was found)
    if n > 0 {
        unmeasured(n - 1, (t,));
        return;
    }
    drop(t);
}

#[cfg(not(handoff))]
pub struct Chain;
#[cfg(not(handoff))]
impl Chain {
    pub fn go(self) {
        launch()
    }
}

#[cfg(not(handoff))]
fn unmeasured_chain() -> Chain { //[spawning,quiet]~ NOTE not enumerated (no spawn was found)
    unmeasured(3, 0u8);
    Chain
}

#[cfg(not(handoff))]
pub fn chain_spawn_wins() { unmeasured_chain().go() }
//[spawning]~^ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
//[quiet]~^^ NOTE not enumerated (no spawn was found)

#[cfg(not(spawning))]
fn unmeasured_taker<F>(_f: F) { //[handoff,quiet]~ NOTE not enumerated (no spawn was found)
    unmeasured(3, 0u8)
}

#[cfg(not(spawning))]
pub fn hand_off() { unmeasured_taker(launch) }
//[handoff,quiet]~^ NOTE not enumerated (no spawn was found)

#[cfg(not(spawning))]
pub fn hand_off_caller() { hand_off() }
//[handoff,quiet]~^ NOTE not enumerated (no spawn was found)

// The callee calls what it is handed and reaches the sink.
#[cfg(not(spawning))]
fn helper<F: Fn()>(f: F) { //[handoff]~ NOTE local callee reaches a std thread spawn through calls and drops
    //[quiet]~^ NOTE not enumerated (no spawn was found)
    unmeasured(3, 0u8);
    f()
}
#[cfg(not(spawning))]
pub fn masked() { helper(launch) }
//[handoff]~^ NOTE local callee reaches a std thread spawn through calls and drops
//[quiet]~^^ NOTE not enumerated (no spawn was found)
