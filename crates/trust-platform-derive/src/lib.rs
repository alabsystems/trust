//! trust-platform-derive: the D-11(e) derivation at M1 scope (plan §2.3
//! D2/D3/D7) — an event program in, the `TyTemporalModelPayload`
//! NativeTyEngine checks out.
//!
//! # Pipeline
//!
//! 1. [`program`]: the event program — per body a CFG of platform events,
//!    local scalar statements and branches; spawn sites with their child-side
//!    programs (`pre_exec` closures); thread roots as concurrent event
//!    sources. Every statement carries its source location. It is what the
//!    THIR -> trust-ir census will produce; until the producer lowers the
//!    aterm-uds bodies, [`fixtures`] are written in it by hand.
//! 2. [`lower`]: std calls become their trust-platform summary rows' events
//!    (STD-PAIR, STD-SPAWN-FORK with std's error path, STD-SPAWN-POSIX —
//!    whichever std itself picks for the command), every name is joined with
//!    `trust_platform::symbols` (an unknown name is a named refusal), and
//!    each policy site's static `Declared` part is computed.
//! 3. [`partition`]: the points the program can tell descriptor numbers apart
//!    by — where RL-INIT places a foreign descriptor.
//! 4. [`mod@env`]: RL-INIT tables.
//! 5. [`interp`] + [`explore`]: explicit-state exploration AT THE REAL
//!    CONSTANTS in which every platform step is `trust_platform::step` (one
//!    definition, SD-9), torn table copies included.
//! 6. [`mod@derive`]: the D7 scalar encoding, the full machine, its
//!    bisimulation quotient (the `StateMachineMetadata` ty checks), the event
//!    map, and [`derive::Derived::payload`] (refutation-only, formula atoms
//!    vetted against the model's vocabulary).
//! 7. [`property`]: fd-inherit (and the fd-bound premise, per child) as
//!    state propositions and CTL; since M2 also P-LOCK-RELEASE (no lock of a
//!    released description outlives its owner's release point in another
//!    process) and fd-identity (every event on a descriptor number reaches
//!    the description its actor bound there).
//! 8. [`trace`]: a ty trace -> lifted to the full machine -> actions ->
//!    source events, and its re-execution with a per-step check.
//!
//! What the census needs on top (design 2026-10-01 §2.6, PR 6):
//!
//! * **X1** — values and guards the census could not track:
//!   [`program::Expr::Opaque`], checked by [`track`] (an untracked value
//!   that reaches an event operand, a guard or a loop bound is the named
//!   refusal [`lower::LowerError::Untracked`]); [`program::Cond::Nondet`],
//!   explored both ways as explicit choice steps by [`nondet`] and listed in
//!   every replay that takes one ([`trace::Replay::overapprox`]).
//! * **X6** — [`alpha::alpha_eq`]: equality of event programs up to
//!   numbering, class names and locations (the E4 twin check), M2's
//!   constructs included: release marks, thread start and join, std opens,
//!   the M2 policies, and whether a raw read/write carries the census's
//!   assumption (M2's `lower` admits it only with one).
//!
//! # What a verdict here means
//!
//! A `Failed` from NativeTyEngine on a derived machine, re-executed by
//! [`trace`], is a refutation graded below RF-M: the trace replays on the
//! Rust model (`trust_platform`, conformance-tested against Darwin), not on
//! a kernel-checked Clean model, and the event program was transcribed by
//! hand. There is no pass: the payload is refutation-only, so ty reports
//! "no counterexample" as `Unknown` (SD-8) — the RL-INIT enumeration, the
//! RL-FOREIGN stand-in and the SD-3 reduction are argued, not proved.
//!
//! A `Cond::Nondet` guard makes the model larger than the program (both
//! arms are explored whatever the program would compute), so a refutation
//! whose replay lists an over-approximating choice
//! ([`trace::Replay::overapprox`] non-empty) may follow a path the program
//! cannot take: it is not an error (Critique C-9, `PC-OVERAPPROX`), and as a
//! non-vacuity witness it does not show that the program reaches the exec.

pub mod alpha;
pub mod derive;
pub mod env;
pub mod explore;
pub mod fixtures;
pub mod interp;
pub mod lower;
pub mod nondet;
pub mod partition;
pub mod program;
pub mod property;
pub mod trace;
pub mod track;

pub use derive::{DeriveError, DeriveOptions, Derived, derive};
pub use property::{
    Premise, fd_identity_formula, fd_inherit_formula, lock_release_formula, non_vacuity_formula,
};

#[cfg(test)]
mod tests;
