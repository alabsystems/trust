//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@ edition: 2021
//@ dont-check-compiler-stderr
//@ check-pass
#![crate_type = "lib"]
//! A loop's EXIT block must not inherit the bindings its BODY made.
//!
//! `lower_loop` step 8 opens the exit block and rebinds every CARRIED local to its exit
//! param — and leaves every other binding the body made sitting in `self.locals`. A
//! `let` inside the body is such a binding, and its value lives in a body block that does
//! not dominate the exit (the exit is reached from the header's break edge, never from
//! the body's tail). Rust's own scoping says the local is dead at the exit; the producer's
//! environment says it is live, bound to a value that is out of scope there.
//!
//! Nothing reads it — until a JOIN downstream captures the exit block as an arm. The
//! `for`-desugar's inner `if let Some(k) = next()` has exactly ONE reaching arm (the
//! `None` arm always `break`s), so `merged_locals`' wave-UI rule — a local with no
//! pre-split binding that EVERY reaching arm binds is carried as a dead join param —
//! carries the leaked local, and `seal_arm_into_join` emits, IN THE EXIT BLOCK,
//!
//!     br join(.., %leaked)      ; %leaked defined in a block that does not dominate here
//!
//! which `validate_module` reports as `UseBeforeDefInBlock { value: %leaked, block: exit }`
//! — one row per leaked `let` (two `let`s, two rows). Measured on the sealed toolchain
//! trust-11aae56c: ay's `ay_brancher::regret_simulation::{adversarial_trace,dominant_trace}`
//! fail with exactly this, and every face below fails; with the fix all compile.
//!
//! It is NOT nesting-specific and NOT `for`-specific: any single-reaching-arm join whose
//! reaching arm ENDS at a loop exit sees it (`if c { for .. } else { return }`, and the
//! `while` twin). Nested `for` is merely the shape where the enclosing join ALWAYS has one
//! reaching arm. The opaque-carrier mutation in each face was load-bearing only in that it
//! REFUSED the wave-ER foreach summary, so the loop took the real CFG lane where the leak
//! exists. That summary was removed on 2026-10-01 (it erased loops it could not see into —
//! tests/run-make/trust-for-loop-no-erasure), so `summary_control` now takes the real CFG
//! lane too and pins the same property for a scalar-only body.
//!
//! THE FLAG POSTURE IS LOAD-BEARING, as for #189: keep `-Ztrust-verify=off
//! -Ztrust-ir-lower=on`. (Here the minimal case is NOT masked under `-Ztrust-verify=on
//! -Ztrust-policy=advisory` either — measured — but the off/on lane is the one that
//! validates the module unconditionally.)
//!
//! STATUS ON MAIN (2026-09-24). This file was written with a fix on the seal line
//! (6a51d6d5dc: `lower_loop` snapshots the binding environment at loop entry and RESTORES
//! it before opening the exit). That fix was never carried to main, and main no longer
//! needs it: every face below lowers with no finalization warning on the sealed
//! `trust-7d5533b2` (main as of 2026-09-23), measured with this exact file under the flag
//! posture above. The file lands WITHOUT the fix, as the regression pin the class never
//! had on main: whatever closed it there, a producer change that re-opens it trips here.
//! The failure mode to expect is the spanless `semantic finalization failed ...
//! [UseBeforeDefInBlock]` WARN, which fails this test because the
//! `dont-require-annotations: WARN` waiver is deliberately absent.
//!
//! RE-OPENED AND FIXED ON MAIN (2026-10-01). Removing the wave-ER for-loop summary sent
//! `summary_control`'s scalar range loop down the real CFG lane, and it tripped exactly this:
//! `UseBeforeDefInBlock { value: 20, block: 5 }` (and `escaped_local_for_loop_iterator_still_
//! proves.rs` failed the same way, a hard error under the strict policy). The opaque-carrier
//! faces had stopped reaching the leak; the range lane had not. `lower_loop` now drops, when it
//! opens the exit, every binding of a local that had none before the loop — the seal-line fix's
//! effect, narrowed so a pre-loop local keeps its latest binding.

// ── faces: each failed `UseBeforeDefInBlock` on seal trust-11aae56c (2026-09-07) ─────

/// The ay shape (`regret_simulation::dominant_trace`): nested `for`, a let-bound join in
/// the inner body, and an opaque carrier pushed there.
pub fn nested_for_face(n: usize, rounds: usize, high: f64, low: f64) -> Vec<f64> {
    let mut v = Vec::new();
    for _ in 0..rounds {
        for k in 0..n {
            let reward = if k == 0 { high } else { low };
            v.push(reward);
        }
    }
    v
}

/// The join is not needed: a plain `let` leaks the same way.
pub fn plain_let_face(n: usize, rounds: usize) -> Vec<f64> {
    let mut v = Vec::new();
    for _ in 0..rounds {
        for k in 0..n {
            let r = k + 1;
            v.push(r as f64);
        }
    }
    v
}

/// Nesting is not needed: any single-reaching-arm join whose arm ends at a loop exit.
pub fn if_arm_face(n: usize, c: bool) -> Vec<f64> {
    let mut v = Vec::new();
    if c {
        for k in 0..n {
            let r = k + 1;
            v.push(r as f64);
        }
    } else {
        return v;
    }
    v
}

/// `for` is not needed: the `while` twin leaks at its exit identically.
pub fn while_face(n: usize, c: bool) -> Vec<f64> {
    let mut v = Vec::new();
    if c {
        let mut k = 0;
        while k < n {
            let r = k + 1;
            v.push(r as f64);
            k += 1;
        }
    } else {
        return v;
    }
    v
}

/// Not `Vec`-specific: `String` is an opaque carrier too.
pub fn string_face(n: usize, rounds: usize) -> String {
    let mut s = String::new();
    for _ in 0..rounds {
        for k in 0..n {
            let c = if k == 0 { 0x61u8 } else { 0x62u8 };
            s.push(c as char);
        }
    }
    s
}

// ── negative controls: these lower today and must keep lowering ─────────────────────

/// No `let` in the inner body: nothing leaks, nothing is carried.
pub fn no_let_control(n: usize, rounds: usize) -> Vec<f64> {
    let mut v = Vec::new();
    for _ in 0..rounds {
        for k in 0..n {
            v.push(k as f64);
        }
    }
    v
}

/// Both arms reach the join: a local bound in only one arm is never carried.
pub fn both_arms_reach_control(n: usize, c: bool) -> Vec<f64> {
    let mut v = Vec::new();
    if c {
        for k in 0..n {
            let r = k + 1;
            v.push(r as f64);
        }
    } else {
        v.push(0.0);
    }
    v
}

/// A join AFTER the loop sees the leaked local as pre-split, unchanged: not merged.
pub fn after_loop_control(n: usize, c: bool) -> Vec<f64> {
    let mut v = Vec::new();
    for k in 0..n {
        let r = k + 1;
        v.push(r as f64);
    }
    if c {
        v.push(1.0);
    }
    v
}

/// Scalar-only body: until 2026-10-01 the wave-ER foreach summary erased this loop, so no loop
/// CFG existed; it now takes the faithful range lane (a real loop and its exit join).
pub fn summary_control(n: usize, c: bool) -> u32 {
    let mut acc = 0u32;
    if c {
        for k in 0..n {
            let r = k as u32 + 1;
            acc = acc.wrapping_add(r);
        }
    } else {
        return 0;
    }
    acc
}
