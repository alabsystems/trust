// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§R3b ACCEPTANCE EVIDENCE — the values the emitted `gcd` is checked
//! against, decided at the REAL kernel, each with a refuting control.**
//!
//! Promoted from a probe on 2026-08-27. Every row it used to print it now
//! ASSERTS, because the rows are what `tests/ui/trust/clean_origin_wf_rec_gcd.rs`
//! rests on: that fixture runs the EMITTED binary and compares it to these
//! literals, so a literal that is not itself a kernel decision would make the
//! fixture a tautology about two copies of the same guess.
//!
//! # THE ONE THING THIS FILE MAY NOT BE READ AS SAYING
//!
//! It does not say `gcd` is PROVED correct. `n1` measures that `Nat.gcd` is
//! ABSENT from the prelude, so there is no prelude gcd to state agreement with
//! and no correctness theorem is available to state at all. What is decided
//! here is that specific closed applications of `gcdF` reduce to specific
//! numerals — nine of them, plus tight-fuel rows, plus the five the fixture
//! uses — and that the wrong numerals do NOT. That is an acceptance table with
//! controls, exactly as the shipped `addAcc`/`dbl`/`fact` fixtures use, and it
//! is the honest ceiling of this increment.
//!
//! The fuel-sufficiency fact — any `f >= a + 2b` returns `gcd a b`, because
//! `a + 2b` strictly decreases by `b` on every non-fixed step and the only
//! fixed points are `(g, 0)` — is TRUE and is measured at both ends by `n3`.
//! It is not proved. A later increment can close that with a Clean theorem.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Name};

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|o| o.errors.iter().map(|e| e.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|c| c.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(220).collect()
}

const GCD_FUEL: &str = "def gcdF (f a b : Nat) : Nat := \
                        if h : 0 < f then gcdF (f - 1) ((a - b) + (b - a)) (a - (a - b)) else a\n\
                        termination_by f";

const WRAPPER: &str = "def gcd2 (a b : Nat) : Nat := gcdF (a + b + b) a b";

/// **WHY THE ACCEPTANCE ROWS ARE LITERALS.** If the prelude carried a `gcd`,
/// every row below could be stated against IT (`gcd2 12 18 = Nat.gcd 12 18`)
/// and would then be a claim about agreement with a definition somebody else
/// wrote, which is much stronger than agreement with a numeral. It does not.
/// Recorded as an assertion rather than a comment so that the day the prelude
/// GAINS one, this fails and the acceptance table gets upgraded instead of
/// quietly staying weaker than it needs to be.
#[test]
fn n1_the_prelude_has_no_gcd_to_state_correctness_against() {
    let env = island("def unit : Nat := 0").expect("trivial island");
    for name in ["Nat.gcd", "Nat.gcdAux", "gcd"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` is now in the prelude. The acceptance rows in this file and in \
             `tests/ui/trust/clean_origin_wf_rec_gcd.rs` are hand-computed literals BECAUSE \
             there was nothing to compare against; state them against `{name}` instead, and \
             say so in the fixture's header, which currently claims this absence."
        );
    }
}

/// The closed values, through the two-argument Clean wrapper `gcd2`, at the
/// kernel. The refuting controls below are what make the admits DECISIONS: a
/// kernel that admitted `gcd2 12 18 = 3` would admit anything.
#[test]
fn n2_closed_values_through_the_wrapper() {
    for (a, b, want) in [
        (0_u32, 0_u32, 0_u32),
        (5, 0, 5),
        (0, 5, 5),
        (1, 1, 1),
        (6, 6, 6),
        (7, 13, 1),
        (12, 18, 6),
        (18, 12, 6),
        (48, 18, 6),
    ] {
        let src = format!("{GCD_FUEL}\n{WRAPPER}\ntheorem v : gcd2 {a} {b} = {want} := rfl");
        assert!(
            island(&src).is_ok(),
            "the KERNEL must reduce `gcd2 {a} {b}` to `{want}`: {}",
            island(&src).err().map_or_else(String::new, |why| first_line(&why))
        );
        assert_eq!(want, gcd(a, b), "…and `{want}` must be the real gcd of {a} and {b}");
    }
    for (a, b, wrong) in [(7_u32, 13_u32, 7_u32), (48, 18, 18), (12, 18, 3)] {
        let src = format!("{GCD_FUEL}\n{WRAPPER}\ntheorem v : gcd2 {a} {b} = {wrong} := rfl");
        assert!(
            island(&src).is_err(),
            "CONTROL: `gcd2 {a} {b} = {wrong}` is FALSE and the kernel must refuse it — if it \
             admits, the rows above are not decisions"
        );
    }
}

/// Does the fuel bound `a + b + b` hold at every input, or only at the ones
/// above? The step map's fixed point is `(g, 0)`, and `a + 2b` strictly
/// decreases by `b` per step while `b > 0` — so `a + 2b` steps always suffice.
/// This row asks the kernel the same question at the TIGHT end: exactly enough
/// fuel, and one less.
#[test]
fn n3_the_fuel_bound_is_tight_enough() {
    for (a, b) in [(1_u32, 7_u32), (7, 1), (12, 18), (13, 5)] {
        let exact = a + b + b;
        for fuel in [exact, exact + 1] {
            let want = gcd(a, b);
            let src = format!("{GCD_FUEL}\ntheorem v : gcdF {fuel} {a} {b} = {want} := rfl");
            assert!(
                island(&src).is_ok(),
                "fuel {fuel} must already suffice for ({a}, {b}) -> {want}; the bound claimed \
                 in this file's header is `a + 2b`, and this row is its TIGHT end"
            );
        }
        // …and one BELOW the bound must not be assumed to work. Recorded as a
        // measurement rather than a claim: for these inputs the map reaches its
        // fixed point early, so short fuel may still be enough. What must never
        // happen is a fixture row resting on fuel nobody measured.
        let short = a + b + b - 1;
        let want = gcd(a, b);
        let src = format!("{GCD_FUEL}\ntheorem v : gcdF {short} {a} {b} = {want} := rfl");
        eprintln!(
            "ROW n3 short fuel={short:>3} ({a},{b}) -> {want} | {}",
            if island(&src).is_ok() { "still admits (fixed point reached early)" } else { "REFUSED" }
        );
    }
}

const fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
/// **THE FIXTURE'S OWN FIVE ROWS**, decided here so that
/// `tests/ui/trust/clean_origin_wf_rec_gcd.rs` is comparing the emitted binary
/// against kernel decisions rather than against my arithmetic. `270 192` is the
/// large one — 654 units of fuel, so 654 emitted frames — and it is included
/// precisely because a shallow row cannot distinguish a working recursion from
/// one that returns its argument.
#[test]
fn n4_the_run_pass_fixture_rows_are_kernel_decisions() {
    for (a, b, want) in [(12_u32, 18_u32, 6_u32), (270, 192, 6), (7, 13, 1), (0, 5, 5), (5, 0, 5)] {
        assert_eq!(want, gcd(a, b), "the fixture's expected value must be the real gcd");
        let src = format!("{GCD_FUEL}\n{WRAPPER}\ntheorem v : gcd2 {a} {b} = {want} := rfl");
        assert!(
            island(&src).is_ok(),
            "the KERNEL must reduce `gcd2 {a} {b}` to `{want}` — this is the row the run-pass \
             fixture asserts about the EMITTED binary: {}",
            island(&src).err().map_or_else(String::new, |why| first_line(&why))
        );
    }
    for (a, b, wrong) in [(270_u32, 192_u32, 2_u32), (270, 192, 12), (12, 18, 18), (7, 13, 7)] {
        let src = format!("{GCD_FUEL}\n{WRAPPER}\ntheorem v : gcd2 {a} {b} = {wrong} := rfl");
        assert!(
            island(&src).is_err(),
            "CONTROL: `gcd2 {a} {b} = {wrong}` must be REFUSED. `{wrong}` is a DIVISOR of \
             both (or one of the inputs) in every row here, so a body that returned a common \
             divisor rather than the GREATEST one would pass the admits and fail here"
        );
    }
}
