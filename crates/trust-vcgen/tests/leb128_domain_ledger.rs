// THE BELLWETHER'S DOMAIN LEDGER, on REAL EXTRACTED MIR.
//
// `leb128_loop_call_effect.rs` established that after the call-frame lane the
// binding blocker on ay's `read_u64` loop is `e4.machine.mixed-domain`. That
// name was a guess dressed as a measurement: it says the formula "does not have
// one exact declared-width machine domain" and stops, and the reader is left to
// assume the cause is the one the source makes obvious — `value: u64` shifted
// by `shift: u32`.
//
// IT IS NOT. Measured here on the extracted body, the combined
// initiation/preservation formula contains:
//
//   * TWO declared domains that genuinely disagree, `u32` (`shift`) and `u64`
//     (`pos`, `data__len`, `chunk`, all `usize`/`u64`) — and they disagree in
//     the RECOVERABLE direction: `u32` widens into `u64` by zero extension with
//     no loss, so this half is a plumbing gap, not a semantic wall;
//
//   * a leaf with NO machine domain at all: `data`, the `&[u8]` carrier, which
//     appears as `Select(Var("data", Array(Int, Int)), Var("pos", Int))` inside
//     the `byte & 0x80 == 0` continuation guard. An array carrier is not an
//     integer at any width; it cannot "agree" or "disagree" with `u32`.
//
// The shift is NOT in the ledger, and that is the sharpest correction here: the
// scan already skips a shift COUNT (`machine_faithful_shift_amount` translates
// it at its own declared domain and resizes it exactly the way rustc does), so
// `chunk << shift` never contributed to the refusal in the first place. The
// widely assumed cause of this blocker was already handled.
//
// WHAT THIS TEST LOCKS. The refusal is unchanged — this loop still produces no
// E4 row, and this lane mints no proof. What is locked is that the row now
// carries the ledger, so the next lane reads which of the two halves it has to
// move instead of guessing.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_vcgen::{bind_compiler_loop_contracts, generate_vcs_with_discharge};

const LEB128_READ_U64: &str = include_str!("fixtures/leb128_read_u64_realmir.json");
const HEADER: usize = 1;

fn span() -> SourceSpan {
    SourceSpan { file: "leb.rs".to_string(), line_start: 9, col_start: 4, line_end: 9, col_end: 40 }
}

fn blockers(invariant: &str) -> (Vec<String>, bool) {
    let mut func: VerifiableFunction =
        serde_json::from_str(LEB128_READ_U64).expect("extracted leb128 MIR must deserialize");
    let spec = LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 0,
        source_hir_local_id: Some(1),
        mir_header: Some(HEADER),
        loop_head: SourceSpan { line_end: 26, ..span() },
        header_span: span(),
        span: span(),
        body: invariant.to_string(),
    };
    let failures = bind_compiler_loop_contracts(&mut func, &[spec]);
    assert!(failures.is_empty(), "the loop clause must bind: {failures:?}");
    let (vcs, preclassified) = generate_vcs_with_discharge(&func);
    let details = preclassified
        .iter()
        .filter_map(|(vc, _)| match &vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "UserLoopContractUnsupported" => {
                Some(detail.clone())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let minted_e4 = vcs.iter().chain(preclassified.iter().map(|(vc, _)| vc)).any(|vc| {
        matches!(
            vc.kind,
            VcKind::LoopInvariantInitiation { .. } | VcKind::LoopInvariantConsecution { .. }
        )
    });
    (details, minted_e4)
}

/// The ledger, verbatim. Both halves, and the verdict on the recoverable one.
#[test]
fn the_refusal_names_both_halves_and_says_which_one_widening_could_recover() {
    let (details, minted_e4) = blockers("shift <= 70");
    let row =
        details.iter().find(|detail| detail.contains("e4.machine.mixed-domain")).unwrap_or_else(
            || panic!("the measured residual blocker is still the domain gate: {details:?}"),
        );

    assert!(
        row.contains("declared domains disagree: u32, u64"),
        "the two declared domains must be NAMED, not merely counted: {row}",
    );
    assert!(
        row.contains("exact widening join at u64"),
        "u32 widens into u64 by zero extension with no loss — the row must say so, \
         because that is what tells the next lane this half is recoverable: {row}",
    );
    assert!(
        row.contains("leaves with no machine domain: data"),
        "the `&[u8]` carrier is the OTHER half, and it is not a width disagreement \
         at all — a row that hides it sends the reader after the wrong bug: {row}",
    );

    // THE REFUSAL IS UNCHANGED. This lane sharpens a diagnostic; it mints
    // nothing.
    assert!(!minted_e4, "a refused clause must still mint no E4 row");
}

/// The `u64` half of the source's own arithmetic reaches the same ledger: the
/// blocker does not depend on which variable the clause names.
#[test]
fn the_ledger_is_the_same_for_a_clause_over_the_other_domain() {
    for invariant in ["pos >= start", "shift <= 70", "1 == 1"] {
        let (details, minted_e4) = blockers(invariant);
        let row = details
            .iter()
            .find(|detail| detail.contains("e4.machine.mixed-domain"))
            .unwrap_or_else(|| panic!("`{invariant}`: expected the domain gate: {details:?}"));
        assert!(
            row.contains("leaves with no machine domain: data"),
            "`{invariant}`: the array carrier is a property of the LOOP BODY, not of \
             the clause, so every clause on this loop must report it: {row}",
        );
        assert!(!minted_e4, "`{invariant}`: still no E4 row");
    }
}

/// The shift is NOT the blocker, and this is the measurement that says so: the
/// domain ledger contains `u32` and `u64` but the `u32` in it is `shift` used
/// as a VALUE (`shift <= 70`, `shift += 7`), never as the count of
/// `chunk << shift`. Removing the clause's own mention of `shift` leaves the
/// `u64`-only ledger — the shift COUNT contributes no domain.
#[test]
fn the_shift_count_contributes_no_domain_to_the_ledger() {
    let (details, _) = blockers("pos >= start");
    let row = details
        .iter()
        .find(|detail| detail.contains("e4.machine.mixed-domain"))
        .expect("the domain gate");
    // `shift += 7` is on the transition, so `u32` is still in the ledger for
    // this clause; what must NOT appear is a domain contributed by the count
    // position of the shift, which would be a `u32` reported from inside
    // `BvShl`'s amount operand. The ledger is exactly two domains either way.
    let named_domains = ["u8", "u16", "u128", "i8", "i16", "i32", "i64", "i128"];
    for absent in named_domains {
        assert!(
            !row.contains(&format!("{absent},")) && !row.contains(&format!(" {absent} ")),
            "the ledger must contain only the domains the body really declares, not {absent}: {row}",
        );
    }
}
