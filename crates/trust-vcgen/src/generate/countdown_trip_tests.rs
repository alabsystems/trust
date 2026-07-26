use super::*;

fn load(fixture: &str) -> VerifiableFunction {
    serde_json::from_str(fixture).expect("fixture MIR must deserialize")
}

fn fact_strings(func: &VerifiableFunction) -> Vec<String> {
    build_countdown_trip_facts(func).iter().map(|f| format!("{f:?}")).collect()
}

/// The DOWNWARD-INDUCTION fact family for the same function — the `Le`
/// upper-bound lane whose underflow-free gate rides the countdown `Ge`s.
/// Every countdown trap must silence BOTH families: a surviving
/// `Le(result, B - c)` would conjoin onto the mutant's own underflow VC.
fn downward_strings(func: &VerifiableFunction) -> Vec<String> {
    build_downward_induction_facts(func).iter().map(|f| format!("{f:?}")).collect()
}

// ------------------------------------------------ the T / K(v) tables

#[test]
fn trip_count_table_is_exactly_tight() {
    let d = 10_000u128;
    // u8: M = 255 <= C = 999 — the body is unreachable; T = 0 emits NOTHING.
    assert_eq!(countdown_trip_count(u8::MAX as u128, d, 999), 0);
    assert_eq!(countdown_trip_count(u16::MAX as u128, d, 999), 1);
    assert_eq!(countdown_trip_count(u32::MAX as u128, d, 999), 2);
    // u64::MAX = 18446744073709551615 (20 digits) runs the quad loop EXACTLY
    // 5 times (offsets 16, 12, 8, 4, 0). A T = 4 derivation is WRONG and
    // mints a false proof for a 16-byte buffer.
    assert_eq!(countdown_trip_count(u64::MAX as u128, d, 999), 5);
    // u128::MAX has 39 digits; each trip strips 4: trips run at 39, 35, ...,
    // 7 digits (all > 999) and the 9th division leaves 3 digits — EXACTLY 9.
    assert_eq!(countdown_trip_count(u128::MAX, d, 999), 9);
    // The wrong-divisor trap: D = 10 gives 17 trips (20 digits -> 3 digits).
    assert_eq!(countdown_trip_count(u64::MAX as u128, 10, 999), 17);
    // Degenerate guard C = 0: every division until zero.
    assert_eq!(countdown_trip_count(u8::MAX as u128, 2, 0), 8);
}

#[test]
fn k_max_table_is_exactly_tight() {
    let d = 10_000u128;
    assert_eq!(countdown_k_max(u64::MAX as u128, d, 1, 10), Some(4));
    assert_eq!(countdown_k_max(u64::MAX as u128, d, 1, 1), Some(4));
    assert_eq!(countdown_k_max(u64::MAX as u128, d, 100, 1), Some(4));
    assert_eq!(countdown_k_max(u32::MAX as u128, d, 1, 10), Some(2));
    // The reseat tightening: `remain /= 100` between exit and the guard
    // multiplies R, dropping K(1) from 2 to 1 for u32.
    assert_eq!(countdown_k_max(u32::MAX as u128, d, 100, 1), Some(1));
    assert_eq!(countdown_k_max(u32::MAX as u128, d, 1, 1), Some(2));
    // Infeasible guard: x >= v cannot hold — the path never executes.
    assert_eq!(countdown_k_max(u8::MAX as u128, d, 1, 1000), None);
    assert_eq!(countdown_k_max(u32::MAX as u128, d, u128::MAX, 1), None);
}

// ------------------------------------------------ WIN shapes (facts fire)

#[test]
fn fmt_u32_emits_the_three_exactly_tight_site_bounds() {
    // LEN 10, c_loop 4, D 10^4, C 999 => T = 2:
    //   loop `-=4`:  _t.0 >= 10 - 8            = 2
    //   post `-=2`:  K(10) = 2 => 10 - 8 - 2   = 0   (exactly tight)
    //   post `-=1`:  min over exit paths       = 1   (reseat + zero-trip)
    let func = load(include_str!("../../tests/fixtures/countdown_fmt_u32_mir.json"));
    let facts = fact_strings(&func);
    assert_eq!(facts.len(), 3, "exactly one fact per decrement site: {facts:?}");
    assert!(facts.iter().all(|f| f.starts_with("Ge(Var(\"_") && f.contains(".0\"")));
    let mut bounds: Vec<i128> = build_countdown_trip_facts(&func)
        .iter()
        .map(|f| match f {
            Formula::Ge(_, b) => match b.as_ref() {
                Formula::Int(n) => *n,
                other => panic!("non-constant countdown bound: {other:?}"),
            },
            other => panic!("non-Ge countdown fact: {other:?}"),
        })
        .collect();
    bounds.sort_unstable();
    assert_eq!(bounds, vec![0, 1, 2]);
}

#[test]
fn fmt_u64_loop_bound_is_exactly_zero() {
    // LEN 20, T = 5: the loop-site bound is EXACTLY 0 — u64::MAX consumes
    // the buffer to offset 0. Post sites: `-=2` -> 2, `-=1` -> 1.
    let func = load(include_str!("../../tests/fixtures/countdown_fmt_u64_mir.json"));
    let mut bounds: Vec<i128> = build_countdown_trip_facts(&func)
        .iter()
        .map(|f| match f {
            Formula::Ge(_, b) => match b.as_ref() {
                Formula::Int(n) => *n,
                other => panic!("non-constant countdown bound: {other:?}"),
            },
            other => panic!("non-Ge countdown fact: {other:?}"),
        })
        .collect();
    bounds.sort_unstable();
    assert_eq!(bounds, vec![0, 1, 2]);
}

#[test]
fn fmt_u32_macro_resolves_consts_through_b0_expect() {
    // The itoa macro spelling: guard `remain > 999.try_into().expect(..)`,
    // divisor `let scale: u32 = 1_00_00.try_into().expect(..)`. B0 resolves
    // both; the same three bounds must fire.
    let func = load(include_str!("../../tests/fixtures/countdown_fmt_u32_macro_mir.json"));
    let consts: Vec<i128> = {
        let mut v: Vec<i128> = expect_infallible_const_map(&func).values().copied().collect();
        v.sort_unstable();
        v
    };
    assert_eq!(consts, vec![999, 10_000], "B0 must pin both expect destinations");
    let mut bounds: Vec<i128> = build_countdown_trip_facts(&func)
        .iter()
        .map(|f| match f {
            Formula::Ge(_, b) => match b.as_ref() {
                Formula::Int(n) => *n,
                other => panic!("non-constant countdown bound: {other:?}"),
            },
            other => panic!("non-Ge countdown fact: {other:?}"),
        })
        .collect();
    bounds.sort_unstable();
    assert_eq!(bounds, vec![0, 1, 2]);
}

// ------------------------------------------------ traps (every gate bails)

#[test]
fn short_buffer_emits_nothing_exactly_tight() {
    // LEN 19, T = 5: 19 - 20 < 0 — the REAL underflow at n = u64::MAX. Any
    // fact here is a false proof.
    let func = load(include_str!("../../tests/fixtures/countdown_short_buffer_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(downward_strings(&func).is_empty(), "{:?}", downward_strings(&func));
}

#[test]
fn wrong_stride_emits_nothing() {
    // c = 5: 20 - 25 < 0.
    let func = load(include_str!("../../tests/fixtures/countdown_wrong_stride_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(downward_strings(&func).is_empty(), "{:?}", downward_strings(&func));
}

#[test]
fn wrong_divisor_emits_nothing() {
    // D = 10: T = 17, 20 - 68 < 0.
    let func = load(include_str!("../../tests/fixtures/countdown_wrong_divisor_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(downward_strings(&func).is_empty(), "{:?}", downward_strings(&func));
}

#[test]
fn conditional_division_emits_nothing() {
    // `if flag { remain /= D }` — THE unbounded-trip false-proof trap
    // (gate 6: the division must be unavoidable on every body path).
    let func = load(include_str!("../../tests/fixtures/countdown_conditional_div_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(downward_strings(&func).is_empty(), "{:?}", downward_strings(&func));
}

#[test]
fn companion_reinflate_emits_nothing() {
    // An in-loop non-division def of the companion re-inflates x (gate 5).
    let func = load(include_str!("../../tests/fixtures/countdown_companion_reinflate_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(downward_strings(&func).is_empty(), "{:?}", downward_strings(&func));
}

#[test]
fn cursor_reseat_kills_countdown_and_downward_facts() {
    // `bump(&mut offset)` mid-loop: the `local_mut_escapes` P0 fix — BOTH
    // the countdown facts and the pre-existing downward-induction facts
    // must vanish (the latter falsely proved `s[i]` before the fix).
    let func = load(include_str!("../../tests/fixtures/countdown_cursor_reseat_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(
        build_downward_induction_facts(&func).is_empty(),
        "a mut-escaped cursor must not carry downward-induction facts"
    );
}

#[test]
fn guard_on_other_variable_emits_nothing() {
    // `while other > 999 { .. remain /= D .. }` — the guarded variable is
    // never divided (no in-loop division of `other`), so trips are unbounded.
    let func = load(include_str!("../../tests/fixtures/countdown_guard_other_var_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(downward_strings(&func).is_empty(), "{:?}", downward_strings(&func));
}

#[test]
fn division_by_one_emits_nothing() {
    // D = 1 never shrinks x — rejected BEFORE simulating (which also keeps
    // the analyzer's own T loop terminating). The fixture spells the
    // divisor as a VARIABLE (`let step = 1u64; remain /= step`):
    // `countdown_resolve_const` must chase the SSA copy chain to the 1 and
    // the D >= 2 gate must reject it — an unresolved variable divisor is
    // equally NOT a division fact (fail closed), never a default D.
    let func = load(include_str!("../../tests/fixtures/countdown_div_by_one_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(downward_strings(&func).is_empty(), "{:?}", downward_strings(&func));
}

#[test]
fn two_on_cycle_decrements_emit_nothing() {
    // A second on-cycle `offset -= 1` under-counts the per-trip stride.
    let func = load(include_str!("../../tests/fixtures/countdown_two_decrements_mir.json"));
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
    assert!(downward_strings(&func).is_empty(), "{:?}", downward_strings(&func));
}

#[test]
fn two_digit_short_post_loop_site_gets_no_fact() {
    // B3 exact tightness (mutant countdown_two_digit_short): u32 with a
    // 9-byte buffer. The LOOP site is genuinely safe — T = 2, so the
    // `-=4` result `_9.0 >= 9 - 4*2 = 1` (and the downward upper bound
    // `_9.0 <= 9 - 4 = 5`) both fire. The POST-LOOP `-=2` site `_18` is
    // the REAL bug (u32::MAX exits the loop at offset 1; 1 - 2 wraps):
    // K(10) = 2 gives 9 - 8 - 2 = -1 < 0, so NEITHER family may say
    // anything about `_18.0` — its underflow VC must stay live.
    let func = load(include_str!("../../tests/fixtures/countdown_two_digit_short_mir.json"));
    let facts = fact_strings(&func);
    assert_eq!(facts, vec!["Ge(Var(\"_9.0\", Int), Int(1))".to_string()], "{facts:?}");
    let downward = downward_strings(&func);
    assert_eq!(downward, vec!["Le(Var(\"_9.0\", Int), Int(5))".to_string()], "{downward:?}");
}

#[test]
fn two_conjunct_guard_falls_through_to_the_countdown_companion() {
    // The REAL itoa loop condition is `mem::size_of::<Self>() > 1 &&
    // remain > limit` — TWO chained boolean switches that both dominate
    // the decrement. The first candidate's "companion" is a CALL DEST
    // (gate 5 rejects it); the analysis must fall through to the `remain`
    // switch instead of bailing the family (the first cut bailed: every
    // real-itoa SUB row stayed failed while the IOB rows proved).
    let func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/countdown_two_conjunct_guard_mir.json"
    ))
    .unwrap();
    let bounds: Vec<i128> = build_countdown_trip_facts(&func)
        .iter()
        .map(|f| match f {
            Formula::Ge(_, b) => match b.as_ref() {
                Formula::Int(n) => *n,
                other => panic!("non-constant countdown bound: {other:?}"),
            },
            other => panic!("non-Ge countdown fact: {other:?}"),
        })
        .collect();
    // u32, D=10^4, C=999 => T=2; LEN 10 => loop-site bound 10 - 8 = 2.
    assert_eq!(bounds, vec![2], "{bounds:?}");
}

#[test]
fn negative_constant_bounds_are_never_emitted() {
    // The fuzzer-caught FALSE-PROOF pin (sr_countdown[u16;N=3;short]): u16
    // companion, stride 4, buffer 3. B - c = -1 — a negative constant Le
    // fact collides with the VC lane's `result >= 0` type range into an
    // UNSAT premise set (everything vacuously proved, underflow included).
    // BOTH fact families must emit NOTHING here.
    let func: VerifiableFunction =
        serde_json::from_str(include_str!("../../tests/fixtures/countdown_u16_short_mir.json"))
            .unwrap();
    for f in build_downward_induction_facts(&func) {
        let s = format!("{f:?}");
        assert!(!s.contains("Int(-"), "negative-constant downward fact: {s}");
    }
    assert!(
        build_countdown_trip_facts(&func).is_empty(),
        "{:?}",
        build_countdown_trip_facts(&func)
    );
}

#[test]
fn b0_expect_const_global_facts_pin_both_destinations() {
    // The GLOBAL value lane (`build_expect_const_facts`): `_9 == 999` and
    // `scale == 10000` — the loop-body remzero/divzero discharge channel
    // (the versioned call-dest lane cannot cross the loop-head join).
    let func: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/countdown_fmt_u32_macro_mir.json"
    ))
    .unwrap();
    let facts: Vec<String> =
        build_expect_const_facts(&func).iter().map(|f| format!("{f:?}")).collect();
    assert_eq!(facts.len(), 2, "{facts:?}");
    assert!(facts.iter().any(|f| f.contains("Int(999)")), "{facts:?}");
    assert!(facts.iter().any(|f| f.contains("Int(10000)")), "{facts:?}");
    // The unfitting u8 twin pins nothing in this lane either.
    let func_u8: VerifiableFunction = serde_json::from_str(include_str!(
        "../../tests/fixtures/countdown_b0_u8_overflow_mir.json"
    ))
    .unwrap();
    assert!(build_expect_const_facts(&func_u8).is_empty());
}

#[test]
fn b0_unfitting_const_pins_nothing() {
    // `999.try_into().expect(..)` into u8 FAILS the width-exact range check:
    // the expect genuinely panics if reached — no value fact, no suppression.
    let func = load(include_str!("../../tests/fixtures/countdown_b0_u8_overflow_mir.json"));
    assert!(
        expect_infallible_const_map(&func).is_empty(),
        "999 must not be modeled as fitting u8"
    );
    assert!(fact_strings(&func).is_empty(), "{:?}", fact_strings(&func));
}
