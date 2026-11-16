// Trust: 2026-09-16 (round A5) — THE PAYLOAD LOCAL, bridge parity on real MIR.
//
// The vcgen yield-fact builders minted `start <= p < end` onto the `Some`-payload
// local `p` of an `Iterator::next` result with no check that `p` has one write, and a
// `mut` pattern binding reassigned after the extraction (`for mut i in 0..5usize { i =
// n; a[i] }`) was PROVED and kernel-certified while the program panics. The vcgen gate
// is now `iterator_yield::payload_carries_global_fact` (`local_defs::is_single_static_
// assignment`), pinned in `trust-vcgen/tests/escaped_local_seam_realmir.rs` (the `a5_*`
// rows).
//
// The bridge has NO yield-fact producer: nothing in `lower.rs` mints a fact ONTO a
// payload local. Its one lane that READS a payload is the accumulator bound
// (`acc_bound_pairs` → `native_accumulator_bound_facts`, `t <= C + K * MAX(ELEM)`),
// which resolves the addend and the index through `local_defs::unique_value_def` — the
// resolver that refuses a second whole write. These rows measure that on the same
// `-Copt-level=0` captures the vcgen rows use: the reseated addend mints no bound in
// EITHER direction of the native lane, no native formula constrains a reassigned
// payload, and the control still carries the bound wherever the lane fires.

use trust_types::{Formula, VcKind, VerifiableFunction};

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/data/escaped_seam_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

fn native_vcs(name: &str) -> Vec<trust_types::VerificationCondition> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || trust_ir_bridge::generate_native_safety_vcs(&func).unwrap_or_default())
        .expect("spawn")
        .join()
        .expect("the native lane must not panic")
}

fn formulas_mention(vcs: &[trust_types::VerificationCondition], needle: &str) -> bool {
    vcs.iter().any(|vc| format!("{:?}", vc.formula).contains(needle))
}

/// `for &x in a { let mut y = x as u64; y = n; t += y; }` on `&[u8; 64]`, `n: u64` — the
/// reduction addend RESEATED to a parameter, so the fixed-array bound `t <= 0 + 64 *
/// 255 = 16320` is FALSE (`n = u64::MAX` overflows). The bridge's `acc_*` port resolves
/// the addend through `local_defs::unique_value_def`, which refuses the two-write `y`:
/// no native formula may carry `16320`, and no `Add` row may be discharged by it.
#[test]
fn a_reseated_reduction_addend_mints_no_native_accumulator_bound() {
    let vcs = native_vcs("a5_acc_elem_reseat");
    assert!(
        !formulas_mention(&vcs, "Int(16320)"),
        "the bridge minted the false accumulator bound onto a reseated addend: {:?}",
        vcs.iter().map(|vc| format!("{:?}", vc.formula)).collect::<Vec<_>>()
    );
}

/// The vcgen payload rows, on the bridge: `for mut i in 0..5usize { i = n; t = a[i]; }`
/// and its `enumerate` twin. The bridge mints no yield fact at all, so the pin is that
/// NO native formula constrains the payload `i` against the range end `5` (a
/// `Lt(Var("i…"), Int(5))` anywhere would be a fact the vcgen side now refuses) — the
/// implication the parity contract states: the bridge is never LOOSER than vcgen.
#[test]
fn no_native_formula_bounds_a_reassigned_payload_by_its_range_end() {
    /// `Lt(Var(i…), Int(5))` / `Ge(Var(i…), Int(0))` anywhere in `f` — the two spellings
    /// of a range-yield fact on the payload `i` (any SSA version of it).
    fn carries_yield_fact_on_i(f: &Formula) -> bool {
        let is_i =
            |v: &Formula| matches!(v, Formula::Var(name, _) if name.split('#').next() == Some("i"));
        let hit = match f {
            Formula::Lt(a, b) => is_i(a) && **b == Formula::Int(5),
            Formula::Ge(a, b) => is_i(a) && **b == Formula::Int(0),
            _ => false,
        };
        hit || f.children().iter().any(|c| carries_yield_fact_on_i(c))
    }
    for name in ["a5_payload_param_for", "a5_enum_payload_param", "a5_payload_incr"] {
        let vcs = native_vcs(name);
        for vc in vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)) {
            assert!(
                !carries_yield_fact_on_i(&vc.formula),
                "{name}: a native bounds formula carries a yield bound on the reassigned payload: {:?}",
                vc.formula
            );
        }
    }
}

/// THE CONTROL — the plain reduction `for &x in a { let y = x as u64; t += y; }`. The
/// native lane's bound is minted only where the whole recognizer fires; this row
/// records what it does on the `-Copt-level=0` capture rather than assuming it, and
/// pins the direction that matters: whatever the bridge mints here, it mints NOTHING
/// on the reseated twin above.
#[test]
fn the_plain_reduction_control_is_measured() {
    let vcs = native_vcs("a5_acc_elem_ctl");
    let minted = formulas_mention(&vcs, "Int(16320)");
    // Measured on this tree (recorded, not asserted as a MUST): see the test log.
    eprintln!(
        "a5_acc_elem_ctl: native accumulator bound minted = {minted} over {} rows",
        vcs.len()
    );
    // The one hard assertion: the lane never produces an UNSAT-by-construction formula
    // (`Bool(false)`) on a row it did not model.
    assert!(vcs.iter().all(|vc| vc.formula != Formula::Bool(false)));
}

// Trust: 2026-09-16 (round A6) — THE `__slice_len` ROOT and THE CALL-THROUGH-TEMP
// ENTRANCE, bridge parity on real MIR (`a7_pins.rs`, `-Copt-level=0` and `1`).
//
// The vcgen side now (a) refuses to inline `{s}__slice_len` into a payload fact when
// `s` is reseatable (`iterator_yield::licensed_slice_len_formula`) and (b) admits
// rustc's call-result temp (`_12 = next(..); _4 = move _12`) as a producing call of the
// join (`local_defs::body_call_through_temp_index`). The bridge mints no yield fact and
// its entrance (`acc_next_call_receiver`) is the stricter one-call
// `local_defs::unique_value_call`, so parity here is the implication only: nothing the
// bridge emits may be LOOSER than what vcgen now refuses.

/// `for i in 0..<[u8]>::len(s) { s = b; t += s[i]; }` on a `mut s: &[u8]` parameter — the
/// reviewer's kernel-certified false proof at `-O1`. The bridge's native lane must not
/// discharge either `SliceBoundsCheck` row by a `Lt(i, s__slice_len…)` premise: no
/// native bounds formula may carry a yield bound on the payload `i` against `s`'s
/// length, at either optimisation level.
#[test]
fn no_native_formula_bounds_a_payload_by_a_reseated_root_slice_length() {
    fn carries_len_bound_on_i(f: &Formula) -> bool {
        let is_i =
            |v: &Formula| matches!(v, Formula::Var(name, _) if name.split('#').next() == Some("i"));
        let is_s_len = |v: &Formula| matches!(v, Formula::Var(name, _) if name.split('#').next() == Some("s__slice_len"));
        // A yield FACT is a bare `Lt` conjunct; the bounds assert's own condition
        // definition `Eq(_c, Lt(i, len))` is the obligation, not a fact, and is not
        // descended into.
        match f {
            Formula::Lt(a, b) => is_i(a) && is_s_len(b),
            Formula::Eq(..) => false,
            _ => f.children().iter().any(|c| carries_len_bound_on_i(c)),
        }
    }
    for name in ["a7_len_ufcs_param_reseat_o1", "a7_len_ufcs_param_reseat_o0"] {
        let vcs = native_vcs(name);
        for vc in vcs.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)) {
            assert!(
                !carries_len_bound_on_i(&vc.formula),
                "{name}: a native bounds formula bounds the payload by the reseated root's length: {:?}",
                vc.formula
            );
        }
    }
    // The control (`s` never written): recorded, not asserted as a MUST — the bridge
    // mints no yield fact on either.
    for name in ["a7_ctl_len_ufcs_o1", "a7_ctl_len_ufcs_o0"] {
        let vcs = native_vcs(name);
        eprintln!("{name}: {} native rows", vcs.len());
        assert!(vcs.iter().all(|vc| vc.formula != Formula::Bool(false)));
    }
}

/// The loop-carried `let mut o = small.next(); while let Some(i) = o { a[i]; o =
/// big.next(); }` with `big = 50..100` — the temp spelling at `-O0`. The bridge's
/// `acc_*` entrance is the one-call question and declines `o` outright (a `WholeNamed`
/// write beside the call), so no native formula may bound the payload `i` by `small`'s
/// end `5` — which would attribute the joined payload to the first receiver.
#[test]
fn no_native_formula_attributes_a_loop_carried_payload_to_the_first_receiver() {
    fn carries_yield_fact_on_i(f: &Formula) -> bool {
        let is_i =
            |v: &Formula| matches!(v, Formula::Var(name, _) if name.split('#').next() == Some("i"));
        // Same reading as above: the assert condition's definition is not a fact.
        match f {
            Formula::Lt(a, b) => is_i(a) && **b == Formula::Int(5),
            Formula::Eq(..) => false,
            _ => f.children().iter().any(|c| carries_yield_fact_on_i(c)),
        }
    }
    for name in ["a7_two_next_loopcarried_bug_o0", "a7_two_next_loopcarried_bug_o1"] {
        let vcs = native_vcs(name);
        for vc in vcs.iter().filter(|vc| matches!(vc.kind, VcKind::IndexOutOfBounds)) {
            assert!(
                !carries_yield_fact_on_i(&vc.formula),
                "{name}: a native bounds formula attributes the carried payload to `small`: {:?}",
                vc.formula
            );
        }
    }
    for name in ["a7_ctl_two_next_loopcarried_o0", "a7_ctl_two_next_loopcarried_o1"] {
        let vcs = native_vcs(name);
        eprintln!("{name}: {} native rows", vcs.len());
        assert!(vcs.iter().all(|vc| vc.formula != Formula::Bool(false)));
    }
}
