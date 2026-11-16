// Real-MIR cover for a per-statement row whose operand the SAME block writes
// AFTER the read (a false refutation of valid Rust, and a bogus model on the
// unsafe twin).
//
// Built with `-O` (the release profile), rustc reads a mutable divisor local
// directly and overwrites it in the same block:
//
//   pub fn if_guarded_rem(x: u64, mut d: u64) -> u64 {
//       let mut r = 0;
//       if d != 0 { r = x % d; d = r; }
//       r ^ d
//   }
//
//   bb0: _3 = 0; _4 = copy _2; switch _4 -> [0: bb3, otherwise: bb1]
//   bb1: _5 = Eq(copy _2, 0); assert(!move _5, RemainderByZero) -> bb2
//   bb2: _3 = Rem(copy _1, move _2); _2 = copy _3; goto bb4
//
// `d` (`_2`) is a parameter with a store, so the per-statement `Rem` row is not
// folded into the assert row, and it reads `d` at `bb2[0]`, where it is still the
// ENTRY value (a bare `d`). The row body was then renamed a second time at the
// block TERMINAL, which stamped that bare read with the POST-write token `d#s2_1`.
// The path-def conjoin (`v2_live_path_defs_at_point`) had to drop every entry fact
// about bare `d` to stay sound against that rename, so the row kept the guards
// `_4` / `!_5` with nothing tying them to the divisor, and ay refuted it with the
// infeasible model `d = 1, d#s2_1 = 0`. The strict `-O` compile of all three safe
// functions below failed.
//
// Root fix: the whole-row version rename runs at the row's own use point, the
// same point its body read and its path defs are versioned at
// (`conjoin_preconditions_versioned_at_point_recorded`), so the read and its
// facts name the same value and nothing has to be dropped.
//
// Fixtures: the MIR `-Ztrust-dump=mir:<dir>` extracted from the stage1 compiler
// with `--edition 2021 -O`:
//
//  * SAFE, write-after-read of the divisor under an if guard (above); in a loop,
//    where the write leaves the loop (`while i < n { if d != 0 { let r = x % d;
//    d = r; return r ^ d; } i += 1; }`); and through a tuple field (`let mut p =
//    (a, b); if p.1 != 0 { r = x % p.1; p.1 = r; }`, which the release MIR
//    scalar-replaces into its own local). Every RemainderByZero row must be
//    PROVED.
//  * UNSAFE twins, whose guard tests another value (`x != 0`, and `p.0 != 0`).
//    Each must still be refuted, and every refutation must carry a model of an
//    execution that really divides by zero (the guard holds and the ENTRY
//    divisor is 0). Before the fix the statement rows were refuted with a
//    nonzero divisor and a zero post-write token, a model no execution has.
use trust_types::{
    Counterexample, CounterexampleValue, VcKind, VerifiableFunction, VerificationCondition,
    VerificationResult,
};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/write_after_read_rem_{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn rem_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::RemainderByZero))
        .collect()
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict").1
}

/// The block holding the `Rem` statement, and the statement's index there.
fn rem_site(func: &VerifiableFunction) -> (usize, usize) {
    let mut sites = Vec::new();
    for block in &func.body.blocks {
        for (index, stmt) in block.stmts.iter().enumerate() {
            if let trust_types::Statement::Assign {
                rvalue: trust_types::Rvalue::BinaryOp(trust_types::BinOp::Rem, ..),
                ..
            } = stmt
            {
                sites.push((block.id.0, index));
            }
        }
    }
    assert_eq!(sites.len(), 1, "each fixture has exactly one `Rem` statement: {sites:?}");
    sites[0]
}

/// The shape this file pins: the `Rem` block writes the divisor AFTER reading it.
fn assert_write_after_read(func: &VerifiableFunction) {
    let (block, index) = rem_site(func);
    let stmts = &func.body.blocks[block].stmts;
    let trust_types::Statement::Assign {
        rvalue: trust_types::Rvalue::BinaryOp(_, _, trust_types::Operand::Move(divisor)),
        ..
    } = &stmts[index]
    else {
        panic!("the release MIR moves the divisor local into the `Rem`: {:?}", stmts[index]);
    };
    assert!(divisor.projections.is_empty(), "the divisor is a whole local: {divisor:?}");
    let written_later = stmts[index + 1..].iter().any(|s| {
        matches!(s, trust_types::Statement::Assign { place, .. }
            if place.local == divisor.local && place.projections.is_empty())
    });
    assert!(written_later, "bb{block} must write the divisor after the `Rem` reads it");
}

fn int_named(cex: &Counterexample, name: &str) -> Option<i128> {
    cex.assignments.iter().find_map(|(n, value)| match value {
        CounterexampleValue::Int(v) if n == name => Some(*v),
        CounterexampleValue::Uint(v) if n == name => i128::try_from(*v).ok(),
        _ => None,
    })
}

/// No row may name a value the `Rem` block writes: every row of that block reads
/// the divisor BEFORE the write (the assert row reads it in the predecessor). A
/// post-write token here means an entry fact or the read itself was moved onto
/// the value written after the read, which is how a stale fact turns into a
/// false proof.
fn assert_no_post_write_read(name: &str, index: usize, block: usize, vc: &VerificationCondition) {
    let post_write = format!("#s{block}_");
    let stale: Vec<String> =
        vc.formula.free_variables().into_iter().filter(|v| v.contains(&post_write)).collect();
    assert!(
        stale.is_empty(),
        "{name} row {index}: reads a value bb{block} writes after the `Rem` ({stale:?})\n\
         formula: {:?}",
        vc.formula
    );
}

fn assert_safe_proved(name: &str) {
    let func = load(name);
    assert_write_after_read(&func);
    let (block, _) = rem_site(&func);
    let rows = rem_rows(&func);
    // The assert row and the per-statement row: the statement row is the one
    // this defect refuted, so its presence is part of the pin.
    assert_eq!(rows.len(), 2, "{name}: the assert row and the `Rem` statement row; got {rows:#?}");
    for (index, vc) in rows.iter().enumerate() {
        assert_no_post_write_read(name, index, block, vc);
        let result = verdict(vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "{name} row {index}: the divisor is guarded nonzero where it is read, so the \
             row must be PROVED; a refutation is a false refutation of valid Rust and \
             Unknown is a lost proof. got {result:?}\nformula: {:?}",
            vc.formula
        );
    }
}

/// `real_state` decides whether a refutation's model is an execution that really
/// divides by zero.
fn assert_unsafe_refuted(name: &str, real_state: impl Fn(&Counterexample) -> bool) {
    let func = load(name);
    assert_write_after_read(&func);
    let (block, _) = rem_site(&func);
    let rows = rem_rows(&func);
    assert_eq!(rows.len(), 2, "{name}: the assert row and the `Rem` statement row; got {rows:#?}");
    let mut refuted = 0;
    for (index, vc) in rows.iter().enumerate() {
        assert_no_post_write_read(name, index, block, vc);
        match verdict(vc) {
            VerificationResult::Failed { counterexample, .. } => {
                refuted += 1;
                let cex = counterexample.expect("a refutation must carry its model");
                assert!(
                    real_state(&cex),
                    "{name} row {index}: the counterexample must be a state that divides \
                     by zero (guard holds, entry divisor 0); got {cex:?}\nformula: {:?}",
                    vc.formula
                );
            }
            // The statement row sits under the assert's success edge, so it may
            // discharge; the assert row carries the refutation.
            VerificationResult::Proved { .. } => {}
            other => {
                panic!("{name} row {index}: every row needs a definite verdict; got {other:?}")
            }
        }
    }
    assert!(refuted >= 1, "{name}: the unguarded divisor divides by zero; nothing refuted it");
}

#[test]
fn if_guarded_write_after_read_is_proved() {
    assert_safe_proved("if_safe");
}

#[test]
fn loop_guarded_write_after_read_is_proved() {
    assert_safe_proved("loop_safe");
}

#[test]
fn tuple_field_write_after_read_is_proved() {
    assert_safe_proved("tuple_safe");
}

#[test]
fn if_unguarded_twin_is_refuted_with_a_real_model() {
    // `if x != 0 { r = x % d; .. }`: panics iff x != 0 and d == 0.
    assert_unsafe_refuted("if_unsafe", |cex| {
        int_named(cex, "x").is_some_and(|x| x != 0) && int_named(cex, "d") == Some(0)
    });
}

#[test]
fn loop_unguarded_twin_is_refuted_with_a_real_model() {
    // `while i < n { if x != 0 { let r = x % d; .. } .. }`: panics iff the loop
    // is entered (0 <= i < n) with x != 0 and the entry d == 0.
    //
    // Only the divide-by-zero half of that state is checked. vcgen ranges the
    // PARAMETERS (`x`, `d`, `n`) but no other integer local, so the loop
    // counter's versioned read (`i#s0_1_s6_0` once vac Phase 0 sealed bare
    // reads) admits `i = -1, n = 0` — a loop that never ran. That is
    // KNOWN_HAZARDS R-e; when locals carry their type range, restore the
    // `0 <= i < n` conjunct.
    assert_unsafe_refuted("loop_unsafe", |cex| {
        int_named(cex, "x").is_some_and(|x| x != 0)
            && int_named(cex, "d") == Some(0)
            && int_named(cex, "d#e").is_none_or(|d| d == 0)
    });
}

#[test]
fn tuple_field_unguarded_twin_is_refuted_with_a_real_model() {
    // `let mut p = (a, b); if p.0 != 0 { r = x % p.1; .. }`: the release MIR
    // keeps `p.0` as `_2` (it is `a`) and scalar-replaces `p.1` into `_3`.
    // Panics iff p.0 != 0 and p.1 == 0.
    assert_unsafe_refuted("tuple_unsafe", |cex| {
        int_named(cex, "_2").is_some_and(|p0| p0 != 0) && int_named(cex, "_3") == Some(0)
    });
}
