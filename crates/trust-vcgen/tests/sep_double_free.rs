// The separation engine's free/use-after-free channel, on REAL MIR.
//
// MEASURED 2026-09-19/20: `[unsafe:sep:free]` never fired on an extracted body.
// The only positive control in the tree (`sep_engine::tests::
// test_double_free_generates_vc`) is HAND-BUILT MIR with two `Drop` terminators
// on the raw pointer local itself — a shape rustc does not emit. Two stacked
// defects kept the channel dark on real MIR:
//
//  1. CLASSIFICATION. `alloc::alloc::dealloc` (the extracted callee path)
//     contains the substring `alloc::alloc`, so `is_alloc_call` matched it and
//     the dispatch took the ALLOCATION arm. `interpret_dealloc_call` was
//     unreachable for the global deallocator, and each `dealloc` minted a
//     spurious `[unsafe:sep:alloc] allocation result null check` about its `()`
//     result place. (Since closed on its own by the keyed recognizers: the
//     exact `SysrootItem` tags route `AllocDealloc` to the dealloc arm.)
//
//  2. PLACE. `interpret_dealloc_call` resolved the freed allocation from the
//     call's DESTINATION place. `dealloc(ptr, layout)` returns `()`, so the
//     destination is a unit temporary that is never in `local_to_ptr`. The
//     handler could not free anything even when reached.
//
// Defect 2 is what this suite now guards; the channel's PATH CONDITION (a free
// is visible only in the blocks its freeing block dominates, and only while the
// walk is inside them) is probed separately by `sep_free_scope_gap.rs`.
//
// Fixtures are the REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>
// -Ztrust-policy=advisory`) of `fixtures/sep_dealloc_probe_fx.rs`, re-extracted
// 2026-09-24 with stage1 trustc fc5538510 so they carry the compiler-resolved
// `callee_key` the engine now decides on. (The 2026-09-20 originals, from sealed
// trustc 321aaeda7, predate that key; on today's engine they recognise no
// allocator at all and every assertion below would be vacuous or fail.)
use trust_types::*;
use trust_vcgen::generate_vcs;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn sep_messages(vcs: &[VerificationCondition], tag: &str) -> Vec<String> {
    vcs.iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::Assertion { message } if message.contains(tag) => Some(message.clone()),
            _ => None,
        })
        .collect()
}

const ONCE: &str = include_str!("fixtures/sep_dealloc_once_mir.json");
const TWICE: &str = include_str!("fixtures/sep_dealloc_twice_mir.json");
const THEN_READ: &str = include_str!("fixtures/sep_dealloc_then_read_mir.json");
const BRANCHES: &str = include_str!("fixtures/sep_dealloc_exclusive_branches_mir.json");
const IN_LOOP: &str = include_str!("fixtures/sep_dealloc_in_loop_mir.json");
const REALLOC: &str = include_str!("fixtures/sep_dealloc_realloc_same_local_mir.json");

/// Not an assertion — a census. `--nocapture` prints the full `[unsafe:sep:*]`
/// row set of every probe so a before/after comparison is measured, not inferred.
#[test]
#[ignore = "measurement instrument: a census that prints every probe's sep rows and asserts \
            nothing (the tests below pin each probe); run with --ignored --nocapture"]
fn census_of_sep_rows_on_the_dealloc_probes() {
    for (name, json) in [
        ("alloc_free_once", ONCE),
        ("alloc_free_twice", TWICE),
        ("alloc_free_then_read", THEN_READ),
        ("alloc_free_branch", BRANCHES),
        ("alloc_free_loop", IN_LOOP),
        ("realloc_same_local", REALLOC),
    ] {
        let func = load(json);
        let vcs = generate_vcs(&func);
        let rows = sep_messages(&vcs, "[unsafe:sep:");
        println!("CENSUS {name}: {} sep rows", rows.len());
        for r in &rows {
            println!("CENSUS {name}   | {r}");
        }
    }
}

// ── POSITIVE CONTROL ────────────────────────────────────────────────────────

#[test]
fn a_single_correct_dealloc_is_not_a_double_free() {
    let vcs = generate_vcs(&load(ONCE));
    let frees = sep_messages(&vcs, "[unsafe:sep:free]");
    assert!(
        frees.is_empty(),
        "`let p = alloc(l); dealloc(p, l);` frees the allocation exactly once; \
         it must carry no double-free row: {frees:#?}"
    );
}

/// The two `dealloc` calls are on MUTUALLY EXCLUSIVE arms of one `SwitchInt`, so
/// no execution performs both. A path-insensitive "have I seen a free of this
/// provenance?" test reports a double free here — on correct code, with the
/// undischargeable `Formula::Bool(true)`. The free row is minted only when the
/// earlier free's block DOMINATES the later one's, which is exactly the
/// condition that makes `Bool(true)` a true statement about every execution.
#[test]
fn two_frees_on_exclusive_branches_are_not_a_double_free() {
    let vcs = generate_vcs(&load(BRANCHES));
    let frees = sep_messages(&vcs, "[unsafe:sep:free]");
    assert!(
        frees.is_empty(),
        "`if c {{ dealloc(p, l) }} else {{ dealloc(p, l) }}` frees once on every \
         execution; neither arm dominates the other: {frees:#?}"
    );
}

/// A loop body that allocates and frees on each iteration. The free is of a
/// provenance minted in the same iteration, so no iteration frees twice.
#[test]
fn alloc_and_free_inside_a_loop_is_not_a_double_free() {
    let vcs = generate_vcs(&load(IN_LOOP));
    let frees = sep_messages(&vcs, "[unsafe:sep:free]");
    assert!(
        frees.is_empty(),
        "`while i < n {{ let p = alloc(l); dealloc(p, l); }}` frees each \
         allocation once: {frees:#?}"
    );
}

/// The same source local is re-allocated between the two frees. The second
/// `dealloc` frees a provenance the first free never touched, so the "have I
/// freed this provenance?" test must key on PROVENANCE and not on the pointer's
/// abstract name — `alloc_N` is derived from the destination local and is reused
/// across allocations.
#[test]
fn a_reallocation_of_the_same_local_is_not_a_double_free() {
    let vcs = generate_vcs(&load(REALLOC));
    let frees = sep_messages(&vcs, "[unsafe:sep:free]");
    assert!(
        frees.is_empty(),
        "`p = alloc(l); dealloc(p, l); p = alloc(l); dealloc(p, l);` frees two \
         distinct allocations once each: {frees:#?}"
    );
}

// ── NEGATIVE CONTROL ────────────────────────────────────────────────────────

#[test]
fn a_second_dealloc_of_the_same_allocation_is_refuted() {
    let vcs = generate_vcs(&load(TWICE));
    let frees = sep_messages(&vcs, "[unsafe:sep:free]");
    assert!(
        !frees.is_empty(),
        "`dealloc(p, l); dealloc(p, l);` on one tracked allocation is a double \
         free and must mint an `[unsafe:sep:free]` row"
    );
    assert!(
        frees.iter().any(|m| m.contains("double-free")),
        "the row must name the double free: {frees:#?}"
    );
}

#[test]
fn a_read_through_a_freed_pointer_is_refuted() {
    let vcs = generate_vcs(&load(THEN_READ));
    let uaf = sep_messages(&vcs, "use-after-free");
    assert!(
        !uaf.is_empty(),
        "`dealloc(p, l); *p` reads through a freed pointer and must mint a \
         use-after-free row"
    );
}

/// The refuting rows are DEFINITE violations (`Formula::Bool(true)`): no solver
/// can discharge them, which is what makes the double free a refutation rather
/// than an obligation the body might still prove.
#[test]
fn the_double_free_row_is_a_definite_violation() {
    let vcs = generate_vcs(&load(TWICE));
    let row = vcs
        .iter()
        .find(|vc| {
            matches!(&vc.kind, VcKind::Assertion { message }
            if message.contains("[unsafe:sep:free]"))
        })
        .expect("the double free must mint a row");
    assert_eq!(
        row.formula,
        Formula::Bool(true),
        "a dominating earlier free makes the second free unconditional on every \
         execution, so the violation formula is a constant, not a guess"
    );
}

/// The report classifier (`trust_types::unsafe_demand_is_definite_violation`)
/// must recognise exactly the rows this engine mints as DEFINITE violations,
/// so a forced-Failed double free / use-after-free keeps reading as refuted
/// rather than "unproved, no counterexample". Pinned on the engine's REAL
/// output so a reworded message cannot silently drop out of the class. The
/// double free's row is the bare constant `Bool(true)`; the use-after-free's
/// is that constant under the read's path guard (the violation holds on every
/// execution REACHING the read), which is the class's meaning too.
#[test]
fn definite_free_rows_are_the_rows_the_report_classifies_as_definite() {
    for (name, json, tag, bare_constant) in [
        ("alloc_free_twice", TWICE, "[unsafe:sep:free]", true),
        ("alloc_free_then_read", THEN_READ, "use-after-free", false),
    ] {
        let vcs = generate_vcs(&load(json));
        let rows: Vec<&VerificationCondition> = vcs
            .iter()
            .filter(|vc| matches!(&vc.kind, VcKind::Assertion { message } if message.contains(tag)))
            .collect();
        assert!(!rows.is_empty(), "{name}: the probe must mint a {tag} row");
        for vc in rows {
            let VcKind::Assertion { message } = &vc.kind else { unreachable!() };
            assert!(
                unsafe_demand_is_definite_violation(message),
                "{name}: `{message}` must classify as a definite violation"
            );
            if bare_constant {
                assert_eq!(vc.formula, Formula::Bool(true), "{name}: `{message}`");
            } else {
                assert!(
                    violation_core_is_constant_true(&vc.formula),
                    "{name}: `{message}` must be the constant violation under its path guard: {:?}",
                    vc.formula
                );
            }
        }
    }
    // CONTROL: no row minted on a correct single free is classified definite.
    let vcs = generate_vcs(&load(ONCE));
    for vc in &vcs {
        if let VcKind::Assertion { message } = &vc.kind {
            assert!(!unsafe_demand_is_definite_violation(message), "`{message}`");
        }
    }
}

/// `Bool(true)`, or a guard conjunction whose LAST conjunct (recursively) is
/// `Bool(true)` — the shape the vcgen gives a constant violation under a path
/// guard.
fn violation_core_is_constant_true(formula: &Formula) -> bool {
    match formula {
        Formula::Bool(true) => true,
        Formula::And(conjuncts) => conjuncts.last().is_some_and(violation_core_is_constant_true),
        _ => false,
    }
}
