// Regression: an OPAQUE deref store `*p = v` must invalidate what it can reseat,
// and must NOT invalidate what it cannot.
//
// Two separable defects, both measured as kernel-certified proofs on bodies that
// panic when run (`-O -C debug-assertions=on`, every input swept):
//
//   * RESEAT SCOPE. A store whose pointee is the slice reference ITSELF
//     (`p: &mut &[T]`, `*p = t`) replaces the fat pointer, so the array→slice
//     tie minted before the store no longer describes it. The store's havoc list
//     carried only the BASE names, and `s__slice_len` is not reached from `s` by
//     `place_names_overlap` (`_` is not a projection separator), so `s__slice_len
//     == 8` stayed live across the reseat and discharged `s[7]`.
//
//   * OUTFLOW. `v2_live_path_defs` drops a block's ENTRY facts that its own opaque
//     store invalidates, but `v2_path_def_fixpoint` applied only the statement-def
//     and terminator kills, so the same facts reached the SUCCESSORS untouched.
//     `block_written_names` does include the deref-store havoc, so the stale fact
//     was renamed to the post-store version token and unified with the live read.
//     This one needs no slice at all — `scalar_outflow_loop` below is `u32` — and
//     it is invisible in straight-line code, where rustc puts the two-branch `&mut`
//     join, the store and the use in ONE block.
//
//   * THE `&raw const` SLOT CHANNEL. The opaque-store havoc judges its base names
//     with the PLAIN relation (`KillSet::havoc`): a store THROUGH `s` writes the
//     pointee, never `s`'s own length. That is sound only if every pointer that can
//     address `s`'s SLOT puts `s` — and so its explicit `s__slice_len` twin — on the
//     havoc list. `&mut s` and `&raw mut s` did; `&raw const s` did not, and a
//     write through `&raw const s as *mut _` is defined under Tree Borrows for a
//     `let mut s` (for an immutable binding the Reference makes it UB; the rule
//     counts both, see tests/data/raw_const_slot_reseat.rs). The straight-line,
//     shared-slice-loop and call shapes were kernel-certified false proofs on
//     `main` before the plain relation landed (stage 1 `a7ea88986d`), and the
//     `&mut [u8]` loop became one when it did (`aebf15b1ed`, the fixpoint outflow
//     kill). The same channel was missing from the stability scans that read a
//     local's own storage (`place_source_is_stable` and its siblings), so a `mut`
//     PARAMETER written through `&raw const x` kept collapsing onto its entry value.
//     The rule is one predicate, `generate::own_storage_write_borrow` (main's H2
//     statement of it, 96db9eb9f0; this lane's `slot_write_channel` was merged into
//     it); its arm-by-arm and per-consumer pins are in
//     src/generate/slot_write_channel_tests.rs.
//
// The controls are the point. Over-killing here is the false REFUTATION
// `write_covers_derived_slice_len` exists to prevent: a store through a pointer to
// an ELEMENT (`e: &mut T`) preserves the length, and an opaque store to an
// UNRELATED local must cost a neighbouring fact nothing. Both directions are
// asserted, because a "havoc everything at every opaque store" mutant passes every
// refute test here and fails every proof test.
//
// Fixtures are the REAL extracted MIR (`-Ztrust-dump=mir-only:<dir>`) of the
// function quoted beside each loader. The `raw_const_slot_reseat_*_mir.json`
// fixtures were dumped from tests/data/raw_const_slot_reseat.rs by Trust `main`
// stage 1 `a7ea88986d` with the command that file's header gives, run from the
// repository root; nothing in the dumps was edited.
use trust_types::*;
use trust_vcgen::generate_vcs;

fn fixture(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    trust_router::Router::deterministic_in_process_ay(
        30_000,
        trust_types::determinism::EffortScale::BUILTIN,
    )
}

fn safety_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_vcs(func)
        .into_iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::ArithmeticOverflow { .. }
                    | VcKind::IndexOutOfBounds
                    | VcKind::SliceBoundsCheck
            )
        })
        .collect()
}

/// The obligations a fixture carries, paired with "is this discharged?" in the
/// sense the COMPILER reports: an ay `Proved`, or a kernel certificate — the in-process
/// ay backend downgrades some UNSATs it cannot strictly certify to `Unknown`, and
/// `trust_certify::certify_vc` is what the "of which N kernel-certified" note counts.
/// Reading only the router verdict hides a proof behind an `Unknown`.
fn discharged(func: &VerifiableFunction) -> Vec<bool> {
    let vcs = safety_vcs(func);
    let router = router();
    router
        .verify_all(&vcs)
        .iter()
        .map(|(vc, res)| {
            matches!(res, VerificationResult::Proved { .. })
                || trust_certify::certify_vc(vc).is_some()
        })
        .collect()
}

fn is_bounds(kind: &VcKind) -> bool {
    matches!(kind, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
}

/// The obligation that can actually fault in the scalar fixtures: the `u32`
/// addition. The 64-bit `i += 1` in the same body is genuinely safe and IS proved,
/// so a whole-function assertion would be asserting something false.
fn is_u32_add(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::Int { width: 32, .. }, _) }
    )
}

/// A body that PANICS when run may not be accepted, and no obligation selected by
/// `select` may be discharged by anything but a runtime check that PASSED.
///
///  1. At least one selected row is NOT discharged — the check that faults.
///  2. Every DISCHARGED selected row loses its proof once the bare success guards
///     of the body's own `BoundsCheck` asserts are dropped from it: its proof rests
///     on a check that passed, never on a stale fact.
///
/// WHY NOT "NONE DISCHARGED" (the assertion until 2026-09-29). rustc pairs "the
/// assert can fail" (the `Assert` terminator's row) with "after the assert, the
/// index is in bounds" (the load/store row of the block the assert's success edge
/// enters). The second is safe by construction — it is reached only when the check
/// passed — and while the load/store lane conjoined path GUARDS without their
/// DEFINITIONS it could never be discharged, so "none discharged" held and doubled
/// as a proxy for "the first one is not falsely proved". Once that lane carries the
/// dominating assert's definition (`_12 == (_10 < _11)` with `_11` the LIVE,
/// post-reseat length), the second row proves from the live length and the proxy
/// asserts something false. Clause 2 is the property the proxy stood for: a stale
/// `s__slice_len == 8` discharging the FAULTING row is still caught (dropping the
/// guards leaves the stale fact, so the row stays proved), and so is a row proved
/// with every check in place but nothing to do with them.
fn assert_none_discharged(func: &VerifiableFunction, select: fn(&VcKind) -> bool, what: &str) {
    let vcs = safety_vcs(func);
    let router = router();
    let rows: Vec<(VerificationCondition, bool)> = router
        .verify_all(&vcs)
        .into_iter()
        .filter(|(vc, _)| select(&vc.kind))
        .map(|(vc, res)| {
            let ok = is_discharged(&vc, &res);
            (vc, ok)
        })
        .collect();
    assert_rows_rest_on_passed_checks(func, rows, &ay_verdict, what);
}

/// One row decided by the deterministic in-process ay router alone — the
/// `generate_vcs` lane's decider.
fn ay_verdict(vc: &VerificationCondition) -> VerificationResult {
    let (_, res) =
        router().verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict");
    res
}

/// Discharged in the sense the COMPILER reports (see [`discharged`]).
fn is_discharged(vc: &VerificationCondition, res: &VerificationResult) -> bool {
    matches!(res, VerificationResult::Proved { .. }) || trust_certify::certify_vc(vc).is_some()
}

/// The two clauses of [`assert_none_discharged`] over already-decided `rows`; a
/// guard-stripped row is re-decided by `decide`, the lane that decided `rows`.
fn assert_rows_rest_on_passed_checks(
    func: &VerifiableFunction,
    rows: Vec<(VerificationCondition, bool)>,
    decide: &dyn Fn(&VerificationCondition) -> VerificationResult,
    what: &str,
) {
    let conds = bounds_assert_conditions(func);
    let census: Vec<(String, bool)> =
        rows.iter().map(|(vc, ok)| (format!("{:?}", vc.kind), *ok)).collect();
    assert!(!rows.is_empty(), "{what}: the selected obligation was never generated");
    assert!(
        rows.iter().any(|(_, ok)| !ok),
        "{what}: a body that PANICS when run has EVERY selected obligation discharged: \
         {census:?}"
    );
    for (vc, ok) in &rows {
        if !ok {
            continue;
        }
        let mut stripped = vc.clone();
        stripped.formula = drop_passed_bounds_guards(&vc.formula, &conds);
        let res = decide(&stripped);
        assert!(
            !matches!(res, VerificationResult::Proved { .. }),
            "{what}: a body that PANICS when run has a DISCHARGED obligation whose proof \
             does not rest on a passed runtime check — a stale fact is vacuously \
             discharging it: {census:?}\nrow: {:?}",
            vc.kind
        );
    }
}

/// The formula names of the conditions of every `Assert { msg: BoundsCheck,
/// expected: true }` in `func`.
fn bounds_assert_conditions(func: &VerifiableFunction) -> Vec<String> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Assert {
                cond: Operand::Copy(p) | Operand::Move(p),
                expected: true,
                msg: AssertMessage::BoundsCheck,
                ..
            } => Some(trust_vcgen::place_to_var_name(func, p)),
            _ => None,
        })
        .collect()
}

/// `f` with every bare positive Boolean conjunct naming one of `conds` — the path
/// guard of that assert's SUCCESS edge — replaced by `true`. An assert's
/// definition (`Eq(cond, Lt(..))`) and every other conjunct are kept.
fn drop_passed_bounds_guards(f: &Formula, conds: &[String]) -> Formula {
    let is_guard = |g: &Formula| {
        matches!(g, Formula::Var(n, Sort::Bool)
            if conds.iter().any(|c| n.split('#').next() == Some(c.as_str())))
    };
    match f {
        Formula::And(parts) => Formula::And(
            parts
                .iter()
                .map(|p| {
                    if is_guard(p) {
                        Formula::Bool(true)
                    } else {
                        drop_passed_bounds_guards(p, conds)
                    }
                })
                .collect(),
        ),
        Formula::Or(parts) => {
            Formula::Or(parts.iter().map(|p| drop_passed_bounds_guards(p, conds)).collect())
        }
        other => other.clone(),
    }
}

/// True when some safety obligation of `func` still carries a slice-length
/// variable pinned to the constant `n`.
///
/// This is what an over-eager havoc destroys and what a refute-only test cannot
/// see: the tie is an ENTRY fact, so a store that re-versions `{s}__slice_len`
/// drops it outright rather than leaving a contradictory one behind. Asserting
/// discharge alone is not enough either — an obligation can be discharged by an
/// unrelated guard on the same path.
fn some_obligation_pins_a_length_to(func: &VerifiableFunction, n: i128) -> bool {
    fn pins(f: &Formula, n: i128) -> bool {
        match f {
            Formula::Eq(lhs, rhs) => {
                let named_len = |b: &Formula| {
                    b.var_name()
                        .is_some_and(|v| v.split('#').next().unwrap_or(v).ends_with("__slice_len"))
                };
                let is_n = |b: &Formula| matches!(b, Formula::Int(k) if *k == n);
                (named_len(lhs) && is_n(rhs)) || (named_len(rhs) && is_n(lhs))
            }
            other => other.children().iter().any(|c| pins(c, n)),
        }
    }
    safety_vcs(func).iter().any(|vc| pins(&vc.formula, n))
}

fn assert_length_tie_survives(func: &VerifiableFunction, n: i128, what: &str) {
    assert!(
        some_obligation_pins_a_length_to(func, n),
        "{what}: no obligation carries the source array's length {n} any more — \
         an element store re-versioned `__slice_len` and dropped the tie, which \
         refutes an index that cannot go out of bounds"
    );
    let d = discharged(func);
    assert!(d.iter().any(|ok| *ok), "{what}: the tie is present but nothing discharges — {d:?}");
}

// ---------------------------------------------------------------- reseat scope

#[test]
fn reborrow_reseat_through_an_opaque_pointer_still_refutes() {
    // pub fn f(a: &[u8; 8], b: &[u8; 2], flag: bool) -> u8 {
    //     let mut s: &[u8] = a;
    //     let mut t: &[u8] = b;
    //     let p: &mut &[u8] = if flag { &mut s } else { &mut t };
    //     *p = b;                 // RESEATS `s` when flag — `s.len()` becomes 2
    //     s[7]                    // panics for flag = true
    // }
    // Two `&mut` borrows in different arms, so the pointer does not fold and the
    // store is opaque. Safe Rust: no `unsafe`, no raw pointer.
    assert_none_discharged(
        &fixture(include_str!("fixtures/reseat_r_opaque_reborrow.json")),
        is_bounds,
        "reborrow reseat",
    );
}

#[test]
fn reseat_through_a_struct_carried_pointer_still_refutes() {
    // The same reseat with the pointer travelling through a struct field and read
    // back out (`let q = w.p; *q = b;`), so the store's pointer is one copy further
    // from its `&mut` site.
    assert_none_discharged(
        &fixture(include_str!("fixtures/reseat_r_field_ptr.json")),
        is_bounds,
        "field-carried pointer reseat",
    );
}

#[test]
fn reseat_inside_a_loop_still_refutes() {
    // The reseat is in the LOOP BODY and the index is after the loop, so the stale
    // fact has to survive the back-edge and the header join to reach the read.
    // This is the shape the block-entry kill alone does not reach.
    assert_none_discharged(
        &fixture(include_str!("fixtures/reseat_r_in_loop.json")),
        is_bounds,
        "reseat in a loop",
    );
}

// --------------------------------------------------------------------- outflow

#[test]
fn a_scalar_reseat_in_a_loop_still_refutes() {
    // pub fn f(c: bool, n: usize) -> u32 {
    //     let mut x: u32 = 5;
    //     let mut y: u32 = 0;
    //     let mut i: usize = 0;
    //     while i < n {
    //         let p: &mut u32 = if c { &mut x } else { &mut y };
    //         *p = 4_000_000_000;
    //         i += 1;
    //     }
    //     x + x                   // panics for c = true, n >= 1
    // }
    // No slice anywhere: this is the OUTFLOW defect on its own. The `x == 5`
    // established before the loop must not reach the addition.
    assert_none_discharged(
        &fixture(include_str!("fixtures/reseat_r_scalar_outflow_loop.json")),
        is_u32_add,
        "scalar reseat in a loop",
    );
}

// -------------------------------------------------------------------- controls

/// The element-store control for the OUTFLOW kill: the store is in the loop
/// body and the index is after the loop, mirroring `reseat_inside_a_loop`
/// exactly except for the pointee type. It asserts the PRECISION side — a store
/// that writes an ELEMENT does not change the length, so the array→slice tie
/// `s__slice_len == 8` must survive it.
///
/// HISTORY. It held on `70a7534fd1`, then (measured 2026-08-26) the tie was
/// dropped by the STORE-HAVOC retain in `v2_path_def_fixpoint`: the havoc list
/// (`mutably_borrowed_havoc_names` + `mutable_pointer_local_names`) carries the
/// bare pointer local `s`, and the kill judged it with the DESTINATION relation,
/// whose derived channel (`write_covers_derived_slice_len`) reads a write of `s`
/// as a write of `s__slice_len`. The test was turned into a pin of that
/// regression, with the instruction to restore this control once the tie came
/// back. It came back on 2026-09-29: every opaque-store havoc kill now judges its
/// base names with the PLAIN relation (`KillSet::havoc`, the contract
/// `dest_write_rebinds` states) — a store THROUGH `s` writes the pointee, never
/// `s`'s own length, and a local whose slot can be aliased is a mutably-borrowed
/// havoc member whose `__slice_len` twin is minted explicitly. The reseat
/// canaries above are the soundness side of that change and still hold: the
/// stale `== 8` discharges nothing there. That premise was INCOMPLETE as first
/// landed: the slot-aliasing list omitted `&raw const` of an owned place, and a
/// loop reseat through it became a kernel-certified proof under the plain
/// relation. Closed 2026-09-30 by the own-storage write-channel rule (now
/// `path_defs::own_storage_write_borrow`); pinned by the
/// `a_raw_const_*` tests at the end of this file. This control is also the
/// precision side of that rule's `Deref` guard for rustc's own `&raw const (*s)`
/// (its `PtrMetadata` idiom, present in this fixture).
///
/// Merge 2026-10-14: the local twin of the same fix (`formula_survives_havoc`, the
/// overlap and index-segment relation for every havoc name, the derived channel
/// only for a PROJECTED one) is composed with `KillSet::havoc` at the fixpoint's
/// store kill; a bare `s` still spares `s__slice_len`, so this control holds under
/// both.
#[test]
fn an_element_store_in_a_loop_keeps_the_slice_length() {
    let func = fixture(include_str!("fixtures/reseat_s_elem_store_loop.json"));
    assert_length_tie_survives(&func, 8, "element store in a loop");
}

// ------------------------------------------ the `&raw const` slot-write channel
//
// MEASURED before the rule (2026-09-30, these fixtures through the compiler's
// entry, hardened ON, interval backend then deterministic in-process ay): every
// `&raw const` body below had its faulting row AND that assert's hardened twin
// kernel-certified PROVED (the parameter rows with the havoc-list half of the rule
// alone: the twin refuted, the per-statement row stayed PROVED); the `&raw mut`
// controls refuted. Every body PANICS natively (-O0 and -O3: `index out of
// bounds: the len is 2 (or 0) but the index is 3`, `attempt to add with
// overflow`, and an index of `usize::MAX`). Source: tests/data/raw_const_slot_reseat.rs.

fn raw_const_fixture(name: &str) -> VerifiableFunction {
    named_fixture("raw_const_slot_reseat", name)
}

/// `tests/fixtures/<data file>_<name>_mir.json`, dumped from `tests/data/<data file>.rs`.
fn named_fixture(data_file: &str, name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{data_file}_{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

const BOUNDS_ASSERT: &str = "mir_assert::BoundsCheck";
const ADD_ASSERT: &str = "mir_assert::Overflow(Add)";

/// The `unix_hardened` twin of the MIR assert whose callee label is `assert`
/// ("this assert cannot fail"). In a body whose only such assert is the one that
/// faults, it IS the panic, so it may not be discharged at all.
fn is_twin_of(kind: &VcKind, assert: &str) -> bool {
    matches!(kind, VcKind::HardenedBoundary { callee, .. } if callee == assert)
}

fn is_u8_add(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::Int { width: 8, .. }, _) }
    )
}

/// One row's verdict as the compiler's lanes give it: the interval backend's when
/// it PROVES (the compiler runs `IntervalBackend` on the same row and keeps its
/// proof; the installed lane's false `[slice]` proofs of these bodies were
/// `(interval, … kernel-rechecked)`), else the deterministic in-process ay verdict.
fn compiler_entry_verdict(vc: &VerificationCondition) -> VerificationResult {
    let interval = trust_router::Router::with_backends(vec![Box::new(
        trust_router::interval_backend::IntervalBackend,
    )]);
    let decide = |r: &trust_router::Router| {
        let (_, res) =
            r.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict per VC");
        res
    };
    let by_interval = decide(&interval);
    if matches!(by_interval, VerificationResult::Proved { .. }) {
        return by_interval;
    }
    decide(&router())
}

/// Every row the COMPILER decides for `func` — the entry `trust_verify` calls
/// (`generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops`,
/// hardened profile ON, no synthesized box derefs), pre-classified rows included —
/// paired with "is it discharged" in the sense the compiler reports (a proof by
/// [`compiler_entry_verdict`], or a kernel certificate). `generate_vcs` alone never
/// builds the hardened twin.
fn compiler_entry_rows(func: &VerifiableFunction) -> Vec<(VerificationCondition, bool)> {
    compiler_entry_rows_with_callees(func, &[])
}

/// [`compiler_entry_rows`] with `callees`' extracted bodies in the summary database,
/// each keyed by its `def_path` — the name the caller's `Terminator::Call` carries —
/// as the compiler's `extracted_callee_body_for_tracing` installs every local
/// non-generic callee with MIR. This is what turns on the callee write-set lane
/// (`callee_write_set::refine_call_havoc_delta`); with no body it never fires.
fn compiler_entry_rows_with_callees(
    func: &VerifiableFunction,
    callees: &[VerifiableFunction],
) -> Vec<(VerificationCondition, bool)> {
    let func = func.clone();
    let callees = callees.to_vec();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let mut db = trust_vcgen::SummaryDatabase::new();
            for callee in callees {
                db.insert(
                    trust_vcgen::FunctionSummary::new(callee.def_path.clone())
                        .with_extracted_body(std::sync::Arc::new(callee)),
                );
            }
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func,
                    &db,
                    true,
                    &context,
                    &std::collections::HashSet::<(BlockId, usize)>::new(),
                );
            let decided: Vec<_> = solver_vcs
                .into_iter()
                .map(|vc| {
                    let res = compiler_entry_verdict(&vc);
                    (vc, res)
                })
                .collect();
            preclassified
                .into_iter()
                .chain(decided)
                .map(|(vc, res)| {
                    let ok = is_discharged(&vc, &res);
                    (vc, ok)
                })
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

/// A body that PANICS at the check `select` picks may not have that check proved
/// on any lane the compiler reports:
///
///  * the per-statement rows of `generate_vcs` and of the compiler's entry satisfy
///    [`assert_none_discharged`]'s property (some row unproved; every proved one
///    rests on a passed runtime check, not a stale fact), each re-decided by the
///    lane that decided it;
///  * the `unix_hardened` twin of the MIR assert (`twin`) — "this assert cannot
///    fail" — is neither proved nor kernel-certified. It is the assert that fails.
fn assert_panicking_check_refutes(name: &str, select: fn(&VcKind) -> bool, twin: &str) {
    assert_fixture_refutes(&raw_const_fixture(name), name, select, Some(twin));
}

/// [`assert_panicking_check_refutes`] over an already-loaded `func`. `twin` is `None`
/// for a check that is a CALL (`<Vec as Index>::index`), which has no MIR assert and
/// so no hardened twin.
fn assert_fixture_refutes(
    func: &VerifiableFunction,
    name: &str,
    select: fn(&VcKind) -> bool,
    twin: Option<&str>,
) {
    assert_none_discharged(func, select, name);

    let rows = compiler_entry_rows(func);
    if let Some(twin) = twin {
        let twins: Vec<(String, bool)> = rows
            .iter()
            .filter(|(vc, _)| is_twin_of(&vc.kind, twin))
            .map(|(vc, ok)| (format!("{:?}", vc.kind), *ok))
            .collect();
        assert!(!twins.is_empty(), "{name}: the hardened `{twin}` twin was never generated");
        assert!(
            twins.iter().all(|(_, ok)| !ok),
            "{name}: the hardened twin of an assert that FAILS at runtime is discharged: \
             {twins:?}"
        );
    }
    let selected: Vec<_> = rows.into_iter().filter(|(vc, _)| select(&vc.kind)).collect();
    assert_rows_rest_on_passed_checks(
        func,
        selected,
        &compiler_entry_verdict,
        &format!("{name} (compiler entry, hardened)"),
    );
}

/// A body that reseats a slice local through a pointer to its SLOT and then indexes
/// it: every bounds row, on both lanes.
fn assert_slot_reseat_refutes(name: &str) {
    assert_panicking_check_refutes(name, is_bounds, BOUNDS_ASSERT);
}

/// THE B2 REGRESSION: `let mut s: &mut [u8] = a; let p = &raw const s as *mut
/// &mut [u8]; while k < n { *p = &mut []; k += 1 } s[i]`. Before the plain relation
/// the fixpoint's outflow kill judged the havoc base `s` (a mutable-pointer local)
/// with the destination relation, which also killed `s__slice_len` and so happened
/// to cover the missing slot channel; after it, the stale `s__slice_len == 8`
/// reached `s[i]` and every bounds row plus the hardened twin was kernel-certified
/// (measured on `ed7b99afc1`).
#[test]
fn a_raw_const_slot_reseat_in_a_loop_still_refutes() {
    assert_slot_reseat_refutes("reseat_raw_const_mut_loop");
}

/// The straight-line shapes, a kernel-certified false proof before B2 as well: the
/// reseat, the length read and the index share one block, so no outflow kill is
/// involved — only the store's own havoc list. Over a `&mut [u8]` local (a
/// mutable-pointer local) and a `&[u8]` local (on no havoc list at all without the
/// rule).
#[test]
fn a_raw_const_slot_reseat_straight_line_still_refutes() {
    assert_slot_reseat_refutes("reseat_raw_const_mut");
    assert_slot_reseat_refutes("reseat_raw_const_shared");
}

/// A SHARED slice local is not a mutable-pointer local, so even the old destination
/// relation never covered it: this loop was a false proof before B2.
#[test]
fn a_raw_const_shared_slice_reseat_in_a_loop_still_refutes() {
    assert_slot_reseat_refutes("reseat_raw_const_shared_loop");
}

/// A CALL writes the slot through the `&raw const`-derived pointer
/// (`reseat_through(&raw const s as *mut &[u8], &TWO)`): the call havoc reads the
/// same list, through `function_havoc_names`.
#[test]
fn a_raw_const_slot_written_by_a_call_still_refutes() {
    assert_slot_reseat_refutes("reseat_call_raw_const_shared");
}

/// CONTROLS: the same programs through `&raw mut`, the channel the list always
/// named. Green before and after the rule; red if `&raw mut` ever leaves it.
#[test]
fn a_raw_mut_slot_reseat_in_a_loop_still_refutes() {
    assert_slot_reseat_refutes("reseat_raw_mut_loop");
}

#[test]
fn a_raw_mut_slot_written_by_a_call_still_refutes() {
    assert_slot_reseat_refutes("reseat_call_raw_mut_shared");
}

/// Not only lengths: a scalar's value fact (`y == 5`) survived a write through
/// `&raw const y as *mut u8`, in the body and through a call, and `y + x.min(10)`
/// PROVED where it overflows at `250 + 10`.
#[test]
fn a_raw_const_scalar_write_does_not_keep_the_old_value() {
    assert_panicking_check_refutes("scalar_raw_const", is_u8_add, ADD_ASSERT);
    assert_panicking_check_refutes("scalar_call_raw_const", is_u8_add, ADD_ASSERT);
}

/// A guarded index whose index local is rewritten through `&raw const` between
/// the guard and the index: the guard's `m < s.len()` is about the OLD `m`.
#[test]
fn a_raw_const_write_of_a_guarded_index_still_refutes() {
    assert_slot_reseat_refutes("guard_then_raw_const");
}

/// A `mut` PARAMETER written through its own `&raw const` slot, in the body and by
/// a call. A parameter no statement assigns has its versions collapsed onto its
/// ENTRY value (`local_versions_collapse_to_bare`), gated by
/// `place_source_is_stable`, which listed `&mut` / `&raw mut` as the only alias
/// channels. So even with the store's havoc re-versioning `x`, the collapse folded
/// the new version back onto the entry `x`, and the guard `x < 5` discharged
/// `x + 10` after `x` became 250 (and `n < s.len()` discharged `s[n]` after `n`
/// became `usize::MAX`). Kernel-certified on both lanes on `main` before this
/// change; with only the havoc-list half of the fix the hardened twin refuted and
/// the per-statement row stayed proved (measured on the direct shapes; the union
/// review measured the call shapes the same way on the havoc-list-only branch).
#[test]
fn a_parameter_written_through_its_raw_const_slot_is_not_its_entry_value() {
    assert_panicking_check_refutes("reseat_raw_const_param", is_u8_add, ADD_ASSERT);
    assert_slot_reseat_refutes("reseat_raw_const_param_index");
    assert_panicking_check_refutes("param_written_by_a_call", is_u8_add, ADD_ASSERT);
    assert_slot_reseat_refutes("param_index_written_by_a_call");
}

// ------------------------------------ the pointee is not the slot (the `Deref` guard)

/// PRECISION CONTROL for the rule's `Deref` guard: `&raw const (*s)` of a SHARED
/// `s: &[u8]` hands out a pointer to the POINTEE, through which a write is UB under
/// both Stacked and Tree Borrows. The element fact `s[0] < 100` must survive the
/// call that receives that pointer, so `s[0] + 100` PROVES on both twins.
/// MEASURED on the union branch (2026-09-30): with the guard removed (every `&raw
/// const` listed) the add row and its hardened twin went to FAILED. Since the merge
/// with main's H2 rule (2026-10-08) this shared, `Freeze` pointee is ALSO left off by
/// `addr_of_is_read_only` (a write through it is UB), so removing the guard alone no
/// longer turns this control red (measured: the ledger's guard mutant leaves it
/// green); the guard itself is pinned by the unit tests of
/// generate/slot_write_channel_tests.rs. (rustc's own `PtrMetadata` idiom `&raw const
/// (*s)` appears only for a `&mut` slice, whose base name already covers its pointee.)
#[test]
fn the_pointee_of_a_shared_slice_keeps_its_element_fact() {
    let rows = compiler_entry_rows(&raw_const_fixture("raw_const_pointee_then_call"));
    let picked: Vec<_> = rows
        .iter()
        .filter(|(vc, _)| is_u8_add(&vc.kind) || is_twin_of(&vc.kind, ADD_ASSERT))
        .collect();
    assert_eq!(picked.len(), 2, "one add row and its hardened twin: {rows:#?}");
    for (vc, ok) in picked {
        assert!(
            ok,
            "`s[0] + 100` under `s[0] < 100` must prove across a call handed `&raw const \
             (*s)` of a shared slice — a pointer to the pointee is not a slot-write \
             channel: {:?}",
            vc.kind
        );
    }
}

/// SOUNDNESS COUNTER to the control above: the same shape over `s: &mut [u8]`,
/// with a callee that really writes `s[0] = 200` through the `&raw const (*s)`
/// pointer (defined under Tree Borrows). The pointee is not listed, and must not
/// need to be: `s` is a mutable-pointer local, on the havoc list by its type, and
/// its base name kills `s*[0]`. Panics natively (`attempt to add with overflow`).
#[test]
fn the_pointee_of_a_mut_slice_is_havoced_by_its_base() {
    assert_panicking_check_refutes("raw_const_pointee_write_through_mut", is_u8_add, ADD_ASSERT);
}

// ------------------ memory a SHARED reference reaches through a raw pointer
//
// A shared reference freezes the bytes it covers, not what a raw pointer stored in
// them points to: the pointer is `Copy`, `w.p` reads it out, and a write through it
// is defined under both aliasing models. `ty_contains_mut_pointer` does not recurse
// through `&`, so until 2026-09-30 nothing put that pointee on the havoc list, and
// the base-name coverage the slot rule's `Deref` exclusion cites
// (`mutable_pointer_local_names`) did not hold for it. The union closed it with a walk
// of its own (`shared_reach_pointer_names`, 2026-09-30, never on main). Main closed the
// CALL shapes independently (CALL-HAVOC-ESCAPE-2, 2026-10-06:
// `path_defs::stored_ref_pointee_names` havocs the memory behind every pointer stored
// in memory at every call, drop and opaque terminator). The STORE shapes stayed open
// on main `2767c5ff28` (no call between the write and the read): at landing
// (2026-10-08) the same names go on `function_havoc_names`, which every opaque store
// takes, in a function that has one; the union's walk was dropped. The frozen field
// beside the pointer keeps its fact. Source: tests/data/shared_reach_pointer_havoc.rs; every
// counter-program panics natively (-O0 and -O3: `the len is 4 but the index is
// 18446744073709551615`).

fn shared_reach(name: &str) -> VerifiableFunction {
    named_fixture("shared_reach_pointer_havoc", name)
}

/// MEASURED before the union's fix (2026-09-30, these fixtures through the compiler's
/// entry): each body's `[slice]` row AND its hardened `BoundsCheck` twin were
/// kernel-certified PROVED — the r8c union review's F2, whose first body's `[slice]`
/// row is also PROVED, kernel-rechecked, on the installed `321aaeda7` lane. A callee
/// handed a copy of the field (`poke_usize(w.p)`, no `&raw` anywhere), a write in the
/// body through `&raw const *w.p` and through `env.p as *mut usize`, and a closure
/// body (`_1: &{closure}`) writing through its captured `*const usize`. MEASURED on
/// main `2767c5ff28` (2026-10-08): the first refutes (CALL-HAVOC-ESCAPE-2); the three
/// in-body writes were still kernel-certified PROVED end to end on its stage 1
/// (`[slice]` row, clean-kernel evidence) and through this entry for
/// `shared_struct_raw_const_pointee`; all four refute after the landing.
#[test]
fn a_raw_pointer_reached_through_a_shared_reference_is_havoced() {
    for name in [
        "shared_struct_with_raw_ptr",
        "shared_struct_raw_const_pointee",
        "shared_env_cast_write",
        "closure_body_raw_const_deref_closure0",
    ] {
        assert_fixture_refutes(&shared_reach(name), name, is_bounds, Some(BOUNDS_ASSERT));
    }
}

/// Regression rows for the walk's other arms — the pointer two shared references
/// deep (`w**.0`), an owned tuple carrying the `&` (`w.1*.0`), and a `Box` behind the
/// `&` (`w*.0`, the `Box` place). These three refuted before the fix as well (each
/// read of the pointee goes through a fresh copy of the pointer, and the fact never
/// forms), so they are not evidence FOR the fix; the walk's names for these shapes
/// are pinned in src/generate/slot_write_channel_tests.rs.
#[test]
fn the_walks_other_arms_keep_refuting_their_panicking_bodies() {
    for name in [
        "shared_shared_struct_with_raw_ptr",
        "owned_tuple_carrying_a_shared_ref",
        "shared_struct_box_field",
    ] {
        assert_fixture_refutes(&shared_reach(name), name, is_bounds, Some(BOUNDS_ASSERT));
    }
}

/// PRECISION CONTROLS: the field BESIDE the raw pointer (`w.n`), and beside a `Box`,
/// sits in the frozen bytes, so `w.n < 8` still bounds `s[w.n]` across a call that
/// can write through the pointer. Both twins prove. A havoc of the shared
/// reference's BASE name (`w`) would kill `w*.1` too and turn both red.
#[test]
fn a_frozen_field_beside_a_raw_pointer_keeps_its_fact() {
    for name in ["shared_sibling_keeps_its_fact", "shared_box_sibling_keeps_its_fact"] {
        let rows = compiler_entry_rows(&shared_reach(name));
        let picked: Vec<_> = rows
            .iter()
            .filter(|(vc, _)| is_bounds(&vc.kind) || is_twin_of(&vc.kind, BOUNDS_ASSERT))
            .collect();
        assert_eq!(picked.len(), 2, "{name}: one index row and its hardened twin: {rows:#?}");
        for (vc, ok) in picked {
            assert!(
                ok,
                "{name}: `s[w.n]` under `w.n < 8` must prove across a call that writes only \
                 through the raw pointer beside `w.n`: {:?}",
                vc.kind
            );
        }
    }
}

// ------------------------- the field-length guard fact and the pointee channel
//
// `container_len`'s `build_len_guard_field_map` injects `coll_len(&self.v) >= C`
// after a dominating `if self.v.len() < C { return }`. It asked whether `self`'s own
// SLOT was stable (`place_source_is_stable`), which leaves `&raw const (*self)` off
// by design, so a callee handed `&raw const *self as *mut VH` cleared the `Vec`
// between the guard and a kernel-certified `self.v[3]`. It now asks
// `place_is_body_stable`, which adds the pointer rule over every place rooted at a
// reference root. Source: tests/data/field_len_guard_pointee_channel.rs; every
// counter-program panics natively (-O0 and -O3: `the len is 0 but the index is 3`).

fn field_len(name: &str) -> VerifiableFunction {
    named_fixture("field_len_guard_pointee_channel", name)
}

/// MEASURED before the fix (2026-09-30, the compiler's entry): each body's `[slice]`
/// row was kernel-certified PROVED — the r8c union review's F1. The index is a call
/// (`<Vec as Index>::index`), so there is no MIR assert and no hardened twin.
#[test]
fn a_field_length_guard_does_not_survive_a_pointer_to_the_pointee() {
    for name in
        ["field_len_guard_raw_const", "field_len_guard_raw_const_direct", "field_len_guard_free"]
    {
        assert_fixture_refutes(&field_len(name), name, is_bounds, None);
    }
}

/// CONTROLS: the same program through `&raw mut *self`, which the slot rule always
/// counted (refuted before and after), and a `Box` root, which refuted before as well
/// and which the rule now refuses by its root type.
#[test]
fn the_raw_mut_and_box_root_twins_still_refute() {
    for name in ["field_len_guard_raw_mut", "box_root_raw_const"] {
        assert_fixture_refutes(&field_len(name), name, is_bounds, None);
    }
}

/// PRECISION CONTROLS, the shapes the fact exists for: no pointer to `*self` is
/// minted, under `&mut self` and under `&self`, and `self.v[3]` proves from the guard.
#[test]
fn a_field_length_guard_with_no_pointer_to_the_pointee_still_proves() {
    for name in ["field_len_guard_no_channel", "field_len_guard_shared"] {
        let rows = compiler_entry_rows(&field_len(name));
        let picked: Vec<_> = rows.iter().filter(|(vc, _)| is_bounds(&vc.kind)).collect();
        assert_eq!(picked.len(), 1, "{name}: one index row: {rows:#?}");
        assert!(
            picked.iter().all(|(_, ok)| *ok),
            "{name}: `self.v[3]` after `if self.v.len() < 4 {{ return }}` with nothing able \
             to write `self.v` must prove: {picked:?}"
        );
    }
}

// -------- targets no retag protects, at a call with no pointer argument
//
// A call whose every argument is a pointer-free value reaches no caller local and no
// protected argument bytes, and `terminator_def_names`' 13b skip used to kill only
// its destination. But it can write through a copy of a pointer this function never
// retagged — a raw pointer anywhere, a `&mut` or `Box` stored behind a reference —
// stashed before the call, and that write is defined under both aliasing models. The
// union killed those targets by sub-place (`pure_value_call_havoc_names`, 2026-09-30,
// never on main). Main closed the same shapes independently on 2026-10-06: the TINV-18
// correction made the arm havoc `path_defs::escape_havoc` (the whole-function list but
// a protected private `&mut` parameter's own names), and CALL-HAVOC-ESCAPE-2 havocs
// the memory behind every stored pointer at every call. Every counter-program below
// refutes on main `2767c5ff28` (measured 2026-10-08, this entry and end to end), so at
// landing the union's walk was dropped for main's two rules; its precision is the
// cost recorded by `the_coarse_escape_rule_costs_a_scalar_beside_a_stored_pointer`.
// Source: tests/data/raw_pointee_across_pure_value_call.rs (MIR
// dumped with `-Zub-checks=no`); every counter-program panics natively (-O0 and -O3:
// `the len is 4 but the index is 18446744073709551615`).

fn pure_value(name: &str) -> VerifiableFunction {
    named_fixture("raw_pointee_across_pure_value_call", name)
}

/// MEASURED before the fix (2026-09-30, these fixtures through the compiler's
/// entry): each body's `[slice]` row and its hardened `BoundsCheck` twin were
/// kernel-certified PROVED — a raw-pointer parameter, the same across a call handed a
/// constant, a raw pointer behind `&` and behind `&mut`, a `&mut` stored behind
/// `&mut` and behind `&`, and a closure body's captured raw pointer, each across
/// `poke_global()`, which writes through `G`.
#[test]
fn a_target_no_retag_protects_dies_at_a_call_with_no_pointer_argument() {
    for name in [
        "stash_raw_param",
        "stash_raw_param_value_arg",
        "stash_shared_ref",
        "stash_mut_ref",
        "stash_mut_ref_behind_mut_ref",
        "stash_mut_ref_behind_shared_ref",
        "stash_closure_capture_closure0",
    ] {
        assert_fixture_refutes(&pure_value(name), name, is_bounds, Some(BOUNDS_ASSERT));
    }
}

/// A regression row for the walk's `Box` arm: a `Box` stored behind `&mut`, its
/// pointee written through a stashed child. It refuted before the fix as well (each
/// read of `*w.b` goes through a fresh place temp and the fact never forms), so it is
/// not evidence FOR the fix; the walk's name for it is pinned in
/// src/generate/slot_write_channel_tests.rs.
#[test]
fn a_box_stored_behind_a_mut_ref_keeps_refuting() {
    let name = "stash_box_behind_mut_ref";
    assert_fixture_refutes(&pure_value(name), name, is_bounds, Some(BOUNDS_ASSERT));
}

/// MEASURED before the fix: a `&mut` stored behind a SHARED reference kept its
/// target's fact across a call handed a pointer (`poke_global_ref(&i)`), because the
/// whole-function havoc list named only raw pointers and `Box`es reached through a
/// `&`; both rows were kernel-certified PROVED.
#[test]
fn a_mut_ref_stored_behind_a_shared_ref_dies_at_any_call() {
    let name = "stash_mut_ref_behind_shared_ref_pointer_arg";
    assert_fixture_refutes(&pure_value(name), name, is_bounds, Some(BOUNDS_ASSERT));
}

/// PRECISION CONTROLS that hold under the merged rule: a `&mut` parameter's own target
/// and a scalar parameter in a body that holds a raw pointer each keep `x < 8` across
/// `poke_global()`. Both rows prove.
#[test]
fn what_a_retag_protects_keeps_its_fact_across_a_call_with_no_pointer_argument() {
    for name in ["mut_ref_param_target_keeps_its_fact", "scalar_param_keeps_its_fact"] {
        let rows = compiler_entry_rows(&pure_value(name));
        let picked: Vec<_> = rows
            .iter()
            .filter(|(vc, _)| is_bounds(&vc.kind) || is_twin_of(&vc.kind, BOUNDS_ASSERT))
            .collect();
        assert_eq!(picked.len(), 2, "{name}: one index row and its hardened twin: {rows:#?}");
        for (vc, ok) in picked {
            assert!(
                ok,
                "{name}: the index must prove across a call that can write only targets no \
                 retag protects: {:?}",
                vc.kind
            );
        }
    }
}

/// THE PRICE OF THE COARSE ESCAPE RULE, MEASURED (2026-10-08). The union's own
/// pure-value kill (`pure_value_call_havoc_names`, by sub-place) proved these three: a
/// scalar in the bytes a `&mut` parameter protects, beside a raw pointer, a `Box` or a
/// stored `&mut`. Main's TINV-18 correction (2026-10-06) replaced the pure-value arm's
/// havoc by `path_defs::escape_havoc`, which spares a `&mut` parameter's names only
/// when its pointee holds no pointer but shared references to plain data
/// (`protected_private_mut_param`), and CALL-HAVOC-ESCAPE-2 havocs the memory behind
/// every stored pointer at every call. At landing the union's walk was dropped for
/// those two rules (one rule per question), and these rows refute: false refutations
/// of correct programs (each returns natively), never false proofs. On main's stage 1
/// `2767c5ff28`, end to end (`-Zub-checks=no`), the same three `bounds` rows are
/// `failed`. This test FAILS if a row is recovered — that is progress (an escape rule
/// that spares a protected scalar beside a stored pointer); promote it with this doc.
#[test]
fn the_coarse_escape_rule_costs_a_scalar_beside_a_stored_pointer() {
    for name in [
        "mut_ref_scalar_keeps_its_fact",
        "mut_ref_scalar_beside_a_box_keeps_its_fact",
        "mut_ref_scalar_beside_a_stored_mut_ref_keeps_its_fact",
    ] {
        let rows = compiler_entry_rows(&pure_value(name));
        let picked: Vec<_> = rows
            .iter()
            .filter(|(vc, _)| is_bounds(&vc.kind) || is_twin_of(&vc.kind, BOUNDS_ASSERT))
            .collect();
        assert_eq!(picked.len(), 2, "{name}: one index row and its hardened twin: {rows:#?}");
        assert!(
            picked.iter().any(|(_, ok)| !ok),
            "{name}: a row was recovered — promote it to the control above: {picked:?}"
        );
    }
}

// ------------------------- the establish point of a store through a pointer
//
// A store `*x = v` emits the block def `x* == v`, and the lanes that thread block
// defs into successors version each def at the statement that establishes it. Every
// establish search was keyed on the subject's BASE `x` (the borrow `x = &..`), which
// a store through `x` never writes, so the store's def was threaded BARE and shared
// its symbol with the bare read of `*x` BEFORE the store: `i == m*` and `m* ==
// usize::MAX` together made the guard `i < s.len()` read `usize::MAX < s.len()`.
// `block_defs::def_subject_establish_stmt` keys the search on the subject. Source:
// tests/data/store_through_pointer_establish.rs; every counter-program panics
// natively (-O0 and -O3: `the len is 4 but the index is 18446744073709551615`).

fn store_establish(name: &str) -> VerifiableFunction {
    named_fixture("store_through_pointer_establish", name)
}

/// MEASURED before the fix (2026-09-30, these fixtures through the compiler's
/// entry): each body's `[slice]` row was kernel-certified PROVED (its hardened twin
/// refuted) — a store through a raw-pointer parameter, through a raw pointer behind
/// `&` and behind `&mut`, through `&raw mut *w.p`, and a closure body storing through
/// its captured `*mut usize` directly and through `&raw mut *p` (the r8c union
/// review's two closure controls).
#[test]
fn a_store_through_a_pointer_is_not_the_value_read_before_it() {
    for name in [
        "store_through_raw_param",
        "store_through_shared_ref_field",
        "store_through_mut_ref_field",
        "store_through_raw_mut_reborrow",
        "store_through_closure_capture_closure0",
        "store_through_closure_capture_reborrow_closure0",
    ] {
        assert_fixture_refutes(&store_establish(name), name, is_bounds, Some(BOUNDS_ASSERT));
    }
}

/// A regression row: the same store through a `&mut` PARAMETER refuted before the fix
/// as well (its pre-store read is versioned by another lane), so it is not evidence
/// FOR the fix.
#[test]
fn a_store_through_a_mut_ref_param_keeps_refuting() {
    let name = "store_through_mut_ref_param";
    assert_fixture_refutes(&store_establish(name), name, is_bounds, Some(BOUNDS_ASSERT));
}

/// PRECISION CONTROLS: the stored value itself bounds the index (`*m = 3; s[*m]`
/// with `s: &[u8; 8]`), through a raw pointer and through a `&mut`. The versioned
/// store def must connect to the read after it; both rows prove.
#[test]
fn the_stored_value_still_bounds_the_read_after_the_store() {
    for name in
        ["stored_value_through_raw_param_proves", "stored_value_through_mut_ref_param_proves"]
    {
        let rows = compiler_entry_rows(&store_establish(name));
        let picked: Vec<_> = rows
            .iter()
            .filter(|(vc, _)| is_bounds(&vc.kind) || is_twin_of(&vc.kind, BOUNDS_ASSERT))
            .collect();
        assert_eq!(picked.len(), 2, "{name}: one index row and its hardened twin: {rows:#?}");
        for (vc, ok) in picked {
            assert!(ok, "{name}: `*m = 3; s[*m]` must prove: {:?}", vc.kind);
        }
    }
}

// ------------------------- a standard-library struct in the unretagged-pointer walk
//
// The union's walk (`unretagged_pointer_names_of`, dropped at landing for
// `path_defs::stored_ref_pointee_names`) walked a std struct like any other struct. A WIP
// carve-out of it (2026-09-30, never landed) left every `alloc::`/`core::`/`std::`
// struct but `Box` out, on the premise that a std struct's fields are private and
// never spelled in a caller's body. `Range<*mut T>`'s `start` and `Wrapping<*mut T>`'s
// `.0` are public. `stored_ref_pointee_names` skips std structs only in a body that
// never projects a std struct field (`body_projects_into_std_adt`, fail-closed), and
// these bodies do; all refute on main `2767c5ff28` and after the landing. Source: tests/data/std_struct_pointer_havoc.rs (MIR dumped with
// `-Zub-checks=no`); every counter-program panics natively (-O0 and -O3: `the len is 4
// but the index is 18446744073709551615`).

fn std_struct(name: &str) -> VerifiableFunction {
    named_fixture("std_struct_pointer_havoc", name)
}

/// MEASURED under the carve-out (2026-09-30, these fixtures through the compiler's
/// entry): the `[slice]` row and its hardened `BoundsCheck` twin of each of these four
/// bodies were kernel-certified PROVED — the F2 shape with a callee handed
/// `w.start` / `w.0` behind `&Range<*mut usize>` / `&Wrapping<*mut usize>`, and the
/// pure-value twin behind `&Range` and `&mut Range`. They refute.
#[test]
fn a_raw_pointer_in_a_std_struct_is_havoced_like_any_other() {
    for name in [
        "shared_range_raw_ptr",
        "shared_range_pure_value_call",
        "shared_wrapping_raw_ptr",
        "mut_range_pure_value_call",
    ] {
        assert_fixture_refutes(&std_struct(name), name, is_bounds, Some(BOUNDS_ASSERT));
    }
}

/// Regression rows, refuted with and without the carve-out, so not evidence FOR the
/// walk: an owned `Range<*mut usize>`, and a `Vec`'s buffer written through a stashed
/// copy of `as_mut_ptr()` between two `v[0]` reads. The extraction renders `&Vec<T>`
/// as `&Seq`, whose element reads are fresh call results that nothing ties together;
/// `value_facts`' global `Vec` index/value tie admits only a `Vec` rendered with its
/// fields, so it does not fire here.
#[test]
fn an_owned_std_struct_and_a_vec_buffer_keep_refuting() {
    for name in [
        "owned_range_pure_value_call",
        "vec_index_across_a_pure_value_call",
        "vec_index_across_a_pointer_call",
        "vec_index_local_across_a_pure_value_call",
    ] {
        assert_fixture_refutes(&std_struct(name), name, is_bounds, Some(BOUNDS_ASSERT));
    }
}

/// PRECISION CONTROL: a `Vec`'s length lives in the bytes `&v` freezes, and `&Seq` is
/// not walked, so `i < v.len()` still bounds `v[i]` (`<Vec as Index>::index`, a call
/// with no MIR assert and so no hardened twin) across `poke_global()`.
#[test]
fn a_vec_length_guard_survives_a_call_with_no_pointer_argument() {
    let name = "vec_len_guard_across_a_pure_value_call";
    let rows = compiler_entry_rows(&std_struct(name));
    let picked: Vec<_> = rows.iter().filter(|(vc, _)| is_bounds(&vc.kind)).collect();
    assert_eq!(picked.len(), 1, "{name}: one index row: {rows:#?}");
    for (vc, ok) in picked {
        assert!(ok, "{name}: `v[i]` under `i < v.len()` must prove: {:?}", vc.kind);
    }
}

// ------------------------- a user type NAMED `Vec`
//
// `generate::panic_calls::is_owned_slice_container_name` grants every fact about
// std's `Vec` — among them `value_facts`' index/value tie, "two `v[i]` reads at one
// index are one element". It matched the path's TAIL, so a user type named `Vec`
// qualified, with an `Index` impl of its own. Source: tests/data/user_type_named_vec.rs
// (safe code: the impl flips a `Cell` and returns a different element on each call);
// every counter-program panics natively (-O0 and -O3: `the len is 4 but the index is
// 18446744073709551615`).

fn user_vec(name: &str) -> VerifiableFunction {
    named_fixture("user_type_named_vec", name)
}

/// MEASURED before the fix (2026-09-30, these fixtures through the compiler's entry):
/// the `[slice]` row of `s[v[0]]` and its hardened `BoundsCheck` twin were
/// kernel-certified PROVED for each body — the tie equated the two `v[0]` reads.
#[test]
fn a_user_type_named_vec_gets_no_std_vec_fact() {
    for name in ["user_vec_twice", "user_vec_local", "user_generic_vec_twice"] {
        assert_fixture_refutes(&user_vec(name), name, is_bounds, Some(BOUNDS_ASSERT));
    }
}

/// PRECISION CONTROL: a slice root keeps its element tie (a direct place read, a
/// different builder), so every index row of `if !v.is_empty() && v[0] < s.len() {
/// s[v[0]] }` proves, with its hardened twin (measured: three of each, before and
/// after the fix).
#[test]
fn a_slice_read_twice_still_proves() {
    let name = "slice_read_twice";
    let rows = compiler_entry_rows(&user_vec(name));
    let picked: Vec<_> = rows
        .iter()
        .filter(|(vc, _)| is_bounds(&vc.kind) || is_twin_of(&vc.kind, BOUNDS_ASSERT))
        .collect();
    assert_eq!(picked.len(), 6, "{name}: three index rows and their twins: {rows:#?}");
    for (vc, ok) in picked {
        assert!(ok, "{name}: `s[v[0]]` under `v[0] < s.len()` must prove: {:?}", vc.kind);
    }
}

// ------------------------- the callee write-set lane over a stored pointer
//
// With a callee's extracted body in the summary database, a call handed a whole `&mut`
// local replaces that local's base-name havoc with the paths the callee's MIR writes
// through it (`callee_write_set::refine_call_havoc_delta`). Both of the lane's
// refusals ask the unretagged-pointer question since 2026-09-30, so a receiver whose
// pointee stores a `&mut`, raw pointer or `Box` behind a `&` keeps its base-name
// havoc. Source: tests/data/callee_write_set_unretagged.rs; every counter-program
// panics natively (-O0 and -O3: `the len is 4 but the index is
// 18446744073709551615`). The refusals themselves are pinned in
// src/generate/callee_write_set/tests.rs, which is what kills the old question:
// these bodies refute with it as well, because reading the stored pointer's target
// takes two deref temporaries and the second one's pointee is never renamed to a
// place under the receiver (measured 2026-10-01, the probe with and without the
// r8c finish's mutant `MCWS`).

fn cws(name: &str) -> VerifiableFunction {
    named_fixture("callee_write_set_unretagged", name)
}

/// Regression rows: each body refutes with its callee's body in the summary
/// database, the database the compiler builds.
#[test]
fn a_pointer_stored_behind_a_shared_ref_keeps_refuting_with_the_callee_body() {
    for (name, callee) in [
        ("stored_mut_behind_shared", "touch_mr"),
        ("stored_raw_behind_shared", "touch_pr"),
        ("stored_box_behind_shared", "touch_br"),
    ] {
        let func = cws(name);
        let rows = compiler_entry_rows_with_callees(&func, &[cws(callee)]);
        let twins: Vec<_> =
            rows.iter().filter(|(vc, _)| is_twin_of(&vc.kind, BOUNDS_ASSERT)).collect();
        assert!(!twins.is_empty(), "{name}: the hardened twin was never generated");
        assert!(
            twins.iter().all(|(_, ok)| !ok),
            "{name}: the twin of an assert that FAILS at runtime is discharged: {twins:?}"
        );
        let selected: Vec<_> = rows.into_iter().filter(|(vc, _)| is_bounds(&vc.kind)).collect();
        assert_rows_rest_on_passed_checks(
            &func,
            selected,
            &compiler_entry_verdict,
            &format!("{name} (compiler entry, hardened, with `{callee}`'s body)"),
        );
    }
}

/// PRECISION CONTROL, and the evidence that the lane is live in this harness: with
/// only a frozen `&usize` under `*x`'s `&`, `x.n < s.len()` bounds `s[x.n]` across
/// `touch_sr(x)` once `touch_sr`'s body (which writes nothing through `x`) is in the
/// database; without it the base-name havoc of `x` kills the guard. Both rows, each
/// way (measured 2026-10-01).
#[test]
fn a_callee_body_spares_a_field_it_does_not_write() {
    let name = "frozen_field_across_a_callee_body";
    let pick = |rows: Vec<(VerificationCondition, bool)>| -> Vec<(String, bool)> {
        rows.into_iter()
            .filter(|(vc, _)| is_bounds(&vc.kind) || is_twin_of(&vc.kind, BOUNDS_ASSERT))
            .map(|(vc, ok)| (format!("{:?}", vc.kind), ok))
            .collect()
    };
    let with = pick(compiler_entry_rows_with_callees(&cws(name), &[cws("touch_sr")]));
    assert_eq!(with.len(), 2, "{name}: one index row and its hardened twin: {with:?}");
    assert!(with.iter().all(|(_, ok)| *ok), "{name}: must prove with the body: {with:?}");
    let without = pick(compiler_entry_rows(&cws(name)));
    assert_eq!(without.len(), 2, "{name}: one index row and its hardened twin: {without:?}");
    assert!(
        without.iter().all(|(_, ok)| !ok),
        "{name}: without the callee's body the call havocs `x` whole: {without:?}"
    );
}
