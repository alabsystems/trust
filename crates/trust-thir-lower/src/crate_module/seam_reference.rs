//! Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): the crate-seam differential AS
//! IT WAS before its one-working-copy rewrite, kept as the CROSS-CHECK ORACLE for that rewrite.
//!
//! `run_seam_differentials` and `row1_uc_probe` below are the pre-R8-SEAM text of
//! `crate_module.rs` (blob `cf20b80d0dfc10181e87217b234ab7d73e7b83f0`; since the merge of trust-ir
//! train T8, a0715f99d4, the text of its blob `d1433859048026a220e257be63fdd2babf15584f`, whose one
//! hunk in these two functions — the oracle-assert strip binds `Inst::Assert { cond, .. }`, forced
//! by trust-ir v52's new fields — is applied here too), verbatim except for the
//! edits marked `[reference: ...]`, their `pub(super)` visibility, and the `uc_events` sink both
//! signatures take: the UC probe records its outcome into that sink instead of tracing it (the
//! live seam traces it), and the row-1 dead-path probe (an instrument behind tracing, unchanged in
//! the live seam) is not run a second time. Each copies the WHOLE assembled module where the live
//! seam patches its one working copy: `row1_uc_probe` once per sample leg, `module_without_drops`
//! once per drop-bearing closure, and the differential once per pointer-lane comparison. Both
//! compare through the pre-R8-SEAM DIFFERENTIAL too: `differential::compare_entries_reference::
//! compare_entries` (verbatim, with the copying `build_pointee_wrapper` and the THIR-side
//! promoted-global pairing), not `differential::compare_entries`, which R8-SEAM split at its step
//! boundaries and re-paired — so the cross-check is the old seam end to end, both frozen files'
//! old code, against the new one end to end, and a fault in either file's movement is a
//! difference.
//!
//! [`cross_checked`] runs the live seam and this one over the same records and module and
//! compares every verdict and every traced UC probe outcome, field for field. It is reached
//! only through the TEST-ONLY tracked option `-Ztrust-ir-seam-reference=<report path>`
//! (`TRUST_AUTHORITY: EvidenceControl`, unset in every real build): a difference fails crate
//! finalization, and the report file says what was compared. R-2's deletion of the seam
//! differential deletes this file with it.

use std::cell::RefCell;
use std::fmt::Write as _;
use std::path::Path;

use super::*;

/// The test hook's option; its value is the path the cross-check's report is written to.
pub(super) const OPTION: &str = "-Ztrust-ir-seam-reference";

/// Run the live seam and the reference over the same input, compare them, write the report to
/// `report`, and push one error onto `errors` when anything differs. Returns the live verdicts.
pub(super) fn cross_checked(
    records: &[BodyRecord],
    assembled: &Assembled,
    report: &Path,
    errors: &mut Vec<String>,
) -> Vec<SeamVerdict> {
    let live_events = RefCell::new(Vec::new());
    let (live, stats) = super::run_seam_differentials(records, assembled, Some(&live_events));
    let reference_events = RefCell::new(Vec::new());
    let reference = run_seam_differentials(records, assembled, &reference_events);
    let (live_events, reference_events) = (live_events.into_inner(), reference_events.into_inner());

    let differences = differences(&live, &reference, &live_events, &reference_events, &stats);
    if let Err(error) = std::fs::write(report, render(&live, &live_events, &stats, &differences)) {
        errors.push(format!(
            "trust-ir-lower seam cross-check ({OPTION}): could not write {}: {error}",
            report.display()
        ));
    }
    if let Some(first) = differences.first() {
        errors.push(format!(
            "trust-ir-lower seam cross-check ({OPTION}, R8-SEAM): the one-working-copy seam differs \
             from the pre-R8-SEAM reference in {} place(s); first: {first}",
            differences.len()
        ));
    }
    live
}

/// Every place the live seam's output differs from the reference's.
pub(super) fn differences(
    live: &[SeamVerdict],
    reference: &[SeamVerdict],
    live_events: &[UcProbeEvent],
    reference_events: &[UcProbeEvent],
    stats: &SeamScratchStats,
) -> Vec<String> {
    let key = |v: &SeamVerdict| (v.def_index, v.equal, v.samples, v.mode, v.note.clone());
    let mut out = Vec::new();
    if live.len() != reference.len() {
        out.push(format!("{} verdict(s) against the reference's {}", live.len(), reference.len()));
    }
    for (l, r) in live.iter().zip(reference) {
        if key(l) != key(r) {
            out.push(format!("verdict {:?} against the reference's {:?}", key(l), key(r)));
        }
    }
    if live_events.len() != reference_events.len() {
        out.push(format!(
            "{} UC probe outcome(s) against the reference's {}",
            live_events.len(),
            reference_events.len()
        ));
    }
    for (l, r) in live_events.iter().zip(reference_events) {
        if l != r {
            out.push(format!("UC probe outcome {l:?} against the reference's {r:?}"));
        }
    }
    if !stats.restored {
        out.push("the working copy is not the assembled module after the pass".to_string());
    }
    out
}

/// The report: one `key value` line per count, one `difference` line per difference, then one
/// line per live verdict and per traced UC probe outcome.
fn render(
    live: &[SeamVerdict],
    live_events: &[UcProbeEvent],
    stats: &SeamScratchStats,
    differences: &[String],
) -> String {
    use crate::differential::DiffMode;
    let mut text = String::new();
    let _ = writeln!(text, "verdicts {}", live.len());
    for mode in [
        DiffMode::NotRun,
        DiffMode::MirOracle,
        DiffMode::Agreed,
        DiffMode::AgreedUninterpretedCallee,
    ] {
        let n = live.iter().filter(|v| v.mode == mode).count();
        let _ = writeln!(text, "mode {mode:?} {n}");
    }
    let mut outcomes: BTreeMap<&str, usize> = BTreeMap::new();
    for event in live_events {
        *outcomes.entry(event.outcome.as_str()).or_default() += 1;
    }
    let _ = writeln!(text, "uc-events {}", live_events.len());
    for (outcome, n) in outcomes {
        let _ = writeln!(text, "uc {outcome} {n}");
    }
    let _ = writeln!(text, "copies {}", stats.copies);
    let _ = writeln!(text, "comparisons {}", stats.comparisons);
    let _ = writeln!(text, "uc-legs {}", stats.uc_legs);
    let _ = writeln!(text, "drop-strips {}", stats.drop_strips);
    let _ = writeln!(text, "patched-blocks {}", stats.patched_blocks);
    let _ = writeln!(text, "wrapped {}", stats.wrapped);
    let _ = writeln!(text, "restored {}", stats.restored);
    let _ = writeln!(text, "differences {}", differences.len());
    for difference in differences {
        let _ = writeln!(text, "difference {difference}");
    }
    // Every live verdict and traced outcome, in order, so two reports can be compared byte for byte.
    for v in live {
        let _ = writeln!(
            text,
            "verdict {} {} {} {:?} {:?}",
            v.def_index, v.equal, v.samples, v.mode, v.note
        );
    }
    for e in live_events {
        let _ = writeln!(
            text,
            "uc-event {} {} {} {:?}",
            e.def_index, e.outcome, e.samples, e.detail
        );
    }
    text
}

/// Trust (B9-A): the crate-seam call-linking differential. For every DEFERRED body (clean +
/// call-bearing, `BodyRecord::deferred`), interpretation-equivalence was NOT asserted at the hook
/// because the per-body module carried its callees as bodyless declarations. Here — after
/// [`assemble`] spliced the whole crate and rewrote every intra-crate callee `FuncId` — we gather
/// the deferred body's reachable-callee CLOSURE, build the MIR-side oracle by bundling each
/// closure member's `mir_snapshot` through the SAME `lower_to_trust_ir_functions` path the hook
/// uses for a single body, and run the sampled-interpretation comparison. Exactly one
/// [`SeamVerdict`] per deferred body; every gate fails CLOSED to a coverage-only `NotRun` skip
/// (never a false equivalence claim).
pub(super) fn run_seam_differentials(
    records: &[BodyRecord],
    assembled: &Assembled,
    uc_events: &RefCell<Vec<UcProbeEvent>>,
) -> Vec<SeamVerdict> {
    use crate::differential::{self, DiffMode};

    let skip = |def_index: u32, note: &str| SeamVerdict {
        def_index,
        equal: false,
        samples: 0,
        mode: DiffMode::NotRun,
        note: note.to_string(),
    };

    // `records` and `assembled.assigned` are both def_index-sorted; `assigned[i] == (def_i, FuncId(i))`
    // (spliced functions are added in ascending def_index == ascending FuncId order, `f.id = new_id`).
    let rec_by_def = |def_index: u32| -> Option<&BodyRecord> {
        records.binary_search_by_key(&def_index, |r| r.def_index).ok().map(|i| &records[i])
    };
    // Spliced (dense) FuncId -> its callee def_index. Declaration FuncIds (>= assigned.len()) return
    // None here — but they are filtered by the step-2 declaration gate before this is reached.
    let def_of_func =
        |fid: FuncId| -> Option<u32> { assembled.assigned.get(fid.as_usize()).map(|(d, _)| *d) };
    let func_of_def = |def_index: u32| -> Option<FuncId> {
        assembled
            .assigned
            .binary_search_by_key(&def_index, |(d, _)| *d)
            .ok()
            .map(|i| assembled.assigned[i].1)
    };

    let mut verdicts = Vec::new();
    for r in records.iter().filter(|r| r.deferred) {
        // Trust (slice 20) — THE PENDING-CONST FAIL-CLOSE. MANDATORY, and it must be the FIRST
        // gate in this loop.
        //
        // `r.deferred` was decided at the HOOK, before `resolve_pending_consts` ran. That pass
        // is not infallible and does not merely fail to improve a body — it BUMPS
        // `r.unsupported` at every failure site it has (`PendingStr(eval failed at finalize)`,
        // `PendingStr(empty)`, `PendingStr(global not patched)`, `PendingStr(global patch
        // conflict)`, `PendingConst(eval failed at finalize)`, `PendingConst(placeholder not
        // found)`, `PendingConst(sentinel leak)`, and the `check_str_global_ledger` rows).
        //
        // A body that took any of those still carries its PLACEHOLDER. Interpreting it is
        // precisely what the hook-time gate exists to prevent: the placeholder is a
        // `Constant::PhantomData` where the oracle has a real value, so the comparison
        // manufactures a false TypeError-vs-value DIVERGENCE — a published claim that the
        // producer is wrong about a body whose const nobody ever evaluated.
        //
        // Re-testing emptiness here is therefore not belt-and-braces: it is the same gate,
        // re-asked at the only point where its answer can have changed. It is stated for ALL
        // deferred bodies rather than only pending-const ones because it is true of all of them
        // (a call-only deferred body's `unsupported` is untouched by that pass), and a gate that
        // reads "no body may be linked while it carries an unsupported shape" is a stronger and
        // more obviously correct invariant than one scoped to the lane that motivated it.
        if !r.unsupported.is_empty() {
            // Trust (decision 2026-09-17(b)): SPLIT THE NOTE BY CAUSE. The gate is unchanged
            // — any unsupported shape still refuses interpretation — but the note is read as
            // data: `scripts/trust_ir_producer_scorecard.py` buckets
            // "finalizer const resolution failed" as `clean-skip-pending-const-unresolved`,
            // "the only number that says whether the lane's ceiling is the gate or the
            // evaluator". A body refused for minting an unsignable Rust-ABI call edge has
            // nothing to do with const evaluation, and reusing that note would inflate that
            // number with a population it does not measure. The two sets are disjoint by
            // construction: the unsignable-edge refusal only ever marks a body that SPLICED,
            // and a body `resolve_pending_consts` marked never splices.
            // [reference: WS5.2's one hunk in this function, applied here too as the T8 hunk was:
            // the live seam's note gained a third cause (a body refused for link-time symbol
            // identity), so both seams read it from the one `unsupported_body_skip_note`. A note
            // is data, never a decision: the skip itself, and every verdict field the
            // cross-check compares besides this text, is the pre-R8-SEAM code above.]
            verdicts.push(skip(r.def_index, super::unsupported_body_skip_note(&r.unsupported)));
            continue;
        }
        // Trust (B3-2c seam guard): a place-path VALUE-carrier body is CLEAN-ONLY
        // by the wave-RS/MC contract ("never interpreted") — the carrier arg is a
        // VALUE standing in for the callee's pointer param, so linked
        // interpretation manufactures a signature-mismatch THIR-defect verdict
        // out of a deliberate spelling. Fail closed to coverage. Genuinely
        // ill-typed calls (no carrier) still surface as defects.
        if r.place_path_carrier {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: call args carry a place-path value carrier \
                 (CLEAN-ONLY receiver spelling); linked interpretation not asserted \
                 (coverage-only)",
            ));
            continue;
        }
        // Trust (wave-ZC): a ZST-closure-arg body is refused by `splice_ok` on its own field, so
        // step 0 below already skips it (`func_of_def` → `None`). State the skip HERE too, on the
        // flag itself, so the seam wall is a SECOND decision of ours and not a consequence of the
        // splice verdict: if `splice_ok`'s line is ever relaxed (the recovery path needs a
        // positive witness at the callee's declared input — see `Lowered::zst_closure_arg`), the
        // linked interpreter must still not be handed a `Ty::Unit` standing in for a callee's
        // declared closure param, which is exactly the manufactured signature-mismatch defect the
        // `place_path_carrier` skip above exists to prevent.
        if r.zst_closure_arg {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: call args carry a ZST closure value (Ty::Unit/PhantomData \
                 standing in for a closure-typed param); linked interpretation not asserted \
                 (coverage-only)",
            ));
            continue;
        }
        // Trust (fn-ptr adapter lane): an adapter-bearing body is refused by `splice_ok` on its
        // own field, so step 0 below already skips it (`func_of_def` → `None`). State the skip
        // HERE too, on the flag itself, for the same reason the `zst_closure_arg` skip above is
        // stated twice: the linked interpreter must never be handed a body whose instruction
        // stream names a function the assembled module does not contain, and that must not depend
        // on `splice_ok`'s line staying where it is.
        if r.fnptr_adapter {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: module carries a producer-synthesized closure→fn-pointer \
                 adapter (no rustc counterpart, dropped at record); linked interpretation not \
                 asserted (coverage-only)",
            ));
            continue;
        }
        // step 0 — entry: the deferred body must be spliced into the crate module.
        let Some(entry) = func_of_def(r.def_index) else {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: entry not spliced into the crate module; coverage-only skip",
            ));
            continue;
        };

        // step 1 — reachable-callee closure: BFS over the assembled module from `entry`. Edges:
        // `Inst::Call{callee}`, `Inst::Const{Constant::FnDef}` (reified fn pointers — the same
        // ledger-rewritten ids assemble produced), and a defensive `Inst::Invoke{callee}` arm (the
        // producer never emits it). `CallIndirect` carries no static target — every reified target
        // is a FnDef const already walked, and a fn-ptr PARAM cannot inject an outside target
        // (`Ty::Func` params fail the scalar sample gate downstream).
        let mut closure: Vec<FuncId> = Vec::new();
        let mut seen: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut stack = vec![entry];
        while let Some(fid) = stack.pop() {
            if !seen.insert(fid.index()) {
                continue;
            }
            closure.push(fid);
            let Some(func) = assembled.module.function_by_id(fid) else { continue };
            for block in &func.blocks {
                for node in &block.body {
                    match &node.inst {
                        Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
                            stack.push(*callee)
                        }
                        Inst::Const { value: Constant::FnDef(target), .. } => stack.push(*target),
                        _ => {}
                    }
                }
            }
        }

        // step 2 — declaration gate: any bodyless callee in the closure means there is no local
        // body to link. LOAD-BEARING: a reachable vararg-sig declaration would err
        // `SignatureMismatch` in the interpreter, which would surface as a FALSE oracle verdict.
        //
        // Trust (B8 step 1): "no local body to link" is FIVE different facts — see [`DeclKind`].
        // This gate is the corpus's largest single non-verdict class (983 clean rows on
        // postbuild-slice20-control), and until this slice it reported all five under one name,
        // which happened to be the name of only one of them. `blocker_summary` below names them.
        //
        // NOTE FOR ANYONE PRICING THIS CLASS: the count here is a FIRST-BLOCKER count. This loop
        // is an eight-step first-wins chain, so a body refused at step 2 has never been tested
        // against steps 3-8, and clearing step 2 for it is not the same as reaching a verdict.
        // Measured on the same artifact, the bodies that DO clear step 2 reach `Agreed` 70 times
        // out of 164 — and they are the easy end of the population (a fully bodyful closure).
        let declarations: Vec<FuncId> = closure
            .iter()
            .copied()
            .filter(|&fid| {
                assembled.module.function_by_id(fid).map(|f| f.is_declaration()).unwrap_or(true)
            })
            .collect();
        if !declarations.is_empty() {
            // Trust (absent-callee Stage 3): the fenced UC adjudication is SEMANTICS now — the
            // sanctioned graduation of the Stage-1.5 probe, per
            // docs/design/2026-08-31-absent-callee-adjudication.md §6 stages 2-3. It runs
            // unconditionally (a verdict cannot depend on the tracing level), traces every
            // outcome exactly as the probe did (single emission — the dead-path probe below no
            // longer calls it), and mints `DiffMode::AgreedUninterpretedCallee` — NEVER plain
            // `Agreed` — only when every sampled leg agreed under the full no-channel fence
            // and the count/shape pairing. Every other outcome keeps the skip verbatim.
            let uc = build_expected_absent_bundle(r, &closure, &declarations, records, assembled)
                .ok()
                .and_then(|(bundle, entry_slot)| {
                    row1_uc_probe(r, entry, &declarations, assembled, &bundle, entry_slot, uc_events)
                });
            // [reference: the row-1 DEAD-PATH probe, an instrument behind tracing, runs in the
            // live seam only, where it is unchanged.]
            if let Some((samples, detail)) = uc {
                verdicts.push(SeamVerdict {
                    def_index: r.def_index,
                    equal: false,
                    samples,
                    mode: DiffMode::AgreedUninterpretedCallee,
                    note: detail,
                });
                continue;
            }
            // Trust (B8 step 1): NAME the blockers. Everything before the `[blockers: …]` marker
            // is the pre-split string byte for byte, because three published analyses quote it as
            // a substring and the scorecard's legacy rule still matches on it.
            verdicts.push(skip(
                r.def_index,
                &format!(
                    "seam-deferred body: reachable callee closure includes an \
                     extern/declaration-only callee (no local body to link) [blockers: {}]; \
                     crate-seam interpretation not asserted (coverage-only)",
                    blocker_summary(assembled, &declarations)
                ),
            ));
            continue;
        }

        // step 3 — THIR Undef tripwire, scoped PER-CLOSURE (not whole-module: one unrelated
        // invariant-violating body must not over-skip every deferred body).
        if closure.iter().any(|&fid| {
            assembled
                .module
                .function_by_id(fid)
                .map(differential::function_has_undef)
                .unwrap_or(false)
        }) {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: THIR crate module function unexpectedly carries Inst::Undef \
                 (producer invariant violated); coverage-only skip",
            ));
            continue;
        }

        // step 4 — snapshot gathering. Map each closure FuncId -> callee def_index -> its record's
        // `mir_snapshot`. Any missing snapshot => callee-set asymmetry => fail-closed skip.
        //
        // Trust (slice 20): a PENDING-CONST callee is no longer an instance of that. It used to
        // be — `compare` returned `None` for such a body, so any deferred caller reaching one
        // lost its whole verdict to this asymmetry skip — and the parenthetical here named it as
        // the example. Moving the pending-const gate below the extraction gives those bodies a
        // snapshot like every other clean body, so the example is now stale and is removed
        // rather than left to mislead. What remains genuinely missing here is a callee whose
        // record never reached extraction at all (unsupported shapes, or the unrevealed-opaque
        // guard), which is the real asymmetry this gate is for.
        let asymmetry = |def_index: u32| {
            skip(
                def_index,
                "seam-deferred body: callee-set asymmetry between THIR crate module and MIR oracle \
                 bundle (callee def_path sets differ, or a declaration / absent-callee marker in \
                 the reachable closure); fail-closed skip (coverage-only)",
            )
        };
        let mut members: Vec<(u32, &trust_types::VerifiableFunction)> = Vec::new();
        let mut ok = true;
        for &fid in &closure {
            let Some(di) = def_of_func(fid) else {
                ok = false;
                break;
            };
            let Some(vf) = rec_by_def(di).and_then(|rec| rec.mir_snapshot.as_ref()) else {
                ok = false;
                break;
            };
            members.push((di, vf));
        }
        if !ok {
            verdicts.push(asymmetry(r.def_index));
            continue;
        }
        // Bundle FuncIds are positional in the passed order; sort by def_index for determinism.
        members.sort_by_key(|(di, _)| *di);
        let Some(entry_slot) = members.iter().position(|(di, _)| *di == r.def_index) else {
            verdicts.push(asymmetry(r.def_index));
            continue;
        };
        let funcs: Vec<trust_types::VerifiableFunction> =
            members.iter().map(|(_, vf)| (*vf).clone()).collect();

        // step 5 — bundle: the PLAIN entry (no expected-absent set) so any absent DIRECT callee
        // keeps the fatal ABSENT_CALLEE marker (screened next).
        let bundle = match trust_ir_bridge::lower_mir_compat_functions_to_trust_ir(
            format!("{}::seam", assembled.module.name),
            &funcs,
        ) {
            Ok(m) => m,
            Err(e) => {
                verdicts.push(skip(
                    r.def_index,
                    &format!(
                        "seam-deferred body: MIR oracle bundle construction failed ({e:?}); \
                         coverage-only skip — NOT a THIR divergence"
                    ),
                ));
                continue;
            }
        };

        // step 6 — absent-callee/asymmetry scan. MUST precede the panic-model scan (the absent
        // encoding IS an `Assert(const false)`). A marker means the MIR side demanded a callee
        // outside the THIR closure's body set => the callee def_path sets differ.
        if bundle.proof_obligations.iter().any(|o| {
            o.description.contains(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        }) {
            verdicts.push(asymmetry(r.def_index));
            continue;
        }

        // step 7 — bundle preprocessing (same order/semantics as the hook's single-body path).
        if differential::oracle_has_const_false_assert(&bundle) {
            verdicts.push(skip(
                r.def_index,
                "seam-deferred body: oracle bundle models a diverging panic call as an \
                 unconditional assert(false) (oracle-panic-model); coverage-only skip",
            ));
            continue;
        }
        let mut bundle = bundle;
        differential::rewrite_bool_not_icmp(&mut bundle);
        // Trust (vtable slice 12): same order as the hook's single-body path — the array
        // InsertField→InsertElement respell runs BEFORE classification so the Array
        // dead-seed walk sees the interpreter-native form.
        differential::rewrite_array_insert_fields(&mut bundle);
        // Trust (absent-callee Stage 0, instrument only): the TRACED classifier, so
        // the skip note names WHICH Undef broke the dead-seed proof. This is the
        // number the absent-callee design needs priced: of the live havocs, how many
        // are the ABSENT-CALLEE result Undef versus an unrelated havoc. Same
        // classification, same skip; only the note gains the offender.
        let bundle = match differential::classify_undefs_traced(&bundle) {
            (differential::UndefClass::Live, offender) => {
                verdicts.push(skip(
                    r.def_index,
                    &format!(
                        "seam-deferred body: MIR oracle bundle carries a LIVE havoc \
                         (`Inst::Undef` outside the proven-dead-seed shape){}; coverage-only \
                         skip — NOT a THIR divergence",
                        offender.map(|o| format!(" — offender: {o}")).unwrap_or_default()
                    ),
                ));
                continue;
            }
            (differential::UndefClass::DeadSeeds, _) => differential::substitute_dead_seeds(bundle),
            (differential::UndefClass::None, _) => bundle,
        };
        // Trust (vtable slice 6): the seam mirrors the hook's single-body preprocessing
        // step for step — same slot after the dead-seed substitution, same differential-
        // local scope (the bundle is this comparison's own assembly). The call-bearing
        // promoted-borrow mains (regions-reassign-let-bound-pointer, macro-named-default)
        // carry the once-stored escaping slot in the ENTRY body and reach the tail gate
        // only here, so a hook-only rewrite would leave the seam population unaligned.
        let mut bundle = bundle;
        differential::respell_promoted_slots_as_globals(&mut bundle);

        // step 8 — verdict.
        //
        // Trust (step 2 increment 4b, D18 OD-1): a DROP is an uninterpreted EVENT
        // here, not an instruction the interpreter runs (it refuses `Inst::Drop` with a
        // `TypeError`, which would read as a THIR defect). The THIR side is interpreted with its
        // drops removed — the MIR side's drop glue is neutral in this differential already — so
        // the verdict is about the value flow AROUND the drops, and the drops themselves are
        // compared with rustc's elaborated drop points, event by event, by the
        // effect-conservation gate (`effect_conservation::drop_leg`, `drop_oracle.rs`), which
        // refuses the body for codegen and strict on any difference. No body is excluded.
        let without_drops = module_without_drops(&assembled.module, &closure);
        let thir_side = without_drops.as_ref().unwrap_or(&assembled.module);
        // [reference: the pre-R8-SEAM differential (`differential/compare_entries_reference.rs`),
        // not `differential::compare_entries`, which R8-SEAM split and re-paired.]
        let mut rep = differential::compare_entries_reference::compare_entries(
            thir_side,
            entry,
            &bundle,
            FuncId::new(entry_slot as u32),
        );
        // Trust: `compare_entries` is the classification authority. In particular, a typed
        // `MirOracle` result is never reclassified by matching its human-readable note. Structural
        // signature comparison already resolves module-local ids through each module's own tables,
        // and the producer emits canonical zero-result unit calls, so neither case needs a seam-only
        // exception. Any remaining signature/result-arity mismatch is a genuine lowering defect.
        if rep.mode == DiffMode::Agreed {
            // Trust (slice 20): the seam population is no longer call-bearing bodies alone, so
            // the note names the reason this body was deferred rather than asserting the one
            // that used to be the only possibility. A pending-const body may be call-FREE, and
            // a note that called it "call-bearing" would be false on its face and would also
            // mis-attribute the lane in every downstream reading of the log.
            let why = if r.pending_consts.is_empty() {
                "call-bearing body linked at crate finalize"
            } else if r.contains_call {
                "call-bearing pending-const body linked and const-patched at crate finalize"
            } else {
                "pending-const body re-adjudicated after finalizer const patching"
            };
            rep.notes.push(format!(
                "THIR-trust-ir == MIR-trust-ir on {} sampled input(s) (seam differential: {why})",
                rep.samples_checked
            ));
        }
        verdicts.push(SeamVerdict {
            def_index: r.def_index,
            equal: rep.equal,
            samples: rep.samples_checked,
            mode: rep.mode,
            note: rep.notes.last().cloned().unwrap_or_default(),
        });
    }
    verdicts
}


/// Trust (absent-callee Stage 2→3): the fenced UNINTERPRETED-CALLEE adjudicator. Returns
/// `Some((samples, detail))` — and ONLY then may the caller mint
/// `DiffMode::AgreedUninterpretedCallee` — when every sampled leg of the substitution agreed
/// under the full no-channel fence of `docs/design/2026-08-31-absent-callee-adjudication.md`
/// §6 (conjuncts 1–5) plus the Stage-2 count/shape pairing. Every refusal and every
/// non-agreeing outcome traces exactly as the Stage-1.5 probe did and returns `None`, so the
/// scorecard's disclosed adjudication line keeps its full population.
///
/// The legs are `differential::sample_values` over the (single, fence-enforced) declared
/// return type — the design's "sample_values(ret_ty) outer loop" — not the probe's fixed
/// {0, 1}; a plan whose every site is zero-result runs one leg (nothing is substituted, the
/// deletion is the whole model).
pub(super) fn row1_uc_probe(
    r: &BodyRecord,
    entry: FuncId,
    declarations: &[FuncId],
    assembled: &Assembled,
    oracle_bundle: &trust_ir::Module,
    entry_slot: usize,
    uc_events: &RefCell<Vec<UcProbeEvent>>,
) -> Option<(usize, String)> {
    use crate::differential::{self, DiffMode};
    use trust_ir::{Constant, Inst, Ty};

    // [reference: recorded for the comparison instead of traced; the live seam traces it.]
    let emit = |outcome: &str, samples: usize, detail: &str| {
        uc_events.borrow_mut().push(UcProbeEvent {
            def_index: r.def_index,
            outcome: outcome.to_string(),
            samples,
            detail: detail.to_string(),
        });
    };

    // The scalar constant for leg `v`, or None — the fence.
    fn const_of(ty: &Ty, v: i128) -> Option<Constant> {
        match ty {
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char => Some(Constant::Int(v)),
            // Trust (Stage 3): `Ty::Ptr` is DELIBERATELY absent — substituting a
            // pointer-returning callee with fabricated integer addresses would hand both
            // sides a value whose derefs trap "identically" only by construction of the
            // fabrication. A pointer return refuses the row as `uc-unfenced`, matching
            // the design's conjunct 2 (`is_interpretable_scalar` excludes `Ptr`).
            Ty::Bool => Some(Constant::Bool(v != 0)),
            Ty::F32 | Ty::F64 => Some(Constant::Float(v as f64)),
            Ty::Unit => Some(Constant::PhantomData),
            // Trust (wave-UCF): a FAT-POINTER return is modeled at the ONE constant trust-ir
            // fecd740 admits — the two-zero aggregate `[Int(0), Int(0)]`, the null/empty
            // fat value (`shape_matches_ty` refuses any nonzero word, and
            // `constant_to_value` materializes NullPtr data + the zero of the kind's own
            // metadata type). `v` is deliberately IGNORED: no other fat constant exists to
            // sample, so the leg selection below runs this type at a single leg, and the
            // per-row detail discloses single-value modeling. Both sides receive the same
            // constant; a callee whose real return is dereferenced would trap on BOTH sides
            // identically only for the null value — which is exactly the disclosed
            // uninterpreted-callee assumption, no stronger here than for scalars.
            Ty::FatPtr(_) => Some(Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)])),
            _ => None,
        }
    }

    let decl_set: std::collections::HashSet<FuncId> = declarations.iter().copied().collect();

    // ---- Stage 3 no-channel fence, conjuncts 1/2/3/5 (4 is structural: after the
    // substitution no declaration call remains, so `compare_entries` runs the FULL
    // observation tail gate with nothing excused). Any miss traces `uc-unfenced` with the
    // conjunct named and the row stays a disclosed probe outcome, never a verdict. ----
    // Trust (wave-UCF2): a plan may span SEVERAL return types (`caller_str` reaches both a
    // `fatptr<str>`-returning extern and a bodyless `usize`-returning std helper — measured,
    // the single-type fence refused exactly that shape). Each site substitutes a value from
    // ITS OWN type's admissible sample list; a joint leg is one assignment across all sites,
    // and the leg count is the largest per-type list (shorter lists cycle). Every substituted
    // constant is well-formed for its own type by construction, so no ill-typed constant can
    // reach either module.
    let mut planned_ret_tys: Vec<Ty> = Vec::new();
    for &fid in declarations {
        let Some(decl) = assembled.module.function_by_id(fid) else {
            emit("uc-unfenced", 0, "declaration unresolvable");
            return None;
        };
        // conjunct 3 — one arity, no per-site result-count split.
        if decl.name.contains("|nres:") {
            emit("uc-unfenced", 0, &format!("arity-split declaration {}", decl.name));
            return None;
        }
        let Some(ft) = assembled.module.func_types.get(decl.ty.as_usize()) else {
            emit("uc-unfenced", 0, "declaration func_type unresolvable");
            return None;
        };
        // H1 + conjuncts 1 and 2, as the pure [`uc_declaration_fence`] so the vacuity H1
        // closes is pinned by a unit test rather than by a trace nobody reads.
        match uc_declaration_fence(ft) {
            Err(detail) => {
                emit("uc-unfenced", 0, &detail);
                return None;
            }
            Ok(Some(rt)) => {
                if !planned_ret_tys.iter().any(|t| *t == rt) {
                    planned_ret_tys.push(rt);
                }
            }
            Ok(None) => {}
        }
    }
    // conjunct 5 — no pointer-shaped channel on the CALLER's own entry: every entry param an
    // interpretable scalar.
    {
        let Some(ef) = assembled.module.function_by_id(entry) else {
            emit("uc-unfenced", 0, "entry unresolvable");
            return None;
        };
        let Some(eft) = assembled.module.func_types.get(ef.ty.as_usize()) else {
            emit("uc-unfenced", 0, "entry func_type unresolvable");
            return None;
        };
        if let Some(bad) = eft.params.iter().find(|t| !differential::is_interpretable_scalar(t))
        {
            emit("uc-unfenced", 0, &format!("non-scalar entry param {bad}"));
            return None;
        }
    }
    // The sampled legs: the design's `sample_values(ret_ty)` outer loop, generalized to a
    // JOINT leg over every planned return type. A fat-pointer type has exactly ONE
    // admissible constant (the two-zero null/empty fat value `const_of` mints ignoring the
    // leg), so its list is the singleton. Zero-result-only plans run one leg — the deletion
    // is the whole model.
    let mut ty_samples: Vec<(Ty, Vec<i128>)> = Vec::new();
    for rt in &planned_ret_tys {
        let vs = if matches!(rt, Ty::FatPtr(_)) {
            vec![0]
        } else {
            let vs = differential::sample_values(rt);
            if vs.is_empty() {
                emit("uc-unfenced", 0, &format!("no sample values for ret {rt}"));
                return None;
            }
            vs
        };
        ty_samples.push((rt.clone(), vs));
    }
    let leg_count = ty_samples.iter().map(|(_, vs)| vs.len()).max().unwrap_or(1);
    let value_for = |ty: &Ty, leg_idx: usize| -> i128 {
        ty_samples
            .iter()
            .find(|(t, _)| t == ty)
            .map(|(_, vs)| vs[leg_idx % vs.len()])
            .unwrap_or(0)
    };

    let mut legs: Vec<differential::DiffMode> = Vec::new();
    let mut last_note = String::new();
    let mut samples_total = 0usize;
    // Trust (Stage 2 pairing): the conjuncts the 16 measured uc-diverged rows exist to
    // justify — checked on the first leg (the counts are leg-invariant) and refused as
    // `uc-unpaired` rather than compared. (1) COUNT pairing: every producer call site
    // with a bound result must pair with exactly one oracle absent-callee `Undef`, and
    // every producer zero-result site with an oracle `Assert(false)` that has no Undef;
    // (2) SHAPE pairing: the multiset of producer return types must equal the multiset
    // of oracle Undef types — a divergence between two differently-typed constants is a
    // pairing artifact, not a producer defect, and must not be compared at all.
    let mut pairing_checked = false;
    for leg_idx in 0..leg_count {
        // ---- producer side: Call{decl} -> Const, on a clone -----------------
        let mut prod = assembled.module.clone();
        let mut prod_sites = 0usize;
        let mut prod_unit_sites = 0usize;
        let mut prod_ret_tys: Vec<String> = Vec::new();
        let mut unfenced: Option<String> = None;
        for f in &mut prod.functions {
            for blk in &mut f.blocks {
                let mut keep: Vec<bool> = Vec::with_capacity(blk.body.len());
                for node in &mut blk.body {
                    let mut retain = true;
                    if let Inst::Call { callee, .. } = &node.inst {
                        if decl_set.contains(callee) {
                            prod_sites += 1;
                            let rets: Vec<Ty> = assembled
                                .module
                                .function_by_id(*callee)
                                .and_then(|d| {
                                    assembled.module.func_types.get(d.ty.as_usize()).cloned()
                                })
                                .map(|ft| ft.returns)
                                .unwrap_or_default();
                            match (rets.len(), node.results.len()) {
                                (0, 0) => {
                                    retain = false;
                                    prod_unit_sites += 1;
                                }
                                (1, 1) => match const_of(&rets[0], value_for(&rets[0], leg_idx)) {
                                    Some(c) => {
                                        prod_ret_tys.push(format!("{}", rets[0]));
                                        node.inst = Inst::Const { ty: rets[0].clone(), value: c };
                                    }
                                    None => {
                                        unfenced =
                                            Some(format!("producer ret {}", rets[0]));
                                    }
                                },
                                _ => {
                                    unfenced = Some("producer arity".to_string());
                                }
                            }
                        }
                    }
                    keep.push(retain);
                }
                let mut it = keep.into_iter();
                blk.body.retain(|_| it.next().unwrap_or(true));
            }
        }
        // ---- oracle side: Assert(false) removed, Undef -> the same const ----
        let mut oracle = oracle_bundle.clone();
        let mut oracle_sites = 0usize;
        let mut oracle_asserts = 0usize;
        let mut oracle_undef_tys: Vec<String> = Vec::new();
        for f in &mut oracle.functions {
            for blk in &mut f.blocks {
                // value ids defined by `Const Bool(false)` in this block
                let false_ids: std::collections::HashSet<trust_ir::ValueId> = blk
                    .body
                    .iter()
                    .filter(|n| {
                        matches!(
                            &n.inst,
                            Inst::Const { value: Constant::Bool(false), .. }
                        )
                    })
                    .flat_map(|n| n.results.iter().copied())
                    .collect();
                let mut keep: Vec<bool> = Vec::with_capacity(blk.body.len());
                for node in &mut blk.body {
                    let mut retain = true;
                    match &node.inst {
                        Inst::Assert { cond, .. } if false_ids.contains(cond) => {
                            retain = false;
                            oracle_asserts += 1;
                        }
                        Inst::Undef { ty } => {
                            oracle_sites += 1;
                            oracle_undef_tys.push(format!("{ty}"));
                            match const_of(ty, value_for(ty, leg_idx)) {
                                Some(c) => {
                                    node.inst = Inst::Const { ty: ty.clone(), value: c };
                                }
                                None => {
                                    unfenced = Some(format!("oracle undef {ty}"));
                                }
                            }
                        }
                        _ => {}
                    }
                    keep.push(retain);
                }
                let mut it = keep.into_iter();
                blk.body.retain(|_| it.next().unwrap_or(true));
            }
        }
        if let Some(u) = unfenced {
            emit("uc-unfenced", 0, &u);
            return None;
        }
        if prod_sites == 0 && oracle_sites == 0 {
            emit("uc-no-sites", 0, "");
            return None;
        }
        if !pairing_checked {
            pairing_checked = true;
            let ret_sites = prod_sites - prod_unit_sites;
            if ret_sites != oracle_sites || prod_sites != oracle_asserts {
                emit(
                    "uc-unpaired",
                    0,
                    &format!(
                        "counts: prod {prod_sites} ({ret_sites} ret) vs oracle \
                         {oracle_asserts} asserts / {oracle_sites} undefs"
                    ),
                );
                return None;
            }
            let mut a = prod_ret_tys.clone();
            let mut b = oracle_undef_tys.clone();
            a.sort();
            b.sort();
            if a != b {
                emit("uc-unpaired", 0, &format!("ty multiset: {a:?} vs {b:?}"));
                return None;
            }
        }
        // [reference: the pre-R8-SEAM differential, as in `run_seam_differentials`.]
        let rep = differential::compare_entries_reference::compare_entries(
            &prod,
            entry,
            &oracle,
            FuncId::new(entry_slot as u32),
        );
        samples_total += rep.samples_checked;
        last_note = rep.notes.last().cloned().unwrap_or_default();
        legs.push(rep.mode);
        if !matches!(legs.last(), Some(DiffMode::Agreed)) {
            break; // one non-agreeing leg decides the row
        }
    }
    let outcome = if legs.iter().all(|m| matches!(m, DiffMode::Agreed)) && legs.len() == leg_count
    {
        "uc-agreed"
    } else if legs.iter().any(|m| matches!(m, DiffMode::MirOracle)) {
        "uc-diverged"
    } else {
        "uc-not-run"
    };
    emit(
        outcome,
        samples_total,
        if outcome == "uc-not-run" { &last_note } else { "" },
    );
    if outcome == "uc-agreed" {
        let detail = format!(
            "agreed under the uninterpreted-callee substitution: {} declaration(s) modeled \
             as the same constant on both sides at {} sampled return value(s) ({} input \
             sample(s) total); no-channel fence conjuncts 1-5 + count/shape pairing held. NOT \
             plain agreement: the call sites themselves are erased by the substitution and \
             callee effects are assumed absent -- see docs/TCB.md",
            declarations.len(),
            leg_count,
            samples_total
        );
        return Some((samples_total, detail));
    }
    None
}
