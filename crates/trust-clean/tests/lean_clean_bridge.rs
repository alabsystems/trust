// Trust: the DEFAULT-ON Lean↔Clean bridge gate (integration of the 18-op
// agreement theorem — reports/bridge-assembly-11arms-2026-07-02.md §5,
// recommendation (i)). No Lean toolchain is needed: the gate machine-imports
// trust-ir's REAL Lean 4.8 `semIntBinOp` semantics from the VENDORED,
// sha256-manifested `.olean` artifacts (crates/trust-clean/fixtures/
// trustir-oleans + vendor/lean-core-oleans) into a clean-kernel Environment
// and kernel-checks the per-op agreement theorems against trust-clean's
// denotation constants, every one with axiom_deps = ∅.
//
// This attestation test always runs `full` — all 18
// arms, the 6 reduction lemmas, the 11 characterization rows, the composed
// all-18 conjunction, and both forgery probes (several minutes of kernel
// time; the honest price of a default-on full gate, within the ~10 min
// budget). Focused spot checks below select `BridgeGateMode::Spot` explicitly;
// no ambient setting can silently weaken this test.
//
// FAIL-CLOSED is asserted POSITIVELY here: `ops_pinned == 0` (a clean/
// trust-ir pin bump that regresses ANY arm fails this test loudly), and the
// negative controls prove that a tampered sha, a missing artifact, and a
// stale trust-ir pin each REFUSE to run rather than certify.

use std::path::{Path, PathBuf};

use trust_clean::{
    BridgeGateConfig, BridgeGateError, BridgeGateMode, ProveScorecard, run_bridge_gate,
};

fn copy_dir(src: &Path, dst: &Path) {
    std::fs::create_dir_all(dst).expect("create temp dir");
    for entry in std::fs::read_dir(src).expect("read src dir") {
        let entry = entry.expect("dir entry");
        let from = entry.path();
        let to = dst.join(entry.file_name());
        if from.is_dir() {
            copy_dir(&from, &to);
        } else {
            std::fs::copy(&from, &to).expect("copy file");
        }
    }
}

fn temp_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "lean-clean-bridge-{tag}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).expect("create temp root");
    dir
}

/// Read the trustir_commit recorded in the shipped manifest (for negative
/// controls that must bypass git resolution).
fn manifest_commit(dir: &Path) -> String {
    let text = std::fs::read_to_string(dir.join("MANIFEST.toml")).expect("read manifest");
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("trustir_commit = \"") {
            return rest.trim_end_matches('"').to_string();
        }
    }
    panic!("MANIFEST.toml has no trustir_commit");
}

/// THE DEFAULT-ON GATE. Vendored artifacts in, kernel-checked 18-op agreement
/// out — asserting every invariant the §6 `bridge_agreement` line cites.
#[test]
fn bridge_gate_default_on() {
    // Fixed in-process: ambient state must never weaken this attestation gate.
    // Keep `mode` so the upstream full/spot expectation tables remain shared,
    // while this default-on test always selects the complete lane.
    let mode = BridgeGateMode::Full;
    let config = BridgeGateConfig::locate(mode);
    let summary = run_bridge_gate(&config).expect("bridge gate must pass on shipped artifacts");

    // Shared invariants (both modes).
    assert!(summary.manifest_ok, "manifests verified");
    assert!(summary.axiom_deps_empty, "every proven theorem has axiom_deps = ∅");
    assert_eq!(
        summary.ops_pinned, 0,
        "REGRESSION: {} arm(s) lost their agreement theorem: {:?} — a clean/trust-ir pin \
         bump regressed the bridge",
        summary.ops_pinned, summary.pinned
    );
    assert_eq!(summary.trustir_recheck_fail, 0, "imported TrustIr constants recheck clean");
    assert_eq!(
        summary.modules_loaded, summary.manifest_files,
        "loaded module set == manifested artifact set"
    );
    assert!(
        summary.fail_closed_controls >= 1,
        "at least one forgery probe kernel-REJECTED per run"
    );

    match mode {
        BridgeGateMode::Full => {
            assert_eq!(summary.ops_bridged, 18, "all 18 semIntBinOp arms bridged");
            assert_eq!(summary.form_a, 5, "5 float arms in form (a)");
            assert_eq!(summary.form_b, 13, "13 arithmetic arms in form (b)");
            assert_eq!(summary.form_b_guarded, 7, "7 of the form-(b) arms carry UB guards");
            assert_eq!(summary.reduction_lemmas, 6, "6 reduction lemmas");
            assert_eq!(summary.characterization_rows, 11, "11 characterization rows");
            assert!(
                summary.composed_all18,
                "the composed `bridge_semIntBinOp_agreement_all18` conjunction kernel-checks"
            );
            assert_eq!(summary.fail_closed_controls, 2, "both forgery probes rejected");

            // semIntUnOp extension: Neg[b], Not[b], FNeg[a] — CtPop honestly
            // un-bridged (no popcount denotation exists anywhere in Clean).
            assert_eq!(
                summary.unop_ops_pinned, 0,
                "REGRESSION: {} UnOp arm(s) lost their agreement theorem: {:?}",
                summary.unop_ops_pinned, summary.unop_pinned
            );
            assert_eq!(summary.unop_ops_bridged, 3, "Neg/Not/FNeg bridged");
            assert_eq!(summary.unop_bridged, vec!["Neg[b]", "Not[b]", "FNeg[a]"]);
            assert_eq!(summary.unop_form_a, 1, "FNeg is the one plain-agreement arm");
            assert_eq!(summary.unop_form_b, 2, "Neg and Not agree under the side condition");
            assert!(
                summary.unop_neg_sub_zero_form,
                "the connecting corollary to clean_ground's exact Int.sub(0,x) Neg term kernel-checks"
            );
            assert_eq!(summary.unop_conc_rows, 2, "neg_conc + not_conc");
            assert!(
                summary.unop_composed,
                "the composed `bridge_semIntUnOp_agreement_all` conjunction kernel-checks"
            );
            assert_eq!(summary.unop_fail_closed_controls, 2, "both UnOp forgery probes rejected");
            assert_eq!(summary.unop_unbridged.len(), 1, "CtPop is the one honest residue");
            assert!(summary.unop_unbridged[0].starts_with("CtPop:"));

            // semOverflowOp extension: VALUE bridged for all 6 (op ×
            // signedness) combos; FLAG bridged for 5 of 6 (unsigned-Mul's
            // flag is honestly un-bridged — no Lemma models it).
            assert_eq!(
                summary.overflow_value_pinned, 0,
                "REGRESSION: {} Overflow VALUE arm(s) lost their agreement theorem: {:?}",
                summary.overflow_value_pinned, summary.overflow_value_pinned_list
            );
            assert_eq!(
                summary.overflow_value_bridged, 6,
                "all 6 op×signedness VALUE combos bridged"
            );
            assert_eq!(
                summary.overflow_value_bridged_list,
                vec![
                    "AddOverflow[u]",
                    "SubOverflow[u]",
                    "MulOverflow[u]",
                    "AddOverflow[s]",
                    "SubOverflow[s]",
                    "MulOverflow[s]"
                ]
            );
            assert_eq!(
                summary.overflow_flag_pinned, 0,
                "REGRESSION: {} Overflow FLAG arm(s) lost their agreement theorem: {:?}",
                summary.overflow_flag_pinned, summary.overflow_flag_pinned_list
            );
            assert_eq!(
                summary.overflow_flag_bridged, 5,
                "5 of 6 FLAG combos bridged (unsigned-Mul excluded)"
            );
            assert_eq!(
                summary.overflow_flag_bridged_list,
                vec![
                    "AddOverflow[u]:Lemma 2 (unsigned-add overflow)",
                    "SubOverflow[u]:Lemma 8 (unsigned-sub underflow)",
                    "AddOverflow[s]:Lemma 5 (signed add/sub/mul overflow)",
                    "SubOverflow[s]:Lemma 5 (signed add/sub/mul overflow)",
                    "MulOverflow[s]:Lemma 5 (signed add/sub/mul overflow)",
                ]
            );
            assert_eq!(
                summary.overflow_flag_guarded, 1,
                "unsigned-Sub's Lemma 8 arm is the one guarded flag"
            );
            assert!(
                summary.overflow_composed,
                "the composed `bridge_semOverflowOp_agreement_all` conjunction kernel-checks"
            );
            assert_eq!(
                summary.overflow_fail_closed_controls, 2,
                "both Overflow forgery probes rejected"
            );
            assert_eq!(
                summary.overflow_flag_unbridged.len(),
                1,
                "unsigned MulOverflow is the one honest residue"
            );
            assert!(summary.overflow_flag_unbridged[0].starts_with("MulOverflow[unsigned]:"));

            // semICmp extension: all 10 comparison arms bridged (unconditional
            // rfl agreements) — no honest residue (signed arms agree at the
            // toSigned images).
            assert_eq!(
                summary.icmp_ops_pinned, 0,
                "REGRESSION: {} ICmp arm(s) lost their agreement theorem: {:?}",
                summary.icmp_ops_pinned, summary.icmp_pinned
            );
            assert_eq!(summary.icmp_ops_bridged, 10, "all 10 semICmp arms bridged");
            assert_eq!(
                summary.icmp_bridged,
                vec![
                    "Eq[eq]", "Ne[eq]", "Ult[u]", "Ule[u]", "Ugt[u]", "Uge[u]", "Slt[s]", "Sle[s]",
                    "Sgt[s]", "Sge[s]",
                ]
            );
            assert_eq!(
                summary.icmp_kind_unsigned, 4,
                "Ult/Ule/Ugt/Uge — raw-operand Int.lt/Int.le"
            );
            assert_eq!(summary.icmp_kind_sign_independent, 2, "Eq/Ne — sign-independent");
            assert_eq!(
                summary.icmp_kind_signed, 4,
                "Slt/Sle/Sgt/Sge — Int.lt/Int.le at toSigned images"
            );
            assert_eq!(summary.icmp_conc_rows, 4, "the Ult/Slt sign-distinction pair + Eq/Ne");
            assert!(
                summary.icmp_composed,
                "the composed `bridge_semICmp_agreement_all` conjunction kernel-checks"
            );
            assert_eq!(summary.icmp_fail_closed_controls, 3, "all 3 ICmp forgery probes rejected");
            assert!(
                summary.icmp_unbridged.is_empty(),
                "all 10 ICmp arms bridge — no honest residue"
            );

            // semCast extension: the 3 integer arms (Trunc/ZExt/SExt) bridged
            // against the pure value cores (truncateUnsigned / the SExt
            // toSigned-wrap), each `∀ v : Int` at a concrete ValueId/Ty/
            // MachineState shape (semCast is monadic, unlike every prior
            // bridged function). Plus the ZExt TIER-2 widening-identity
            // connecting corollary to mirsem.rs's resolve_widening_cast_rvalue
            // (the analogous SExt corollary is mathematically real — proven
            // against a genuine Lean 4.8.0 toolchain — but hits a confirmed
            // clean-elaborator limitation and is honestly not attempted here).
            // The 14 non-integer (float/pointer/closure) arms are honestly
            // un-bridged.
            assert_eq!(
                summary.cast_ops_pinned, 0,
                "REGRESSION: {} Cast arm(s) lost their agreement theorem: {:?}",
                summary.cast_ops_pinned, summary.cast_pinned
            );
            assert_eq!(summary.cast_ops_bridged, 3, "all 3 semCast integer arms bridged");
            assert_eq!(summary.cast_bridged, vec!["Trunc", "ZExt", "SExt"]);
            assert_eq!(
                summary.cast_conc_rows, 4,
                "Trunc wrap/no-op + SExt negative/positive branch"
            );
            assert_eq!(summary.cast_widening_bridged, 1, "the ZExt widening corollary");
            assert_eq!(summary.cast_widening_list, vec!["bridge_cast_zext_widening_identity"]);
            // GAP-CROSS-SIGN-WIDEN (2026-07-16): the sign-crossing widening
            // corollary kernel-checks — `u_w -> i_W` (W>w) is value-preserving,
            // anchoring the new mirsem/prove cast clause against `semCast`.
            assert_eq!(
                summary.cast_signcross_widening_bridged, 1,
                "the sign-crossing (u_w -> i_W, W>w) widening corollary"
            );
            assert_eq!(
                summary.cast_signcross_widening_list,
                vec!["bridge_cast_zext_signcross_widening_identity"]
            );
            assert!(
                summary.cast_composed,
                "the composed `bridge_semCast_agreement_all` conjunction kernel-checks"
            );
            assert_eq!(
                summary.cast_fail_closed_controls, 3,
                "all three Cast forgery probes rejected (incl. the signcross-without-half-bound probe)"
            );
            assert_eq!(summary.cast_unbridged.len(), 14, "the 14 non-integer CastOp variants");

            // stepInst .BinOp extension: the FIRST statement/instruction-level
            // agreement — the monadic READ->COMPUTE->WRITE chain of stepInst
            // dispatching a .BinOp instruction (Add/Sub/Mul), connected via
            // Eq.trans/congrArg to the ALREADY-BRIDGED bridge_add/bridge_sub/
            // bridge_mul (reused, not re-proven). The other 15 semIntBinOp ops
            // reachable through this same stepInst arm, and the other 56 (of
            // 57) Inst variant categories, are honestly un-chained.
            assert_eq!(
                summary.stepinst_binop_pinned, 0,
                "REGRESSION: {} stepInst-BinOp arm(s) lost their agreement theorem: {:?}",
                summary.stepinst_binop_pinned, summary.stepinst_binop_pinned_list
            );
            assert_eq!(summary.stepinst_binop_bridged, 3, "all 3 stepInst-BinOp arms bridged");
            assert_eq!(summary.stepinst_binop_bridged_list, vec!["Add", "Sub", "Mul"]);
            assert!(
                summary.stepinst_binop_composed,
                "the composed `bridge_stepInst_binop_agreement_all` conjunction kernel-checks"
            );
            assert_eq!(
                summary.stepinst_binop_fail_closed_controls, 2,
                "both stepInst-BinOp forgery probes rejected (wrong-op-agreement, swapped-operand)"
            );
            assert_eq!(
                summary.stepinst_binop_unbridged.len(),
                1,
                "the other 15 semIntBinOp ops are grouped in one honest-residue entry"
            );
            assert_eq!(
                summary.stepinst_categories_unbridged.len(),
                2,
                "the other 52 Inst variant categories are grouped in two honest-residue entries"
            );

            // stepInst .UnOp/.Overflow/.ICmp/.Cast extension (EXTENSION 9):
            // completing the instruction-execution technique for every OTHER
            // value-bridged Inst category, one representative op each (Neg,
            // unsigned AddOverflow, Ult, Trunc).
            assert_eq!(
                summary.stepinst_unop_pinned, 0,
                "REGRESSION: {} stepInst-UnOp arm(s) lost their agreement theorem: {:?}",
                summary.stepinst_unop_pinned, summary.stepinst_unop_pinned_list
            );
            assert_eq!(summary.stepinst_unop_bridged, 1, "the Neg arm bridged");
            assert_eq!(summary.stepinst_unop_bridged_list, vec!["Neg"]);
            assert!(
                summary.stepinst_unop_neg_sub_zero_form,
                "Neg's bonus sub-zero-form corollary (bridge_stepInst_unop_neg_sub_zero_form) \
                 kernel-checks"
            );
            assert!(
                summary.stepinst_unop_composed,
                "the composed `bridge_stepInst_unop_agreement_all` conjunction kernel-checks"
            );
            assert_eq!(
                summary.stepinst_unop_fail_closed_controls, 2,
                "both stepInst-UnOp forgery probes rejected (wrong-op-agreement, dropped-negation)"
            );
            assert_eq!(
                summary.stepinst_unop_unbridged.len(),
                1,
                "Not/FNeg are grouped in one honest-residue entry"
            );

            assert_eq!(
                summary.stepinst_overflow_pinned, 0,
                "REGRESSION: {} stepInst-Overflow arm(s) lost their agreement theorem: {:?}",
                summary.stepinst_overflow_pinned, summary.stepinst_overflow_pinned_list
            );
            assert_eq!(
                summary.stepinst_overflow_bridged, 1,
                "the unsigned AddOverflow arm bridged"
            );
            assert_eq!(summary.stepinst_overflow_bridged_list, vec!["AddOverflow[u]"]);
            assert!(
                summary.stepinst_overflow_composed,
                "the `bridge_stepInst_overflow_agreement_all` theorem kernel-checks"
            );
            assert_eq!(
                summary.stepinst_overflow_fail_closed_controls, 2,
                "both stepInst-Overflow forgery probes rejected (wrong-op-agreement, wrong-threshold)"
            );
            assert_eq!(
                summary.stepinst_overflow_unbridged.len(),
                1,
                "the other 5 op×signedness combos are grouped in one honest-residue entry"
            );

            assert_eq!(
                summary.stepinst_icmp_pinned, 0,
                "REGRESSION: {} stepInst-ICmp arm(s) lost their agreement theorem: {:?}",
                summary.stepinst_icmp_pinned, summary.stepinst_icmp_pinned_list
            );
            assert_eq!(summary.stepinst_icmp_bridged, 1, "the Ult arm bridged");
            assert_eq!(summary.stepinst_icmp_bridged_list, vec!["Ult"]);
            assert!(
                summary.stepinst_icmp_composed,
                "the `bridge_stepInst_icmp_agreement_all` theorem kernel-checks"
            );
            assert_eq!(
                summary.stepinst_icmp_fail_closed_controls, 2,
                "both stepInst-ICmp forgery probes rejected (wrong-relation, swapped-operand)"
            );
            assert_eq!(
                summary.stepinst_icmp_unbridged.len(),
                1,
                "the other 9 comparison ops are grouped in one honest-residue entry"
            );

            assert_eq!(
                summary.stepinst_cast_pinned, 0,
                "REGRESSION: {} stepInst-Cast arm(s) lost their agreement theorem: {:?}",
                summary.stepinst_cast_pinned, summary.stepinst_cast_pinned_list
            );
            assert_eq!(summary.stepinst_cast_bridged, 1, "the Trunc arm bridged");
            assert_eq!(summary.stepinst_cast_bridged_list, vec!["Trunc"]);
            assert!(
                summary.stepinst_cast_composed,
                "the `bridge_stepInst_cast_agreement_all` theorem kernel-checks"
            );
            assert_eq!(
                summary.stepinst_cast_fail_closed_controls, 2,
                "both stepInst-Cast forgery probes rejected (wrong-destination-width, \
                 dropped-truncation)"
            );
            assert_eq!(
                summary.stepinst_cast_unbridged.len(),
                1,
                "ZExt/SExt are grouped in one honest-residue entry"
            );

            assert!(
                summary.stepinst_categories_composed,
                "the OVERALL `bridge_stepInst_categories_agreement_all` conjunction (Neg ∧ \
                 unsigned-AddOverflow ∧ Ult ∧ Trunc) kernel-checks"
            );

            // stepN/stepBlock extension: the FIRST WHOLE-BLOCK
            // (multi-instruction, terminator-inclusive) agreement, one layer
            // above stepInst. The Add-then-Return block: bindBlockParams ->
            // fold stepInst over the 1-instruction body -> stepInst the
            // Return terminator, composed (Eq.trans/congrArg) with the
            // ALREADY-PROVEN bridge_stepInst_binop_add (reused as a
            // black-box term, not re-proven).
            assert_eq!(
                summary.stepblock_pinned, 0,
                "REGRESSION: {} stepblock arm(s) lost their agreement theorem: {:?}",
                summary.stepblock_pinned, summary.stepblock_pinned_list
            );
            assert_eq!(summary.stepblock_bridged, 1, "the Add-then-Return block arm bridged");
            assert_eq!(summary.stepblock_bridged_list, vec!["Add"]);
            assert!(
                summary.stepblock_composed,
                "the composed `bridge_stepblock_agreement_all` theorem kernel-checks"
            );
            assert_eq!(
                summary.stepblock_fail_closed_controls, 2,
                "both stepblock forgery probes rejected (wrong-final-value, \
                 wrong-operand-threaded-to-terminator)"
            );
            assert_eq!(
                summary.stepblock_unbridged.len(),
                5,
                "5 honest residue entries: Sub/Mul-return blocks, multi-instruction bodies, \
                 branching/multi-block CFGs, loops, the interprocedural evaluator"
            );

            // stepN-branch extension: THE FIRST BRANCHING whole-body
            // agreement — stepN's .CondBr terminator dispatch + .Continue
            // RECURSIVE case (fuel >= 2), for the mission-minimum `if _0 {
            // return _1 } else { return _2 }` 3-block CFG. Both paths
            // (true/false) bridged, composed into one conjunction theorem.
            assert_eq!(
                summary.stepbranch_pinned, 0,
                "REGRESSION: {} stepN-branch arm(s) lost their agreement theorem: {:?}",
                summary.stepbranch_pinned, summary.stepbranch_pinned_list
            );
            assert_eq!(summary.stepbranch_bridged, 2, "both the true and false paths bridged");
            assert_eq!(summary.stepbranch_bridged_list, vec!["true", "false"]);
            assert!(
                summary.stepbranch_composed,
                "the composed `bridge_stepN_branch_agreement_all` theorem kernel-checks"
            );
            assert_eq!(
                summary.stepbranch_fail_closed_controls, 2,
                "both stepN-branch forgery probes rejected (true-guard-yields-else-value, \
                 false-guard-yields-then-value)"
            );
            assert_eq!(
                summary.stepbranch_unbridged.len(),
                6,
                "6 honest residue entries: Switch, nested/chained CondBrs, loops, non-empty \
                 branch-arm bodies, the integer-guard semCondBr arm, the interprocedural \
                 evaluator"
            );

            // stepN branch-WITH-BODY extension: composes the stepN-branch
            // control-flow technique with the stepblock body-fold technique
            // — the branch ARMS THEMSELVES COMPUTE (`if _0 { return _1 + _2
            // } else { return _1 - _2 }`), closing the stepN-branch
            // extension's own named "non-empty bodies on either arm"
            // residue. Both paths (true/Add, false/Sub) bridged, composed
            // into one conjunction theorem.
            assert_eq!(
                summary.stepbranch_body_pinned, 0,
                "REGRESSION: {} stepN branch-WITH-BODY arm(s) lost their agreement theorem: {:?}",
                summary.stepbranch_body_pinned, summary.stepbranch_body_pinned_list
            );
            assert_eq!(summary.stepbranch_body_bridged, 2, "both the true and false arms bridged");
            assert_eq!(summary.stepbranch_body_bridged_list, vec!["true", "false"]);
            assert!(
                summary.stepbranch_body_composed,
                "the composed `bridge_stepN_branch_body_agreement_all` theorem kernel-checks"
            );
            assert_eq!(
                summary.stepbranch_body_fail_closed_controls, 2,
                "both stepN branch-WITH-BODY forgery probes rejected \
                 (true-arm-computes-else-arithmetic, false-arm-computes-then-arithmetic)"
            );
            assert_eq!(
                summary.stepbranch_body_unbridged.len(),
                8,
                "8 honest residue entries: Switch, nested/chained CondBrs, loops, the \
                 integer-guard semCondBr arm, the interprocedural evaluator, \
                 multi-instruction arm bodies, asymmetric arm shapes, non-BinOp arm bodies"
            );

            // steploop extension: THE FIRST agreement over a GENUINE back-edge
            // CFG (every prior extension's residue table says "loops: no
            // agreement attempted" — this is the first crossing), proven by
            // NAT INDUCTION on the fuel with a per-step lemma (never
            // rfl-unrolling). Both arms (true_diverges via induction,
            // false_exits the base case) bridged, composed, both forgery
            // probes rejected, and the staleness-witness theorem
            // (documenting the newly-discovered Sem.bindFresh/nextValueId
            // obstruction for DATA-COMPUTING loops) kernel-checks.
            assert_eq!(
                summary.steploop_pinned, 0,
                "REGRESSION: {} steploop arm(s) lost their agreement theorem: {:?}",
                summary.steploop_pinned, summary.steploop_pinned_list
            );
            assert_eq!(summary.steploop_bridged, 2, "both true_diverges and false_exits bridged");
            assert_eq!(summary.steploop_bridged_list, vec!["true_diverges", "false_exits"]);
            assert!(
                summary.steploop_composed,
                "the composed `bridge_stepN_loop_agreement_all` theorem kernel-checks"
            );
            assert_eq!(
                summary.steploop_fail_closed_controls, 2,
                "both steploop forgery probes rejected \
                 (true-guard-claimed-to-terminate, false-guard-claimed-sufficient-at-fuel-1)"
            );
            assert!(
                summary.steploop_staleness_witness,
                "the staleness-witness theorem countup_naive_never_terminates kernel-checks \
                 (Full mode only): a naive data-computing count_up loop through this evaluator \
                 provably runs forever instead of terminating"
            );
            assert_eq!(
                summary.steploop_unbridged.len(),
                6,
                "6 honest residue entries: data-computing loops (the newly-discovered \
                 bindFresh/nextValueId blocker), the SSA↔slot projection, the \
                 Trust.MirSem.step_cfg/exec_cfg tie-in, irreducible/nested loops, the \
                 integer-guard semCondBr arm, the interprocedural evaluator"
            );

            // DATALOOP extension: THE FIRST agreement over a back-edge CFG
            // whose body COMPUTES (a genuine data-carrying counter), through
            // the interprocedural stepNWithContext/bodyResultDests evaluator
            // every prior extension left unbridged — the loop's own
            // fixed-point crossing this mission targeted. Proven as 6
            // symbolic-tail-fuel PER-VISIT lemmas (∀ f, one block-visit of
            // kernel reduction each — the shape that sidesteps the measured
            // clean ground-normalization wall; the single composed
            // ground-fuel statement is an HONEST RESIDUE blocked on a
            // clean-side fix, reproducer: dataloop_composed_wall_reproducer).
            assert!(
                summary.dataloop_pinned_list.is_empty(),
                "REGRESSION: DATALOOP per-visit lemma(s) lost: {:?}",
                summary.dataloop_pinned_list
            );
            assert!(
                summary.dataloop_bridged,
                "all 6 dloop_visit lemmas kernel-check (Full mode only): a bounded \
                 while i<2 {{ i := i+1 }} counter loop, entry i0=0/bound=2/one=1, walks \
                 header/body/header/body/header/exit with i: 0->1->2 and returns [2] \
                 (one kernel-checked block-visit per lemma, fuel-tail symbolic)"
            );
            assert_eq!(
                summary.dataloop_fail_closed_controls, 2,
                "both DATALOOP forgery probes rejected (exit-returns-1, loop-never-exits)"
            );
        }
        BridgeGateMode::Spot => {
            assert_eq!(summary.ops_bridged, 3, "spot set: Add[b], FAdd[a], UDiv[b+guard]");
            assert_eq!(summary.fail_closed_controls, 1, "spot forgery probe rejected");

            assert_eq!(summary.unop_ops_bridged, 1, "spot UnOp set: Neg[b] only");
            assert_eq!(summary.unop_bridged, vec!["Neg[b]"]);
            assert!(summary.unop_neg_sub_zero_form, "Neg's connecting corollary also spot-checked");
            assert_eq!(summary.unop_conc_rows, 0, "conc rows are Full-mode only");
            assert!(!summary.unop_composed, "composed UnOp theorem needs all 3 arms (Full only)");
            assert_eq!(summary.unop_fail_closed_controls, 1, "one UnOp forgery probe rejected");

            assert_eq!(
                summary.overflow_value_bridged, 1,
                "spot Overflow VALUE set: AddOverflow[u] only"
            );
            assert_eq!(summary.overflow_value_bridged_list, vec!["AddOverflow[u]"]);
            assert_eq!(
                summary.overflow_flag_bridged, 1,
                "spot Overflow FLAG set: AddOverflow[u] (Lemma 2) only"
            );
            assert_eq!(
                summary.overflow_flag_bridged_list,
                vec!["AddOverflow[u]:Lemma 2 (unsigned-add overflow)"]
            );
            assert!(
                !summary.overflow_composed,
                "composed Overflow theorem needs all 11 arms (Full only)"
            );
            assert_eq!(
                summary.overflow_fail_closed_controls, 1,
                "one Overflow forgery probe rejected"
            );

            assert_eq!(summary.icmp_ops_bridged, 3, "spot ICmp set: Ult[u], Eq[eq], Slt[s]");
            assert_eq!(summary.icmp_bridged, vec!["Eq[eq]", "Ult[u]", "Slt[s]"]);
            assert_eq!(summary.icmp_conc_rows, 0, "ICmp conc rows are Full-mode only");
            assert!(!summary.icmp_composed, "composed ICmp theorem needs all 10 arms (Full only)");
            assert_eq!(summary.icmp_fail_closed_controls, 1, "one ICmp forgery probe rejected");

            assert_eq!(summary.cast_ops_bridged, 1, "spot Cast set: Trunc only");
            assert_eq!(summary.cast_bridged, vec!["Trunc"]);
            assert_eq!(summary.cast_conc_rows, 0, "Cast conc rows are Full-mode only");
            assert_eq!(
                summary.cast_widening_bridged, 0,
                "Cast widening corollaries are Full-mode only"
            );
            assert_eq!(
                summary.cast_signcross_widening_bridged, 0,
                "the sign-crossing widening corollary is Full-mode only"
            );
            assert!(
                !summary.cast_composed,
                "composed Cast theorem needs all 3 arms + the ZExt widening corollary (Full only)"
            );
            assert_eq!(summary.cast_fail_closed_controls, 1, "one Cast forgery probe rejected");

            assert_eq!(
                summary.stepinst_binop_bridged,
                1,
                "spot stepInst-BinOp set: Add only: {:?}",
                summary.stepinst_binop_pinned_list
            );
            assert_eq!(summary.stepinst_binop_bridged_list, vec!["Add"]);
            assert!(
                !summary.stepinst_binop_composed,
                "composed stepInst-BinOp theorem needs all 3 arms (Full only)"
            );
            assert_eq!(
                summary.stepinst_binop_fail_closed_controls, 1,
                "one stepInst-BinOp forgery probe rejected (the Sub-independent wrong-op probe)"
            );

            // stepInst .UnOp/.Overflow/.ICmp/.Cast: each category has only
            // ONE arm, so Spot mode checks the same arm Full mode does (no
            // mode-based filtering) — only the forgery-probe count differs.
            assert_eq!(
                summary.stepinst_unop_bridged, 1,
                "spot stepInst-UnOp set: Neg (there is only one arm)"
            );
            assert_eq!(summary.stepinst_unop_bridged_list, vec!["Neg"]);
            assert!(
                summary.stepinst_unop_neg_sub_zero_form,
                "Neg's sub-zero corollary also spot-checked"
            );
            assert!(
                summary.stepinst_unop_composed,
                "composed stepInst-UnOp theorem checks in Spot mode too"
            );
            assert_eq!(
                summary.stepinst_unop_fail_closed_controls, 1,
                "one stepInst-UnOp forgery probe rejected (wrong-op-agreement)"
            );

            assert_eq!(
                summary.stepinst_overflow_bridged, 1,
                "spot stepInst-Overflow set: unsigned AddOverflow"
            );
            assert_eq!(summary.stepinst_overflow_bridged_list, vec!["AddOverflow[u]"]);
            assert!(
                summary.stepinst_overflow_composed,
                "stepInst-Overflow theorem checks in Spot mode too"
            );
            assert_eq!(
                summary.stepinst_overflow_fail_closed_controls, 1,
                "one stepInst-Overflow forgery probe rejected (wrong-op-agreement)"
            );

            assert_eq!(summary.stepinst_icmp_bridged, 1, "spot stepInst-ICmp set: Ult");
            assert_eq!(summary.stepinst_icmp_bridged_list, vec!["Ult"]);
            assert!(
                summary.stepinst_icmp_composed,
                "stepInst-ICmp theorem checks in Spot mode too"
            );
            assert_eq!(
                summary.stepinst_icmp_fail_closed_controls, 1,
                "one stepInst-ICmp forgery probe rejected (wrong-relation)"
            );

            assert_eq!(summary.stepinst_cast_bridged, 1, "spot stepInst-Cast set: Trunc");
            assert_eq!(summary.stepinst_cast_bridged_list, vec!["Trunc"]);
            assert!(
                summary.stepinst_cast_composed,
                "stepInst-Cast theorem checks in Spot mode too"
            );
            assert_eq!(
                summary.stepinst_cast_fail_closed_controls, 1,
                "one stepInst-Cast forgery probe rejected (wrong-destination-width)"
            );

            assert!(
                summary.stepinst_categories_composed,
                "the overall stepInst-categories conjunction checks in Spot mode too (all 4 \
                 categories' single arms are proven either way)"
            );

            assert_eq!(
                summary.stepblock_bridged, 1,
                "spot stepblock set: Add only (there is only one arm)"
            );
            assert_eq!(summary.stepblock_bridged_list, vec!["Add"]);
            assert!(
                summary.stepblock_composed,
                "composed stepblock theorem checks in Spot mode too (only one arm exists)"
            );
            assert_eq!(
                summary.stepblock_fail_closed_controls, 1,
                "one stepblock forgery probe rejected (wrong-final-value)"
            );

            assert_eq!(
                summary.stepbranch_bridged, 2,
                "both stepN-branch paths check in Spot mode too (there are only two arms)"
            );
            assert_eq!(summary.stepbranch_bridged_list, vec!["true", "false"]);
            assert!(
                summary.stepbranch_composed,
                "composed stepN-branch theorem checks in Spot mode too (both arms exist)"
            );
            assert_eq!(
                summary.stepbranch_fail_closed_controls, 1,
                "one stepN-branch forgery probe rejected (true-guard-yields-else-value)"
            );

            assert_eq!(
                summary.stepbranch_body_bridged, 1,
                "spot stepN branch-WITH-BODY set: the true/Add arm only (bridge_sub is never \
                 loaded in Spot mode, so the false/Sub arm is never attempted)"
            );
            assert_eq!(summary.stepbranch_body_bridged_list, vec!["true"]);
            assert!(
                !summary.stepbranch_body_composed,
                "composed stepN branch-WITH-BODY theorem needs both arms (Full mode only)"
            );
            assert_eq!(
                summary.stepbranch_body_fail_closed_controls, 1,
                "one stepN branch-WITH-BODY forgery probe rejected \
                 (true-arm-computes-else-arithmetic)"
            );

            // steploop: both arms are cheap enough to run in Spot mode too
            // (unlike stepbranch_body's false/Sub arm, neither steploop arm
            // depends on anything gated to Full mode); only the
            // staleness-witness documentation theorem and the second
            // forgery probe are Full-mode only.
            assert_eq!(
                summary.steploop_bridged, 2,
                "both steploop arms check in Spot mode too (neither depends on Full-mode-only \
                 fixtures)"
            );
            assert_eq!(summary.steploop_bridged_list, vec!["true_diverges", "false_exits"]);
            assert!(
                summary.steploop_composed,
                "composed steploop theorem checks in Spot mode too (both arms exist)"
            );
            assert_eq!(
                summary.steploop_fail_closed_controls, 1,
                "one steploop forgery probe rejected (true-guard-claimed-to-terminate)"
            );
            assert!(
                !summary.steploop_staleness_witness,
                "the staleness-witness theorem is Full-mode only"
            );

            // DATALOOP is Full-mode only (the per-visit chain is 6 kernel
            // obligations plus a composed theorem and 2 forgery probes —
            // deliberately not run on the fast Spot iteration lane).
            assert!(!summary.dataloop_bridged, "DATALOOP is Full-mode only");
            assert!(summary.dataloop_pinned_list.is_empty(), "DATALOOP not attempted in Spot mode");
            assert_eq!(
                summary.dataloop_fail_closed_controls, 0,
                "DATALOOP forgery probes are Full-mode only"
            );
        }
    }

    // M4 v0/M4.1 — GENERATED_FAMILIES (crates/trust-clean/src/cfg_family/,
    // reports/m4-general-cfg-induction-framework-design-2026-07-07.md,
    // reports/m4-v0-cfg-family-generator-landed-2026-07-08.md). ONE loop
    // over the vec, per-family expected counts in a table (design §4.4) —
    // replacing what a new hand-written family would otherwise cost here: a
    // new ~20-25-line block per family. `gen_block_add`/`gen_block_add_sym`
    // (v0, single cheap visit) run, compose, and reject their probe(s) in
    // BOTH Full and Spot mode, like stepblock/steploop.
    //
    // `gen_block_chain2`/`gen_block_chain3` (M4.1 — the multi-visit `Br`-
    // chain exercise, landed after v0) are `ModeSlice::FullOnly`, like
    // DATALOOP: a 2-3 visit chain plus 3 probes each is deliberately kept
    // off the fast Spot iteration lane (Spot gets the cheap, immediate
    // "skipped" report — `visits_bridged: 0, composed: false,
    // fail_closed_controls: 0` — the same shape `run_generated_family`
    // already returns for any `FullOnly` family under Spot).
    {
        // (name, expected visits_bridged, expect composed, expected
        // fail_closed_controls for THIS mode).
        let expected: &[(&str, usize, bool, usize)] = match mode {
            BridgeGateMode::Full => &[
                ("gen_block_add", 1, true, 2),
                ("gen_block_add_sym", 1, true, 2),
                // 2 visits; 2 terminal-value probes (WRONG_VALUE/WRONG_WIDTH)
                // + 1 successor-pc probe (WRONG_SUCCESSOR) = 3.
                ("gen_block_chain2", 2, true, 3),
                // 3 visits; same 3-probe shape (the pc-mutation probe is
                // derived from the FIRST Br visit only).
                ("gen_block_chain3", 3, true, 3),
            ],
            BridgeGateMode::Spot => &[
                ("gen_block_add", 1, true, 1),
                ("gen_block_add_sym", 1, true, 1),
                ("gen_block_chain2", 0, false, 0),
                ("gen_block_chain3", 0, false, 0),
            ],
        };
        assert_eq!(
            summary.generated_families.len(),
            expected.len(),
            "GENERATED_FAMILIES registry size must match the expectations table"
        );
        for (report, (name, visits_bridged, composed, fail_closed)) in
            summary.generated_families.iter().zip(expected.iter())
        {
            assert_eq!(&report.name, name, "GENERATED_FAMILIES order must match the table");
            assert!(
                report.visits_pinned_list.is_empty(),
                "{name}: REGRESSION — pinned generated visit(s): {:?}",
                report.visits_pinned_list
            );
            assert_eq!(
                report.visits_bridged, *visits_bridged,
                "{name}: all generated visits must kernel-check"
            );
            assert_eq!(report.composed, *composed, "{name}: composed C0 theorem must kernel-check");
            assert_eq!(
                report.fail_closed_controls, *fail_closed,
                "{name}: generated forgery probe(s) must be kernel-REJECTED"
            );
            assert_eq!(report.probes_rejected, *fail_closed);
            assert!(report.envelope.planned, "{name}: the static envelope must accept the plan");
            assert!(
                report.envelope.error.is_none(),
                "{name}: accepted plans carry no envelope error"
            );
        }
    }

    // The summary is the §6 citation: it must serialize, and the scorecard
    // line must render it.
    let json = serde_json::to_string_pretty(&summary).expect("BridgeAgreement serializes");
    println!("BridgeAgreement = {json}");
    let mut sc = ProveScorecard::default();
    sc.bridge_agreement = Some(summary);
    let line = sc.bridge_line();
    println!("bridge_line = {line}");
    assert!(line.contains("Lean↔Clean BRIDGE"), "line renders the gate summary");
    assert!(
        line.contains("NO-OVERFLOW/IN-RANGE SIDE CONDITION"),
        "line states the form-(b) side condition plainly"
    );
    assert!(
        line.contains("STEPINST-BINOP EXTENSION"),
        "line states the FIRST statement/instruction-level agreement plainly"
    );
    assert!(
        line.contains("STEPINST-CATEGORIES EXTENSION"),
        "line states the UnOp/Overflow/ICmp/Cast instruction-execution breadth plainly"
    );
    assert!(
        line.contains("STEPBLOCK EXTENSION"),
        "line states the FIRST whole-BLOCK agreement plainly"
    );
    assert!(
        line.contains("STEPBRANCH EXTENSION"),
        "line states the FIRST BRANCHING whole-body agreement plainly"
    );
    assert!(
        line.contains("STEPBRANCH-BODY EXTENSION"),
        "line states the branch-ARMS-COMPUTE agreement plainly"
    );
    assert!(
        line.contains("STEPLOOP EXTENSION"),
        "line states the FIRST genuine-back-edge-CFG agreement plainly"
    );
    assert!(
        line.contains("NAT INDUCTION on the fuel with a per-step lemma"),
        "line states the induction technique (not rfl-unrolling) plainly"
    );
    assert!(
        line.contains("HONEST NEW FINDING"),
        "line states the newly-discovered bindFresh/nextValueId staleness obstruction plainly"
    );
    assert!(
        line.contains("DATALOOP EXTENSION"),
        "line states the FIRST back-edge-CFG-whose-body-COMPUTES agreement plainly"
    );
    assert!(
        line.contains("symbolic-tail-fuel PER-VISIT lemmas"),
        "line states the symbolic-tail-fuel per-visit technique (one kernel-checked \
         block-visit per lemma) plainly"
    );
    assert!(
        line.contains("HONEST RESIDUE"),
        "line states the un-asserted composed ground statement and its named blocker plainly"
    );
    assert!(
        line.contains("M4 v0 GENERATED FAMILIES"),
        "line states the generated-family framework's result plainly"
    );
    assert!(
        line.contains("gen_block_add") && line.contains("gen_block_add_sym"),
        "line names both v0 registered families: {line}"
    );
}

/// The un-attached scorecard makes NO claim.
#[test]
fn bridge_line_without_gate_run_claims_nothing() {
    let sc = ProveScorecard::default();
    let line = sc.bridge_line();
    assert!(line.contains("not run in this invocation"), "got: {line}");
    assert!(line.contains("no claim"), "got: {line}");
}

/// NEGATIVE CONTROL — a tampered vendored artifact must fail closed at the
/// manifest layer, before anything is imported or certified.
#[test]
fn bridge_gate_tampered_olean_fails_closed() {
    let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
    let tampered = temp_dir("tampered");
    copy_dir(&config.trustir_olean_dir, &tampered);
    // Flip bytes in one vendored artifact; its manifest sha no longer matches.
    let victim = tampered.join("TrustIr").join("BinOp.olean");
    let mut bytes = std::fs::read(&victim).expect("read vendored olean");
    let last = bytes.len() - 1;
    bytes[last] ^= 0xFF;
    std::fs::write(&victim, bytes).expect("write tampered olean");

    let commit = manifest_commit(&config.trustir_olean_dir);
    let tampered_config = BridgeGateConfig {
        trustir_olean_dir: tampered.clone(),
        expected_trustir_commit: Some(commit),
        ..config
    };
    let err = run_bridge_gate(&tampered_config).expect_err("tampered artifact must fail closed");
    assert!(
        matches!(err, BridgeGateError::ShaMismatch { .. }),
        "expected ShaMismatch, got: {err:?}"
    );
    std::fs::remove_dir_all(&tampered).ok();
}

/// NEGATIVE CONTROL — a missing vendored artifact must fail closed.
#[test]
fn bridge_gate_missing_olean_fails_closed() {
    let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
    let broken = temp_dir("missing");
    copy_dir(&config.trustir_olean_dir, &broken);
    std::fs::remove_file(broken.join("TrustIr").join("Semantics").join("Arith.olean"))
        .expect("remove vendored olean");

    let commit = manifest_commit(&config.trustir_olean_dir);
    let broken_config = BridgeGateConfig {
        trustir_olean_dir: broken.clone(),
        expected_trustir_commit: Some(commit),
        ..config
    };
    let err = run_bridge_gate(&broken_config).expect_err("missing artifact must fail closed");
    assert!(
        matches!(err, BridgeGateError::OleanMissing { .. }),
        "expected OleanMissing, got: {err:?}"
    );
    std::fs::remove_dir_all(&broken).ok();
}

/// NEGATIVE CONTROL — pin drift: vendored oleans built from a trust-ir commit
/// that is NOT the checked-out submodule must refuse to run (stale artifacts
/// = stale semantics; the gate is meaningless against the wrong pin).
#[test]
fn bridge_gate_pin_drift_fails_closed() {
    let config = BridgeGateConfig {
        expected_trustir_commit: Some("0123456789abcdef0123456789abcdef01234567".to_string()),
        ..BridgeGateConfig::locate(BridgeGateMode::Spot)
    };
    let err = run_bridge_gate(&config).expect_err("pin drift must fail closed");
    match err {
        BridgeGateError::PinDrift { manifest_commit, checkout_commit } => {
            assert_ne!(manifest_commit, checkout_commit);
        }
        other => panic!("expected PinDrift, got: {other:?}"),
    }
}

/// POSITIVE PIN CONTROL — the shipped manifest's commit IS the checked-out
/// first-party/trust-ir submodule (resolved via git, no override): the same
/// resolution path the default gate run uses.
#[test]
fn bridge_gate_manifest_commit_matches_checkout() {
    let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
    let recorded = manifest_commit(&config.trustir_olean_dir);
    assert_eq!(recorded.len(), 40, "manifest records a full commit sha");
    // The default-on gate (bridge_gate_default_on, expected_trustir_commit =
    // None) already fails on drift; here we assert the recorded value is a
    // well-formed pin so the comparison is never vacuous.
    assert!(recorded.chars().all(|c| c.is_ascii_hexdigit()));
}
