use trust_cg_codegen::Compiler;
use trust_cg_codegen::target::TargetSpec;
use trust_machine_sem::{Aarch64Semantics, ConcreteState, Effect, MachineState, Semantics};

use super::*;
use crate::compiler_input_capture::CompilerInputCapture;
use crate::f1_compile::{
    F1CompileConfig, F1CompileInput, F1OptLevel, F1Refusal, F1Target,
    compile_and_verify_trust_ir_module_captured, f1_codegen_license,
};
use crate::verify_output::EmitPolicy;

const INPUT: &[u8] = include_bytes!("current-e76-caller/actual-input.json");
const CALLER: &str = "source_memory_caller";

fn config(data: &crate::compiler_input_capture::DecodedCompilerInputs) -> F1CompileConfig {
    F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O0,
        relocation: crate::compiled_object::RelocationModel::Pic,
        never_inline: data
            .m_cg
            .functions
            .iter()
            .filter(|f| f.name != CALLER)
            .map(|f| f.name.clone())
            .collect(),
        upstream_mir_lane: false,
    }
}

fn bound(data: &crate::compiler_input_capture::DecodedCompilerInputs) -> ObjectLayout {
    let object = CompiledObject::parse(&data.object).unwrap();
    let expect =
        ObjectExpectations::from_module(&data.m_cg, object.format, data.relocation).unwrap();
    ObjectLayout::bind(object, &expect).unwrap()
}

#[test]
fn actual_e76_reconstructed_caller_retains_frame_inputs_without_claiming_the_missing_semantics() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(32 << 20)
            .spawn_scoped(scope, check_actual)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn check_actual() {
    assert_eq!(
        artifact_digest(INPUT),
        "e4b0e9030c002ebfa9d3a6395e6322197dffe6f96d5b524e913ddb7eea67cd38"
    );
    let data = CompilerInputCapture::from_bytes(INPUT).unwrap().decode_inputs().unwrap();
    assert_eq!(
        artifact_digest(&data.object),
        "b20aa8af874f0bc71b54e3144632d0df1c1d17dc4b821f9d402b50d23f17d01b"
    );
    assert!(data.m_cg.closure_layouts.is_empty());
    assert!(
        data.m_cg
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.body)
            .all(|n| !matches!(n.inst, trust_ir::Inst::Alloca { .. }))
    );
    let config = config(&data);
    let compiler = Compiler::new_for_target_spec(
        config.compiler_config(),
        TargetSpec::parse(config.target.triple()).unwrap(),
    )
    .with_codegen_license(f1_codegen_license(false));
    let result = compiler.compile(&data.m_cg).unwrap();
    assert_eq!(result.object_code, data.object, "AOT observation must not change actual bytes");
    assert_eq!(result.aarch64_frame_inputs.len(), 2);
    let mut report = crate::call_event::verify_compiled_module(&data.input()).unwrap();
    let old = report
        .certificates
        .iter()
        .map(|row| {
            (
                row.grade.clone(),
                row.obligations.clone(),
                serde_json::to_vec(&row.original_proof).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    attach(&data.input(), &result.aarch64_frame_inputs, &mut report).unwrap();
    assert_eq!(
        old,
        report
            .certificates
            .iter()
            .map(|row| (
                row.grade.clone(),
                row.obligations.clone(),
                serde_json::to_vec(&row.original_proof).unwrap()
            ))
            .collect::<Vec<_>>()
    );
    let caller = report.certificates.iter().find(|row| row.symbol == CALLER).unwrap();
    assert!(matches!(caller.verdict, OutputVerdict::Unknown { .. }));
    assert_eq!(caller.obligations.o5_frame.grade, Grade::Unknown);
    assert!(caller.obligations.o5_frame.detail.contains("M5 memory-call premises are unproved"));
    let request = caller.frame_inputs.as_ref().unwrap();
    assert_eq!(request.producer_frame_bytes, Some(16));
    assert!(request.producer_slots.is_empty());
    assert!(matches!(request.envelope, FrameEnvelopeInput::ObservedFpLr16DirectCall { .. }));
    assert_eq!(request.outstanding.len(), 7);
    assert!(request.outstanding.contains(&FrameInputObligation::SemRAllocationEmbedding));
    assert!(request.outstanding.contains(&FrameInputObligation::OriginalUnrestrictedArrayEquation));
    let memory = request.machine_memory_inputs.as_ref().unwrap();
    assert_eq!(memory.steps.len(), 5);
    assert_eq!(memory.calls.len(), 1);
    assert_eq!(memory.returns.len(), 1);
    assert_eq!(memory.entry.gpr.len(), 31);
    assert_eq!(memory.entry.fpr.len(), 32);
    assert_eq!(Some(&memory.entry.sp), request.entry_sp.as_ref());
    assert_eq!(
        memory.steps.iter().map(|step| step.occurrence).collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4]
    );
    assert_eq!(memory.calls[0].occurrence, 2);
    assert_eq!(memory.calls[0].kind, crate::cer_memory_machine::CallKind::Call);
    assert_eq!(memory.returns[0].occurrence, 4);
    assert_eq!(memory.returns[0].kind, crate::cer_memory_machine::ExitKind::Return);
    assert_eq!(memory.steps.iter().flat_map(|s| &s.accesses).count(), 4);
    assert!(report.certificates.iter().all(|row| row.frame_execution.is_none()));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());

    // Actual F1 producer use, not a caller-built frame report or weakened lane.
    let original = compile_and_verify_trust_ir_module_captured(&F1CompileInput {
        m_cg: &data.m_cg,
        producers: &data.producers,
        bodies: &data.bodies,
        placements: &data.placements,
        policy: EmitPolicy::StrictProvenOnly,
        config: &config,
    });
    let Err(F1Refusal::Policy(reason)) = original.outcome else {
        panic!("framed caller unexpectedly escaped its existing Strict refusal")
    };
    // The refusal names the caller's blocker (a Refuted obligation before any Unknown one) under
    // its own label, and the pending frame list only as the PKG-B request it is, which decides
    // no grade.
    let ordered = [
        ("o0", &caller.obligations.o0_abi),
        ("o1", &caller.obligations.o1_binding),
        ("o2", &caller.obligations.o2_pairing),
        ("o3", &caller.obligations.o3_events),
        ("o4", &caller.obligations.o4_return),
        ("o5", &caller.obligations.o5_frame),
    ];
    let first = |grade: Grade| ordered.iter().find(|(_, g)| g.grade == grade);
    let first = first(Grade::Refuted)
        .or_else(|| first(Grade::Unknown))
        .map(|(n, g)| format!("{CALLER} {n}: {:?}: ", g.grade))
        .expect("the non-proven caller has an undecided obligation");
    assert!(reason.contains("; blockers: "), "{reason}");
    assert!(reason.contains(&first), "{reason}");
    let request = reason
        .split("; ")
        .find(|entry| entry.starts_with("PKG-B SemR request (decides no grade) from "))
        .unwrap_or_else(|| panic!("no SemR request entry: {reason}"));
    assert!(request.contains(&format!("`{CALLER}`")), "{reason}");
    assert!(request.contains(": [SemRAllocationEmbedding"), "{reason}");
    assert!(!reason.contains("frame inputs pending"), "{reason}");
    // The whole refusal as the ladder reads it carries one class tag, the gate's own.
    let shown = F1Refusal::Policy(reason.clone()).to_string();
    assert_eq!(
        untagged(&shown),
        shown.replacen("[f1-output-gate:policy]", "[`f1-output-gate:policy`]", 1),
        "{shown}"
    );
    assert!(reason.contains("OriginalUnrestrictedArrayEquation"));
    assert!(original.capture.is_ok());

    let layout = bound(&data);
    let window = &layout.windows[CALLER];
    let index = result.aarch64_frame_inputs.iter().position(|row| row.symbol == CALLER).unwrap();
    let mut missing_layout = result.aarch64_frame_inputs.clone();
    missing_layout[index].layout = None;
    let mut missing_report = report.clone();
    attach(&data.input(), &missing_layout, &mut missing_report).unwrap();
    assert!(matches!(
        missing_report
            .certificates
            .iter()
            .find(|row| row.symbol == CALLER)
            .unwrap()
            .frame_inputs
            .as_ref()
            .unwrap()
            .envelope,
        FrameEnvelopeInput::MissingProducerLayout
    ));
    assert!(missing_report.ships(EmitPolicy::StrictProvenOnly).is_err());
    for mutation in 0..3 {
        let mut changed = result.aarch64_frame_inputs.clone();
        match mutation {
            0 => changed[index].layout.as_mut().unwrap().total_frame_size = 0,
            1 => {
                changed.pop();
            }
            _ => changed.push(changed[0].clone()),
        }
        assert!(attach(&data.input(), &changed, &mut report.clone()).is_err());
    }
    let mut wrong_saved = result.aarch64_frame_inputs[index].clone();
    wrong_saved.layout.as_mut().unwrap().callee_saved_pairs[0].reg1 = trust_cg_ir::regs::X19;
    assert!(matches!(envelope(window, &wrong_saved), FrameEnvelopeInput::Unsupported { .. }));
    for (offset, word) in [(0usize, 0xa9bf_7bf3u32), (16, 0xd65f_0120)] {
        let mut changed = window.clone();
        changed.code[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
        assert!(matches!(
            envelope(&changed, &result.aarch64_frame_inputs[index]),
            FrameEnvelopeInput::Unsupported { .. }
        ));
    }
    for destination in [0x3000, 0x1000 - 16, 0x1000 - 8] {
        alias_counterexample(&layout, destination);
    }

    // The framed caller with NO P entry: its row already grades Unknown ("P has no placement
    // for this function"), so attaching retains no frame request for it and refuses nothing.
    // Before the fix `attach` refused the whole module ("frame has no actual P entry"), a
    // module-level `[f1-output-gate:binding]` under allow-unknown too (809eeaba39).
    let mut unplaced = CompilerInputCapture::from_bytes(INPUT).unwrap().decode_inputs().unwrap();
    assert!(unplaced.placements.remove(CALLER).is_some());
    let mut unplaced_report = crate::call_event::verify_compiled_module(&unplaced.input()).unwrap();
    let grades = |report: &CerReport| {
        report
            .certificates
            .iter()
            .map(|row| (row.symbol.clone(), row.grade.clone(), row.obligations.clone()))
            .collect::<Vec<_>>()
    };
    let before = grades(&unplaced_report);
    attach(&unplaced.input(), &result.aarch64_frame_inputs, &mut unplaced_report).unwrap();
    assert_eq!(before, grades(&unplaced_report), "attach never changes a verdict");
    let caller = unplaced_report.certificates.iter().find(|row| row.symbol == CALLER).unwrap();
    assert!(!caller.verdict.is_proven());
    assert!(caller.frame_inputs.is_none(), "no P entry, no frame request");
    assert!(unplaced_report.ships(EmitPolicy::StrictProvenOnly).is_err());
}

/// `scripts/trust_f1_ladder.py`'s `CLASS_TAG`, `\[[a-z][a-z0-9:-]*\]`, finds
/// `[mk]`, `[f1-output-gate:policy]`, `[x9:-]` and `[z]` in `TAGGED` and nothing in
/// `UNTAGGED` (checked with Python's `re.findall` on 2026-11-14).
const TAGGED: &str =
    "for [mk] and [f1-output-gate:policy] [VALIDATED] [a_b] [\u{e9}] [x9:-] [`q`] [9a] [[z]] [";
const UNTAGGED: &str = "for [`mk`] and [`f1-output-gate:policy`] [VALIDATED] [a_b] [\u{e9}] [`x9:-`] [`q`] [9a] [[`z`]] [";

#[test]
fn untagged_quotes_exactly_what_the_ladder_reads_as_a_class() {
    assert_eq!(untagged(TAGGED), UNTAGGED);
    assert_eq!(untagged(UNTAGGED), UNTAGGED);
}

/// The blockers no single obligation names, and a refutation graded after an Unknown. Grades are
/// set by hand on the actual e76 reconstructed-subject report, so this pins only the refusal text: a [VALIDATED] row is
/// "Proven without kernel evidence", a kernel-proved row left unclosed names its unclosed callees,
/// a Refuted function is named by its refuting obligation even when an earlier-numbered one is
/// Unknown, and a refutation is the only cause named under either policy.
#[test]
fn refusal_context_names_each_blocker_and_only_the_refutation_when_refuted() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(32 << 20)
            .spawn_scoped(scope, check_unproved_blockers)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn check_unproved_blockers() {
    use crate::verify_output::ProvenEvidence;
    let data = CompilerInputCapture::from_bytes(INPUT).unwrap().decode_inputs().unwrap();
    let mut report = crate::call_event::verify_compiled_module(&data.input()).unwrap();
    let caller = report.certificates.iter().position(|row| row.symbol == CALLER).unwrap();
    let callee = report.certificates[caller]
        .assumptions
        .iter()
        .find_map(|a| match a {
            crate::call_event::Assumption::CoEmitted(callee) => Some(callee.clone()),
            crate::call_event::Assumption::External(_) => None,
        })
        .expect("the current caller calls a co-emitted callee");
    for row in &mut report.certificates {
        let (verdict, grade) = if row.symbol == CALLER {
            (
                ProvenEvidence::KernelInstantiated { theorem: "test".into(), original: None },
                "[PROVED]",
            )
        } else {
            (ProvenEvidence::AyValidated, "[VALIDATED]")
        };
        row.verdict = OutputVerdict::Proven { evidence: verdict };
        row.grade = grade.into();
    }
    report.closure = crate::call_event::closure_report(&report.certificates);
    let text = refusal_context(&report, EmitPolicy::StrictProvenOnly);
    assert!(text.starts_with("blockers: "), "{text}");
    assert!(text.contains(&format!("{callee}: Proven without kernel evidence")), "{text}");
    assert!(text.contains(&format!("{CALLER}: blocked by callees [`{callee}`]")), "{text}");
    assert_eq!(untagged(&text), text);
    // Allow-unknown ships with nothing Refuted, so it has no blocker to name.
    assert_eq!(refusal_context(&report, EmitPolicy::AllowUnknown), "");

    // O0 is graded after O5, so a Refuted O5 can sit beside an Unknown O0: the refutation
    // decides the verdict and is what the refusal names.
    let row = &mut report.certificates[caller];
    row.obligations.o0_abi = ObligationGrade { grade: Grade::Unknown, detail: "o0 open".into() };
    row.obligations.o5_frame =
        ObligationGrade { grade: Grade::Refuted, detail: "a store outside the frame".into() };
    row.verdict = OutputVerdict::Refuted { detail: "o5 refuted".into() };
    row.grade = "[REFUTED]".into();
    report.closure = crate::call_event::closure_report(&report.certificates);
    for policy in [EmitPolicy::StrictProvenOnly, EmitPolicy::AllowUnknown] {
        let text = refusal_context(&report, policy);
        assert_eq!(text, format!("refuted by: {CALLER} o5: Refuted: a store outside the frame"));
    }
    // Under Strict with nothing Refuted, the same row's blocker is still its Refuted obligation
    // before its Unknown one.
    let row = &report.certificates[caller];
    let unclosed = crate::call_event::Unclosed {
        symbol: CALLER.into(),
        grade: "[UNKNOWN]".into(),
        blocked_by: Vec::new(),
    };
    assert_eq!(
        blocker(&unclosed, Some(row)),
        format!("{CALLER} o5: Refuted: a store outside the frame")
    );
    assert_eq!(blocker(&unclosed, None), format!("{CALLER}: no certificate"));
    assert_eq!(clipped(" "), "no reason recorded");
    let long = "x".repeat(MAX_DETAIL + 5);
    assert_eq!(clipped(&long), format!("{}... (+5 bytes)", "x".repeat(MAX_DETAIL)));
}

// A finite counterexample on the captured machine instructions, not a proof
// of their general semantics. Relocated call dispatch comes from the bound
// object's actual site. The existing concrete evaluator handles data effects.
fn execute(state: &mut ConcreteState, word: u32, pc: u64) -> bool {
    state.pc = pc;
    let decoded = trust_disasm::decode_aarch64(&word.to_le_bytes(), pc).unwrap();
    let effects = Aarch64Semantics.effects(&MachineState::symbolic(), &decoded).unwrap();
    let before = state.clone();
    let mut call = false;
    for effect in effects {
        match effect {
            Effect::Call { return_addr, .. } => {
                state.gpr[30] = before.eval_bv(&return_addr, 64).unwrap() as u64;
                call = true;
            }
            Effect::Return { target } => state.pc = before.eval_bv(&target, 64).unwrap() as u64,
            other => state.apply_effect_with_eval_state(&before, &other).unwrap(),
        }
    }
    call
}

fn alias_counterexample(layout: &ObjectLayout, destination: u64) {
    let caller = &layout.windows[CALLER];
    let callee = &layout.windows[caller.sites[0].callee.as_ref().unwrap()];
    let mut state = ConcreteState::new();
    state.sp = 0x1000;
    state.gpr[0] = destination;
    state.gpr[1] = 0x2000;
    state.gpr[2] = 0xab;
    state.gpr[29] = 0x1122_3344_5566_7788;
    state.gpr[30] = 0x1234_5678;
    for address in 0xff0..0x1000 {
        state.memory.insert(address, 0);
    }
    state.memory.insert(0x2000, 7);
    state.memory.insert(0x3000, 0);
    let original = state.clone();
    let caller_words = words(caller).unwrap();
    for (index, word) in caller_words.into_iter().enumerate() {
        if execute(&mut state, word, caller.start + index as u64 * 4) {
            assert_eq!(index, 2);
            for (index, word) in words(callee).unwrap().into_iter().enumerate() {
                assert!(!execute(&mut state, word, callee.start + index as u64 * 4));
            }
            assert_eq!(state.pc, caller.start + 12);
        }
    }
    assert_eq!(state.sp, original.sp);
    assert_eq!(state.gpr[0], 7);
    if destination == 0xff0 {
        assert_ne!(state.gpr[29], original.gpr[29], "raw output aliases saved FP");
    } else if destination == 0xff8 {
        assert_ne!(state.pc, original.gpr[30], "raw output aliases the saved return target");
    } else {
        assert_eq!(state.gpr[29], original.gpr[29]);
        assert_eq!(state.pc, original.gpr[30]);
    }
    // Even the separated case changes a frame byte, so the old unrestricted
    // source-array goal cannot be certified by simply hiding that interval.
    assert_ne!(state.memory[&0xff0], original.memory[&0xff0]);
}
