use super::*;
#[path = "../../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::inst::CastOp;
use trust_ir::{Endianness, Linkage, StructPassingPolicy, TargetInfo};

fn fixture() -> Fixture {
    fixture_with_wide(false)
}
fn fixture_with_wide(include_wide: bool) -> Fixture {
    let mut b = ModBuilder::new("frameless_leaf_memory");
    let store = b.sig(&[IrTy::Ptr, IrTy::U64], Some(IrTy::U64));
    b.define("leaf_store", store, Linkage::External, |f| {
        let value = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: IrTy::U64,
            dst_ty: IrTy::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: IrTy::U8,
            ptr: f.p(0),
            value,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(IrTy::U64, 0);
        f.ret(zero);
    });
    if include_wide {
        b.define("leaf_store_wide", store, Linkage::External, |f| {
            f.push_inst_void(Inst::Store {
                ty: IrTy::U64,
                ptr: f.p(0),
                value: f.p(1),
                volatile: false,
                align: Some(1),
            });
            let zero = f.konst(IrTy::U64, 0);
            f.ret(zero);
        });
    }
    let load = b.sig(&[IrTy::Ptr], Some(IrTy::U64));
    b.define("leaf_load", load, Linkage::External, |f| {
        let byte =
            f.push_inst(Inst::Load { ty: IrTy::U8, ptr: f.p(0), volatile: false, align: Some(1) });
        let value = f.push_inst(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: IrTy::U8,
            dst_ty: IrTy::U64,
            operand: byte,
        });
        f.ret(value);
    });
    let copy = b.sig(&[IrTy::Ptr, IrTy::Ptr], Some(IrTy::U64));
    b.define("leaf_copy", copy, Linkage::External, |f| {
        let byte =
            f.push_inst(Inst::Load { ty: IrTy::U8, ptr: f.p(1), volatile: false, align: Some(1) });
        f.push_inst_void(Inst::Store {
            ty: IrTy::U8,
            ptr: f.p(0),
            value: byte,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(IrTy::U64, 0);
        f.ret(zero);
    });
    b.define("leaf_gep", store, Linkage::External, |f| {
        let offset = f.konst(IrTy::U64, 1);
        let pointer = f.push_inst(Inst::GEP {
            pointee_ty: IrTy::U8,
            base: f.p(0),
            indices: vec![offset],
            inbounds: false,
        });
        let value = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: IrTy::U64,
            dst_ty: IrTy::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: IrTy::U8,
            ptr: pointer,
            value,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(IrTy::U64, 0);
        f.ret(zero);
    });
    let mut module = b.finish();
    module.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    for function in &mut module.functions {
        function.calling_conv = CallingConv::Rust;
    }
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O3,
            parallel: false,
            emit_proofs: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&module)
    .unwrap()
    .object_code;
    Fixture::with_object(module, object, DARWIN)
}
fn evaluated(fixture: &Fixture, name: &str) -> (Source, Execution, SpecResult, PathOutcome) {
    let bound = BoundFunction::bind(&fixture.object, &fixture.m_cg, name, fixture.model).unwrap();
    let module = &fixture.m_cg;
    let function = module.functions.iter().find(|f| f.name == name).unwrap();
    let input = CerInput {
        m_cg: module,
        producers: &fixture.producers,
        bodies: &fixture.bodies,
        placements: &fixture.placements,
        object: &fixture.object,
        relocation_model: fixture.model,
    };
    let spec = eval_spec(
        &input,
        module,
        function,
        &signature_of(module, function.ty).unwrap(),
        &fixture.placements[name],
        &BTreeMap::new(),
    )
    .unwrap();
    let source = Source::read(module, function, &spec, module, name).unwrap();
    let mut state = MachineState::symbolic();
    state.memory = spec.memory.entry.clone();
    let places = BTreeMap::new();
    let mut exec = CerExec::new(bound.window(), &places, &fixture.placements[name].ret, true);
    exec.leaf_trace = Some(Trace::begin(&bound, bound.window(), &state).unwrap());
    let outcome =
        exec.run(bound.window().start, state, Vec::new(), 0, false, Formula::Bool(true)).unwrap();
    assert!(exec.leaf_refusal.is_none(), "{:?}", exec.leaf_refusal);
    (source, exec.leaf_trace.take().unwrap().finish().unwrap(), spec, outcome)
}
fn inputs(fixture: &Fixture, name: &str) -> KernelInputs {
    let (source, execution, spec, outcome) = evaluated(fixture, name);
    let bound = BoundFunction::bind(&fixture.object, &fixture.m_cg, name, fixture.model).unwrap();
    let plan = KernelInputs::derive(source, execution).unwrap();
    if let Some(output) = std::env::var_os("TRUST_LEAF_MEMORY_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output);
        std::fs::create_dir_all(&output).unwrap();
        let stem = format!("{name}-{}", &bound.binding().object_sha256[..12]);
        let mut all = plan.equations.clone();
        all.push((outcome.value.clone(), spec.value.clone()));
        let o0: Vec<_> =
            abi_guarantee_residue(&outcome, true).into_iter().map(|c| c.claim).collect();
        for claim in &o0 {
            if let Formula::Eq(left, right) = claim {
                all.push(((**left).clone(), (**right).clone()));
            }
        }
        let record = serde_json::json!({"binding":bound.binding(),"memory_coverage_equations":&plan.equations,
            "normal_scalar_and_memory_equations":all,"original_o0_claims":o0,"diagnostic":&plan.diagnostic});
        std::fs::write(
            output.join(format!("{stem}.json")),
            serde_json::to_vec_pretty(&record).unwrap(),
        )
        .unwrap();
        std::fs::write(output.join(format!("{stem}.o")), &fixture.object).unwrap();
    }
    plan
}
#[test]
#[cfg(feature = "kernel-recheck")]
fn real_cer_leaf_store_load_copy_and_gep_close_one_original_kernel_goal_and_strict_entire_object() {
    let fixture = fixture();
    let report = fixture.report();
    for name in ["leaf_store", "leaf_load", "leaf_copy", "leaf_gep"] {
        let certificate = report.certificate(name).unwrap();
        assert!(certificate.is_kernel_proved(), "{}", explain(&report));
        if let Some(out) = std::env::var_os("TRUST_LEAF_MEMORY_OUTPUT_DIR") {
            let out = std::path::PathBuf::from(out).join("complete-four-leaf-proof");
            std::fs::create_dir_all(&out).unwrap();
            std::fs::write(out.join("certificates.json"), report.to_json()).unwrap();
            std::fs::write(out.join("object.o"), &fixture.object).unwrap();
            std::fs::write(
                out.join(format!("{name}.kernel-evidence.txt")),
                format!("{:?}\n", certificate.verdict),
            )
            .unwrap();
        }
        let actual = certificate.leaf_memory.as_ref().unwrap();
        assert_eq!(actual.private_frame_bytes, Some(0), "{}", actual.status);
        assert!(actual.status.contains("conjunction checked by Clean kernel"));
        assert!(actual.original_joint_equations.is_some_and(|count| count >= 24));
        let plan = inputs(&fixture, name);
        assert_eq!(plan.diagnostic.source_coverage_bytes + 1, plan.equations.len());
        let (machine, source) = plan.equations.last().unwrap();
        assert!(matches!(machine, Formula::Select(..)) && matches!(source, Formula::Select(..)));
        assert!(matches!(discharge_equal_pre(machine, source, None), Discharge::Proven));
        // Existing multi-item scalar bitblast cannot be substituted for the
        // required original scalar+memory conjunction.
        let mut joint = vec![(
            Formula::BitVec { value: 0, width: 64 },
            Formula::BitVec { value: 0, width: 64 },
        )];
        joint.extend(plan.equations);
        assert!(try_kernel_recheckable_conjunction(&joint).is_none());
    }
    assert_eq!(report.certificates.len(), 4);
    assert_eq!(report.closure.closed_kernel.len(), 4);
    assert!(report.closure.unclosed.is_empty());
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok());
}
#[test]
fn missing_step_effect_or_real_post_register_cannot_mint_leaf_execution() {
    let fixture = fixture();
    let bound =
        BoundFunction::bind(&fixture.object, &fixture.m_cg, "leaf_store", fixture.model).unwrap();
    let state = MachineState::symbolic();
    let pc = bound.window().start;
    let decoded = decode_aarch64(&bound.window().code[..4], pc).unwrap();
    let effects = Aarch64Semantics.effects(&state, &decoded).unwrap();
    let mut missing = Trace::begin(&bound, bound.window(), &state).unwrap();
    assert!(missing.before(pc + 4, &Formula::Bool(true), &state, &effects).is_err());
    assert!(missing.finish().is_err());
    let mut wrong = Trace::begin(&bound, bound.window(), &state).unwrap();
    assert!(wrong.before(pc, &Formula::Bool(true), &state, &[]).is_err());
    assert!(wrong.finish().is_err());
    let mut dropped = Trace::begin(&bound, bound.window(), &state).unwrap();
    dropped.before(pc, &Formula::Bool(true), &state, &effects).unwrap();
    let mut post = dropped.expected.clone();
    post.gpr[5] = Formula::BitVec { value: 7, width: 64 };
    assert!(dropped.after(&post).is_err());
    assert!(dropped.finish().is_err());
}
#[test]
fn initialized_native_bytes_distinguish_memory_mutants_with_the_same_scalar_return() {
    let fixture = fixture();
    let words = function_words(&fixture.object, "leaf_store");
    let store = words
        .iter()
        .find(|(_, word)| word & 0xffc00000 == 0x39000000)
        .copied()
        .expect("actual STRB");
    let good = inputs(&fixture, "leaf_store");
    for (label, word) in [
        ("dropped", 0xd503201f),
        ("wrong", (store.1 & !31) | 31),
        ("offset", store.1 + (1 << 10)),
        ("extra-read", 0x3940041f),
    ] {
        let mutant = fixture.patched(|bytes| patch_word(bytes, store.0, word));
        let report = mutant.report();
        assert!(matches!(
            report.certificate("leaf_store").unwrap().verdict,
            OutputVerdict::Unknown { .. }
        ));
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
        if label == "extra-read" || label == "offset" {
            assert!(
                report
                    .certificate("leaf_store")
                    .unwrap()
                    .leaf_memory
                    .as_ref()
                    .unwrap()
                    .status
                    .contains("without source coverage")
            );
        } else {
            let bad = inputs(&mutant, "leaf_store");
            let (machine, source) = bad.equations.last().unwrap();
            assert!(matches!(
                discharge_equal_pre(machine, source, None),
                Discharge::CounterExample
            ));
            assert_ne!(bad.diagnostic.query, good.diagnostic.query);
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        {
            use std::fs;
            use std::process::Command;
            let dir = tempfile::tempdir().unwrap();
            fs::write(dir.path().join("object.o"), &mutant.object).unwrap();
            fs::write(
                dir.path().join("driver.c"),
                r#"#include <stdint.h>
extern uint64_t leaf_store(uint8_t *,uint64_t);
int main(void) { uint8_t bytes[3]={19,23,29}; uint64_t r=leaf_store(bytes,71);
if(r!=0)return 2; return bytes[0]==71 && bytes[1]==23 && bytes[2]==29 ? 0:1; }
"#,
            )
            .unwrap();
            let output = Command::new("/usr/bin/cc")
                .current_dir(dir.path())
                .args(["driver.c", "object.o", "-o", "driver"])
                .output()
                .unwrap();
            assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
            assert_eq!(
                Command::new(dir.path().join("driver")).status().unwrap().code(),
                Some(1),
                "{label}"
            );
        }
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn native(bytes: &[u8], label: &str, driver: &str, expected: i32) {
    use std::fs;
    use std::process::Command;
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("object.o"), bytes).unwrap();
    fs::write(dir.path().join("driver.c"), driver).unwrap();
    let output = Command::new("/usr/bin/cc")
        .current_dir(dir.path())
        .args(["-O2", "-Wall", "-Wextra", "-Werror", "driver.c", "object.o", "-o", "driver"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(
        Command::new(dir.path().join("driver")).status().unwrap().code(),
        Some(expected),
        "{label}"
    );
    if let Some(out) = std::env::var_os("TRUST_LEAF_MEMORY_OUTPUT_DIR") {
        let out = std::path::PathBuf::from(out).join(label);
        fs::create_dir_all(&out).unwrap();
        for name in ["object.o", "driver.c", "driver"] {
            fs::copy(dir.path().join(name), out.join(name)).unwrap();
        }
    }
}
#[test]
fn initialized_aliasing_leaf_drivers_and_narrow_store_keep_the_entire_array_obligation() {
    let fixture = fixture_with_wide(true);
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    native(
        &fixture.object,
        "positive-store-load-copy-gep",
        include_str!("../../../../../tests/run-make/trust-cg-frameless-leaf-memory/driver.c"),
        0,
    );
    let good = inputs(&fixture, "leaf_store_wide");
    let words = function_words(&fixture.object, "leaf_store_wide");
    let store =
        words.iter().find(|(_, w)| w & 0xffc00000 == 0xf9000000).copied().expect("actual STR64");
    let narrow =
        fixture.patched(|bytes| patch_word(bytes, store.0, 0x39000000 | (store.1 & 0x3ff)));
    let bad = inputs(&narrow, "leaf_store_wide");
    let (machine, source) = bad.equations.last().unwrap();
    assert!(matches!(discharge_equal_pre(machine, source, None), Discharge::CounterExample));
    assert!(bad.diagnostic.source_coverage_bytes < good.diagnostic.source_coverage_bytes);
    assert!(matches!(
        narrow.report().certificate("leaf_store_wide").unwrap().verdict,
        OutputVerdict::Unknown { .. }
    ));
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        let driver = r#"#include <stdint.h>
extern uint64_t leaf_store_wide(uint8_t *,uint64_t);
int main(void) { uint8_t bytes[10]={19,23,29,31,37,41,43,47,53,59};
if(leaf_store_wide(bytes,0x0807060504030201ULL)!=0)return 2;
for(unsigned i=0;i<8;i++)if(bytes[i]!=i+1)return 1;
return bytes[8]==53 && bytes[9]==59 ? 0:1; }
"#;
        native(&fixture.object, "wide-positive", driver, 0);
        native(&narrow.object, "narrow-store", driver, 1);
    }
}

#[test]
fn dead_extra_read_can_preserve_every_exit_byte_and_return_yet_coverage_refuses() {
    let fixture = fixture();
    let words = function_words(&fixture.object, "leaf_store");
    let store = words.iter().find(|(_, w)| w & 0xffc00000 == 0x39000000).copied().unwrap();
    let extract = words
        .iter()
        .find(|(_, w)| w & 0xfffffc00 == 0x53001c00)
        .copied()
        .expect("actual redundant U8 truncation");
    let mutant = fixture.patched(|bytes| {
        // STRB already takes low8; retain the exact store/return while replacing
        // its redundant producer mask with a dead read outside source coverage.
        patch_word(bytes, extract.0, 0x3940041f); // ldrb wzr,[x0,#1]
        patch_word(bytes, store.0, (store.1 & !31) | 1); // strb w1,[x0]
    });
    let (source, execution, spec, outcome) = evaluated(&mutant, "leaf_store");
    let q = Formula::Var("independent_dead_read_query".into(), Sort::BitVec(64));
    assert!(matches!(
        discharge_equal_pre(
            &Formula::Select(b(execution.exit.memory.clone()), b(q.clone())),
            &Formula::Select(b(source.exit.clone()), b(q)),
            None
        ),
        Discharge::Proven
    ));
    assert!(matches!(discharge_equal_pre(&outcome.value, &spec.value, None), Discharge::Proven));
    assert!(
        KernelInputs::derive(source, execution).err().unwrap().contains("without source coverage")
    );
    let report = mutant.report();
    assert!(
        report
            .certificate("leaf_store")
            .unwrap()
            .leaf_memory
            .as_ref()
            .unwrap()
            .status
            .contains("without source coverage")
    );
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    native(
        &mutant.object,
        "dead-extra-read-same-bytes",
        include_str!("../../../../../tests/run-make/trust-cg-frameless-leaf-memory/driver.c"),
        0,
    );
}
#[test]
fn actual_source_codegen_authority_and_fresh_query_are_not_inferred_from_counts() {
    let fixture = fixture();
    let name = "leaf_store";
    let (source, mut execution, spec, _) = evaluated(&fixture, name);
    let module = &fixture.m_cg;
    let function = module.functions.iter().find(|f| f.name == name).unwrap();
    let mut wrong = (**module).clone();
    wrong.target_info.as_mut().unwrap().pointer_size = 4;
    assert!(Source::read(module, function, &spec, &wrong, name).is_err());
    let mut wrong = (**module).clone();
    wrong.functions[0].calling_conv = CallingConv::C;
    assert!(Source::read(module, function, &spec, &wrong, name).is_err());
    let mut wrong = (**module).clone();
    wrong.func_types[function.ty.as_usize()].params[1] = IrTy::U32;
    assert!(Source::read(module, function, &spec, &wrong, name).is_err());
    let query =
        format!("CER_LEAF_QUERY@{}:{}", execution.binding.object_sha256, execution.binding.symbol);
    execution.entry.gpr[28] = Formula::Var(query, Sort::BitVec(64));
    assert!(
        KernelInputs::derive(source, execution).err().unwrap().contains("query is contaminated")
    );
}

#[test]
#[cfg(feature = "kernel-recheck")]
fn full_f1_strict_policy_closes_the_complete_four_leaf_denominator() {
    use crate::f1_compile::{
        F1CompileConfig, F1CompileInput, F1OptLevel, F1Target, compile_and_verify_trust_ir_module,
    };
    let fixture = fixture();
    let mut module = (*fixture.m_cg).clone();
    // Hand-authored IR exercises the actual D31 license and F1 consumer; this
    // does not invent a Rust instance or claim actual frontend/source admission.
    for function in &mut module.functions {
        function.body_gate = Some(trust_ir::BodyGate::Gated {
            authority: "trust-direct-lane-structural".into(),
            evidence: None,
        });
    }
    let config = F1CompileConfig {
        force_frame_pointers: false,
        target: F1Target::Aarch64AppleDarwin,
        opt_level: F1OptLevel::O3,
        relocation: fixture.model,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    };
    for original_unclassified in [false, true] {
        let mut original = module.clone();
        if original_unclassified {
            original.target_info.as_mut().unwrap().struct_passing =
                StructPassingPolicy::Unclassified;
        }
        let producers = [ProducerModule::named_by_symbols(std::sync::Arc::new(original))];
        let shipped = compile_and_verify_trust_ir_module(&F1CompileInput {
            m_cg: &module,
            producers: &producers,
            bodies: &fixture.bodies,
            placements: &fixture.placements,
            policy: EmitPolicy::StrictProvenOnly,
            config: &config,
        })
        .expect("actual complete F1 strict memory-leaf object");
        assert_eq!(shipped.report.certificates.len(), 4);
        assert_eq!(shipped.report.closure.closed_kernel.len(), 4);
        assert!(shipped.report.certificates.iter().all(|c| c.is_kernel_proved()));
        assert!(shipped.report.ships(EmitPolicy::StrictProvenOnly).is_ok());
        if let Some(out) = std::env::var_os("TRUST_LEAF_MEMORY_OUTPUT_DIR") {
            let out = std::path::PathBuf::from(out)
                .join(format!("strict-f1-original-unclassified-{original_unclassified}"));
            std::fs::create_dir_all(&out).unwrap();
            std::fs::write(out.join("object.o"), &shipped.object).unwrap();
            std::fs::write(out.join("certificates.json"), shipped.report.to_json()).unwrap();
        }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        native(
            &shipped.object,
            &format!("strict-native-{original_unclassified}"),
            include_str!("../../../../../tests/run-make/trust-cg-frameless-leaf-memory/driver.c"),
            0,
        );
    }
}
#[test]
fn original_scalar_return_and_callee_saved_abi_cannot_be_omitted_from_memory_goal() {
    let fixture = fixture();
    let words = function_words(&fixture.object, "leaf_store");
    let store = words.iter().find(|(_, w)| w & 0xffc00000 == 0x39000000).copied().unwrap();
    let extract = words.iter().find(|(_, w)| w & 0xfffffc00 == 0x53001c00).copied().unwrap();
    let zero = words.iter().find(|(_, w)| *w == 0xd2800000).copied().expect("actual mov x0,#0");
    for (label, mutant) in [
        ("return", fixture.patched(|bytes| patch_word(bytes, zero.0, 0xd28000e0))),
        (
            "abi",
            fixture.patched(|bytes| {
                patch_word(bytes, extract.0, 0xd2800013); // mov x19,#0
                patch_word(bytes, store.0, (store.1 & !31) | 1); // same low8 store
            }),
        ),
    ] {
        let (source, execution, _, _) = evaluated(&mutant, "leaf_store");
        let q = Formula::Var(format!("independent_{label}_memory_query"), Sort::BitVec(64));
        assert!(matches!(
            discharge_equal_pre(
                &Formula::Select(b(execution.exit.memory), b(q.clone())),
                &Formula::Select(b(source.exit), b(q)),
                None
            ),
            Discharge::Proven
        ));
        let report = mutant.report();
        assert!(
            matches!(
                report.certificate("leaf_store").unwrap().verdict,
                OutputVerdict::Unknown { .. }
            ),
            "{}",
            explain(&report)
        );
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
        assert!(
            report.certificates.iter().all(|c| !matches!(c.verdict, OutputVerdict::Refuted { .. }))
        );
    }
}

#[test]
fn object_relative_adr_and_adrp_cannot_prove_a_loaded_native_address_is_zero() {
    let fixture = fixture();
    let (pc, _) = function_words(&fixture.object, "leaf_store")
        .into_iter()
        .find(|(_, word)| *word == 0xd2800000)
        .expect("actual mov x0,#0");
    assert!(pc < 4096);
    // Resolve both data addresses to zero in object coordinates. Neither is
    // zero after loading this relocation-free instruction into an executable.
    let immediate = pc.wrapping_neg() & 0x1f_ffff;
    let adr =
        0x10000000 | ((immediate as u32 & 3) << 29) | (((immediate as u32 >> 2) & 0x7ffff) << 5);
    for (label, opcode, word) in
        [("unplaced-adr", Opcode::Adr, adr), ("unplaced-adrp", Opcode::Adrp, 0x90000000)]
    {
        let mutant = fixture.patched(|bytes| patch_word(bytes, pc, word));
        let bound =
            BoundFunction::bind(&mutant.object, &mutant.m_cg, "leaf_store", mutant.model).unwrap();
        assert!(bound.window().relocations.is_empty());
        let decoded = decode_aarch64(&word.to_le_bytes(), pc).unwrap();
        assert_eq!(decoded.opcode, opcode);
        assert!(unplaced_pc_data(&decoded));
        assert!(Aarch64Semantics.effects(&MachineState::symbolic(), &decoded).unwrap().iter().any(
            |effect| matches!(
                effect,
                Effect::RegWrite { index: 0, value: Formula::BitVec { value: 0, width: 64 }, .. }
            )
        ));
        let report = mutant.report();
        let certificate = report.certificate("leaf_store").unwrap();
        assert!(
            matches!(&certificate.verdict, OutputVerdict::Unknown { reason }
                if reason.contains("runtime placement witness")),
            "{}",
            explain(&report)
        );
        assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
        assert!(
            report.certificates.iter().all(|c| !matches!(c.verdict, OutputVerdict::Refuted { .. }))
        );
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        native(
            &mutant.object,
            label,
            r#"#include <stdint.h>
extern uint64_t leaf_store(uint8_t *,uint64_t);
int main(void) { uint8_t bytes[3]={19,23,29}; uint64_t r=leaf_store(bytes,71);
if(bytes[0]!=71 || bytes[1]!=23 || bytes[2]!=29)return 1;
return r!=0 ? 2:0; }
"#,
            2,
        );
    }
    let literal = decode_aarch64(&0x58000000u32.to_le_bytes(), pc).unwrap();
    assert_eq!(literal.opcode, Opcode::LdrLiteral);
    assert!(unplaced_pc_data(&literal));
}

#[test]
#[cfg(not(feature = "kernel-recheck"))]
fn missing_real_kernel_feature_cannot_admit_any_memory_leaf() {
    let fixture = fixture();
    let report = fixture.report();
    assert!(report.certificates.iter().all(|c| matches!(c.verdict, OutputVerdict::Unknown { .. })));
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_err());
}
