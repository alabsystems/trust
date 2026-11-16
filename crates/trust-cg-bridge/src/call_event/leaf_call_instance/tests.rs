#![cfg(feature = "kernel-recheck")]
use super::*;
#[path = "../../../tests/cer_common/mod.rs"]
mod cer_common;
use cer_common::*;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::inst::CastOp;
use trust_ir::{CallingConv, Endianness, Linkage, StructPassingPolicy, TargetInfo, Ty};

use crate::original_conjunction_certificate::without_production;
use crate::verify_output::EmitPolicy;

fn fixture(opt: OptLevel) -> Fixture {
    let mut b = ModBuilder::new("m5_actual_tail_instances");
    let store_sig = b.sig(&[Ty::Ptr, Ty::U64], Some(Ty::U64));
    let store = b.define("memory_store", store_sig, Linkage::External, |f| {
        let byte = f.push_inst(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U64,
            dst_ty: Ty::U8,
            operand: f.p(1),
        });
        f.push_inst_void(Inst::Store {
            ty: Ty::U8,
            ptr: f.p(0),
            value: byte,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(Ty::U64, 0);
        f.ret(zero);
    });
    let copy_sig = b.sig(&[Ty::Ptr, Ty::Ptr], Some(Ty::U64));
    let copy = b.define("memory_copy", copy_sig, Linkage::External, |f| {
        let byte =
            f.push_inst(Inst::Load { ty: Ty::U8, ptr: f.p(1), volatile: false, align: Some(1) });
        f.push_inst_void(Inst::Store {
            ty: Ty::U8,
            ptr: f.p(0),
            value: byte,
            volatile: false,
            align: Some(1),
        });
        let zero = f.konst(Ty::U64, 0);
        f.ret(zero);
    });
    b.define("tail_store", store_sig, Linkage::External, |f| {
        let value = f.call(store, &[f.p(0), f.p(1)]);
        f.ret(value);
    });
    b.define("tail_copy", copy_sig, Linkage::External, |f| {
        let value = f.call(copy, &[f.p(0), f.p(1)]);
        f.ret(value);
    });
    b.define("tail_alias", copy_sig, Linkage::External, |f| {
        let value = f.call(copy, &[f.p(0), f.p(0)]);
        f.ret(value);
    });
    let mut module = b.finish();
    module.target_info = Some(TargetInfo {
        triple: DARWIN.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    for f in &mut module.functions {
        f.calling_conv = CallingConv::Rust;
    }
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            parallel: false,
            emit_proofs: false,
            never_inline: ["memory_store", "memory_copy"].into_iter().map(str::to_owned).collect(),
            ..Default::default()
        },
        TargetSpec::parse(DARWIN).unwrap(),
    )
    .with_codegen_license(fixture_license())
    .compile(&module)
    .unwrap()
    .object_code;
    Fixture::with_object(module, object, DARWIN)
}
fn input(f: &Fixture) -> CerInput<'_> {
    CerInput {
        m_cg: &f.m_cg,
        producers: &f.producers,
        bodies: &f.bodies,
        placements: &f.placements,
        object: &f.object,
        relocation_model: f.model,
    }
}
fn sample() -> &'static Fixture {
    static F: std::sync::OnceLock<Fixture> = std::sync::OnceLock::new();
    F.get_or_init(|| fixture(OptLevel::O2))
}
fn prepared() -> &'static PreparedLeafCalls<'static> {
    static P: std::sync::OnceLock<PreparedLeafCalls<'static>> = std::sync::OnceLock::new();
    P.get_or_init(|| prepare_leaf_calls(&input(sample())).unwrap())
}
#[test]
fn actual_coemitted_tail_instances_retain_complete_leaf_goal_and_do_not_license_callers() {
    let p = prepared();
    assert_eq!(p.report().certificates.len(), 5, "{}", explain(p.report()));
    for symbol in ["memory_store", "memory_copy"] {
        assert!(
            p.report().certificate(symbol).unwrap().is_kernel_proved(),
            "{}",
            explain(p.report())
        );
    }
    let mut outputs = Vec::new();
    for (caller, callee) in [("tail_store", "memory_store"), ("tail_copy", "memory_copy")] {
        let row = p.report().certificate(caller).unwrap();
        assert_eq!(row.grade, "Unknown");
        assert!(row.obligations.o5_frame.detail.contains("M5 memory-call premises"));
        assert_eq!(row.call_sites.len(), 1);
        assert_eq!(row.call_sites[0].kind, CallSiteKind::Tail);
        let instance =
            without_production(|| p.specialize(caller)).unwrap_or_else(|e| panic!("{caller}: {e}"));
        let original = p.providers[callee].checked.original_equations();
        assert_eq!(
            instance.original_equations().len(),
            original.len() + p.input.placements[callee].params.len()
        );
        assert!(instance.original_equations().iter().any(|(a,c)|matches!((a,c),(Formula::Select(_,q),Formula::Select(_,r)) if matches!(q.as_ref(),Formula::Var(_,Sort::BitVec(64)))&&q==r)));
        let bytes = instance.to_untrusted_json().unwrap();
        let wire: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(wire["binding"]["caller_symbol"], caller);
        assert_eq!(wire["binding"]["callee_symbol"], callee);
        let indices = wire["binding"]["prefix_abi_conjuncts"].as_array().unwrap();
        assert_eq!(indices.len(), 21);
        assert_eq!(
            indices.iter().map(|index| index.as_u64().unwrap()).collect::<BTreeSet<_>>().len(),
            21
        );
        for index in indices {
            let equation = &instance.original_equations()[index.as_u64().unwrap() as usize];
            assert_eq!(equation.0, equation.1);
        }

        assert_eq!(
            wire["packet"]["original"].as_array().unwrap().len(),
            instance.original_equations().len()
        );
        outputs.push((caller, bytes));
    }
    let alias = p.report().certificate("tail_alias").unwrap();
    assert_eq!(alias.grade, "Unknown");
    let error = without_production(|| p.specialize("tail_alias")).err().unwrap();
    assert!(
        error.contains("exact original argument"),
        "raw MOV/OR entry needs checked transport: {error}"
    );
    assert!(p.report().ships(EmitPolicy::StrictProvenOnly).is_err());
    actual_native_alias_control(sample());
    if let Some(out) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
        let out = std::path::PathBuf::from(out);
        std::fs::create_dir_all(&out).unwrap();
        for (name, bytes) in outputs {
            std::fs::write(out.join(format!("{name}.instance.json")), bytes).unwrap();
        }
        std::fs::write(out.join("actual-object.o"), &sample().object).unwrap();
        std::fs::write(out.join("ordinary-certificates.json"), p.report().to_json()).unwrap();
        std::fs::write(
            out.join("actual-module.json"),
            serde_json::to_vec(sample().m_cg.as_ref()).unwrap(),
        )
        .unwrap();
    }
}
#[test]
fn actual_subject_p_module_callee_and_source_target_changes_cannot_reuse_provider() {
    let p = prepared();
    let f = sample();
    let mut object = f.object.clone();
    let last = object.len() - 1;
    object[last] ^= 1;
    let mut wrong = p.input;
    wrong.object = &object;
    assert!(without_production(|| specialize_with(p, wrong, "tail_store")).is_err());
    let mut placements = f.placements.clone();
    placements.get_mut("memory_store").unwrap().params[0] =
        ParamPlace::Scalar(ScalarPlace::gpr(1, 64));
    let mut wrong = p.input;
    wrong.placements = &placements;
    assert!(without_production(|| specialize_with(p, wrong, "tail_store")).is_err());
    let mut producers = f.producers.clone();
    let mut module = (*producers[0].module).clone();
    module.name.push_str("_changed_source");
    producers[0].module = Arc::new(module);
    let mut wrong = p.input;
    wrong.producers = &producers;
    assert!(without_production(|| specialize_with(p, wrong, "tail_store")).is_err());
    let mut wrong = p.input;
    wrong.relocation_model = RelocationModel::Pic;
    assert!(without_production(|| specialize_with(p, wrong, "tail_store")).is_err());
}
fn specialize_with<'a>(
    p: &PreparedLeafCalls<'_>,
    input: CerInput<'a>,
    caller: &str,
) -> Result<CheckedLeafAtTailSite, String> {
    PreparedLeafCalls { input, report: p.report.clone(), providers: p.providers.clone() }
        .specialize(caller)
}
#[test]
fn actual_memory_byte_mutations_and_normal_bl_cannot_be_tail_instances() {
    let p = prepared();
    let f = sample();
    let store = function_words(&f.object, "memory_store")
        .into_iter()
        .find(|(_, w)| w & 0xffc00000 == 0x39000000)
        .unwrap();
    let mut object = f.object.clone();
    patch_word(&mut object, store.0, 0xd503201f);
    let mut wrong = p.input;
    wrong.object = &object;
    assert!(without_production(|| specialize_with(p, wrong, "tail_store")).is_err());
    let tail = function_words(&f.object, "tail_store").into_iter().find(|(_, w)| is_b(*w)).unwrap();
    let mut object = f.object.clone();
    patch_word(&mut object, tail.0, (tail.1 & 0x03ff_ffff) | 0x9400_0000);
    let mut wrong = p.input;
    wrong.object = &object;
    let error = without_production(|| specialize_with(p, wrong, "tail_store")).err().unwrap();
    assert!(error.contains("Tail") || error.contains("tail window"), "{error}");
}
#[test]
fn prefix_full_effects_states_occurrences_sp_and_pc_frontiers_are_sealed() {
    let f = sample();
    let object = CompiledObject::parse(&f.object).unwrap();
    let expect = ObjectExpectations::from_module(&f.m_cg, object.format, f.model).unwrap();
    let layout = ObjectLayout::bind(object, &expect).unwrap();
    let window = &layout.windows["tail_store"];
    let mut state = MachineState::symbolic();
    state.memory = crate::cer_memory::shared_entry_memory("prefix-control");
    let mut trace = PrefixTrace::begin(window, &state).unwrap();
    assert!(trace.finish().is_err());
    let pc = window.start;
    let insn = decode_aarch64(&window.code[..4], pc).unwrap();
    let effects = Aarch64Semantics.effects(&state, &insn).unwrap();
    let mut trace = PrefixTrace::begin(window, &state).unwrap();
    assert!(trace.before(pc + 4, &Formula::Bool(true), &state, &effects).is_err());
    let mut trace = PrefixTrace::begin(window, &state).unwrap();
    assert!(trace.before(pc, &Formula::Bool(false), &state, &effects).is_err());
    let mut trace = PrefixTrace::begin(window, &state).unwrap();
    assert!(trace.before(pc, &Formula::Bool(true), &state, &[]).is_err());
    let mut trace = PrefixTrace::begin(window, &state).unwrap();
    trace.before(pc, &Formula::Bool(true), &state, &effects).unwrap();
    let mut changed = state.clone();
    changed.sp = Formula::BitVec { value: 0, width: 64 };
    assert!(trace.after(&changed).is_err());
    let mut trace = PrefixTrace::begin(window, &state).unwrap();
    trace.before(pc, &Formula::Bool(true), &state, &effects).unwrap();
    trace.after(&state).unwrap();
    assert!(trace.after(&state).is_err());
    for word in [0x90000000u32, 0x10000000, 0xd10043ff, 0x3940041f, 0xf10003ff] {
        let mut altered = window.clone();
        let mut bytes = word.to_le_bytes().to_vec();
        bytes.extend_from_slice(&altered.code);
        altered.code = bytes;
        altered.end += 4;
        altered.sites[0].offset += 4;
        let mut trace = PrefixTrace::begin(&altered, &state).unwrap();
        let insn = decode_aarch64(&altered.code[..4], pc).unwrap();
        let effects = Aarch64Semantics.effects(&state, &insn).unwrap();
        assert!(trace.before(pc, &Formula::Bool(true), &state, &effects).is_err());
    }
}

#[test]
fn initial_malformed_logical_arguments_and_copy_types_are_not_call_authority() {
    let f = sample();
    for fake_copy in [false, true] {
        let mut module = (*f.m_cg).clone();
        let index = module.functions.iter().position(|f| f.name == "tail_store").unwrap();
        let mut sig = module.func_types[module.functions[index].ty.as_usize()].clone();
        sig.params[0] = Ty::U64;
        let id = trust_ir::value::FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(sig);
        module.functions[index].ty = id;
        let function = &mut module.functions[index];
        function.blocks[0].params[0].1 = Ty::U64;
        if fake_copy {
            let operand = function.blocks[0].params[0].0;
            let result = trust_ir::value::ValueId::new(300);
            let mut copy = function.blocks[0].body[0].clone();
            copy.inst = Inst::Copy { ty: Ty::Ptr, operand };
            copy.results = vec![result];
            if let Inst::Call { args, .. } = &mut function.blocks[0].body[0].inst {
                args[0] = result;
            }
            function.blocks[0].body.insert(0, copy);
        }
        let malformed = Fixture::with_object(module, f.object.clone(), DARWIN);
        let prepared = prepare_leaf_calls(&input(&malformed)).unwrap();
        assert!(
            prepared.providers.contains_key("memory_store"),
            "valid independent leaf provider must exist"
        );
        let error = without_production(|| prepared.specialize("tail_store")).err().unwrap();
        assert!(error.contains("logical type"), "fake_copy={fake_copy}: {error}");
    }
}
#[test]
fn variadic_metadata_debt_is_refused_without_promoting_any_caller() {
    let f = sample();
    let mut module = (*f.m_cg).clone();
    let index = module.functions.iter().position(|f| f.name == "tail_store").unwrap();
    let mut sig = module.func_types[module.functions[index].ty.as_usize()].clone();
    sig.is_vararg = true;
    let id = trust_ir::value::FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(sig);
    module.functions[index].ty = id;
    let malformed = Fixture::with_object(module, f.object.clone(), DARWIN);
    let prepared = prepare_leaf_calls(&input(&malformed)).unwrap();
    assert!(without_production(|| prepared.specialize("tail_store")).is_err());
    assert!(prepared.report().ships(EmitPolicy::StrictProvenOnly).is_err());
}

fn actual_native_alias_control(fixture: &Fixture) {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let driver = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t tail_copy(unsigned char *, const unsigned char *);
int main(void) {for(unsigned int i=0;i<256;i++){unsigned char value=(unsigned char)i;if(tail_copy(&value,&value)!=0||value!=i)return 9;}puts("alias256 ok");return 0;}
"#;
    std::fs::write(root.join("driver.c"), driver).unwrap();
    std::fs::write(root.join("subject.o"), &fixture.object).unwrap();
    let compile = std::process::Command::new("/usr/bin/clang")
        .arg(root.join("driver.c"))
        .arg(root.join("subject.o"))
        .arg("-o")
        .arg(root.join("native-alias"))
        .output()
        .unwrap();
    std::fs::write(root.join("compile.stdout"), &compile.stdout).unwrap();
    std::fs::write(root.join("compile.stderr"), &compile.stderr).unwrap();
    assert!(compile.status.success(), "{}", String::from_utf8_lossy(&compile.stderr));
    let native = std::process::Command::new(root.join("native-alias")).output().unwrap();
    std::fs::write(root.join("native.stdout"), &native.stdout).unwrap();
    std::fs::write(root.join("native.stderr"), &native.stderr).unwrap();
    assert!(native.status.success(), "alias control: {:?}", native.status);
    assert_eq!(native.stdout, b"alias256 ok\n");
    if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("native-alias");
        std::fs::create_dir_all(&output).unwrap();
        for entry in std::fs::read_dir(root).unwrap() {
            let entry = entry.unwrap();
            std::fs::copy(entry.path(), output.join(entry.file_name())).unwrap();
        }
    }
}

#[test]
fn duplicate_and_forward_ssa_definitions_cannot_supply_site_authority() {
    let f = sample();
    for forward in [false, true] {
        let mut module = (*f.m_cg).clone();
        let index = module.functions.iter().position(|f| f.name == "tail_store").unwrap();
        let function = &mut module.functions[index];
        let operand = function.blocks[0].params[0].0;
        let template = function.blocks[0].body[0].clone();
        let mut first = template.clone();
        first.inst = Inst::Copy { ty: Ty::Ptr, operand };
        first.results = vec![operand];
        if forward {
            let intermediate = trust_ir::value::ValueId::new(301);
            let result = trust_ir::value::ValueId::new(302);
            first.inst = Inst::Copy { ty: Ty::Ptr, operand: intermediate };
            first.results = vec![result];
            let mut second = template;
            second.inst = Inst::Copy { ty: Ty::Ptr, operand };
            second.results = vec![intermediate];
            if let Inst::Call { args, .. } = &mut function.blocks[0].body[0].inst {
                args[0] = result;
            }
            function.blocks[0].body.insert(0, second);
        }
        function.blocks[0].body.insert(0, first);
        let malformed = Fixture::with_object(module, f.object.clone(), DARWIN);
        let prepared = prepare_leaf_calls(&input(&malformed)).unwrap();
        let result = without_production(|| prepared.specialize("tail_store"));
        if let Ok(instance) = &result {
            if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
                let output = std::path::PathBuf::from(output);
                std::fs::create_dir_all(&output).unwrap();
                std::fs::write(
                    output.join("unexpected-duplicate-ssa-instance.json"),
                    instance.to_untrusted_json().unwrap(),
                )
                .unwrap();
                std::fs::write(
                    output.join("duplicate-ssa-module.json"),
                    serde_json::to_vec(malformed.m_cg.as_ref()).unwrap(),
                )
                .unwrap();
                std::fs::write(output.join("duplicate-ssa-object.o"), &malformed.object).unwrap();
                std::fs::write(
                    output.join("duplicate-ssa-report.json"),
                    prepared.report().to_json(),
                )
                .unwrap();
            }
        }
        assert!(
            result.is_err(),
            "invalid SSA prefix must not construct a checked site instance; forward={forward}"
        );
    }
}

#[test]
fn fresh_provider_preparation_cannot_authenticate_nonzero_relocated_tail_operand() {
    let f = sample();
    let pc =
        function_words(&f.object, "tail_store").into_iter().find(|(_, word)| is_b(*word)).unwrap();
    let (record, kind, symbol) = reloc_at(&f.object, pc.0);
    assert_eq!(kind, 2);
    assert_eq!(pc.1 & 0x03ffffff, 0);
    let changed = f.patched(|bytes| patch_word(bytes, pc.0, (pc.1 & 0xfc000000) | 1));
    assert_eq!(reloc_at(&changed.object, pc.0), (record, kind, symbol));
    let prepared = prepare_leaf_calls(&input(&changed)).unwrap();
    assert_eq!(prepared.report().certificates.len(), 5);
    assert!(
        prepared.providers.contains_key("memory_store"),
        "fresh actual provider still verifies under the new object hash"
    );
    let instance = without_production(|| prepared.specialize("tail_store"));
    let baseline = std::env::var_os("TRUST_BR26_BASELINE_OBSERVE").is_some();
    if let Some(output) = std::env::var_os("TRUST_BR26_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("fresh-memory-provider");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(output.join("subject.o"), &changed.object).unwrap();
        std::fs::write(output.join("certificates.json"), prepared.report().to_json()).unwrap();
        if let Ok(instance) = &instance {
            std::fs::write(
                output.join("unexpected-instance.json"),
                instance.to_untrusted_json().unwrap(),
            )
            .unwrap();
        }
    }
    if baseline {
        assert!(instance.is_ok(), "old fresh-hash admission observation: {:?}", instance.err());
    } else {
        assert!(
            instance.is_err(),
            "noncanonical relocation operand must not create a site instance"
        );
        let row = prepared.report().certificate("tail_store").unwrap();
        assert!(!row.is_kernel_proved());
        assert!(row.obligations.o1_binding.detail.contains("BRANCH26"));
    }
    assert!(prepared.report().ships(EmitPolicy::StrictProvenOnly).is_err());
}

fn composition_layout(f: &Fixture) -> ObjectLayout {
    let parsed = CompiledObject::parse(&f.object).unwrap();
    let expect = ObjectExpectations::from_module(&f.m_cg, parsed.format, f.model).unwrap();
    ObjectLayout::bind(parsed, &expect).unwrap()
}
fn four_tail_fixture() -> &'static Fixture {
    static FOUR: std::sync::OnceLock<Fixture> = std::sync::OnceLock::new();
    FOUR.get_or_init(|| {
        let mut module = (*sample().m_cg).clone();
        assert_eq!(module.functions.pop().unwrap().name, "tail_alias");
        let object = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O2,
                parallel: false,
                emit_proofs: false,
                never_inline: ["memory_store", "memory_copy"]
                    .into_iter()
                    .map(str::to_owned)
                    .collect(),
                ..Default::default()
            },
            TargetSpec::parse(DARWIN).unwrap(),
        )
        .with_codegen_license(fixture_license())
        .compile(&module)
        .unwrap()
        .object_code;
        Fixture::with_object(module, object, DARWIN)
    })
}
fn four_tail_report() -> &'static CerReport {
    static REPORT: std::sync::OnceLock<CerReport> = std::sync::OnceLock::new();
    REPORT.get_or_init(|| four_tail_fixture().report())
}

#[test]
fn complete_actual_memory_tail_goal_reuses_retained_proof_without_production_or_solver() {
    let f = sample();
    let p = prepared();
    let layout = composition_layout(f);
    for (caller, callee) in [("tail_store", "memory_store"), ("tail_copy", "memory_copy")] {
        let closed = without_production(|| {
            super::transition::produce(&input(f), &layout, caller, &p.providers[callee])
        })
        .unwrap_or_else(|error| panic!("complete {caller}: {error}"));
        let checked = closed.checked_original().expect("retained full caller original proof");
        let original = checked.original_equations();
        assert_eq!(original.len(), p.providers[callee].checked.original_equations().len() + 2);
        let query = format!("CER_LEAF_QUERY@{}:{}", layout.object.sha256_hex(), caller);
        assert_eq!(checked.variable_sorts().get(&query), Some(&Sort::BitVec(64)));
        assert!(original.iter().any(|(a,c)|matches!((a,c),
            (Formula::Select(_,q),Formula::Select(_,r)) if **q==Formula::Var(query.clone(),Sort::BitVec(64)) && q==r)));
        assert!(checked.variable_sorts().contains_key("X0"));
        assert!(checked.variable_sorts().contains_key("X1"));
        // Distinct symbolic inputs range over ALL alias valuations. No
        // equality/inequality/domain premise is inserted to legalize the copy.
        assert!(!original.iter().any(|(a, c)| *a == Formula::Var("X0".into(), Sort::BitVec(64))
            && *c == Formula::Var("X1".into(), Sort::BitVec(64))));
        if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
            let output = std::path::PathBuf::from(output).join("complete-tail-theorems");
            std::fs::create_dir_all(&output).unwrap();
            std::fs::write(
                output.join(format!("{caller}.packet.json")),
                serde_json::to_vec_pretty(checked.packet()).unwrap(),
            )
            .unwrap();
            std::fs::write(
                output.join(format!("{caller}.original.json")),
                serde_json::to_vec_pretty(original).unwrap(),
            )
            .unwrap();
        }
    }
    assert!(
        without_production(|| super::transition::produce(
            &input(f),
            &layout,
            "tail_alias",
            &p.providers["memory_copy"]
        ))
        .is_err()
    );
}

#[test]
fn ordinary_four_function_tail_object_retains_complete_original_caller_proofs_and_replays() {
    let f = four_tail_fixture();
    let report = four_tail_report();
    assert_eq!(report.certificates.len(), 4, "{}", explain(report));
    for symbol in ["memory_store", "memory_copy", "tail_store", "tail_copy"] {
        let cert = report.certificate(symbol).unwrap();
        assert!(cert.is_kernel_proved(), "{symbol}: {}", explain(report));
        assert!(cert.original_proof.is_some(), "every actual function retains a complete packet");
    }
    for symbol in ["tail_store", "tail_copy"] {
        let cert = report.certificate(symbol).unwrap();
        assert_eq!(cert.call_sites.len(), 1);
        assert_eq!(cert.call_sites[0].kind, CallSiteKind::Tail);
        assert!(cert.obligations.o5_frame.detail.contains("complete zero-frame"));
    }
    assert!(report.ships(EmitPolicy::StrictProvenOnly).is_ok(), "{}", explain(report));
    let bytes = report.to_json().into_bytes();
    let replay = without_production(|| replay_original_certificates(&input(f), &bytes)).unwrap();
    assert_eq!(replay.rows.len(), 4);
    assert!(replay.all_replayed(), "{}", serde_json::to_string_pretty(&replay).unwrap());
    if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("four-function-composition");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(output.join("subject.o"), &f.object).unwrap();
        std::fs::write(
            output.join("module.json"),
            serde_json::to_vec_pretty(f.m_cg.as_ref()).unwrap(),
        )
        .unwrap();
        std::fs::write(output.join("certificates.json"), &bytes).unwrap();
        std::fs::write(output.join("replay.json"), serde_json::to_vec_pretty(&replay).unwrap())
            .unwrap();
    }
    actual_native_complete_tail_control(f);
    // Keep the separate five-function unsupported MOV/OR wrapper visible.
    let full = sample().report();
    assert_eq!(full.certificates.len(), 5);
    assert_eq!(full.certificate("tail_alias").unwrap().grade, "Unknown");
    assert!(full.ships(EmitPolicy::StrictProvenOnly).is_err());
}

#[test]
fn retained_complete_tail_replay_rejects_missing_forged_or_rebound_caller_evidence() {
    let f = four_tail_fixture();
    let report = four_tail_report();
    let sidecar: serde_json::Value = serde_json::from_str(&report.to_json()).unwrap();
    let index = sidecar["certificates"]
        .as_array()
        .unwrap()
        .iter()
        .position(|row| row["symbol"] == "tail_store")
        .unwrap();
    let mut mutants = Vec::new();
    let mut m = sidecar.clone();
    m["certificates"][index]["original_proof"] = serde_json::Value::Null;
    mutants.push(m);
    let mut m = sidecar.clone();
    m["certificates"][index]["text_sha256"] = serde_json::json!("00".repeat(32));
    mutants.push(m);
    let mut m = sidecar.clone();
    m["certificates"][index]["placement_sha256"]["memory_store"] =
        serde_json::json!("00".repeat(32));
    mutants.push(m);
    let mut m = sidecar.clone();
    m["certificates"][index]["original_proof"]["packet"]["original"].as_array_mut().unwrap().pop();
    mutants.push(m);
    let mut m = sidecar.clone();
    m["certificates"][index]["original_proof"]["packet"]["proof_sha256"] =
        serde_json::json!("00".repeat(32));
    mutants.push(m);
    let mut m = sidecar.clone();
    m["certificates"][index]["original_proof"]["packet"]["environment_sha256"] =
        serde_json::json!("00".repeat(32));
    mutants.push(m);
    for (n, mutant) in mutants.iter().enumerate() {
        let bytes = serde_json::to_vec(mutant).unwrap();
        let result = without_production(|| replay_original_certificates(&input(f), &bytes));
        if let Ok(replay) = result {
            assert_eq!(replay.rows.len(), 4);
            assert!(
                !replay.rows.iter().find(|row| row.symbol == "tail_store").unwrap().replayed,
                "mutant {n}"
            );
        }
    }
    // Whole-object/P/source/relocation binding is independently recomputed.
    let bytes = report.to_json().into_bytes();
    let mut object = f.object.clone();
    let last = object.len() - 1;
    object[last] ^= 1;
    let mut wrong = input(f);
    wrong.object = &object;
    assert!(without_production(|| replay_original_certificates(&wrong, &bytes)).is_err());
    let mut placements = f.placements.clone();
    placements.get_mut("memory_store").unwrap().params[0] =
        ParamPlace::Scalar(ScalarPlace::gpr(1, 64));
    let mut wrong = input(f);
    wrong.placements = &placements;
    let replay = without_production(|| replay_original_certificates(&wrong, &bytes)).unwrap();
    assert!(!replay.all_replayed());
}

#[test]
fn fresh_memory_or_source_prefix_mutations_cannot_acquire_complete_tail_theorems() {
    let f = sample();
    let store = function_words(&f.object, "memory_store")
        .into_iter()
        .find(|(_, word)| word & 0xffc00000 == 0x39000000)
        .unwrap();
    for word in [0xd503201fu32, (store.1 & !0x1f) | 31] {
        let mut object = f.object.clone();
        patch_word(&mut object, store.0, word);
        let changed = Fixture::with_object((*f.m_cg).clone(), object, DARWIN);
        let p = prepare_leaf_calls(&input(&changed)).unwrap();
        assert!(
            !p.providers.contains_key("memory_store"),
            "changed actual memory leaf cannot supply checked source equality"
        );
        let report = changed.report();
        assert_eq!(report.certificates.len(), 5);
        assert!(!report.certificate("tail_store").unwrap().is_kernel_proved());
        assert!(report.certificate("tail_store").unwrap().original_proof.is_none());
    }
    let mut module = (*f.m_cg).clone();
    let caller =
        module.functions.iter_mut().find(|function| function.name == "tail_store").unwrap();
    let mut extra = caller.blocks[0].body[0].clone();
    extra.results.clear();
    extra.inst = Inst::Store {
        ty: Ty::U64,
        ptr: caller.blocks[0].params[0].0,
        value: caller.blocks[0].params[1].0,
        volatile: false,
        align: Some(1),
    };
    caller.blocks[0].body.insert(0, extra);
    let changed = Fixture::with_object(module, f.object.clone(), DARWIN);
    let p = prepare_leaf_calls(&input(&changed)).unwrap();
    assert!(p.providers.contains_key("memory_store"));
    let layout = composition_layout(&changed);
    assert!(
        without_production(|| super::transition::produce(
            &input(&changed),
            &layout,
            "tail_store",
            &p.providers["memory_store"]
        ))
        .is_err()
    );
    let report = changed.report();
    assert_eq!(report.certificates.len(), 5);
    assert_eq!(report.certificate("tail_store").unwrap().grade, "Unknown");
    assert!(report.certificate("tail_store").unwrap().original_proof.is_none());
    let unoptimized = fixture(OptLevel::O0);
    let report = unoptimized.report();
    assert_eq!(report.certificates.len(), 5);
    assert_eq!(report.certificate("tail_store").unwrap().grade, "Unknown");
    assert!(report.certificate("tail_store").unwrap().original_proof.is_none());
}

fn actual_native_complete_tail_control(fixture: &Fixture) {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    let driver = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t tail_store(unsigned char*,uint64_t);
extern uint64_t tail_copy(unsigned char*,const unsigned char*);
int main(void){for(unsigned i=0;i<256;i++){unsigned char a[4]={0xa6,0x55,0x3c,0xe1};
if(tail_store(a+1,i)!=0||a[0]!=0xa6||a[1]!=i||a[2]!=0x3c||a[3]!=0xe1)return 1;
if(tail_copy(a,a+1)!=0||a[0]!=i||a[1]!=i||a[2]!=0x3c||a[3]!=0xe1)return 2;
if(tail_copy(a+1,a+1)!=0||a[0]!=i||a[1]!=i||a[2]!=0x3c||a[3]!=0xe1)return 3;
}puts("complete store/copy/alias256 ok");return 0;}
"#;
    std::fs::write(root.join("driver.c"), driver).unwrap();
    std::fs::write(root.join("subject.o"), &fixture.object).unwrap();
    for opt in ["0", "3"] {
        let exe = root.join(format!("native-O{opt}"));
        let linked = std::process::Command::new("/usr/bin/clang")
            .arg(format!("-O{opt}"))
            .arg(root.join("driver.c"))
            .arg(root.join("subject.o"))
            .arg("-o")
            .arg(&exe)
            .output()
            .unwrap();
        std::fs::write(root.join(format!("link-O{opt}.stdout")), &linked.stdout).unwrap();
        std::fs::write(root.join(format!("link-O{opt}.stderr")), &linked.stderr).unwrap();
        assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
        let native = std::process::Command::new(exe).output().unwrap();
        std::fs::write(root.join(format!("native-O{opt}.stdout")), &native.stdout).unwrap();
        std::fs::write(root.join(format!("native-O{opt}.stderr")), &native.stderr).unwrap();
        assert!(native.status.success(), "actual native O{opt}: {:?}", native.status);
        assert_eq!(native.stdout, b"complete store/copy/alias256 ok\n");
    }
    if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("complete-native");
        std::fs::create_dir_all(&output).unwrap();
        for entry in std::fs::read_dir(root).unwrap() {
            let entry = entry.unwrap();
            std::fs::copy(entry.path(), output.join(entry.file_name())).unwrap();
        }
    }
}

#[test]
fn fresh_duplicate_parameter_slots_cannot_narrow_the_memory_caller_alias_domain() {
    let f = sample();
    let load = function_words(&f.object, "memory_copy")
        .into_iter()
        .find(|(_, word)| word & 0xffc00000 == 0x39400000 && (word >> 5) & 31 == 1)
        .unwrap();
    let mut object = f.object.clone();
    patch_word(&mut object, load.0, load.1 & !(31 << 5));
    let mut changed = Fixture::with_object((*f.m_cg).clone(), object, DARWIN);
    for symbol in ["memory_copy", "tail_copy"] {
        changed.placements.get_mut(symbol).unwrap().params[1] =
            ParamPlace::Scalar(ScalarPlace::gpr(0, 64));
        assert!(!scalar64(&changed.placements[symbol]));
    }
    let p = prepare_leaf_calls(&input(&changed)).unwrap();
    let layout = composition_layout(&changed);
    let provider = p.providers.get("memory_copy").expect(
        "fresh independently checked leaf provider must reach this specific caller admission guard",
    );
    assert!(
        without_production(|| super::transition::produce(
            &input(&changed),
            &layout,
            "tail_copy",
            provider
        ))
        .is_err()
    );

    let report = changed.report();
    assert_eq!(report.certificates.len(), 5);
    assert!(!report.certificate("tail_copy").unwrap().is_kernel_proved());
    assert!(report.certificate("tail_copy").unwrap().original_proof.is_none());
    if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("duplicate-P-alias-domain");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(output.join("subject.o"), &changed.object).unwrap();
        std::fs::write(
            output.join("placements.json"),
            serde_json::to_vec_pretty(&changed.placements).unwrap(),
        )
        .unwrap();
        std::fs::write(output.join("certificates.json"), report.to_json()).unwrap();
        std::fs::write(output.join("observation.json"),serde_json::to_vec_pretty(&serde_json::json!({"fresh_alias_only_provider_present":p.providers.contains_key("memory_copy"),"caller_admitted":false,"note":"duplicate physical slots are invalid P; independent pointer values may still alias"})).unwrap()).unwrap();
    }
}

#[test]
fn write_only_source_cannot_cover_an_extra_actual_tail_callee_read() {
    let f = sample();
    let words = function_words(&f.object, "memory_store");
    assert_eq!(words.len(), 4, "actual controlled fixture extent");
    assert_eq!(words[1].1 & 0xffc00000, 0x39000000);
    let mut module = (*f.m_cg).clone();
    let store =
        module.functions.iter_mut().find(|function| function.name == "memory_store").unwrap();
    store.blocks[0].body[0].inst = Inst::Const { ty: Ty::U8, value: Constant::Int(0) };
    let mut object = f.object.clone();
    patch_word(&mut object, words[0].0, 0x3940001f); // actual dead LDRB WZR,[X0]
    patch_word(&mut object, words[1].0, (words[1].1 & !31) | 31); // STRB WZR,[X0]
    let changed = Fixture::with_object(module, object, DARWIN);
    let p = prepare_leaf_calls(&input(&changed)).unwrap();
    let layout = composition_layout(&changed);
    let provider = p.providers.get("memory_store").expect(
        "fresh independently checked leaf provider must reach this specific caller admission guard",
    );
    let error = without_production(|| {
        super::transition::produce(&input(&changed), &layout, "tail_store", provider)
    })
    .err()
    .unwrap();
    assert!(error.contains("source coverage"), "{error}");

    let report = changed.report();
    assert_eq!(report.certificates.len(), 5);
    assert_eq!(report.certificate("tail_store").unwrap().grade, "Unknown");
    assert!(report.certificate("tail_store").unwrap().original_proof.is_none());
    if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("read-from-write-refusal");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(output.join("subject.o"), &changed.object).unwrap();
        std::fs::write(
            output.join("module.json"),
            serde_json::to_vec_pretty(changed.m_cg.as_ref()).unwrap(),
        )
        .unwrap();
        std::fs::write(output.join("certificates.json"), report.to_json()).unwrap();
        std::fs::write(output.join("observation.json"),serde_json::to_vec_pretty(&serde_json::json!({"fresh_old_leaf_provider_present":p.providers.contains_key("memory_store"),"complete_caller_admitted":false})).unwrap()).unwrap();
    }
}

#[test]
fn fresh_unsupported_caller_convention_cannot_borrow_a_supported_leaf_theorem() {
    let f = sample();
    let mut module = (*f.m_cg).clone();
    module
        .functions
        .iter_mut()
        .find(|function| function.name == "tail_store")
        .unwrap()
        .calling_conv = CallingConv::CUnwind;
    let changed = Fixture::with_object(module, f.object.clone(), DARWIN);
    let p = prepare_leaf_calls(&input(&changed)).unwrap();
    let layout = composition_layout(&changed);
    let provider = p.providers.get("memory_store").expect(
        "fresh independently checked leaf provider must reach this specific caller admission guard",
    );
    assert!(
        without_production(|| super::transition::produce(
            &input(&changed),
            &layout,
            "tail_store",
            provider
        ))
        .is_err()
    );

    let report = changed.report();
    assert_eq!(report.certificates.len(), 5);
    assert_eq!(report.certificate("tail_store").unwrap().grade, "Unknown");
    assert!(report.certificate("tail_store").unwrap().original_proof.is_none());
}

#[test]
fn complete_tail_replay_rejects_a_valid_kernel_proof_of_a_narrowed_query() {
    let f = four_tail_fixture();
    let report = four_tail_report();
    let caller = report.certificate("tail_store").unwrap();
    let original = caller.original_proof.as_ref().unwrap().original_equations();
    let query = format!("CER_LEAF_QUERY@{}:{}", report.object_sha256, "tail_store");
    let weakened: Vec<_> = original
        .iter()
        .map(|(a, c)| {
            let mut narrow = |term: Formula| match term {
                Formula::Var(ref name, _) if name == &query => {
                    Formula::BitVec { value: 0, width: 64 }
                }
                other => other,
            };
            (a.clone().map(&mut narrow), c.clone().map(&mut narrow))
        })
        .collect();
    assert_ne!(weakened, original);
    // Build a REAL valid proof of the deliberately weaker statement outside
    // replay. Its packet hashes/context/environment are valid and its subject
    // is the SAME actual object/source/P; only its original theorem is weaker.
    let checked = crate::verify_output_instantiate::try_original_conjunction_discharge(&weakened)
        .expect("actual kernel proof of exit memory at constant address zero");
    let weak = crate::original_conjunction_certificate::OriginalConjunctionCertificate::bind(
        &checked,
        &input(f),
        caller,
    )
    .unwrap();
    weak.require_subject(&input(f), caller).unwrap();
    let mut sidecar: serde_json::Value = serde_json::from_str(&report.to_json()).unwrap();
    let row = sidecar["certificates"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|row| row["symbol"] == "tail_store")
        .unwrap();
    row["original_proof"] = serde_json::to_value(&weak).unwrap();
    row["grade"] = serde_json::json!("[PROVED]");
    let bytes = serde_json::to_vec(&sidecar).unwrap();
    let replay = without_production(|| replay_original_certificates(&input(f), &bytes)).unwrap();
    assert_eq!(replay.rows.len(), 4);
    assert!(!replay.rows.iter().find(|row| row.symbol == "tail_store").unwrap().replayed);
    let refusal = &replay.rows.iter().find(|row| row.symbol == "tail_store").unwrap().detail;
    assert!(refusal.contains("independently expected original equations mismatch"), "{refusal}");
    assert!(!replay.all_replayed());
    if let Some(output) = std::env::var_os("TRUST_M5_INSTANCE_OUTPUT_DIR") {
        let output = std::path::PathBuf::from(output).join("valid-weaker-query-proof");
        std::fs::create_dir_all(&output).unwrap();
        std::fs::write(
            output.join("weak-original.json"),
            serde_json::to_vec_pretty(&weakened).unwrap(),
        )
        .unwrap();
        std::fs::write(
            output.join("valid-weak-certificate.json"),
            serde_json::to_vec_pretty(&weak).unwrap(),
        )
        .unwrap();
        std::fs::write(
            output.join("replay-refusal.json"),
            serde_json::to_vec_pretty(&replay).unwrap(),
        )
        .unwrap();
    }
}
