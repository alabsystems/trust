// trust-wasm-bridge/binary.rs - the real binary-.wasm front door
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The binary-`.wasm` lowering front door for already-closed trust-ir modules,
//! distinct from the fail-closed WAT-text helpers in `lib.rs`.
//!
//! This is not a rustc link step: it does not consume dependency objects,
//! statics, native libraries, exported-symbol policy, or linker arguments.
//! Consequently `rustc_codegen_trust_cg` does not use it to link Rust crates;
//! linked `wasm32` output remains fail-closed until relocatable Wasm objects and
//! rustc's normal linker boundary are wired.
//!
//! ```text
//! VerifiableFunction(s)
//!   → trust_ir_bridge::lower_to_trust_ir_functions   (VF → trust-ir Module)
//!   → trust_cg_codegen::wasm::compile_module          (trust-ir → .wasm)
//!   → Vec<u8>  (a binary WebAssembly module)
//! ```
//!
//! For closed inputs this realizes the `trust-types → trust-ir → trust-cg →
//! .wasm` lowering contract. It does not by itself establish that an arbitrary
//! Rust crate was faithfully closed into those inputs.

use std::fmt;

use trust_cg_codegen::CodegenLicensePolicy;
use trust_cg_codegen::wasm::{self, WasmLowerError};
use trust_ir::Module as TrustIrModule;
use trust_ir_bridge::lower_to_trust_ir_functions;
use trust_types::VerifiableFunction;

/// Failure compiling to a binary wasm module through the front door.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmCompileError {
    /// `VerifiableFunction` → trust-ir lowering failed (trust-ir-bridge).
    /// Carries the bridge error's rendered message.
    TrustIrLowering(String),
    /// trust-ir → wasm lowering failed (trust-cg backend).
    WasmLowering(WasmLowerError),
}

impl fmt::Display for WasmCompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WasmCompileError::TrustIrLowering(m) => {
                write!(f, "VerifiableFunction → trust-ir lowering failed: {m}")
            }
            WasmCompileError::WasmLowering(e) => write!(f, "trust-ir → wasm lowering failed: {e}"),
        }
    }
}

impl std::error::Error for WasmCompileError {}

/// Compile a trust-ir module to a binary `.wasm` module via the trust-cg wasm
/// backend.
pub fn compile_trust_ir_module_to_wasm(
    module: &TrustIrModule,
) -> Result<Vec<u8>, WasmCompileError> {
    wasm::compile_module(module).map_err(WasmCompileError::WasmLowering)
}

/// [`compile_trust_ir_module_to_wasm`] under the caller's codegen-license
/// policy, mirroring the wasm lane's `compile_module_with_license`. The
/// default front door above refuses a claim-less body (trust-ir v41
/// `body_gate`); a caller compiling hand-built or otherwise unlicensed
/// modules states its policy here instead of the bridge deciding for it.
pub fn compile_trust_ir_module_to_wasm_with_license(
    module: &TrustIrModule,
    license: &CodegenLicensePolicy,
) -> Result<Vec<u8>, WasmCompileError> {
    wasm::compile_module_with_license(module, license).map_err(WasmCompileError::WasmLowering)
}

/// Compile trust-types `VerifiableFunction`s to a binary `.wasm` module through
/// the production lowering path (VerifiableFunction → trust-ir → wasm).
///
/// This function performs lowering and returns the emitted bytes; it does not
/// establish a proof over those exact bytes. Callers that require proof-grade
/// output must separately bind and check the emitted artifact. `module_name`
/// names the emitted trust-ir module. Each function is exported under its name.
pub fn compile_functions_to_wasm(
    module_name: &str,
    functions: &[VerifiableFunction],
) -> Result<Vec<u8>, WasmCompileError> {
    let module = lower_to_trust_ir_functions(module_name, functions)
        .map_err(|e| WasmCompileError::TrustIrLowering(e.to_string()))?;
    compile_trust_ir_module_to_wasm(&module)
}

#[cfg(test)]
mod tests {
    use clean_compiler::BoxingConfig;
    use clean_compiler::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use clean_compiler::pass_manager::{PipelineConfig, compile_lcnf_to_trust_ir_with_report};
    use clean_kernel::env::{Declaration, Environment};
    use clean_kernel::{BinderInfo, Expr, Name};
    use trust_ir::{BinOp, Ty};
    use trust_ir_build::ModuleBuilder;

    use super::*;

    /// A trust-ir module with `add(a, b) = a + b` over i32, pinned to the wasm32
    /// target shape. The stamp is a TRUE claim here: the module carries no
    /// pointer-width-dependent content (two i32 params, one i32 add), so nothing in
    /// it was laid out against the 8-byte target-free default the wasm lane refuses.
    fn add_module() -> TrustIrModule {
        let mut mb = ModuleBuilder::new_with_target_info("m", wasm::wasm32_target_info());
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("add", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let r = fb.binop(BinOp::Add, Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// The index of the module's one function with a body, the certified
    /// `identity`. `ExternCalls` declares the Clean runtime ABI
    /// (`clean_alloc_ctor`, `clean_apply_N`, …) as bodyless
    /// `Linkage::External` imports AHEAD of the user functions
    /// (clean-compiler `RuntimeAbi::declare`), so `functions[0]` is an import
    /// and the function count is the ABI's size plus one. An import leaves its
    /// symbol to the link and has no body for a codegen license to cover. "No
    /// unlicensed helper bodies" is therefore: exactly one function has a body,
    /// it is `identity`, and every other function is a bodyless external
    /// import (WASM-FRONT-DOOR-BODIES-1).
    fn the_one_body(module: &TrustIrModule) -> usize {
        let bodies: Vec<usize> = module
            .functions
            .iter()
            .enumerate()
            .filter(|(_, f)| !f.blocks.is_empty())
            .map(|(index, _)| index)
            .collect();
        let [index] = bodies.as_slice() else {
            let names: Vec<_> = bodies.iter().map(|&i| &module.functions[i].name).collect();
            panic!("exactly one body, no unlicensed helper bodies: {names:?}");
        };
        assert_eq!(module.functions[*index].name, "identity", "the one body is the certified decl");
        for import in module.functions.iter().filter(|f| f.blocks.is_empty()) {
            assert_eq!(
                import.linkage,
                trust_ir::Linkage::External,
                "{} is bodyless, so it must be an import the link resolves",
                import.name
            );
        }
        *index
    }

    /// Clean's boxing for a CLOSED module, one no other module links a
    /// closure against: no closure-ABI `_boxed` adapter is generated for a
    /// declaration nothing takes as a closure. Clean still synthesizes exactly
    /// the adapter a `PartialApply` in the module references (clean-compiler
    /// `boxing::visit::visit_vdecl_partial_apply`), so this drops no adapter
    /// the module's own code calls. The general Lean ABI
    /// (`BoxingConfig::default()`) emits every adapter module-wide for other
    /// modules' closures, and Clean licenses none of them: see
    /// `module_front_door_refuses_the_general_abi_boxed_adapter_by_name`.
    fn closed_module_boxing() -> BoxingConfig {
        BoxingConfig { generate_boxed_versions: false, ..BoxingConfig::default() }
    }

    /// Compile the authored UInt32 identity definition through the real Clean
    /// pipeline under `boxing`, with wasm32 selected before lowering and
    /// certificate minting. Returns the module with the environment and name
    /// its source certificate must bind.
    fn compile_identity(boxing: BoxingConfig) -> (TrustIrModule, Environment, Name) {
        let mut env = Environment::try_with_prelude().expect("the real kernel prelude");
        let name = Name::from_string("identity");
        let ty = Expr::const_str("UInt32");
        let value = Expr::lam(BinderInfo::Default, ty.clone(), Expr::bvar(0));
        env.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::arrow(ty.clone(), ty),
            value,
            is_reducible: true,
        })
        .expect("the kernel checks the fixture definition");
        let decl = clean_compiler::to_lcnf::constant_to_decl(&env, env.get_const(&name).unwrap())
            .expect("the checked definition lowers to LCNF")
            .expect("a computational definition");
        let config = TrustIrConfig {
            module_name: "wasm_identity".to_string(),
            target_info: Some(wasm::wasm32_target_info()),
            runtime_lowering: RuntimeLowering::ExternCalls,
            use_clean_dialect: false,
            enforce_handoff_subset: true,
            ..Default::default()
        };
        assert!(config.certify_translation && config.bind_certificates);
        let pipeline = PipelineConfig { boxing, ..PipelineConfig::default() };
        let (module, report) =
            compile_lcnf_to_trust_ir_with_report(&[decl], &env, &pipeline, &config)
                .expect("the real pipeline lowers and certifies identity");
        // The mint report counts SOURCE declarations; a generated adapter is
        // in none of its rows, so this says nothing about helper bodies.
        assert_eq!(report.certified, ["identity"]);
        assert!(report.refused.is_empty() && report.skipped.is_empty(), "{report:?}");
        (module, env, name)
    }

    /// `identity` compiled as a closed module ([`closed_module_boxing`]),
    /// whose one body is the certified declaration. The default bound
    /// certificate is independently kernel-rechecked below. This licenses the
    /// source-to-IR equation; it is not a proof of Wasm bytes.
    fn licensed_identity_module() -> TrustIrModule {
        let (module, env, name) = compile_identity(closed_module_boxing());
        let identity = &module.functions[the_one_body(&module)];
        let obligations: Vec<_> = module
            .proof_obligations
            .iter()
            .filter(|o| {
                o.function == Some(identity.id)
                    && o.kind == trust_ir::ObligationKind::TranslationValidation
            })
            .collect();
        let [obligation] = obligations.as_slice() else {
            panic!("exactly one identity translation obligation: {obligations:?}");
        };
        let binding = module
            .proof_certificates
            .iter()
            .filter(|c| c.obligation == obligation.id)
            .find_map(|c| c.evidence.clean_cic_kernel_recheck())
            .and_then(|r| r.binding.as_deref())
            .expect("the actual pipeline minted a bound kernel certificate");
        let source = binding.source.as_ref().expect("source identity");
        assert_eq!(source.decl, "identity");
        assert_eq!(
            source.closure_digest.bytes,
            env.closure_digest(&name).expect("the authored source closure")
        );
        let errors = trust_ir_build::validate_module_with_config(
            &module,
            &trust_ir_build::ValidationConfig::pinned()
                .with_bound_certificates(true)
                .with_gate_evidence(true),
        )
        .into_errors();
        assert!(errors.is_empty(), "bound kernel evidence: {errors:?}");
        assert!(
            trust_ir_build::validate_module_for_codegen(&module).is_empty(),
            "the independent consumer must re-check the minted evidence"
        );
        module
    }

    /// The wasm lane (`trust-cg` `6439338e`, in the pin since `ebea0f5fb8`) REFUSES a
    /// target-free module instead of defaulting it: target-free trust-ir is laid out
    /// with 8-byte pointers while wasm32 addresses linear memory through i32, so a
    /// silent default would mis-lay-out every frame and GEP. This front door must
    /// pass that refusal through by name, with the fix in the message — it must not
    /// stamp a target on the producer's behalf, because a bridge module's layouts
    /// came from the HOST target and a wasm32 stamp on them would be a false claim.
    #[test]
    fn module_front_door_refuses_a_target_free_module_by_name() {
        let mut module = add_module();
        module.target_info = None;
        let err = compile_trust_ir_module_to_wasm(&module)
            .expect_err("a target-free module must be refused, never defaulted to wasm32");
        let text = err.to_string();
        assert!(
            matches!(err, WasmCompileError::WasmLowering(WasmLowerError::MissingTargetInfo(_))),
            "the refusal must be the lane's own MissingTargetInfo, got {text}"
        );
        assert!(
            text.contains("target-free") && text.contains("wasm32_target_info"),
            "the refusal must name the defect AND the fix, got {text}"
        );
    }

    /// This file's fixture is hand-built and carries no codegen license
    /// (`body_gate: None`), which the wasm lane REFUSES by default
    /// (trust-ir v41). Its success-path compile states the permit
    /// explicitly through the license-taking front door, mirroring
    /// trust-cg's own hand-built fixtures; the default front door's
    /// refusal is pinned below.
    fn permit_unlicensed() -> CodegenLicensePolicy {
        CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
    }

    #[test]
    fn module_front_door_refuses_an_unlicensed_module_by_default() {
        let err = compile_trust_ir_module_to_wasm(&add_module())
            .expect_err("an unlicensed hand-built module must be refused by default");
        assert!(
            err.to_string().contains("carries no codegen license"),
            "the refusal must name the missing license, got {err}"
        );
    }

    #[test]
    fn module_front_door_emits_valid_wasm_header() {
        let bytes =
            compile_trust_ir_module_to_wasm_with_license(&add_module(), &permit_unlicensed())
                .unwrap();
        assert!(bytes.len() > 8, "module too short");
        assert_eq!(
            &bytes[..8],
            &[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00],
            "wasm magic + version"
        );
    }

    #[test]
    fn module_front_door_refuses_an_unlicensed_body() {
        let err = compile_trust_ir_module_to_wasm(&add_module())
            .expect_err("the producer must supply a codegen license");
        assert!(
            matches!(err, WasmCompileError::WasmLowering(WasmLowerError::CodegenLicense(_))),
            "{err}"
        );
        assert!(err.to_string().contains("add"), "{err}");
    }

    /// The general Lean ABI also emits `identity`'s closure-ABI adapter
    /// `l_identity___boxed` (unbox, call, box) and marks it AFFIRMATIVELY
    /// `Ungated`. Clean licenses no such adapter: its marshaling rests on the
    /// runtime's box round trip, the target ABI and pointer-fragment facts no
    /// certificate covers, and a callee's license is never inherited onto it
    /// (clean `docs/validation/2026-11-08-source-equations-and-boxed-entries.md`).
    /// The front door must refuse that module by the adapter's name under
    /// every license, and the adapter must be the only body the closed module
    /// lacks, the certified one being the same in both
    /// (WASM-FRONT-DOOR-BODIES-1).
    #[test]
    fn module_front_door_refuses_the_general_abi_boxed_adapter_by_name() {
        let (general, _, _) = compile_identity(BoxingConfig::default());
        let bodies: Vec<_> = general.functions.iter().filter(|f| !f.blocks.is_empty()).collect();
        let [identity, adapter] = bodies.as_slice() else {
            let names: Vec<_> = bodies.iter().map(|f| &f.name).collect();
            panic!("the certified source and its generated adapter: {names:?}");
        };
        assert_eq!(identity.name, "identity");
        assert_eq!(adapter.name, "l_identity___boxed");
        assert_eq!(
            adapter.body_gate,
            Some(trust_ir::BodyGate::Ungated),
            "Clean records that no gate ran on the adapter"
        );
        let closed = licensed_identity_module();
        let certified = &closed.functions[the_one_body(&closed)];
        assert_eq!(
            (&identity.blocks, &identity.body_gate),
            (&certified.blocks, &certified.body_gate),
            "generating the adapter changes nothing about the certified body"
        );
        for refusal in [
            compile_trust_ir_module_to_wasm(&general),
            compile_trust_ir_module_to_wasm_with_license(&general, &permit_unlicensed()),
        ] {
            // The license refuses `Ungated` under every policy, so the permit
            // that admits a claim-less hand-built body does not admit it.
            let err = refusal.expect_err("an ungated adapter body must not emit Wasm");
            assert!(
                matches!(
                    &err,
                    WasmCompileError::WasmLowering(WasmLowerError::CodegenLicense(why))
                        if why.contains("`l_identity___boxed` is affirmatively ungated")
                ),
                "the refusal must be the license's, naming the adapter: {err}"
            );
        }
    }

    #[test]
    fn module_front_door_refuses_missing_or_tampered_evidence() {
        let original = licensed_identity_module();
        let body = the_one_body(&original);
        // Non-vacuity: the license the default front door applies admits the
        // unmutated module, so each refusal below is its mutation's. Without
        // this, a module the license refuses anyway (an ungated helper body
        // beside the certified one) would make all three refusals vacuous.
        CodegenLicensePolicy::default()
            .enforce_module(&original)
            .expect("the minted evidence licenses the unmutated identity body");
        for mutation in 0..3 {
            let mut module = original.clone();
            match mutation {
                0 => module.proof_certificates.clear(),
                1 => module.functions[body].body_gate = None,
                2 => {
                    let mut changed = false;
                    for node in &mut module.functions[body].blocks[0].body {
                        if matches!(node.inst, trust_ir::Inst::Return { .. }) {
                            node.inst = trust_ir::Inst::Unreachable;
                            changed = true;
                        }
                    }
                    assert!(changed, "the mutation must replace the certified return");
                }
                _ => unreachable!(),
            }
            let err = compile_trust_ir_module_to_wasm(&module)
                .expect_err("missing or stale evidence must not emit Wasm");
            // trust-cg `admit_for_codegen` runs trust-ir's codegen admission,
            // which no license widens, before the license. Admission refuses a
            // Certified obligation stripped of its CleanCic certificate and a
            // gate whose recorded body digest the stale body no longer has;
            // only a removed gate reaches the license, which refuses a
            // claim-less body by default.
            let refused_by_its_gate = match (mutation, &err) {
                (0, WasmCompileError::WasmLowering(WasmLowerError::CodegenAdmission(why))) => {
                    why.contains("carries no CleanCic certificate")
                }
                (1, WasmCompileError::WasmLowering(WasmLowerError::CodegenLicense(why))) => {
                    why.contains("identity")
                }
                (2, WasmCompileError::WasmLowering(WasmLowerError::CodegenAdmission(why))) => {
                    why.contains("GateEvidence does not hold")
                }
                _ => false,
            };
            assert!(refused_by_its_gate, "mutation {mutation}: {err}");
        }
    }

    #[test]
    fn module_front_door_refuses_the_licensed_closed_module_at_the_import_policy() {
        // The end-to-end state, pinned. The license admits the closed
        // `identity` module, yet the default front door emits no Wasm: Clean's
        // module declares its runtime entry `clean_inc` with no body, and the
        // default func-import policy is Forbidden. So no Clean-produced module
        // reaches Wasm bytes through `compile_trust_ir_module_to_wasm` until
        // its runtime imports are bound (docs/OPEN_ISSUES.md
        // WASM-FRONT-DOOR-IMPORTS-1). Binding them changes this test on purpose.
        let module = licensed_identity_module();
        CodegenLicensePolicy::default()
            .enforce_module(&module)
            .expect("the minted evidence licenses the closed identity module");
        let err = compile_trust_ir_module_to_wasm(&module)
            .expect_err("an unbound runtime declaration must not emit Wasm");
        let WasmCompileError::WasmLowering(WasmLowerError::UnboundDeclaration(why)) = &err else {
            panic!("the refusal must be the import policy's, not the license's: {err}");
        };
        assert!(
            why.contains("`clean_inc`"),
            "the unbound declaration is Clean's runtime entry: {why}"
        );
    }
}
