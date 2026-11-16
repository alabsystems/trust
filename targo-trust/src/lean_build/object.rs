//! Checked standalone scalar source to a strict trust-cg object. This is thin
//! in-memory subject transport to existing gates, not a new semantic checker.
//! No runtime imports, caller ABI transformation, linker or executable authority.

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;
use std::sync::Arc;

use trust_certify::lean_source_batch::AcceptedLeanSourceContext;
use trust_cg_bridge::call_event::{FnPlacement, ProducerBody, ProducerModule};
use trust_cg_bridge::compiled_object::RelocationModel;
use trust_cg_bridge::f1_compile::{
    F1CompileConfig, F1CompileInput, F1OptLevel, F1Target, StandaloneCodegenAdmission,
    compile_and_verify_trust_ir_module_with_standalone,
};
use trust_cg_bridge::verify_output::EmitPolicy;
use trust_clean_ir_gate::CodegenRelocation;
use trust_clean_ir_gate::standalone::{admit_standalone_scalar, standalone_codegen_gate_stamp};
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{Linkage, Module, Visibility};

pub(super) const USAGE: &str = "Checked scalar object mode:\n\
    targo trust build FILE.lean --emit=object --out NEW.o [--verbose]\n\
    Every owned computational declaration must pass the existing standalone\n\
    kernel gate and unchanged strict trust-cg machine-output gate. Emit the exact\n\
    checked object for this AArch64 Darwin/Linux host; no executable is linked.\n\
    Runtime imports, unsupported siblings, ABI transformations and unproved\n\
    machine rows refuse the entire object. Stored stamps never grant admission.";

pub(super) fn requested(args: &[String]) -> bool {
    args.iter().any(|a| a == "--emit=object")
        || args.windows(2).any(|a| a[0] == "--emit" && a[1] == "object")
}

fn parse(args: &[String]) -> Result<super::Request, String> {
    let mut args = args.to_vec();
    for i in 0..args.len() {
        if args[i] == "--emit=object" {
            args[i] = "--emit=trust-ir".into();
        } else if i > 0 && args[i - 1] == "--emit" && args[i] == "object" {
            args[i] = "trust-ir".into();
        }
    }
    super::parse(&args)
}

pub(super) fn run(args: &[String]) -> ExitCode {
    if args.iter().any(|a| matches!(a.as_str(), "--help" | "-h")) {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let request = match parse(args) {
        Ok(request) => request,
        Err(error) => {
            eprintln!("error: {error}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match super::build_artifact(&request, true) {
        Ok(count) => {
            println!(
                "wrote {}: {count} standalone kernel-gated declaration(s), strict trust-cg object; no executable linked",
                request.output.display()
            );
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {}", error.render(request.verbose));
            ExitCode::FAILURE
        }
    }
}

pub(super) fn compile(
    context: &AcceptedLeanSourceContext<'_>,
    source: &Module,
    bindings: &[super::BodyBinding],
) -> Result<Vec<u8>, String> {
    let target = match (std::env::consts::ARCH, std::env::consts::OS) {
        ("aarch64", "macos") => F1Target::Aarch64AppleDarwin,
        ("aarch64", "linux") => F1Target::Aarch64UnknownLinuxGnu,
        _ => return Err("standalone strict objects require an AArch64 Darwin/Linux host; no alternate backend selected".into()),
    };
    if source.functions.is_empty() || bindings.len() != source.functions.len() {
        return Err(
            "standalone object requires a nonempty complete computational population".into()
        );
    }
    let mut tokens = Vec::new();
    for binding in bindings {
        let function = source
            .function_by_id(FuncId::new(binding.function_id))
            .ok_or("standalone binding lost its function")?;
        let signature =
            source.func_types.get(function.ty.as_usize()).ok_or("standalone signature missing")?;
        // Placeholder placement is untrusted input to the existing independent
        // kernel gate, which still reads the actual body and source declaration.
        let mut original = function.clone();
        original.id = FuncId::new(0);
        original.ty = FuncTyId::new(0);
        original.producer = None;
        let token = admit_standalone_scalar(context, &binding.declaration, signature, &original)
            .map_err(|e| e.note().to_owned())?;
        tokens.push(
            token
                .authenticate_published(
                    context,
                    &binding.declaration,
                    signature,
                    &original,
                    function,
                )
                .map_err(|e| e.note().to_owned())?,
        );
    }
    let mut codegen = source.clone();
    for function in &mut codegen.functions {
        function.linkage = Linkage::External;
        function.visibility = Visibility::Default;
        function.body_gate = Some(standalone_codegen_gate_stamp());
    }
    let relocations: Vec<_> = codegen
        .functions
        .iter()
        .map(|f| CodegenRelocation {
            function_id: f.id,
            linkage: f.linkage,
            visibility: f.visibility,
        })
        .collect();
    let mut admissions = Vec::new();
    let mut placements = BTreeMap::new();
    let mut bodies = BTreeMap::new();
    for ((binding, token), relocation) in bindings.iter().zip(&tokens).zip(&relocations) {
        let id = FuncId::new(binding.function_id);
        let function = source.function_by_id(id).ok_or("standalone source function missing")?;
        admissions.push(StandaloneCodegenAdmission::checked(
            context,
            token,
            source,
            id,
            &codegen,
            *relocation,
        )?);
        if placements
            .insert(function.name.clone(), FnPlacement::from_scalar_signature(source, function)?)
            .is_some()
            || bodies
                .insert(function.name.clone(), ProducerBody { producer: 0, func: id })
                .is_some()
        {
            return Err("standalone object repeats a link symbol".into());
        }
    }
    let producers = vec![ProducerModule::named_by_symbols(Arc::new(source.clone()))];
    let config = F1CompileConfig {
        target,
        opt_level: F1OptLevel::O0,
        relocation: RelocationModel::Static,
        force_frame_pointers: false,
        never_inline: BTreeSet::new(),
        upstream_mir_lane: false,
    };
    let input = F1CompileInput {
        m_cg: &codegen,
        producers: &producers,
        bodies: &bodies,
        placements: &placements,
        policy: EmitPolicy::StrictProvenOnly,
        config: &config,
    };
    let shipped = compile_and_verify_trust_ir_module_with_standalone(&input, &admissions)
        .map_err(|e| format!("strict standalone object refused: {e}"))?;
    // This is the actual complete gate denominator, never a full-program or
    // general foreign-ABI proof claim. No report/sidecar is silently published.
    println!(
        "object gate: {}/{} functions closed [PROVED], {} unclosed; object sha256 {}; bounded standalone scalar/kernel and existing machine/ABI model evidence",
        shipped.report.closure.closed_kernel.len(),
        shipped.report.certificates.len(),
        shipped.report.closure.unclosed.len(),
        shipped.report.object_sha256
    );
    Ok(shipped.object)
}

#[cfg(test)]
mod tests;
