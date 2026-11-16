// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Compile an actual scalar Rust source file, prove every Boolean input case against
//! its literal EvalIR semantics, and independently certify the corresponding TY model.
//! This is source qualification evidence, not authenticated project or binary authority.

use std::error::Error;
use std::path::{Path, PathBuf};
use std::time::Instant;
use std::{env, fs};

use serde::{Deserialize, Serialize};
use trust_sha2::{Digest, Sha256};
use trust_spec_temporal::literal_property::{
    LiteralPropertyCertificate, certify_literal_property, recheck_literal_property,
};
use trust_spec_temporal::literal_refinement::{
    LiteralInvocation, LiteralRefinementError, LiteralScalar, MAX_LITERAL_MODULE_BYTES,
};
use trust_spec_temporal::{
    certify_automatic_clean_scalar_model, recheck_automatic_clean_scalar_model,
};

#[path = "qualify_bool_source/reuse.rs"]
mod reuse;

#[path = "qualify_bool_source/refinement.rs"]
mod refinement;

#[path = "qualify_bool_source/identity.rs"]
mod identity;
use identity::{CompilerIdentity, compiler_identity};

#[path = "qualify_bool_source/extraction.rs"]
mod extraction;

const EXTRACTION_FLAGS: &[&str] =
    &["--edition=2024", "--crate-type=lib", "--crate-name=source_qualification", "--emit=trust-ir"];
const SOURCE_PATH_POLICY: &str = "snapshot-cwd-relative-source/v1";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Case {
    arguments: Vec<bool>,
    expected: bool,
    permitted: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Suite {
    function: String,
    fuel: u64,
    cases: Vec<Case>,
    mutation_from: String,
    mutation_to: String,
}

fn failure(message: impl Into<String>) -> Box<dyn Error> {
    std::io::Error::other(message.into()).into()
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes).as_ref().iter().map(|byte| format!("{byte:02x}")).collect()
}

fn file_sha256(path: &Path) -> Result<String, Box<dyn Error>> {
    let mut digest = Sha256::new();
    std::io::copy(&mut fs::File::open(path)?, &mut digest)?;
    Ok(digest.finalize().as_ref().iter().map(|byte| format!("{byte:02x}")).collect())
}

fn capture_source(path: &Path) -> Result<(PathBuf, Vec<u8>), Box<dyn Error>> {
    let origin = fs::canonicalize(path)?;
    #[cfg(unix)]
    let bytes = reuse::read_regular(&origin, 32 * 1024 * 1024)?;
    #[cfg(not(unix))]
    let bytes = fs::read(&origin)?;
    Ok((origin, bytes))
}

fn verify_snapshot(path: &Path, expected: &[u8]) -> Result<(), Box<dyn Error>> {
    if fs::read(path)? != expected {
        return Err(failure("compiler source snapshot differs from the recorded exact bytes"));
    }
    Ok(())
}

fn validate_worker_pause_source(source: &Path, bytes: &[u8]) -> Result<(), Box<dyn Error>> {
    let production = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-build-cpu/src/worker/gate/decision.rs")
        .canonicalize()?;
    if source != production
        || bytes != include_bytes!("../../trust-build-cpu/src/worker/gate/decision.rs")
    {
        return Err(failure(
            "worker pause qualification requires the exact compiled production decision source",
        ));
    }
    Ok(())
}

fn validate_source_close_source(source: &Path, bytes: &[u8]) -> Result<(), Box<dyn Error>> {
    let production = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-resource-controller/src/bootstrap_graph/source/decision.rs")
        .canonicalize()?;
    if source != production
        || bytes
            != include_bytes!(
                "../../trust-resource-controller/src/bootstrap_graph/source/decision.rs"
            )
    {
        return Err(failure(
            "source close qualification requires the exact compiled production decision source",
        ));
    }
    Ok(())
}

fn validate(suite: &Suite) -> Result<(), Box<dyn Error>> {
    let arity = suite.cases.first().ok_or("empty input suite")?.arguments.len();
    if arity > 8 || suite.fuel == 0 || suite.fuel > 4096 {
        return Err(failure("Boolean arity must be <= 8 and fuel must be 1..=4096"));
    }
    let mut seen = std::collections::BTreeSet::new();
    for case in &suite.cases {
        if case.arguments.len() != arity || !seen.insert(case.arguments.clone()) {
            return Err(failure("input suite has inconsistent arity or duplicate cases"));
        }
        if case.expected && !case.permitted {
            return Err(failure("expected result violates the authored permission property"));
        }
    }
    if seen.len() != 1usize << arity {
        return Err(failure("input suite does not cover every Boolean input"));
    }
    if suite.mutation_from.is_empty() || suite.mutation_from == suite.mutation_to {
        return Err(failure("mutation must change a nonempty exact source span"));
    }
    Ok(())
}

fn compile(
    compiler: &Path,
    identity: &CompilerIdentity,
    expected: &[u8],
    out: &Path,
) -> Result<Vec<u8>, Box<dyn Error>> {
    fs::create_dir(out)?;
    if compiler_identity(compiler, out)? != *identity {
        return Err(failure("compiler identity changed before source extraction"));
    }
    // Compile only a private immutable snapshot of the one recorded input. The
    // original source path can no longer race identity, positive proof or mutation.
    let source = out.join("source.rs");
    fs::write(&source, expected)?;
    let mut permissions = fs::metadata(&source)?.permissions();
    permissions.set_readonly(true);
    fs::set_permissions(&source, permissions)?;
    verify_snapshot(&source, expected)?;
    let started = Instant::now();
    eprintln!("phase compiler-extraction started");
    let answer = extraction::run(&identity.executable, out);
    eprintln!("phase compiler-extraction finished elapsed_ms={}", started.elapsed().as_millis());
    answer?;
    verify_snapshot(&source, expected)?;
    if compiler_identity(compiler, out)? != *identity {
        return Err(failure("compiler identity changed during source extraction"));
    }
    read_ir(&out.join("source_qualification.trust-ir.bin"))
}

fn read_ir(path: &Path) -> Result<Vec<u8>, Box<dyn Error>> {
    Ok(trust_stage_receipt::read_required_regular_file(path, MAX_LITERAL_MODULE_BYTES as u64)?)
}

fn function(bytes: &[u8], suite: &Suite) -> Result<u32, Box<dyn Error>> {
    if bytes.len() > MAX_LITERAL_MODULE_BYTES {
        return Err(LiteralRefinementError::ModuleTooLarge {
            bytes: bytes.len(),
            maximum: MAX_LITERAL_MODULE_BYTES,
        }
        .into());
    }
    let module = trust_ir::binary::deserialize_module(bytes)
        .map_err(|error| failure(format!("compiler artifact decode refused: {error}")))?;
    let mut found = module
        .functions
        .iter()
        .filter(|f| f.display_path.as_deref() == Some(suite.function.as_str()));
    let function = found.next().ok_or("requested function absent from compiler artifact")?;
    if found.next().is_some() || function.blocks.is_empty() {
        return Err(failure("function identity is ambiguous or has no body"));
    }
    let signature = module.func_types.get(function.ty.as_usize()).ok_or("missing signature")?;
    if signature.params != vec![trust_ir::Ty::Bool; suite.cases[0].arguments.len()]
        || signature.returns != vec![trust_ir::Ty::Bool]
    {
        return Err(failure("requested source function is not the declared Boolean signature"));
    }
    Ok(function.id.index())
}

fn invocation(case: &Case) -> LiteralInvocation {
    LiteralInvocation::closed(
        case.arguments.iter().map(|&value| LiteralScalar::Bool { value }).collect(),
        0,
    )
}

fn property(case: &Case, fuel: u64) -> String {
    // The first conjunct rules out fuel exhaustion, panic and every non-return outcome.
    // The second is the authored safety implication about this actual returned value.
    let proof =
        if case.permitted { "fun _ => rfl" } else { "fun h => Eq.trans (Eq.symm value_exact) h" };
    format!(
        r#"
namespace SourceQualification
def value (o : IROutcome) : Bool :=
  match o with
  | IROutcome.ret values =>
    match values with
    | IRList.cons (IRScalar.bool_ b) IRList.nil => b
    | _ => false
  | _ => false
def outcome : IROutcome :=
  ir_run {fuel} Trust.LiteralRefinement.Program Trust.LiteralRefinement.Initial
theorem outcome_exact : outcome =
    IROutcome.ret (IRList.cons IRScalar (IRScalar.bool_ {expected}) (IRList.nil IRScalar)) := rfl
theorem value_exact : value outcome = {expected} := rfl
theorem checked :
    (outcome = IROutcome.ret (IRList.cons IRScalar (IRScalar.bool_ {expected}) (IRList.nil IRScalar))) ∧
    (value outcome = true → {permitted} = true) :=
  And.intro outcome_exact ({proof})
end SourceQualification
"#,
        expected = case.expected,
        permitted = case.permitted
    )
}

fn model(suite: &Suite) -> String {
    let actions = suite.cases.iter().enumerate().map(|(i, case)| format!(
        r#"Action.mk "Case{i}" Guard.always [Update.mk "released" (ScalarExpr.int {}), Update.mk "permitted" (ScalarExpr.int {})]"#,
        u8::from(case.expected), u8::from(case.permitted),
    )).collect::<Vec<_>>().join(",\n");
    format!(
        r#"
namespace SourceQualification
open Trust.Temporal.FiniteModel
def Model : ScalarModel := ScalarModel.mk "SourceBooleanPermission"
  [Constant.mk "Buggy" 0]
  [StateVar.mk "released" 0, StateVar.mk "permitted" 0]
  [{actions},
   Action.mk "EarlyRelease" (Guard.when (ScalarExpr.eq (ScalarExpr.constRef "Buggy") (ScalarExpr.int 1)))
     [Update.mk "released" (ScalarExpr.int 1), Update.mk "permitted" (ScalarExpr.int 0)]]
  [Invariant.mk "PermissionBeforeRelease" (ScalarExpr.le
     (ScalarExpr.var "released") (ScalarExpr.var "permitted")),
   Invariant.mk "ReleasedBoolean" (ScalarExpr.le (ScalarExpr.var "released") (ScalarExpr.int 1)),
   Invariant.mk "PermittedBoolean" (ScalarExpr.le (ScalarExpr.var "permitted") (ScalarExpr.int 1))]
def Safety : Prop := ScalarModel.safetyClaim Model
end SourceQualification
"#
    )
}

fn recheck_case_blob(
    encoded: &[u8],
    module: &[u8],
    function_id: u32,
    case: &Case,
    fuel: u64,
) -> Result<(), Box<dyn Error>> {
    let certificate: LiteralPropertyCertificate = serde_json::from_slice(encoded)?;
    recheck_literal_property(
        &certificate,
        module,
        function_id,
        &invocation(case),
        &property(case, fuel),
        "SourceQualification.checked",
    )?;
    Ok(())
}

#[derive(Debug, Default, PartialEq, Eq)]
struct Options {
    prior_cases: Option<PathBuf>,
    prior_properties: Option<PathBuf>,
    import_candidates: Option<PathBuf>,
    custody: bool,
    attribution: bool,
    worker_pause: bool,
    source_close: bool,
}

fn parse_options(args: &[std::ffi::OsString]) -> Result<Options, Box<dyn Error>> {
    let mut options = Options::default();
    let mut next = 0;
    while next < args.len() {
        if args[next] == "--reuse-cases"
            && options.prior_cases.is_none()
            && next + 1 < args.len()
            && !args[next + 1].to_string_lossy().starts_with("--")
        {
            options.prior_cases = Some(PathBuf::from(&args[next + 1]));
            next += 2;
        } else if args[next] == "--reuse-source-properties"
            && options.prior_properties.is_none()
            && next + 1 < args.len()
            && !args[next + 1].to_string_lossy().starts_with("--")
        {
            options.prior_properties = Some(PathBuf::from(&args[next + 1]));
            next += 2;
        } else if args[next] == "--import-proof-candidates"
            && options.import_candidates.is_none()
            && next + 1 < args.len()
            && !args[next + 1].to_string_lossy().starts_with("--")
        {
            options.import_candidates = Some(PathBuf::from(&args[next + 1]));
            next += 2;
        } else if args[next] == "--custody-refinement"
            && !options.custody
            && !options.attribution
            && !options.worker_pause
            && !options.source_close
        {
            options.custody = true;
            next += 1;
        } else if args[next] == "--attribution-refinement"
            && !options.custody
            && !options.attribution
            && !options.worker_pause
            && !options.source_close
        {
            options.attribution = true;
            next += 1;
        } else if args[next] == "--worker-pause-refinement"
            && !options.custody
            && !options.attribution
            && !options.worker_pause
            && !options.source_close
        {
            options.worker_pause = true;
            next += 1;
        } else if args[next] == "--source-close-refinement"
            && !options.custody
            && !options.attribution
            && !options.worker_pause
            && !options.source_close
        {
            options.source_close = true;
            next += 1;
        } else {
            return Err(failure("unknown, repeated or incomplete qualification option"));
        }
    }
    if options.prior_properties.is_some()
        && !options.custody
        && !options.attribution
        && !options.worker_pause
        && !options.source_close
    {
        return Err(failure("--reuse-source-properties requires a fixed refinement policy"));
    }
    if options.import_candidates.is_some()
        && (!options.custody || options.prior_cases.is_some() || options.prior_properties.is_some())
    {
        return Err(failure(
            "--import-proof-candidates requires custody and cannot mix with strict reuse",
        ));
    }
    Ok(options)
}

#[derive(Serialize)]
struct PhaseTiming {
    phase: String,
    elapsed_ns: u64,
}

fn elapsed_ns(started: Instant) -> u64 {
    u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

fn record_phase(timings: &mut Vec<PhaseTiming>, phase: impl Into<String>, started: Instant) {
    let timing = PhaseTiming { phase: phase.into(), elapsed_ns: elapsed_ns(started) };
    eprintln!("timing phase={} elapsed_ns={}", timing.phase, timing.elapsed_ns);
    timings.push(timing);
}

fn run() -> Result<(), Box<dyn Error>> {
    let total_started = Instant::now();
    let mut timings = Vec::new();
    let args = env::args_os().skip(1).collect::<Vec<_>>();
    if args.len() < 4 {
        return Err(failure(
            "usage: qualify_bool_source <trustc> <source.rs> <suite.json> <new-evidence-dir> [--reuse-cases <prior-evidence-dir>] [--custody-refinement | --attribution-refinement | --worker-pause-refinement | --source-close-refinement] [--reuse-source-properties <prior-evidence-dir>] [--import-proof-candidates <legacy-evidence-dir>]",
        ));
    }
    let options = parse_options(&args[4..])?;
    let custody = options.custody;
    let attribution = options.attribution;
    let worker_pause = options.worker_pause;
    let source_close = options.source_close;
    let fixed_policy = if custody {
        Some(refinement::FixedPolicy::Custody)
    } else if attribution {
        Some(refinement::FixedPolicy::Attribution)
    } else if worker_pause {
        Some(refinement::FixedPolicy::WorkerPause)
    } else if source_close {
        Some(refinement::FixedPolicy::SourceClose)
    } else {
        None
    };
    let started = Instant::now();
    let compiler = PathBuf::from(&args[0]);
    let (source, source_bytes) = capture_source(Path::new(&args[1]))?;
    #[cfg(unix)]
    let suite_bytes = reuse::read_regular(Path::new(&args[2]), 1024 * 1024)?;
    #[cfg(not(unix))]
    let suite_bytes = fs::read(&args[2])?;
    let suite: Suite = serde_json::from_slice(&suite_bytes)?;
    validate(&suite)?;
    if let Some(policy) = fixed_policy {
        policy.validate(&suite)?;
    }
    if worker_pause {
        validate_worker_pause_source(&source, &source_bytes)?;
    }
    if source_close {
        validate_source_close_source(&source, &source_bytes)?;
    }
    let requested_out = PathBuf::from(&args[3]);
    let (out, prior, prior_properties) = reuse::admit_directories(
        &requested_out,
        options.prior_cases.as_deref().or(options.import_candidates.as_deref()),
        options.prior_properties.as_deref().or(options.import_candidates.as_deref()),
    )?;
    fs::write(out.join("suite.json"), serde_json::to_vec_pretty(&suite)?)?;
    record_phase(&mut timings, "input-capture-and-admission", started);
    let started = Instant::now();
    let identity = compiler_identity(&compiler, &out)?;
    record_phase(&mut timings, "compiler-identity", started);
    fs::write(out.join("compiler-version.txt"), &identity.version)?;
    fs::write(
        out.join("identity.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "trust.source-qualification-identity/v3",
            "source": &source,
            "source_sha256": sha256(&source_bytes),
            "compiler": &identity,
            "source_path_policy": SOURCE_PATH_POLICY,
            "extraction_flags": EXTRACTION_FLAGS,
            "lowering_authority": "trusted-compiler-boundary",
            "project_authority": false,
            "binary_authority": false
        }))?,
    )?;
    let started = Instant::now();
    let bytes = compile(&compiler, &identity, &source_bytes, &out.join("positive"))?;
    let id = function(&bytes, &suite)?;
    record_phase(&mut timings, "positive-extraction", started);
    let inputs = reuse::CaseInputs::new(&source, &source_bytes, &identity, &suite, &bytes, id)?;
    reuse::validate_transport_capacity(&inputs)?;
    let imported = if options.import_candidates.is_some() {
        Some(reuse::ImportedProofCandidates::load(
            prior.as_deref().ok_or("import directory absent")?,
            &inputs,
        )?)
    } else {
        None
    };
    if let Some(imported) = &imported {
        imported.capture_provenance(&out)?;
    }
    let reusable = if imported.is_none() {
        prior.as_deref().map(|dir| reuse::CaseSet::load(dir, &inputs)).transpose()?
    } else {
        None
    };
    let reusable_properties = if imported.is_none() {
        prior_properties
            .as_deref()
            .map(|dir| reuse::SourcePropertySet::load(dir, &inputs))
            .transpose()?
    } else {
        None
    };
    let mut artifacts = Vec::with_capacity(suite.cases.len());
    let mut generated = 0;
    for (index, case) in suite.cases.iter().enumerate() {
        let started = Instant::now();
        eprintln!(
            "phase case-{index} started mode={}",
            if imported.is_some() {
                "import-candidate"
            } else if reusable.is_some() {
                "reuse"
            } else {
                "generate"
            }
        );
        let claim = property(case, suite.fuel);
        let preparation_started = Instant::now();
        let encoded = if let Some(reusable) = &reusable {
            reusable.read_case(index)?
        } else if let Some(imported) = &imported {
            let encoded = imported.read_case(index)?;
            reuse::write_new(
                &out.join(format!("import-literal-candidate-{index}.json")),
                &encoded,
            )?;
            encoded
        } else {
            let certificate = certify_literal_property(
                &bytes,
                id,
                &invocation(case),
                &claim,
                "SourceQualification.checked",
            )?;
            generated += 1;
            serde_json::to_vec(&certificate)?
        };
        record_phase(
            &mut timings,
            format!(
                "literal-case-{index}-{}",
                if reusable.is_some() || imported.is_some() { "read" } else { "generate" }
            ),
            preparation_started,
        );
        let replay_started = Instant::now();
        recheck_case_blob(&encoded, &bytes, id, case, suite.fuel)?;
        record_phase(&mut timings, format!("literal-case-{index}-fresh-replay"), replay_started);
        reuse::write_new(&out.join(format!("case-{index}.json")), &encoded)?;
        artifacts.push(reuse::CaseArtifact::new(index, &encoded));
        eprintln!("phase case-{index} finished elapsed_ms={}", started.elapsed().as_millis());
        println!(
            "case {index}: {} exact returned value and permission property kernel-replayed",
            if imported.is_some() {
                "imported candidate"
            } else if reusable.is_some() {
                "reused"
            } else {
                "generated"
            }
        );
    }
    let case_set_sha256 = reuse::publish_case_set(&out, inputs.clone(), artifacts)?;
    let model_source = model(&suite);
    fs::write(out.join("model.lean"), &model_source)?;
    let started = Instant::now();
    eprintln!("phase model-production-and-replay started");
    let model = certify_automatic_clean_scalar_model(&model_source, "SourceQualification.Model")?;
    record_phase(&mut timings, "model-generation", started);
    let encoded = serde_json::to_vec(&model)?;
    fs::write(out.join("model-certificate.json"), &encoded)?;
    let replay_started = Instant::now();
    recheck_automatic_clean_scalar_model(&serde_json::from_slice(&encoded)?, &model_source)?;
    record_phase(&mut timings, "model-fresh-replay", replay_started);
    eprintln!(
        "phase model-production-and-replay finished elapsed_ms={}",
        started.elapsed().as_millis()
    );
    let started = Instant::now();
    let checked_model = fixed_policy
        .map(|policy| refinement::CheckedModel::new(&suite, &model, policy))
        .transpose()?;
    record_phase(&mut timings, "fixed-model-admission", started);
    let mut properties_generated = 0;
    let mut properties_reused = 0;
    let mut properties_imported = 0;
    let mut properties_replayed = 0;
    let mut property_artifacts = Vec::new();
    let mut property_set_sha256 = None;
    if let Some(checked_model) = &checked_model {
        for (index, case) in suite.cases.iter().enumerate() {
            eprintln!("phase source-model-refinement-{index} started");
            let (encoded, decoded) = if reusable_properties.is_some() || imported.is_some() {
                let started = Instant::now();
                let encoded = if let Some(reusable) = &reusable_properties {
                    reusable.read_case(index)?
                } else {
                    imported
                        .as_ref()
                        .ok_or("property candidate source absent")?
                        .read_property(index)?
                };
                record_phase(&mut timings, format!("source-property-{index}-read"), started);
                let started = Instant::now();
                let decoded = refinement::replay_candidate(
                    &encoded,
                    &bytes,
                    id,
                    &suite,
                    index,
                    checked_model,
                    &out.join(format!("source-refinement-{index}.noindex")),
                )?;
                record_phase(
                    &mut timings,
                    format!("source-property-{index}-fresh-replay"),
                    started,
                );
                if imported.is_some() {
                    properties_imported += 1;
                } else {
                    properties_reused += 1;
                }
                (encoded, decoded)
            } else {
                let started = Instant::now();
                let certificate = refinement::certify(
                    &bytes,
                    id,
                    &suite,
                    index,
                    case.expected,
                    checked_model,
                    refinement::ProjectionMode::Actual,
                    &out.join(format!("source-refinement-{index}.noindex")),
                )?;
                record_phase(&mut timings, format!("source-property-{index}-generate"), started);
                let encoded = serde_json::to_vec(&certificate)?;
                let decoded = serde_json::from_slice(&encoded)?;
                let started = Instant::now();
                refinement::replay(&decoded, &bytes, id, &suite, index, checked_model)?;
                record_phase(
                    &mut timings,
                    format!("source-property-{index}-fresh-replay"),
                    started,
                );
                properties_generated += 1;
                (encoded, decoded)
            };
            properties_replayed += 1;
            if index == 0 {
                let started = Instant::now();
                let count =
                    refinement::splice_controls(&decoded, &bytes, id, &suite, checked_model)?;
                record_phase(&mut timings, "source-property-splice-controls", started);
                reuse::write_new(
                    &out.join("source-refinement-splice-controls.txt"),
                    format!("{count} exact fixed-input refusals\n").as_bytes(),
                )?;
            }
            reuse::write_new(&out.join(format!("source-refinement-{index}.json")), &encoded)?;
            property_artifacts.push(reuse::CaseArtifact::new(index, &encoded));
            eprintln!("phase source-model-refinement-{index} finished");
        }
        property_set_sha256 =
            Some(reuse::publish_source_property_set(&out, inputs, property_artifacts)?);
        for (label, index, mode) in [
            (
                "constant",
                suite
                    .cases
                    .iter()
                    .position(|case| case.expected)
                    .ok_or("no true return witness")?,
                refinement::ProjectionMode::Constant,
            ),
            (
                "result-ignoring",
                suite.cases.iter().position(|case| !case.permitted).ok_or("no forbidden input")?,
                refinement::ProjectionMode::Expected,
            ),
        ] {
            let started = Instant::now();
            let error = match refinement::certify(
                &bytes,
                id,
                &suite,
                index,
                suite.cases[index].expected,
                checked_model,
                mode,
                &out.join(format!("projection-{label}.noindex")),
            ) {
                Err(error) => error,
                Ok(_) => {
                    return Err(failure(
                        "a wrong projection satisfied the fixed Boolean decoder theorem",
                    ));
                }
            };
            record_phase(&mut timings, format!("projection-{label}-refusal"), started);
            if !refinement::is_named_proof_refusal(
                error.as_ref(),
                "SourcePermission.project_return_exact",
            ) {
                return Err(failure(format!(
                    "projection control failed for an unrelated reason: {error}"
                )));
            }
            reuse::write_new(
                &out.join(format!("projection-{label}-rejected.txt")),
                error.to_string().as_bytes(),
            )?;
        }
    }

    let source_text = std::str::from_utf8(&source_bytes)?;
    if source_text.matches(&suite.mutation_from).count() != 1 {
        return Err(failure("mutation source span does not occur exactly once"));
    }
    let mutant = source_text.replace(&suite.mutation_from, &suite.mutation_to);
    let started = Instant::now();
    let mutant_bytes = compile(&compiler, &identity, mutant.as_bytes(), &out.join("negative"))?;
    let mutant_id = function(&mutant_bytes, &suite)?;
    record_phase(&mut timings, "mutant-extraction", started);
    let mut violations = 0;
    let mut witnessed_violations = Vec::new();
    for (index, case) in suite.cases.iter().enumerate().filter(|(_, c)| !c.permitted) {
        let claim = property(case, suite.fuel);
        let started = Instant::now();
        let attempted = certify_literal_property(
            &mutant_bytes,
            mutant_id,
            &invocation(case),
            &claim,
            "SourceQualification.checked",
        );
        record_phase(&mut timings, format!("mutant-{index}-original-property-attempt"), started);
        match attempted {
            Ok(_) => continue,
            Err(error) => fs::write(out.join(format!("negative-{index}.txt")), error.to_string())?,
        }
        // A fresh proof of the counterexample's true return distinguishes a semantic
        // violation from parse failure, missing capability or a stale digest.
        let witness = Case { expected: true, permitted: true, ..case.clone() };
        let started = Instant::now();
        let certificate = certify_literal_property(
            &mutant_bytes,
            mutant_id,
            &invocation(case),
            &property(&witness, suite.fuel),
            "SourceQualification.checked",
        )?;
        record_phase(&mut timings, format!("mutant-{index}-true-return-witness"), started);
        fs::write(
            out.join(format!("negative-witness-{index}.json")),
            serde_json::to_vec(&certificate)?,
        )?;
        if let Some(checked_model) = &checked_model {
            // The fresh true-return witness above establishes I's real initial
            // premise. The original safe model must then refuse this actual
            // wrong return at simulation, not merely an expected-value mismatch.
            let started = Instant::now();
            let error = match refinement::certify(
                &mutant_bytes,
                mutant_id,
                &suite,
                index,
                true,
                checked_model,
                refinement::ProjectionMode::Actual,
                &out.join(format!("negative-refinement-{index}.noindex")),
            ) {
                Err(error) => error,
                Ok(certificate) => {
                    reuse::write_new(
                        &out.join(format!("negative-refinement-unexpected-{index}.json")),
                        &serde_json::to_vec(&certificate)?,
                    )?;
                    return Err(failure("unsafe actual source refined the original safe model"));
                }
            };
            record_phase(
                &mut timings,
                format!("mutant-{index}-source-refinement-refusal"),
                started,
            );
            if !refinement::is_named_proof_refusal(error.as_ref(), "SourcePermission.returnAction")
            {
                return Err(failure(format!(
                    "source refinement mutant failed for an unrelated reason: {error}"
                )));
            }
            reuse::write_new(
                &out.join(format!("negative-refinement-{index}.txt")),
                error.to_string().as_bytes(),
            )?;
        }
        violations += 1;
        witnessed_violations.push(index);
    }
    if violations == 0 {
        return Err(failure(
            "freshly compiled mutant produced no kernel-proved property violation",
        ));
    }
    let worker_credit_case = if worker_pause {
        let index = suite
            .cases
            .iter()
            .position(|case| case.arguments == [true, true, false])
            .ok_or("missing actual outstanding-credit input")?;
        if !witnessed_violations.contains(&index) {
            return Err(failure(
                "credit-ignoring mutant lacks the actual outstanding-credit true-return witness and source refinement refusal",
            ));
        }
        Some(index)
    } else {
        None
    };
    let source_handler_case = if source_close {
        let index = suite
            .cases
            .iter()
            .position(|case| case.arguments == [true, true])
            .ok_or("missing actual active-handler and matching-root input")?;
        if !witnessed_violations.contains(&index) {
            return Err(failure(
                "handler-ignoring mutant lacks the actual active-handler true-return witness and source refinement refusal",
            ));
        }
        Some(index)
    } else {
        None
    };
    let mut result = serde_json::json!({
        "schema": if custody {"trust.source-qualification/v5"} else if attribution {"trust.attribution-source-qualification/v1"} else if worker_pause {"trust.worker-pause-source-qualification/v1"} else if source_close {"trust.source-close-qualification/v1"} else {"trust.source-qualification/v3"},
        "source_sha256": sha256(&source_bytes),
        "module_sha256": sha256(&bytes),
        "function": suite.function,
        "function_id": id,
        "boolean_cases_kernel_replayed": suite.cases.len(),
        "boolean_cases_generated": generated,
        "boolean_cases_reused": if imported.is_some() {0} else {suite.cases.len() - generated},
        "boolean_cases_imported": if imported.is_some() {suite.cases.len()} else {0},
        "case_set_sha256": case_set_sha256,
        "reused_case_set_sha256": reusable.as_ref().map(reuse::CaseSet::manifest_sha256),
        "source_path_policy": SOURCE_PATH_POLICY,
        "ty_model_kernel_replayed": true,
        "mutant_module_sha256": sha256(&mutant_bytes),
        "fresh_mutant_property_violations": violations,
        "custody_source_model_refinements": if custody {suite.cases.len()} else {0},
        "source_properties_generated": properties_generated,
        "source_properties_reused": properties_reused,
        "source_properties_imported": properties_imported,
        "source_properties_freshly_replayed": properties_replayed,
        "source_property_set_sha256": property_set_sha256,
        "reused_source_property_set_sha256": reusable_properties.as_ref().map(reuse::SourcePropertySet::manifest_sha256),
        "imported_case_set_sha256": imported.as_ref().map(reuse::ImportedProofCandidates::case_manifest_sha256),
        "imported_source_property_set_sha256": imported.as_ref().map(reuse::ImportedProofCandidates::property_manifest_sha256),
        "timings": {
            "clock": "std::time::Instant",
            "scope": "qualifier execution through result construction; excludes external machine admission and qualifier compilation",
            "total_ns": elapsed_ns(total_started),
            "phases": timings,
        },
        "project_authority": false,
        "binary_authority": false
    });
    if attribution {
        result["attribution_source_model_refinements"] = serde_json::json!(suite.cases.len());
    }
    if worker_pause {
        result["worker_pause_source_model_refinements"] = serde_json::json!(suite.cases.len());
        result["credit_ignoring_mutant_witness_case"] = serde_json::json!(worker_credit_case);
        result["credit_ignoring_mutant_witness_arguments"] = serde_json::json!([true, true, false]);
    }
    if source_close {
        result["source_close_source_model_refinements"] = serde_json::json!(suite.cases.len());
        result["handler_ignoring_mutant_witness_case"] = serde_json::json!(source_handler_case);
        result["handler_ignoring_mutant_witness_arguments"] = serde_json::json!([true, true]);
    }
    fs::write(out.join("result.json"), serde_json::to_vec_pretty(&result)?)?;
    println!(
        "PASS: {} Boolean cases (generated={generated} reused={} imported={}); TY model replayed; {violations} fresh source-mutant violation(s)",
        suite.cases.len(),
        if imported.is_some() { 0 } else { suite.cases.len() - generated },
        if imported.is_some() { suite.cases.len() } else { 0 },
    );
    println!(
        "scope: compiler-produced literal semantics; compiler lowering trusted; no project or binary authority"
    );
    if custody {
        println!(
            "fixed custody composition: {properties_replayed} exact source/model properties (generated={properties_generated} reused={properties_reused} imported={properties_imported}); actual-return decoder, reachable-change witnesses, projection and splice refusals checked"
        );
    } else if attribution {
        println!(
            "fixed attribution composition: {properties_replayed} exact source/model properties (generated={properties_generated} reused={properties_reused}); actual-return decoder, reachable-change witnesses, projection and splice refusals checked"
        );
    } else if worker_pause {
        println!(
            "fixed worker-pause composition: {properties_replayed} exact production source/model properties; no mutex, OS, concurrency or lifecycle theorem"
        );
    } else if source_close {
        println!(
            "fixed source-close composition: {properties_replayed} exact shared production source/model properties; no atomic, handler Drop, SCM, settlement or lifecycle theorem"
        );
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("qualify_bool_source: {error}");
        std::process::exit(1);
    }
}

#[cfg(all(test, unix))]
#[path = "qualify_bool_source/intake_tests.rs"]
mod intake_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_close_mode_binds_actual_shared_source_and_excludes_other_policies() {
        let parse = |args: &[&str]| {
            parse_options(&args.iter().map(std::ffi::OsString::from).collect::<Vec<_>>())
        };
        let options =
            parse(&["--source-close-refinement", "--reuse-source-properties", "prior"]).unwrap();
        assert!(
            options.source_close
                && !options.custody
                && !options.worker_pause
                && !options.attribution
        );
        for policy in [
            "--custody-refinement",
            "--attribution-refinement",
            "--worker-pause-refinement",
            "--source-close-refinement",
        ] {
            assert!(parse(&["--source-close-refinement", policy]).is_err());
            assert!(parse(&[policy, "--source-close-refinement"]).is_err());
        }
        assert!(parse(&["--source-close-refinement", "--import-proof-candidates", "old"]).is_err());
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../trust-resource-controller/src/bootstrap_graph/source/decision.rs")
            .canonicalize()
            .unwrap();
        let bytes = include_bytes!(
            "../../trust-resource-controller/src/bootstrap_graph/source/decision.rs"
        );
        validate_source_close_source(&path, bytes).unwrap();
        let copied = tempfile::NamedTempFile::new().unwrap();
        fs::write(copied.path(), bytes).unwrap();
        let (copied_path, copied_bytes) = capture_source(copied.path()).unwrap();
        assert!(validate_source_close_source(&copied_path, &copied_bytes).is_err());
        assert!(validate_source_close_source(&path, b"changed body").is_err());
    }

    #[test]
    fn worker_pause_mode_is_exclusive_and_requires_the_original_production_source() {
        let parse = |args: &[&str]| {
            parse_options(&args.iter().map(std::ffi::OsString::from).collect::<Vec<_>>())
        };
        assert!(parse(&["--worker-pause-refinement"]).unwrap().worker_pause);
        for args in [
            vec!["--worker-pause-refinement", "--custody-refinement"],
            vec!["--attribution-refinement", "--worker-pause-refinement"],
            vec!["--worker-pause-refinement", "--worker-pause-refinement"],
            vec!["--worker-pause-refinement", "--import-proof-candidates", "old"],
        ] {
            assert!(parse(&args).is_err());
        }
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../trust-build-cpu/src/worker/gate/decision.rs")
            .canonicalize()
            .unwrap();
        let bytes = include_bytes!("../../trust-build-cpu/src/worker/gate/decision.rs");
        validate_worker_pause_source(&path, bytes).unwrap();
        assert!(validate_worker_pause_source(Path::new("copied-decision.rs"), bytes).is_err());
        assert!(validate_worker_pause_source(&path, b"changed body").is_err());
    }

    #[test]
    fn attribution_mode_is_explicit_exclusive_and_keeps_legacy_import_custody_only() {
        let parse = |arguments: &[&str]| {
            parse_options(&arguments.iter().map(std::ffi::OsString::from).collect::<Vec<_>>())
        };
        let options =
            parse(&["--attribution-refinement", "--reuse-source-properties", "prior"]).unwrap();
        assert!(options.attribution && !options.custody);
        assert_eq!(options.prior_properties, Some(PathBuf::from("prior")));
        for arguments in [
            vec!["--attribution-refinement", "--custody-refinement"],
            vec!["--custody-refinement", "--attribution-refinement"],
            vec!["--attribution-refinement", "--attribution-refinement"],
            vec!["--attribution-refinement", "--import-proof-candidates", "legacy"],
            vec!["--import-proof-candidates", "legacy", "--attribution-refinement"],
        ] {
            assert!(parse(&arguments).is_err(), "{arguments:?}");
        }
    }

    #[test]
    fn source_property_reuse_is_explicit_independent_and_requires_fixed_policy() {
        let parse = |arguments: &[&str]| {
            parse_options(
                &arguments
                    .iter()
                    .map(|argument| std::ffi::OsString::from(*argument))
                    .collect::<Vec<_>>(),
            )
        };
        let options =
            parse(&["--reuse-source-properties", "prior", "--custody-refinement"]).unwrap();
        assert_eq!(options.prior_properties, Some(PathBuf::from("prior")));
        assert_eq!(options.prior_cases, None);
        let options = parse(&[
            "--custody-refinement",
            "--reuse-cases",
            "prior",
            "--reuse-source-properties",
            "prior",
        ])
        .unwrap();
        assert_eq!(options.prior_cases, options.prior_properties);
        let options =
            parse(&["--custody-refinement", "--import-proof-candidates", "legacy"]).unwrap();
        assert_eq!(options.import_candidates, Some(PathBuf::from("legacy")));
        assert_eq!(options.prior_cases, None);
        assert_eq!(options.prior_properties, None);
        for arguments in [
            vec!["--reuse-source-properties", "prior"],
            vec!["--custody-refinement", "--reuse-source-properties"],
            vec!["--reuse-source-properties", "--custody-refinement"],
            vec![
                "--custody-refinement",
                "--reuse-source-properties",
                "a",
                "--reuse-source-properties",
                "b",
            ],
            vec!["--custody-refinement", "--custody-refinement"],
            vec!["--custody-refinement", "--unknown"],
            vec!["--import-proof-candidates", "legacy"],
            vec!["--custody-refinement", "--import-proof-candidates"],
            vec![
                "--custody-refinement",
                "--import-proof-candidates",
                "legacy",
                "--reuse-cases",
                "strict",
            ],
            vec![
                "--custody-refinement",
                "--reuse-source-properties",
                "strict",
                "--import-proof-candidates",
                "legacy",
            ],
            vec![
                "--custody-refinement",
                "--import-proof-candidates",
                "one",
                "--import-proof-candidates",
                "two",
            ],
        ] {
            assert!(parse(&arguments).is_err(), "{arguments:?}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn source_origin_and_bytes_are_captured_once_before_namespace_changes() {
        let directory = tempfile::tempdir().unwrap();
        let a = directory.path().join("a.rs");
        let b = directory.path().join("b.rs");
        fs::write(&a, b"captured source").unwrap();
        fs::write(&b, b"different source").unwrap();
        let (origin, bytes) = capture_source(&a).unwrap();
        fs::remove_file(&a).unwrap();
        std::os::unix::fs::symlink(&b, &a).unwrap();
        let suite = Suite {
            function: "answer".to_owned(),
            fuel: 8,
            cases: vec![Case { arguments: vec![], expected: true, permitted: true }],
            mutation_from: "true".to_owned(),
            mutation_to: "false".to_owned(),
        };
        let compiler = identity::fixture();
        let inputs =
            reuse::CaseInputs::new(&origin, &bytes, &compiler, &suite, b"module", 0).unwrap();
        let record = serde_json::to_value(inputs).unwrap();
        assert_eq!(record["source"], serde_json::to_value(&origin).unwrap());
        assert_eq!(record["source_sha256"], sha256(b"captured source"));
        assert_eq!(fs::read(&a).unwrap(), b"different source");
    }

    #[test]
    fn source_snapshot_mismatch_is_rejected() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("source.rs");
        let expected = b"pub fn answer() -> bool { false }";
        fs::write(&path, expected).unwrap();
        verify_snapshot(&path, expected).unwrap();
        fs::write(&path, b"pub fn answer() -> bool { true }").unwrap();
        assert!(verify_snapshot(&path, expected).is_err());
    }

    #[test]
    fn every_boolean_input_is_required_and_duplicate_cases_do_not_count() {
        let mut suite: Suite =
            serde_json::from_str(include_str!("cleanup_permission.json")).unwrap();
        validate(&suite).unwrap();
        suite.cases[7] = suite.cases[0].clone();
        assert!(validate(&suite).is_err());
        suite.cases.pop();
        assert!(validate(&suite).is_err());
    }
}
