//! Ordinary checked source to diagnostic runtime IR. Never a LibraryEnvelope,
//! carrier gate, external-import admission or executable/refinement claim.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

use clean_compiler::emit_trust_ir::{RuntimeLowering, serialize_tmbc};
use clean_compiler::runtime_lcnf::{
    RuntimeContext, RuntimeEnvironmentPopulation, RuntimeIrStatus, RuntimeLimits,
    RuntimeModuleInput, RuntimeProvenance, RuntimeSourceRecord,
};
use clean_kernel::Name;
use clean_olean::import::runtime::{RuntimeBody, RuntimeOleanInput, RuntimeOleanPart};
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use trust_clean::olean_census::OleanClosureCapture;

pub(super) const USAGE: &str = "Diagnostic development mode:\n\
    targo trust build FILE.lean --emit=diagnostic-runtime-trust-ir --entry NAME\n\
      --out NEW.tmbc --census NEW.json [--census-olean-path DIR ...]\n\
    NAME is a Lean identifier; quoted components retain exact identity. Advanced\n\
    --entry-json '[{\"str\":\"X\"},{\"num\":7}]' selects exact numeric names.\n\
    Emit the selected checked-local entry's supported runtime Call/PAP closure,\n\
    with conservative Object RC and fixed C runtime imports. Every observed\n\
    local/import row and missing body stays in the diagnostic census. This is\n\
    NOT a gated library, executable, complete runtime census, or G4 authority.\n\
    External paths inventory dependencies; they do NOT enable source imports.\n\
    Unsupported selected bodies and conflicting logical/runtime mirrors refuse.\n\
    --verbose is accepted through the shared library parser and changes nothing\n\
    here: these refusals carry no second typed detail level.\n\
    Existing --emit=trust-ir keeps its independently gated library behavior.";

pub(super) fn requested(args: &[String]) -> bool {
    args.iter().any(|a| a == "--emit=diagnostic-runtime-trust-ir")
        || args.windows(2).any(|a| a[0] == "--emit" && a[1] == "diagnostic-runtime-trust-ir")
}

#[derive(Debug)]
struct Request {
    build: super::Request,
    entry: Name,
}

/// Parse grammar normally, but preserve the lexer's segment boundaries instead
/// of rebuilding Name from the surface AST's lossy display projection.
fn entry_name(text: &str) -> Result<Name, String> {
    use clean_parser::lexer::{Lexer, TokenKind};
    if text.is_empty() || text.len() > 4096 {
        return Err("entry identifier byte bound (1..=4096)".into());
    }
    clean_parser::Parser::parse_expr_with_tactics_exact(text, &Default::default())
        .map_err(|e| format!("entry identifier syntax: {e}"))?;
    let tokens = Lexer::tokenize(text);
    let mut name = Name::anon();
    let mut segment = true;
    let mut count = 0;
    for token in tokens {
        match token.kind {
            TokenKind::Ident(value) if segment => {
                count += 1;
                if count > 128 { return Err("entry identifier segment bound".into()); }
                name = name.str(value);
                segment = false;
            }
            TokenKind::Dot if !segment => segment = true,
            TokenKind::Eof if !segment => return Ok(name),
            _ => return Err("entry must be an exact Lean identifier, not an expression/projection; use --entry-json for numeric Name components".into()),
        }
    }
    Err("incomplete entry identifier".into())
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum EntrySegment {
    Str(String),
    Num(u64),
}

fn entry_json(text: &str) -> Result<Name, String> {
    if text.len() > 4096 {
        return Err("entry JSON byte bound".into());
    }
    let segments: Vec<EntrySegment> = serde_json::from_str(text).map_err(|e| e.to_string())?;
    if segments.is_empty() || segments.len() > 128 {
        return Err("entry JSON segment bound (1..=128)".into());
    }
    Ok(segments.into_iter().fold(Name::anon(), |name, segment| match segment {
        EntrySegment::Str(value) => name.str(value),
        EntrySegment::Num(value) => name.num(value),
    }))
}

fn parse(args: &[String]) -> Result<Request, String> {
    let mut ordinary = Vec::new();
    let mut entry = None;
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        let selector = if arg == "--entry" || arg == "--entry-json" {
            i += 1;
            Some((arg == "--entry-json", args.get(i).ok_or("entry requires a value")?.as_str()))
        } else if let Some(v) = arg.strip_prefix("--entry=") {
            Some((false, v))
        } else {
            arg.strip_prefix("--entry-json=").map(|v| (true, v))
        };
        if let Some((typed, value)) = selector {
            if entry.is_some() {
                return Err("one entry selector is required, not duplicates".into());
            }
            entry = Some(if typed { entry_json(value)? } else { entry_name(value)? });
        } else if arg == "--emit=diagnostic-runtime-trust-ir" {
            ordinary.push("--emit=trust-ir".into());
        } else if arg == "--emit"
            && args.get(i + 1).is_some_and(|a| a == "diagnostic-runtime-trust-ir")
        {
            ordinary.push("--emit=trust-ir".into());
            i += 1;
        } else {
            ordinary.push(arg.clone());
        }
        i += 1;
    }
    let build = super::parse(&ordinary)?;
    if build.census_output.is_none() {
        return Err("diagnostic runtime emission requires --census NEW_PATH".into());
    }
    Ok(Request { build, entry: entry.ok_or("diagnostic runtime emission requires --entry NAME")? })
}

/// Each candidate stays in the original observation. Choose the highest
/// physically present cumulative snapshot only when there is exactly one base
/// candidate; absent/error companions are never substituted with base bytes.
fn inputs(capture: &mut OleanClosureCapture) -> (Vec<RuntimeModuleInput>, Vec<String>) {
    let mut errors = capture.observation.issues.clone();
    let mut present = BTreeMap::new();
    for candidate in &capture.candidates {
        if candidate.parts[0].observation["status"] != "absent" {
            *present.entry(candidate.module.clone()).or_insert(0usize) += 1;
        }
    }
    let mut inputs = Vec::new();
    for candidate in &mut capture.candidates {
        if candidate.parts[0].observation["status"] == "absent" {
            continue;
        }
        if present.get(&candidate.module) != Some(&1) {
            errors.push(format!("ambiguous captured module {:?}", candidate.module));
            continue;
        }
        let mut parts = Vec::new();
        let mut failed = false;
        for (index, part) in candidate.parts.iter_mut().take(3).enumerate() {
            let input = match part.bytes.take() {
                Some(bytes) => Some(RuntimeOleanInput {
                    label: part.path.display().to_string(),
                    bytes: bytes.into(),
                }),
                None if index > 0 && part.observation["status"] == "absent" => None,
                None => {
                    failed = true;
                    errors.push(format!("captured part unavailable: {}", part.path.display()));
                    None
                }
            };
            parts.push(input);
        }
        if failed {
            continue;
        }
        let private = parts.pop().unwrap();
        let server = parts.pop().unwrap();
        let base = parts.pop().unwrap().expect("required captured base");
        let selected = if private.is_some() {
            RuntimeOleanPart::Private
        } else if server.is_some() {
            RuntimeOleanPart::Server
        } else {
            RuntimeOleanPart::Base
        };
        inputs.push(RuntimeModuleInput { base, server, private, selected });
    }
    (inputs, errors)
}

fn body_status(body: &RuntimeBody) -> Value {
    match body {
        RuntimeBody::Stored(Ok(_)) => json!({"status":"stored-decoded"}),
        RuntimeBody::Stored(Err(error)) => json!({"status":"stored-decode-error","error":error}),
        RuntimeBody::NoStoredValueForKind => {
            json!({"status":"no-stored-value-for-kind-not-an-implementation"})
        }
        RuntimeBody::MissingRequiredValue => json!({"status":"missing-required-runtime-body"}),
    }
}

fn population(value: &RuntimeEnvironmentPopulation) -> Value {
    json!({"constants":value.constants,"inductives":value.inductives,
        "constructors":value.constructors,"recursors":value.recursors,
        "quotients":value.quotients,"unique_names":value.unique_names})
}

fn part_identity(value: &clean_olean::import::runtime::RuntimePartIdentity) -> Value {
    json!({"part":match value.part {RuntimeOleanPart::Base=>"base",RuntimeOleanPart::Server=>"server",RuntimeOleanPart::Private=>"private"},
        "label":value.label,"bytes":value.byte_count,"blake3":value.blake3})
}

fn provenance(value: &RuntimeProvenance) -> Value {
    match value {
        RuntimeProvenance::Captured { module_index, part, borrowed_prefix, row_index } => json!({
            "kind":"captured-module-part","module_index":module_index,"part":part_identity(part),
            "borrowed_prefix":borrowed_prefix.iter().map(part_identity).collect::<Vec<_>>(),"row_index":row_index}),
        RuntimeProvenance::Environment { snapshot_blake3, row_index, added_since_baseline } => {
            json!({
            "kind":"checked-source-environment-observation","snapshot_blake3":snapshot_blake3,
            "row_index":row_index,"added_since_baseline":added_since_baseline})
        }
    }
}

fn context_report(context: &RuntimeContext) -> Value {
    let source = context.environment_capture().map(|capture| json!({
        "snapshot_blake3": capture.snapshot_blake3,
        "delta_complete": capture.delta_complete,
        "added": capture.added, "changed": capture.changed, "removed": capture.removed,
        "errors": capture.errors, "limitations": capture.limitations,
        "row_failures": capture.row_failures.iter().map(|r| json!({"phase":r.phase,"name":r.name,"reason":r.reason})).collect::<Vec<_>>(),
        "before_population": population(&capture.before_population),
        "after_population": population(&capture.after_population),
        "rows": capture.after.iter().enumerate().map(|(index, row)| {
            let catalog = context.declaration(&row.name);
            json!({"index":index,"name":row.name,"owned_local":capture.added.contains(&row.name),
                "roles":{"constant":row.constant.is_some(),"inductive":row.inductive.is_some(),"constructor":row.constructor.is_some(),"recursor":row.recursor.is_some(),"quotient":row.quotient.is_some()},
                "constant_kind":row.constant.as_ref().map(|c| format!("{:?}",c.kind)),
                "constant_stored_value":row.constant.as_ref().is_some_and(|c| c.value.is_some()),
                "partial":row.partial,"unsafe":row.unsafe_,"noncomputable":row.noncomputable,
                "implemented_by":row.implemented_by,
                "catalog":match catalog {
                    Ok(c) => json!({"kind":format!("{:?}",c.kind),"body":body_status(&c.body),"type_decoded":c.type_.is_ok(),"level_parameters":c.level_params,"dependencies":c.dependencies,"represented_fields_complete":c.represented_fields_complete,"issues":c.issues}),
                    Err(error) => json!({"error":error.to_string()}),
                }})
        }).collect::<Vec<_>>(),
    }));
    json!({"source":source,"capture_errors":context.capture_errors().iter().map(ToString::to_string).collect::<Vec<_>>(),
        "import_snapshots":context.captures().iter().enumerate().map(|(i,m)|json!({"module_index":i,"selected_cumulative_part":format!("{:?}",m.selected),
            "parts":m.parts.iter().map(|p|json!({"part":format!("{:?}",p.identity.part),"label":p.identity.label,"blake3":p.identity.blake3,
                "borrowed_prefix":p.borrowed_prefix.iter().map(|b|json!({"part":format!("{:?}",b.part),"label":b.label,"blake3":b.blake3})).collect::<Vec<_>>(),
                "source_row_count":p.source_row_count,"error":p.error,"rows":p.rows.iter().map(|r|json!({"index":r.index,"declaration":match &r.declaration {
                    Ok(d)=>json!({"name":d.name,"kind":format!("{:?}",d.kind),"body":body_status(&d.body),"dependencies":d.dependencies,"represented_fields_complete":d.represented_fields_complete,"issues":d.issues}),
                    Err(e)=>json!({"error":e}),
                }})).collect::<Vec<_>>() })).collect::<Vec<_>>() })).collect::<Vec<_>>()})
}

/// Untrusted producer DATA, alongside the unchanged Object/RC diagnostic lane.
/// Neither this construction nor a lossless wire roundtrip earns permission.
fn typed_closure_candidate(
    accepted: &trust_certify::lean_source_batch::AcceptedLeanSourceContext<'_>,
    entry: &Name,
) -> Result<Value, String> {
    let proposal = trust_clean_ir::closure_proposal::propose(
        accepted.environment(),
        accepted.owned_declarations(),
        entry,
    )?;
    let bytes = trust_ir::binary::serialize_module(&proposal.module)
        .map_err(|e| format!("typed closure candidate wire: {e}"))?;
    let decoded = trust_ir::binary::deserialize_module(&bytes)
        .map_err(|e| format!("typed closure candidate wire decode: {e}"))?;
    if decoded != proposal.module {
        return Err("typed closure candidate wire roundtrip changed Module DATA".into());
    }
    Ok(json!({
        "status":"candidate-data",
        "authority":"none-data-only-not-source-refinement",
        "source_closure_sha256":accepted.source_closure_sha256(),
        "owned_declarations_sha256":accepted.owned_declarations_sha256(),
        "complete_owned_roster":accepted.owned_declarations(),
        "originals":proposal.originals.iter().map(|r|json!({
            "constant":r.constant,"function":r.function,"role":r.role
        })).collect::<Vec<_>>(),
        "lifted":{"owner":proposal.lifted_owner,"function":proposal.lifted_function,
            "closure_type":proposal.closure_type,"apparent_signature":proposal.apparent_signature,
            "maker_supplied":proposal.maker_supplied,"capture_parameter_indices":proposal.captures},
        "arithmetic_erasure_proposals":proposal.arithmetic.iter().map(|r|json!({
            "owner":r.owner,"source":r.source,"erased_prefix":r.erased_prefix,
            "generated_function":if r.owner == proposal.lifted_owner {
                Some(proposal.lifted_function)
            } else {
                proposal.originals.iter().find(|f| f.constant.name == r.owner).map(|f|f.function)
            },
            "result":r.result,"operation":r.operation
        })).collect::<Vec<_>>(),
        "module":proposal.module,
        "wire_format":"trust_ir::binary::serialize_module",
        "wire_sha256":format!("{:x}",Sha256::digest(&bytes)),
        "wire_bytes":bytes,
        "limitations":["Untrusted bounded proposal from the actual accepted CIC context; source/body/erasure/capture/convention associations are proposed DATA.",
            "All original and lifted bodies are explicitly Ungated; no carrier, source-refinement, runtime, ABI, object or machine authority.",
            "The existing Object/RC runtime producer and every carrier/object refusal remain unchanged."]
    }))
}

fn produce(
    request: &Request,
    checked: &crate::lean_cli::CheckedLeanBatch,
    capture: &mut OleanClosureCapture,
    report: &mut Value,
) -> Result<Vec<u8>, String> {
    report["context_status"] = json!("unavailable-source-closure-not-accepted");
    let accepted = checked.accepted_context().ok_or(
        "source closure not accepted; external observations cannot grant source admission",
    )?;
    let baseline = accepted
        .runtime_baseline_environment()
        .ok_or("sealed pre-source runtime baseline was not retained")?;
    let (inputs, mut errors) = inputs(capture);
    if let Some(module) = checked.verdicts().iter().flat_map(|v| v.standin_imports()).next() {
        errors.push(format!(
            "source import {module:?} was served by a built-in stand-in; captured .olean bytes cannot replace the checked source context"
        ));
    }
    let records = accepted
        .sources()
        .iter()
        .map(|s| RuntimeSourceRecord {
            module: s.module.clone(),
            path: s.path.clone(),
            source: s.source.clone(),
        })
        .collect();
    let context =
        RuntimeContext::capture_with_environment(inputs, baseline, accepted.environment(), records);
    report["context"] = context_report(&context);
    report["context_status"] = json!("captured-diagnostic-context-not-source-refinement");
    let source = context.environment_capture().expect("environment capture requested");
    // Transport the original accepted payloads before attempting any lowering.
    // The old census's name/role/body-present bits cannot reconstruct a source
    // subject. These are the existing capture's complete rows, not summaries or
    // a newly interpreted source language. Failed/truncated captures still owe
    // the checks below and never obtain a module attachment.
    report["accepted_original"] = json!({
        "schema":"trust.lean.accepted-original-data/v1",
        "authority":"none-data-only-not-source-refinement",
        "source_closure_sha256":accepted.source_closure_sha256(),
        "owned_declarations_sha256":accepted.owned_declarations_sha256(),
        "sources":accepted.sources().iter().map(|s|json!({
            "module":s.module,"path":s.path,"source":s.source
        })).collect::<Vec<_>>(),
        "aliases":accepted.aliases().iter().map(|a|json!({
            "module":a.module,"source_index":a.source_index
        })).collect::<Vec<_>>(),
        "owned_declarations":accepted.owned_declarations(),
        "owned_payloads":source.after.iter().filter(|r|source.added.contains(&r.name)).collect::<Vec<_>>(),
        "capture_delta_complete":source.delta_complete,
        "capture_errors":source.errors,
        "limitations":["Eager accepted original kernel payloads, not a complete runtime or lifted-body universe.",
            "Labels and hashes bind observed data, not a Lean-owned source/IR refinement, ABI or admission proof."]
    });
    if !source.delta_complete
        || source.snapshot_blake3.is_none()
        || !source.errors.is_empty()
        || &source.added != accepted.owned_declarations()
    {
        errors.push(
            "fresh runtime delta does not exactly equal the accepted owned source set".into(),
        );
    }
    if !accepted.owns_declaration(&request.entry) {
        errors.push("entry is not an exact owned local source declaration".into());
    }
    if !errors.is_empty() {
        report["preproduction_errors"] = json!(errors);
        return Err(errors.join("; "));
    }
    report["typed_closure_candidate"] = match typed_closure_candidate(&accepted, &request.entry) {
        Ok(mut candidate) => {
            candidate["environment_snapshot_blake3"] = json!(source.snapshot_blake3);
            candidate
        }
        Err(reason) => json!({"status":"refused-no-candidate",
            "authority":"none-data-only-not-source-refinement","reason":reason}),
    };
    let output = context
        .lower_trust_ir_diagnostic(
            &request.entry,
            RuntimeLimits::default(),
            RuntimeLowering::ExternCalls,
        )
        .map_err(|e| e.to_string())?;
    report["selected_dependency_rows"] = json!(output.captured.rows.iter().map(|r|json!({"name":r.origin.name,"provenance":provenance(&r.origin.provenance),
        "status":match &r.status { RuntimeIrStatus::Lowered(ds)=>json!({"lowered":ds.iter().map(|d|&d.name).collect::<Vec<_>>()}),
            RuntimeIrStatus::TypeFormer=>json!("type-former"),RuntimeIrStatus::CapturedFamilyMetadata=>json!("captured-family-not-admitted"),RuntimeIrStatus::Refused(e)=>json!({"refused":e.to_string()})},
        "specializations":r.specializations.iter().map(|s|json!({"generated_name":s.generated_name,"source":s.source.name,"wrapper":s.wrapper.name,"recursor":s.recursor.name,"family":s.family.name})).collect::<Vec<_>>() })).collect::<Vec<_>>());
    let emitted = output.emission.map_err(|e| e.to_string())?;
    report["emission"] = json!({"mode":"extern-calls","assurance":"diagnostic-only-no-refinement-or-carrier-admission",
        "selected_function_names":emitted.owned_ir.iter().map(|d|&d.name).collect::<Vec<_>>(),
        "named_edge_occurrences":emitted.named_edges.iter().map(|e|json!({"caller":e.caller,"callee":e.callee,"kind":format!("{:?}",e.kind),"supplied":e.supplied})).collect::<Vec<_>>(),
        "dynamic_application_sites":emitted.dynamic_applications,
        "fixed_runtime_imports":emitted.runtime_imports.iter().map(|r|json!({"function_index":r.function_index,"function_id":r.function_id.0,"symbol":r.symbol,
            "calling_convention":format!("{:?}",r.calling_convention),"linkage":format!("{:?}",r.linkage),"parameters":format!("{:?}",r.parameters),"returns":format!("{:?}",r.returns),"variadic":r.variadic})).collect::<Vec<_>>()});
    let bytes = serialize_diagnostic_module(&emitted.module)?;
    // This is the actual existing producer's canonical Rust Module and exact
    // returned artifact, associated in this one invocation with the original
    // payload above. It is not the handquoted logical closure model. In
    // particular Object/RC runtime output does not acquire that model's proof.
    // Serialize fallibly: a data encoding failure must not publish a partial
    // or supposedly attached artifact.
    let module = serde_json::to_value(&emitted.module)
        .map_err(|error| format!("diagnostic module data encoding refused: {error}"))?;
    report["module_attachment"] = json!({
        "schema":"trust.lean.produced-module-data/v1",
        "authority":"none-data-only-not-source-refinement",
        "source_closure_sha256":accepted.source_closure_sha256(),
        "owned_declarations_sha256":accepted.owned_declarations_sha256(),
        "module":module,
        "wire_format":"raw-tMBC-current-clean-emitter",
        "wire_sha256":format!("{:x}",Sha256::digest(&bytes)),
        "wire_bytes":bytes,
        "publication":"candidate-data-not-publication-or-postflight-attestation",
        "limitations":["Existing diagnostic Object/RC producer output, not the logical closure quotation.",
            "No Lean-owned source/decoded-module relation, physical closure layout, runtime, ABI, object or admission authority."]
    });
    Ok(bytes)
}

fn serialize_diagnostic_module(module: &trust_ir::Module) -> Result<Vec<u8>, String> {
    serialize_tmbc(module)
        .map_err(|error| format!("diagnostic runtime Trust-IR serialization refused: {error}"))
}

fn postflight_errors(
    checked: &crate::lean_cli::CheckedLeanBatch,
    captured: &OleanClosureCapture,
    before: &Value,
) -> (Vec<String>, Value) {
    let mut errors = captured.recheck_paths();
    for source in checked.sources() {
        match (source.source(), std::fs::read(source.path())) {
            (Ok(expected), Ok(bytes)) if bytes == expected.as_bytes() => {}
            (Err(_), _) => {}
            _ => errors
                .push(format!("checked source path/bytes changed: {}", source.path().display())),
        }
    }
    let after = crate::lean_cli::census::tool_identity().unwrap_or_else(|e| json!({"error":e}));
    if before != &after {
        errors.push("current executable path observation changed".into());
    }
    (errors, after)
}

// Preserve the production result while applying the independent path/tool checks.
fn with_postflight_refusals(
    result: Result<Vec<u8>, String>,
    postflight: &[String],
) -> Result<Vec<u8>, String> {
    if postflight.is_empty() {
        result
    } else {
        let postflight = postflight.join("; ");
        match result {
            Ok(_) => Err(postflight),
            Err(error) => Err(format!("{error}; postflight checks also refused: {postflight}")),
        }
    }
}

fn build_with_census_writer(
    request: &Request,
    write_census: impl FnOnce(&Path, &Value) -> Result<(), String>,
) -> Result<(), String> {
    let path = request.build.census_output.as_ref().expect("parser requires census");
    super::ensure_new_output(&request.build.output)?;
    crate::lean_cli::preflight_census(path)?;
    crate::lean_cli::census::distinct_outputs(path, &request.build.output)?;
    let before = crate::lean_cli::census::tool_identity()?;
    let checked =
        crate::lean_cli::check_batch_for_runtime(std::slice::from_ref(&request.build.input));
    let mut captured = crate::lean_cli::census::capture_external(
        &checked,
        &request.build.olean_paths,
        &[path, &request.build.output],
    )?;
    let mut runtime = json!({"schema":"trust.lean.diagnostic-runtime-build/v1","entry":request.entry,
        "authority":"none-diagnostic-computation-only","population":"all-observed-eager-local-and-captured-import-rows-not-emitted-denominator",
        "limitations":["Not a gated LibraryEnvelope, executable, G4 carrier proof or source/runtime refinement.",
            "The selected exact named call/PAP closure may emit while generic or unselected rows remain unresolved; this is not whole-file compilation completeness.",
            "Implicit/lazy/native runtime dependencies and whole runtime reachability remain unmeasured.",
            "Fresh partial declarations without stored runtime values remain missing bodies; they are not converted to extern stubs.",
            "Strict source policy may reject a bodyless partial header before runtime capture. Its kernel census row remains observed; no rejected/tainted Environment is exposed or claimed captured.",
            "Logical environment and raw import mirrors are not silently prioritized; exact overlapping identities currently refuse.",
            "Object-only conservative ownership and fixed C runtime ABI; downstream execution requires separate evidence.",
            "Path/tool checks are observations, not an atomic filesystem or loaded-image attestation."]});
    let result = produce(request, &checked, &mut captured, &mut runtime);
    let (postflight, after) = postflight_errors(&checked, &captured, &before);
    let result = with_postflight_refusals(result, &postflight);
    runtime["postflight_errors"] = json!(postflight);
    runtime["status"] = json!(if result.is_ok() {
        "diagnostic-artifact-candidate-not-yet-published"
    } else {
        "refused-no-artifact"
    });
    runtime["error"] = json!(result.as_ref().err());
    runtime["candidate_artifact"] = match &result {
        Ok(bytes) => {
            json!({"sha256":format!("{:x}",Sha256::digest(bytes)),"bytes":bytes.len(),"format":"raw-tMBC-current-clean-emitter","publication":"not-observed-by-this-prepublication-receipt"})
        }
        Err(_) => Value::Null,
    };
    let mut report = crate::lean_cli::census::report(
        &checked,
        std::slice::from_ref(&request.build.input),
        "diagnostic-runtime-build",
        &before,
        &after,
    );
    report["external_olean_observation"] =
        serde_json::to_value(&captured.observation).map_err(|e| e.to_string())?;
    report["diagnostic_runtime"] = runtime;
    write_census(path, &report)?;
    let bytes = result?;
    let parent = request
        .build
        .output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let mut temp = tempfile::NamedTempFile::new_in(parent).map_err(|e| e.to_string())?;
    temp.write_all(&bytes).map_err(|e| e.to_string())?;
    temp.as_file().sync_all().map_err(|e| e.to_string())?;
    let (late_errors, _) = postflight_errors(&checked, &captured, &before);
    if !late_errors.is_empty() {
        return Err(format!(
            "diagnostic publication refused after census write: {}",
            late_errors.join("; ")
        ));
    }
    temp.persist_noclobber(&request.build.output).map_err(|e| {
        format!("diagnostic publication refused (existing bytes preserved): {}", e.error)
    })?;
    Ok(())
}

fn build(request: &Request) -> Result<(), String> {
    build_with_census_writer(request, crate::lean_cli::write_census)
}

pub(super) fn run(args: &[String]) -> ExitCode {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let request = match parse(args) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match build(&request) {
        Ok(()) => {
            println!(
                "wrote {}: DIAGNOSTIC runtime Trust-IR only; no carrier/refinement admission, complete runtime closure, or executable claim",
                request.build.output.display()
            );
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("error: diagnostic runtime build refused: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests;
