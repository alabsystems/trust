// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! WS5.5 step 7 — the ZERO-AUTHORITY contract-carry shadow.
//!
//! Precedent: `TRUST_DIRECT_FORMULA_DUMP` (Step 6 increment 2 of
//! `docs/design/DIRECT-LANE-PROOF-AUTHORITY.md`). Behind
//! [`TRUST_CONTRACT_CARRY_SHADOW_ENV`]`=<dir>`, after the crate finalizer has
//! published its module, this:
//!
//! 1. drains the session's [`ContractCarryRegistry`] (filled by the mainline
//!    lowering whether or not the shadow runs);
//! 2. CLONES the published module (`crate_module::with_published_crate_module`);
//! 3. installs the staged carry on the clone ([`install_contract_obligations`]);
//! 4. judges the clone: `trust_ir_build::validate_module`,
//!    `validate_module_with_authority` and `validate_linked_module` (both under
//!    `RejectingModuleProofAuthority`), the staged rung
//!    ([`contract_bound_inventory_errors`]), and the LIVE tier
//!    (`inventory_errors_at_tier(.., DIRECT_OBLIGATION_CAPABILITY.tier())`),
//!    which MUST refuse the clone as long as the owner flip (DG-60) has not
//!    landed; checks the carry survives the artifact encodings (binary round
//!    trip of rows and summaries; no text-companion loss); and runs the
//!    reference interpreter on every zero-argument integer-valued direct body;
//! 5. projects exactly matched authored postconditions through the shared
//!    typed query and native request builders, retaining Pending rows,
//!    unanchored direct-input disclosure and no source-generation authority;
//! 6. writes `<dir>/<crate>.contract-carry.shadow.json` atomically. The shadow
//!    emits diagnostic questions only and runs no solver.
//!
//! It changes NO artifact and NO verdict: the published module is only read
//! (the clone is dropped), nothing is pushed into the finalizer's errors, and
//! an I/O failure is a warning on stderr. Unset, it costs one env read.
//!
//! # Resolving a body to its FuncId — the one place this differs from the flip
//!
//! The finalizer's install (the owner flip) gets assemble pass 1's `assigned`
//! map. The published module does not expose it, so the shadow resolves each
//! registered body by the assembler's own naming rule
//! (`crate_module::emitted_definition_name`: the def path, or
//! `!trust_definition::<def path>::<suffix>` on a name collision; or a
//! `display_path` equal to the def path), among `Producer::TRust` bodies, and
//! requires a UNIQUE match. A body that does not resolve uniquely is reported
//! unresolved and carried nowhere — never matched by guess. The install's own
//! self-checks (arity, loop-header re-resolution) then run on the resolved
//! function as they will at the flip.

use std::collections::BTreeMap;
use std::io::Write as _;
use std::path::{Path, PathBuf};

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LOCAL_CRATE;
use trust_ir::interpret::{InterpretValueKind, Interpreter};
use trust_ir::proof::{ClausePlace, ClauseSort, ProofFormula, RejectingModuleProofAuthority};
use trust_ir::{FuncId, Module, Producer};

use crate::contract_carry::{
    CONTRACT_BOUND_MARKER, CONTRACT_SOURCE_ID, ContractCarryRegistry, ContractInstallOutcome,
    TRUST_CONTRACT_CARRY_SHADOW_ENV, contract_bound_inventory_errors, install_contract_obligations,
};
use crate::crate_module::DIRECT_OBLIGATION_CAPABILITY;

/// The sidecar's schema tag.
pub const SHADOW_SCHEMA: &str = "trust.contract-carry.shadow/v1";

/// Run the shadow if [`TRUST_CONTRACT_CARRY_SHADOW_ENV`] names a directory.
/// Read fresh per call (no `OnceLock`), like `TRUST_DIRECT_FORMULA_DUMP`.
pub fn run(tcx: TyCtxt<'_>) {
    let Some(dir) = std::env::var_os(TRUST_CONTRACT_CARRY_SHADOW_ENV).map(PathBuf::from) else {
        return;
    };
    let registry = tcx.sess.with_trust_compiler_state::<ContractCarryRegistry, _>(std::mem::take);
    let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
    // Clone under the session lock, judge outside it.
    let published = crate::crate_module::with_published_crate_module(tcx.sess, |published| {
        published.map(|p| p.module().clone()).map_err(str::to_string)
    });
    let report = match published {
        Ok(module) => {
            let queries = registry
                .bodies
                .keys()
                .map(|index| {
                    let def = rustc_span::def_id::DefId {
                        krate: LOCAL_CRATE,
                        index: rustc_span::def_id::DefIndex::from_u32(*index),
                    };
                    let converted = trust_mir_extract::convert_trust_contract_bundle(
                        tcx,
                        &tcx.trust_contracts(def),
                    )
                    .map_err(|error| format!("{error:?}"));
                    (*index, converted)
                })
                .collect();
            shadow_report_with_native(&crate_name, module, registry, &queries)
        }
        Err(reason) => unpublished_report(&crate_name, &reason, &registry),
    };
    if let Err(error) = write_atomically(&dir, &crate_name, &report) {
        eprintln!(
            "warning: {TRUST_CONTRACT_CARRY_SHADOW_ENV}={}: failed to write the contract-carry \
             shadow for crate `{crate_name}`: {error} (zero-authority disclosure only; no \
             artifact or verdict is affected)",
            dir.display()
        );
    }
}

/// One registered body and the FuncId it resolved to, or why not.
struct Resolution {
    def_index: u32,
    def_path: String,
    resolved: Result<FuncId, String>,
}

/// Independent images of the original typed query, before the staged install.
struct PostconditionImage {
    def_index: u32,
    ordinal: u32,
    assertion_id: String,
    carried: Option<ProofFormula>,
    typed: Option<trust_types::CompilerContractProposition>,
}

fn resolve(module: &Module, registry: &ContractCarryRegistry) -> Vec<Resolution> {
    let mut out: Vec<Resolution> = registry
        .bodies
        .values()
        .map(|body| {
            let collided = format!("!trust_definition::{}::", body.def_path);
            let candidates: Vec<FuncId> = module
                .functions
                .iter()
                .filter(|f| f.producer == Some(Producer::TRust) && !f.is_declaration())
                .filter(|f| {
                    f.name == body.def_path
                        || f.name.starts_with(&collided)
                        || f.display_path.as_deref() == Some(body.def_path.as_str())
                })
                .map(|f| f.id)
                .collect();
            let resolved = match candidates[..] {
                [fid] => Ok(fid),
                [] => Err("no Producer::TRust body carries this def path".to_string()),
                _ => Err(format!("{} bodies carry this def path", candidates.len())),
            };
            Resolution { def_index: body.def_index, def_path: body.def_path.clone(), resolved }
        })
        .collect();
    // Two bodies may never share one function.
    let fids: Vec<FuncId> = out.iter().filter_map(|r| r.resolved.clone().ok()).collect();
    for resolution in &mut out {
        if let Ok(fid) = resolution.resolved {
            if fids.iter().filter(|other| **other == fid).count() > 1 {
                resolution.resolved =
                    Err(format!("FuncId {} is claimed by two bodies", fid.index()));
            }
        }
    }
    out
}

fn shadow_report(crate_name: &str, module: Module, registry: ContractCarryRegistry) -> String {
    shadow_report_with_native(crate_name, module, registry, &BTreeMap::new())
}

fn shadow_report_with_native(
    crate_name: &str,
    mut module: Module,
    registry: ContractCarryRegistry,
    queries: &BTreeMap<u32, Result<trust_types::CompilerContractBundle, String>>,
) -> String {
    let resolutions = resolve(&module, &registry);
    let duplicates = registry.duplicate_def_indices.clone();
    let mut assigned: Vec<(u32, FuncId)> = resolutions
        .iter()
        .filter_map(|r| r.resolved.as_ref().ok().map(|fid| (r.def_index, *fid)))
        .collect();
    assigned.sort_by_key(|(def_index, _)| *def_index);
    // Retain the emission-time query images independently of the installed
    // module. The bridge compares them before changing either representation.
    let mut postconditions = Vec::new();
    for body in registry.bodies.values() {
        for clause in body
            .clauses
            .iter()
            .filter(|clause| clause.role == crate::contract_carry::ClauseRole::Ensures)
        {
            let expected = assigned
                .binary_search_by_key(&body.def_index, |(index, _)| *index)
                .ok()
                .and_then(|index| module.function_by_id(assigned[index].1))
                .and_then(|function| module.func_type(function.ty))
                .map(|signature| {
                    crate::contract_carry::carry_clause(
                        clause,
                        &crate::contract_carry::ClauseContext {
                            params: &body.params,
                            binding_refusal: body.binding_refusal,
                            param_tys: &signature.params,
                            return_tys: &signature.returns,
                            pointer_bits: module
                                .target_info
                                .as_ref()
                                .map(|target| target.pointer_size.saturating_mul(8)),
                            header: None,
                        },
                    )
                    .formula
                });
            let typed = match &clause.predicate {
                rustc_middle::mir::trust_contract::TrustContractPredicateKind::Typed {
                    text,
                    proposition,
                } => {
                    trust_mir_extract::trust_contract_proposition_to_formula_and_domains_for_class(
                        proposition,
                        trust_types::CompilerContractExpressionClass::Proposition,
                    )
                    .ok()
                    .map(|(formula, variable_domains)| {
                        trust_types::CompilerContractProposition {
                            source_contract_index: clause.ordinal as usize,
                            kind: trust_types::ContractKind::Ensures,
                            body: text.to_string(),
                            formula,
                            variable_domains,
                        }
                    })
                }
                _ => None,
            };
            postconditions.push(PostconditionImage {
                def_index: body.def_index,
                ordinal: clause.ordinal,
                assertion_id: crate::contract_carry::clause_assertion_id(
                    crate_name,
                    &body.def_path,
                    clause.role,
                    clause.ordinal,
                    clause.loop_key,
                ),
                carried: expected,
                typed,
            });
        }
    }
    let mut install_errors = Vec::new();
    let outcome = install_contract_obligations(
        &mut module,
        crate_name,
        &assigned,
        registry,
        &mut install_errors,
    );

    let validate_module: Vec<String> =
        trust_ir_build::validate_module(&module).iter().map(|e| format!("{e:?}")).collect();
    let validate_authority: Vec<String> =
        trust_ir_build::validate_module_with_authority(&module, &RejectingModuleProofAuthority)
            .iter()
            .map(|e| format!("{e:?}"))
            .collect();
    let set = trust_ir_build::ModuleSet::new([]);
    let linked =
        trust_ir_build::validate_linked_module(&module, &set, &RejectingModuleProofAuthority);
    let validate_linked: Vec<String> = linked.errors().iter().map(|e| format!("{e:?}")).collect();
    let text_losses: Vec<String> =
        trust_ir::text_loss::text_losses(&module).iter().map(|l| format!("{l:?}")).collect();
    // An unencodable module (`serialize_module` refuses it) is a failed round trip, never a pass.
    let binary_round_trip = match trust_ir::binary::serialize_module(&module)
        .map_err(|_| ())
        .and_then(|bytes| trust_ir::binary::deserialize_module(&bytes).map_err(|_| ()))
    {
        Ok(decoded) => {
            decoded.proof_obligations == module.proof_obligations
                && decoded
                    .functions
                    .iter()
                    .map(|f| &f.summary)
                    .eq(module.functions.iter().map(|f| &f.summary))
        }
        Err(_) => false,
    };
    let staged = contract_bound_inventory_errors(&module);
    let live = crate::direct_obligations::inventory_errors_at_tier(
        &module,
        DIRECT_OBLIGATION_CAPABILITY.tier(),
    );

    let mut out = String::new();
    out.push_str("{\n");
    field(&mut out, "schema", &string(SHADOW_SCHEMA));
    field(&mut out, "crate", &string(crate_name));
    field(
        &mut out,
        "authority",
        &string(
            "NONE: a staged carry installed on a CLONE of the published module; the published \
             module, its artifacts and every verdict are unchanged",
        ),
    );
    field(&mut out, "published", "true");
    field(&mut out, "staged_marker", &string(CONTRACT_BOUND_MARKER));
    field(&mut out, "live_marker", &string(DIRECT_OBLIGATION_CAPABILITY.marker()));
    field(&mut out, "duplicate_registrations", &format!("{duplicates:?}"));
    field(&mut out, "resolution", &array(resolutions.iter().map(resolution_json)));
    field(&mut out, "outcome", &outcome_json(&outcome));
    field(&mut out, "install_errors", &array(install_errors.iter().map(|e| string(e))));
    field(&mut out, "validate_module", &array(validate_module.iter().map(|e| string(e))));
    field(
        &mut out,
        "validate_module_with_authority",
        &array(validate_authority.iter().map(|e| string(e))),
    );
    field(&mut out, "validate_linked_module", &array(validate_linked.iter().map(|e| string(e))));
    field(&mut out, "text_losses", &array(text_losses.iter().map(|e| string(e))));
    field(&mut out, "binary_round_trip", if binary_round_trip { "true" } else { "false" });
    field(&mut out, "staged_rung_errors", &array(staged.iter().map(|e| string(e))));
    field(&mut out, "live_tier_refuses", if live.is_empty() { "false" } else { "true" });
    field(&mut out, "live_tier_errors", &live.len().to_string());
    field(&mut out, "summaries", &array(summaries_json(&module).into_iter()));
    field(&mut out, "rows", &array(rows_json(&module).into_iter()));
    let native = if queries.is_empty() {
        serde_json::json!({"status": "not_requested", "authority": "NONE"})
    } else if !install_errors.is_empty() || !validate_module.is_empty() {
        serde_json::json!({"status": "refused", "reason": "staged installation or semantic validation failed", "authority": "NONE"})
    } else {
        match native_postcondition_inputs(crate_name, &module, &postconditions, queries) {
            Ok((public, bindings)) => {
                match trust_ir_bridge::direct_contract_shadow_verification_bundle(
                    module.clone(),
                    &public,
                    &bindings,
                ) {
                    Ok(shadow) => serde_json::json!({
                        "status": "questions", "authority": "NONE", "public": public,
                        "bundle": shadow.bundle(),
                        "pristine_module_digest": shadow.disclosure.pristine_module_digest,
                        "non_applying_checks": shadow.disclosure.non_applying_checks,
                    }),
                    Err(reason) => {
                        serde_json::json!({"status": "refused", "reason": reason, "authority": "NONE"})
                    }
                }
            }
            Err(reason) => {
                serde_json::json!({"status": "refused", "reason": reason, "authority": "NONE"})
            }
        }
    };
    field(&mut out, "native_wp", &native.to_string());
    last_field(&mut out, "interpreted", &array(interpreted_json(&module).into_iter()));
    out.push_str("}\n");
    out
}

/// Project the actual compiler query through the shared typed emitter. The
/// installed carry supplies typed places; no MIR, text parser or assumptions
/// are consulted by this diagnostic question producer.
fn native_postcondition_inputs(
    crate_name: &str,
    module: &Module,
    postconditions: &[PostconditionImage],
    queries: &BTreeMap<u32, Result<trust_types::CompilerContractBundle, String>>,
) -> Result<
    (trust_verifier_api::TrustContractBundle, Vec<trust_ir_bridge::DirectContractShadowQuestion>),
    String,
> {
    use trust_verifier_api::{
        BundleSubject, ContractKind, MetadataEntry, ObligationKind, SourceLocation, TrustContract,
        TrustContractBundle, TrustObligation,
    };
    // The query is the denominator, including an ensures clause the retained
    // emission registry accidentally omitted. Never shrink to the old subset.
    for (index, query) in queries {
        let query = query.as_ref().map_err(Clone::clone)?;
        if query
            .contracts
            .iter()
            .any(|contract| contract.kind != trust_types::ContractKind::Ensures)
            || !query.loop_contracts.is_empty()
            || !query.proof_items.is_empty()
            || query.typed_propositions.len() != query.contracts.len()
        {
            return Err("direct native questions require a complete ensures-only query".into());
        }
        let actual: std::collections::BTreeSet<_> = query
            .contracts
            .iter()
            .enumerate()
            .filter(|(_, contract)| contract.kind == trust_types::ContractKind::Ensures)
            .map(|(ordinal, _)| ordinal as u32)
            .collect();
        let retained: Vec<_> = postconditions
            .iter()
            .filter(|image| &image.def_index == index)
            .map(|image| image.ordinal)
            .collect();
        let unique: std::collections::BTreeSet<_> = retained.iter().copied().collect();
        if retained.len() != unique.len() || actual != unique {
            return Err("direct emission/query postcondition inventory differs".into());
        }
    }
    let mut public = TrustContractBundle::empty(
        format!("direct-contract-shadow:{crate_name}"),
        BundleSubject::Crate { name: crate_name.into() },
    );
    let mut bindings = Vec::new();
    for image in postconditions {
        let PostconditionImage { def_index, ordinal, assertion_id, carried, typed } = image;
        let query = queries
            .get(def_index)
            .ok_or("missing direct query snapshot")?
            .as_ref()
            .map_err(Clone::clone)?;
        let contract = query
            .contracts
            .get(*ordinal as usize)
            .ok_or("direct postcondition query lost its dense ordinal")?;
        if typed.is_none() || query.typed_proposition(*ordinal as usize, contract) != typed.as_ref()
        {
            return Err("direct typed query differs from its emission image".into());
        }
        let (predicate, unsupported, _) =
            trust_source_contract::compiler_typed_contract_predicate(query, *ordinal as usize)
                .ok_or("direct postcondition has no exactly bound typed compiler query")?;
        if let Some(reason) = unsupported {
            return Err(reason);
        }
        if contract.kind != trust_types::ContractKind::Ensures {
            return Err("direct postcondition query ordinal names another clause kind".into());
        }
        let matches: Vec<_> = module
            .proof_obligations
            .iter()
            .filter(|row| {
                row.source.as_ref().is_some_and(|source| {
                    source.source_id == CONTRACT_SOURCE_ID && &source.assertion_id == assertion_id
                })
            })
            .collect();
        let [row] = matches[..] else {
            return Err("direct postcondition install correspondence is not unique".into());
        };
        let formula = row.formula.as_ref().ok_or("direct postcondition lost its carry")?;
        if carried.as_ref() != Some(formula) {
            return Err("installed direct clause differs from its emission query image".into());
        }
        let id =
            format!("direct-contract:{}", trust_types::stable_sha256_hex(assertion_id.as_bytes()));
        let contract_id = format!("{id}:ensures");
        let span = &contract.span;
        let location = SourceLocation {
            file: Some(span.file.clone()),
            line: Some(span.line_start),
            column: Some(span.col_start),
            end_line: Some(span.line_end),
            end_column: Some(span.col_end),
        };
        public.contracts.push(TrustContract {
            contract_id: contract_id.clone(),
            kind: ContractKind::Ensures,
            predicate,
            source: location.clone(),
            metadata: vec![MetadataEntry {
                key: trust_verifier_api::TRUST_IR_CLAUSE_BINDINGS_METADATA_KEY.into(),
                value: serde_json::to_string(&formula.bindings)
                    .map_err(|error| error.to_string())?,
            }],
        });
        public.obligations.push(TrustObligation {
            obligation_id: id.clone(),
            kind: ObligationKind::Postcondition,
            contract_id: Some(contract_id),
            proof_item_id: None,
            source: location,
            description: row.description.clone(),
            required_strength: None,
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        });
        bindings.push(trust_ir_bridge::DirectContractShadowQuestion {
            proof_id: row.id,
            public_obligation_id: id,
            assertion_id: assertion_id.clone(),
            carried_clause: formula.clone(),
            public_semantic_digest: String::new(),
        });
    }
    for question in &mut bindings {
        let row = public
            .obligations
            .iter()
            .find(|row| row.obligation_id == question.public_obligation_id)
            .ok_or("direct query inventory lost its postcondition")?;
        question.public_semantic_digest =
            public.canonical_obligation_semantic_digest_sha256(row)?;
    }
    Ok((public, bindings))
}

fn unpublished_report(crate_name: &str, reason: &str, registry: &ContractCarryRegistry) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    field(&mut out, "schema", &string(SHADOW_SCHEMA));
    field(&mut out, "crate", &string(crate_name));
    field(&mut out, "published", "false");
    field(&mut out, "registered_bodies", &registry.bodies.len().to_string());
    last_field(&mut out, "reason", &string(reason));
    out.push_str("}\n");
    out
}

fn resolution_json(r: &Resolution) -> String {
    let resolved = match &r.resolved {
        Ok(fid) => format!("\"function\":{}", fid.index()),
        Err(why) => format!("\"unresolved\":{}", string(why)),
    };
    format!("{{\"def_index\":{},\"def_path\":{},{resolved}}}", r.def_index, string(&r.def_path))
}

fn outcome_json(o: &ContractInstallOutcome) -> String {
    let opaque = array(o.opaque.iter().map(|(def_path, role, ordinal, reason)| {
        format!(
            "{{\"def_path\":{},\"role\":{},\"ordinal\":{ordinal},\"reason\":{}}}",
            string(def_path),
            string(role),
            string(reason)
        )
    }));
    format!(
        "{{\"bodies_installed\":{},\"bodies_skipped_unspliced\":{},\"bodies_withheld\":{},\
         \"summaries_installed\":{},\"rows_installed\":{},\"loop_rows_withheld\":{},\
         \"clauses_typed\":{},\"clauses_opaque\":{},\"opaque\":{opaque}}}",
        o.bodies_installed,
        o.bodies_skipped_unspliced,
        o.bodies_withheld,
        o.summaries_installed,
        o.rows_installed,
        o.loop_rows_withheld,
        o.clauses_typed,
        o.clauses_opaque,
    )
}

fn sort_json(sort: &ClauseSort) -> String {
    match sort {
        ClauseSort::Bool => string("Bool"),
        ClauseSort::Int => string("Int"),
        ClauseSort::BitVec(width) => string(&format!("BitVec({width})")),
        ClauseSort::Float { eb, sb } => string(&format!("Float({eb},{sb})")),
        other => string(&format!("{other:?}")),
    }
}

fn place_json(place: &ClausePlace) -> String {
    match place {
        ClausePlace::Param { index } => format!("{{\"param\":{index}}}"),
        ClausePlace::ResultSlot { index } => format!("{{\"result\":{index}}}"),
        ClausePlace::MutParamExit { index } => format!("{{\"mut_param_exit\":{index}}}"),
        ClausePlace::Value(value) => format!("{{\"value\":{}}}", value.index()),
        other => format!("{{\"other\":{}}}", string(&format!("{other:?}"))),
    }
}

fn formula_json(formula: &ProofFormula) -> String {
    let bindings = array(formula.bindings.iter().map(|(name, binding)| {
        format!(
            "{{\"name\":{},\"sort\":{},\"place\":{}}}",
            string(name),
            sort_json(&binding.sort),
            place_json(&binding.place)
        )
    }));
    format!(
        "{{\"schema\":{},\"payload\":{},\"smtlib\":{},\"bindings\":{bindings}}}",
        string(&formula.schema),
        string(&formula.payload),
        formula.smtlib.as_deref().map_or_else(|| "null".to_string(), string),
    )
}

fn summaries_json(module: &Module) -> Vec<String> {
    module
        .functions
        .iter()
        .filter_map(|f| {
            let summary = f.summary.as_ref()?;
            let list = |clauses: &[ProofFormula]| array(clauses.iter().map(formula_json));
            Some(format!(
                "{{\"function\":{},\"name\":{},\"display_path\":{},\"params\":{},\"proved\":{},\
                 \"backed_by\":{},\"requires\":{},\"ensures\":{},\"decreases\":{}}}",
                f.id.index(),
                string(&f.name),
                display_path_json(f),
                array(summary.params.iter().map(|p| string(p))),
                summary.proved,
                if summary.backed_by.is_some() { "\"present\"" } else { "null" },
                list(&summary.requires),
                list(&summary.ensures),
                list(&summary.decreases),
            ))
        })
        .collect()
}

fn rows_json(module: &Module) -> Vec<String> {
    module
        .proof_obligations
        .iter()
        .filter(|row| row.source.as_ref().is_some_and(|s| s.source_id == CONTRACT_SOURCE_ID))
        .map(|row| {
            let site = row.site.map_or_else(
                || "null".to_string(),
                |site| {
                    format!(
                        "{{\"function\":{},\"block\":{},\"inst\":{}}}",
                        site.function.index(),
                        site.block.index(),
                        site.inst_index
                    )
                },
            );
            format!(
                "{{\"id\":{},\"kind\":{},\"status\":{},\"function\":{},\"assertion_id\":{},\
                 \"site\":{site},\"formula\":{}}}",
                row.id.index(),
                string(&format!("{:?}", row.kind)),
                string(&row.status.to_string()),
                row.function.map_or_else(|| "null".to_string(), |f| f.index().to_string()),
                string(&row.source.as_ref().map_or(String::new(), |s| s.assertion_id.clone())),
                row.formula.as_ref().map_or_else(|| "null".to_string(), formula_json),
            )
        })
        .collect()
}

/// The reference interpreter on every zero-argument integer-valued direct
/// body of the clone (the fixtures' `program`), with the default fuel.
fn interpreted_json(module: &Module) -> Vec<String> {
    let interpreter = Interpreter::with_module(module);
    module
        .functions
        .iter()
        .filter(|f| f.producer == Some(Producer::TRust) && !f.is_declaration())
        .filter(|f| {
            module.func_type(f.ty).is_some_and(|ft| {
                ft.params.is_empty() && matches!(&ft.returns[..], [ty] if ty.is_integer())
            })
        })
        .take(64)
        .map(|f| {
            let value = match interpreter.execute_func(f.id, Vec::new()) {
                Ok(outcome) => match &outcome.returns[..] {
                    [value] => match &value.kind {
                        InterpretValueKind::Int(int) => {
                            format!("{{\"raw\":{}}}", string(&int.raw.to_string()))
                        }
                        other => format!("{{\"error\":{}}}", string(&format!("{other:?}"))),
                    },
                    other => {
                        format!("{{\"error\":{}}}", string(&format!("{} results", other.len())))
                    }
                },
                Err(error) => format!("{{\"error\":{}}}", string(&format!("{:?}", error.code))),
            };
            format!(
                "{{\"function\":{},\"name\":{},\"display_path\":{},\"value\":{value}}}",
                f.id.index(),
                string(&f.name),
                display_path_json(f),
            )
        })
        .collect()
}

/// WS5.2: `Function.name` is the link-time symbol; the def path a reader looks a function up
/// by is its `display_path` (`null` when the producer recorded none).
fn display_path_json(f: &trust_ir::Function) -> String {
    f.display_path.as_deref().map_or_else(|| "null".to_string(), string)
}

fn string(s: &str) -> String {
    format!("\"{}\"", crate::clean_origin_join::json_escape_min(s))
}

fn array(items: impl Iterator<Item = String>) -> String {
    let items: Vec<String> = items.collect();
    if items.is_empty() {
        "[]".to_string()
    } else {
        format!("[\n    {}\n  ]", items.join(",\n    "))
    }
}

fn field(out: &mut String, key: &str, value: &str) {
    out.push_str(&format!("  \"{key}\": {value},\n"));
}

fn last_field(out: &mut String, key: &str, value: &str) {
    out.push_str(&format!("  \"{key}\": {value}\n"));
}

/// One complete file per crate: O_EXCL temp, then rename (last writer wins).
fn write_atomically(dir: &Path, crate_name: &str, content: &str) -> std::io::Result<PathBuf> {
    let final_path = dir.join(format!("{crate_name}.contract-carry.shadow.json"));
    let mut attempt = 0u32;
    let (temp_path, mut file) = loop {
        let candidate = dir.join(format!(
            ".{crate_name}.contract-carry.shadow.json.tmp.{}.{attempt}",
            std::process::id()
        ));
        match std::fs::OpenOptions::new().write(true).create_new(true).open(&candidate) {
            Ok(file) => break (candidate, file),
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists && attempt < 1024 => {
                attempt += 1;
            }
            Err(err) => return Err(err),
        }
    };
    let written = file.write_all(content.as_bytes()).and_then(|()| file.flush());
    drop(file);
    if let Err(err) = written {
        let _ = std::fs::remove_file(&temp_path);
        return Err(err);
    }
    if let Err(err) = std::fs::rename(&temp_path, &final_path) {
        let _ = std::fs::remove_file(&temp_path);
        return Err(err);
    }
    Ok(final_path)
}

#[cfg(test)]
mod native_question_tests {
    use trust_types::{
        CompilerContractBundle, CompilerContractProposition, Contract, ContractKind, Formula,
        SourceSpan,
    };

    use super::*;

    fn bool_query(value: bool) -> (CompilerContractBundle, CompilerContractProposition) {
        let body = format!("__trust_lowered_compiler_contract__:{value}");
        let contract = Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: body.clone(),
        };
        let proposition = CompilerContractProposition {
            source_contract_index: 0,
            kind: ContractKind::Ensures,
            body,
            formula: Formula::Bool(value),
            variable_domains: Vec::new(),
        };
        let query = CompilerContractBundle::new(vec![contract])
            .with_typed_propositions(vec![proposition.clone()]);
        assert_eq!(query.typed_proposition(0, &query.contracts[0]), Some(&proposition));
        (query, proposition)
    }

    #[test]
    fn native_questions_refuse_a_query_ensures_missing_from_the_emission_inventory() {
        let (query, _) = bool_query(true);
        let queries = BTreeMap::from([(7, Ok(query))]);
        // The query is a nonempty denominator even when nothing was retained.
        let error =
            native_postcondition_inputs("inventory", &Module::new("inventory"), &[], &queries)
                .unwrap_err();
        assert_eq!(error, "direct emission/query postcondition inventory differs");
    }

    #[test]
    fn native_questions_refuse_a_changed_valid_typed_query_at_the_same_ordinal() {
        let (_, emission_proposition) = bool_query(true);
        let (changed_query, changed_proposition) = bool_query(false);
        assert_eq!(
            emission_proposition.source_contract_index,
            changed_proposition.source_contract_index,
        );
        assert_eq!(emission_proposition.kind, changed_proposition.kind);
        assert_ne!(emission_proposition, changed_proposition);
        let retained = [PostconditionImage {
            def_index: 7,
            ordinal: 0,
            assertion_id: "inventory::subject#ensures#c0".into(),
            carried: None,
            typed: Some(emission_proposition),
        }];
        let queries = BTreeMap::from([(7, Ok(changed_query))]);
        // Both query snapshots are internally valid and keep the same inventory.
        // Refuse their mismatch before consulting any installed formula or row.
        let error = native_postcondition_inputs(
            "inventory",
            &Module::new("inventory"),
            &retained,
            &queries,
        )
        .unwrap_err();
        assert_eq!(error, "direct typed query differs from its emission image");
    }

    fn assert_omitted_query_lane_refused(
        query: CompilerContractBundle,
        ensures: CompilerContractProposition,
    ) {
        assert_eq!(query.typed_proposition(0, &query.contracts[0]), Some(&ensures));
        let retained = [PostconditionImage {
            def_index: 7,
            ordinal: 0,
            assertion_id: "inventory::subject#ensures#c0".into(),
            carried: None,
            typed: Some(ensures),
        }];
        let queries = BTreeMap::from([(7, Ok(query))]);
        // Only the valid Ensures was retained. The compiler query still owns
        // the omitted lane, so reject it before any installed-row lookup.
        let error = native_postcondition_inputs(
            "inventory",
            &Module::new("inventory"),
            &retained,
            &queries,
        )
        .unwrap_err();
        assert_eq!(error, "direct native questions require a complete ensures-only query");
    }

    fn with_omitted_function_clause(
        kind: ContractKind,
        source: &str,
        formula: Formula,
    ) -> (CompilerContractBundle, CompilerContractProposition) {
        let (mut query, ensures) = bool_query(true);
        let body = format!("__trust_lowered_compiler_contract__:{source}");
        query.contracts.push(Contract { kind, span: SourceSpan::default(), body: body.clone() });
        let omitted = CompilerContractProposition {
            source_contract_index: 1,
            kind,
            body,
            formula,
            variable_domains: Vec::new(),
        };
        query.typed_propositions.push(omitted.clone());
        assert_eq!(query.typed_proposition(1, &query.contracts[1]), Some(&omitted));
        (query, ensures)
    }

    #[test]
    fn native_questions_refuse_a_requires_clause_omitted_from_the_carry() {
        let (query, ensures) =
            with_omitted_function_clause(ContractKind::Requires, "true", Formula::Bool(true));
        assert_omitted_query_lane_refused(query, ensures);
    }

    #[test]
    fn native_questions_refuse_a_function_decreases_clause_omitted_from_the_carry() {
        // Numeric 1 is a valid measure, rather than a malformed Boolean decrease.
        let (query, ensures) =
            with_omitted_function_clause(ContractKind::Decreases, "1", Formula::Int(1));
        assert_omitted_query_lane_refused(query, ensures);
    }

    fn with_omitted_loop_clause(
        loop_kind: trust_types::LoopContractKind,
        contract_kind: ContractKind,
        source: &str,
        formula: Formula,
    ) -> (CompilerContractBundle, CompilerContractProposition) {
        let (mut query, ensures) = bool_query(true);
        let body = format!("__trust_lowered_compiler_contract__:{source}");
        query.loop_contracts.push(trust_types::LoopContractSpec {
            kind: loop_kind,
            source_loop_id: 1,
            source_hir_local_id: Some(9),
            mir_header: None,
            loop_head: SourceSpan::default(),
            header_span: SourceSpan::default(),
            span: SourceSpan::default(),
            body: body.clone(),
        });
        let omitted = CompilerContractProposition {
            source_contract_index: query.contracts.len(),
            kind: contract_kind,
            body: body.clone(),
            formula,
            variable_domains: Vec::new(),
        };
        query.typed_propositions.push(omitted.clone());
        // The query has no MIR-header binding; the public typed accessor's
        // explicit unpaired spelling authenticates the original loop query.
        let unpaired = Contract {
            kind: contract_kind,
            span: SourceSpan::default(),
            body: format!("{}{body}", trust_types::UNPAIRED_LOOP_CONTRACT_PREFIX),
        };
        assert_eq!(query.typed_proposition(query.contracts.len(), &unpaired), Some(&omitted));
        (query, ensures)
    }

    #[test]
    fn native_questions_refuse_a_loop_invariant_omitted_from_the_carry() {
        let (query, ensures) = with_omitted_loop_clause(
            trust_types::LoopContractKind::Invariant,
            ContractKind::LoopInvariant,
            "true",
            Formula::Bool(true),
        );
        assert_omitted_query_lane_refused(query, ensures);
    }

    #[test]
    fn native_questions_refuse_a_loop_decreases_clause_omitted_from_the_carry() {
        let (query, ensures) = with_omitted_loop_clause(
            trust_types::LoopContractKind::Decreases,
            ContractKind::Decreases,
            "1",
            Formula::Int(1),
        );
        assert_omitted_query_lane_refused(query, ensures);
    }

    #[test]
    fn native_questions_refuse_a_required_proof_item_omitted_from_the_carry() {
        let (mut query, ensures) = bool_query(true);
        let proof = trust_types::TrustProofItem::native_proof_fn(
            "inventory_lemma",
            trust_types::TrustProofItemKind::Lemma,
            SourceSpan::default(),
        );
        assert!(proof.is_native_syntax());
        assert!(proof.must_execute_in_full_verify());
        query.proof_items.push(proof);
        assert_omitted_query_lane_refused(query, ensures);
    }

    #[test]
    fn native_questions_refuse_an_unaccounted_typed_proposition() {
        let (mut query, ensures) = bool_query(true);
        let mut orphan = ensures.clone();
        orphan.source_contract_index = 1;
        query.typed_propositions.push(orphan);
        assert_omitted_query_lane_refused(query, ensures);
    }
}
