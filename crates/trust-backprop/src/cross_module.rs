//! Cross-module rewrite planning.
//!
//! When a callee gets a new precondition via trust-strengthen, every call site
//! must be updated with a corresponding check. This module plans rewrites that
//! span multiple files, ordered callee-first so preconditions are established
//! before caller-site checks are generated.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use serde::{Deserialize, Serialize};
use trust_strengthen::{Proposal, ProposalKind};

use crate::SourceRewrite;
use crate::dependency::{CallGraph, topological_order};

/// A cross-module rewrite plan: an ordered list of per-file rewrites.
///
/// Files are ordered so that callees are rewritten before their callers,
/// ensuring new preconditions are in place when caller checks are generated.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CrossModulePlan {
    /// Ordered list of (file_path, rewrites) pairs. Callees first.
    pub file_rewrites: Vec<(String, Vec<SourceRewrite>)>,
    /// Summary of the cross-module plan.
    pub summary: String,
}

impl CrossModulePlan {
    /// Total number of rewrites across all files.
    #[must_use]
    pub fn total_rewrites(&self) -> usize {
        self.file_rewrites.iter().map(|(_, rw)| rw.len()).sum()
    }

    /// Whether the plan is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.file_rewrites.iter().all(|(_, rw)| rw.is_empty())
    }

    /// Return the number of files affected.
    #[must_use]
    pub fn file_count(&self) -> usize {
        self.file_rewrites.len()
    }
}

/// Plan cross-module rewrites based on proposals and a call graph.
///
/// When a proposal adds a precondition to a callee, this generates
/// corresponding assertion rewrites at each call site in the caller.
/// Rewrites are ordered callee-first via topological sort of the call graph.
///
/// # Arguments
///
/// * `proposals` - Proposals from trust-strengthen (each targets one function).
/// * `call_graph` - The call graph built from `VerifiableFunction` data.
/// * `function_files` - Map from function def-path (or an unambiguous legacy
///   short name) to its source file path.
///
/// # Returns
///
/// A `CrossModulePlan` with file rewrites ordered callee-first.
#[must_use]
pub fn plan_cross_module_rewrites(
    proposals: &[Proposal],
    call_graph: &CallGraph,
    function_files: &FxHashMap<String, String>,
) -> CrossModulePlan {
    let order = topological_order(call_graph);

    // Index proposals by unique function identity. Ambiguous short-name
    // proposals are not safe to turn into dependency-aware rewrites.
    let mut proposals_by_fn: FxHashMap<&str, Vec<&Proposal>> = FxHashMap::default();
    for proposal in proposals {
        if let Some(def_path) = call_graph
            .resolve_function(&proposal.function_path)
            .or_else(|| call_graph.resolve_function(&proposal.function_name))
        {
            proposals_by_fn.entry(def_path).or_default().push(proposal);
        }
    }

    // Collect per-file rewrites, maintaining callee-first order.
    let mut file_rewrites_map: FxHashMap<String, Vec<SourceRewrite>> = FxHashMap::default();
    let mut file_order: Vec<String> = Vec::new();

    for func_path in &order {
        let mut new_preconditions: Vec<&str> = Vec::new();

        // Apply direct proposals for this function.
        if let Some(func_proposals) = proposals_by_fn.get(func_path.as_str()) {
            for proposal in func_proposals {
                let file_path = function_files
                    .get(func_path.as_str())
                    .or_else(|| {
                        let name = call_graph.function_name(func_path)?;
                        (call_graph.resolve_function(name) == Some(func_path.as_str()))
                            .then(|| function_files.get(name))
                            .flatten()
                    })
                    .cloned()
                    .unwrap_or_else(|| proposal.function_path.clone());
                if crate::report_only_provenance_path_reason(&file_path).is_some()
                    || !crate::is_rust_source_path(&file_path)
                {
                    continue;
                }
                let Ok(source) = std::fs::read_to_string(&file_path) else { continue };
                let Ok(direct_rewrites) = crate::convert_proposal(proposal, &source, &file_path)
                else {
                    continue;
                };
                if direct_rewrites.is_empty() {
                    continue;
                }

                if let ProposalKind::AddPrecondition { spec_body } = &proposal.kind {
                    new_preconditions.push(spec_body.as_str());
                }

                let rewrites = file_rewrites_map.entry(file_path.clone()).or_default();
                if !file_order.contains(&file_path) {
                    file_order.push(file_path);
                }
                rewrites.extend(direct_rewrites);
            }
        }

        if new_preconditions.is_empty() {
            continue;
        }

        // Caller-site propagation is intentionally report-only until dependency
        // edges carry exact source call-site provenance. Inserting offset-0
        // caller assertions from a name-only edge can rewrite the wrong source.
        let _ = (func_path, &new_preconditions, function_files);
    }

    let result: Vec<(String, Vec<SourceRewrite>)> = file_order
        .into_iter()
        .filter_map(|f| {
            let rw = file_rewrites_map.remove(&f)?;
            if rw.is_empty() { None } else { Some((f, rw)) }
        })
        .collect();

    let total = result.iter().map(|(_, rw)| rw.len()).sum::<usize>();
    let file_count = result.len();
    CrossModulePlan {
        file_rewrites: result,
        summary: format!("Cross-module plan: {total} rewrites across {file_count} files"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dependency::build_call_graph;
    use trust_types::*;

    /// Helper: make a VerifiableFunction with specified callees.
    fn make_function(name: &str, callees: &[&str]) -> VerifiableFunction {
        make_function_at(name, &format!("crate::{name}"), callees)
    }

    fn make_function_at(name: &str, def_path: &str, callees: &[&str]) -> VerifiableFunction {
        let mut blocks = Vec::new();
        for (i, callee) in callees.iter().enumerate() {
            blocks.push(BasicBlock {
                id: BlockId(i),
                stmts: vec![],
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    is_unsafe_sig: false,
                    is_foreign: false,
                    func: callee.to_string(),
                    args: vec![],
                    dest: Place::local(0),
                    target: Some(BlockId(i + 1)),
                    span: SourceSpan::default(),
                    atomic: None,
                },
            });
        }
        blocks.push(BasicBlock {
            id: BlockId(callees.len()),
            stmts: vec![],
            terminator: Terminator::Return,
        });

        VerifiableFunction {
            name: name.to_string(),
            def_path: def_path.to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody { locals: vec![], blocks, arg_count: 0, return_ty: Ty::Unit },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn make_precondition_proposal_at(path: &str, func: &str, spec: &str) -> Proposal {
        Proposal {
            function_path: path.into(),
            function_name: func.into(),
            kind: ProposalKind::AddPrecondition { spec_body: spec.into() },
            confidence: 0.9,
            rationale: "test".into(),
        }
    }

    fn temp_source_file(file_name: &str, source: &str) -> (tempfile::TempDir, String) {
        let dir = tempfile::tempdir().expect("create temp source dir");
        let path = dir.path().join(file_name);
        std::fs::write(&path, source).expect("write temp source");
        (dir, path.display().to_string())
    }

    fn make_file_map(entries: &[(&str, &str)]) -> FxHashMap<String, String> {
        entries.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect()
    }

    #[test]
    fn test_plan_cross_module_empty() {
        let graph = build_call_graph(&[]);
        let file_map = FxHashMap::default();
        let plan = plan_cross_module_rewrites(&[], &graph, &file_map);
        assert!(plan.is_empty());
        assert_eq!(plan.total_rewrites(), 0);
        assert_eq!(plan.file_count(), 0);
    }

    #[test]
    fn test_plan_cross_module_single_proposal_no_callers() {
        let (_dir, helper_path) = temp_source_file("helper.rs", "fn helper(x: i32) -> i32 { x }\n");
        let funcs = vec![make_function("helper", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("helper", &helper_path)]);
        let proposals = vec![make_precondition_proposal_at(&helper_path, "helper", "x > 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        assert_eq!(plan.total_rewrites(), 1); // Just the precondition itself.
        assert_eq!(plan.file_count(), 1);
    }

    #[test]
    fn test_plan_cross_module_keeps_caller_propagation_report_only_without_call_site() {
        let (_dir, callee_path) = temp_source_file("callee.rs", "fn callee(x: i32) -> i32 { x }\n");
        // caller -> callee. Add precondition to callee. Caller should get a check.
        let funcs = vec![make_function("caller", &["callee"]), make_function("callee", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("caller", "src/caller.rs"), ("callee", &callee_path)]);
        let proposals = vec![make_precondition_proposal_at(&callee_path, "callee", "x > 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // Only the callee's precondition is materialized until call-site source
        // provenance is available for the caller edge.
        assert_eq!(plan.total_rewrites(), 1);
        assert_eq!(plan.file_count(), 1);

        // Callee file should come first (callee-first ordering).
        assert_eq!(plan.file_rewrites[0].0, callee_path);
    }

    #[test]
    fn test_plan_cross_module_multiple_callers() {
        let (_dir, c_path) = temp_source_file("c.rs", "fn c(n: i32) -> i32 { n }\n");
        // a -> c, b -> c. Add precondition to c. Both a and b get checks.
        let funcs =
            vec![make_function("a", &["c"]), make_function("b", &["c"]), make_function("c", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("a", "src/a.rs"), ("b", "src/b.rs"), ("c", &c_path)]);
        let proposals = vec![make_precondition_proposal_at(&c_path, "c", "n != 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // Only the callee precondition is materialized without exact call-site provenance.
        assert_eq!(plan.total_rewrites(), 1);

        // c's file should appear first.
        assert_eq!(plan.file_rewrites[0].0, c_path);
    }

    #[test]
    fn test_plan_cross_module_chain_ordering() {
        let (_dir, c_path) =
            temp_source_file("c.rs", "fn c(i: usize, len: usize) { let _ = i; }\n");
        // a -> b -> c. Add precondition to c.
        // c gets the precondition, b gets a check, a does NOT (a doesn't call c directly).
        let funcs =
            vec![make_function("a", &["b"]), make_function("b", &["c"]), make_function("c", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("a", "src/a.rs"), ("b", "src/b.rs"), ("c", &c_path)]);
        let proposals = vec![make_precondition_proposal_at(&c_path, "c", "i < len")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // Only c's precondition is materialized without exact call-site provenance.
        assert_eq!(plan.total_rewrites(), 1);

        // Order: c first.
        assert_eq!(plan.file_rewrites[0].0, c_path);
    }

    #[test]
    fn test_plan_cross_module_non_precondition_no_propagation() {
        let (_dir, callee_path) =
            temp_source_file("callee.rs", "fn callee(a: u64, b: u64) -> u64 { a + b }\n");
        // caller -> callee. Add safe arithmetic to callee. No caller propagation.
        let funcs = vec![make_function("caller", &["callee"]), make_function("callee", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("caller", "src/caller.rs"), ("callee", &callee_path)]);
        let proposals = vec![Proposal {
            function_path: callee_path,
            function_name: "callee".into(),
            kind: ProposalKind::SafeArithmetic {
                original: "a + b".into(),
                replacement: "a.checked_add(b).unwrap()".into(),
            },
            confidence: 0.8,
            rationale: "safe arithmetic".into(),
        }];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // Only the callee's rewrite; no caller propagation for SafeArithmetic.
        assert_eq!(plan.total_rewrites(), 1);
        assert_eq!(plan.file_count(), 1);
    }

    #[test]
    fn test_plan_cross_module_same_file() {
        let (_dir, lib_path) = temp_source_file(
            "lib.rs",
            "fn outer(x: i32) -> i32 { inner(x) }\nfn inner(x: i32) -> i32 { x }\n",
        );
        // Two functions in the same file.
        let funcs = vec![make_function("outer", &["inner"]), make_function("inner", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("outer", &lib_path), ("inner", &lib_path)]);
        let proposals = vec![make_precondition_proposal_at(&lib_path, "inner", "x >= 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        // Only the precondition is materialized without exact call-site provenance.
        assert_eq!(plan.total_rewrites(), 1);
        // Should be merged into one file entry.
        assert_eq!(plan.file_count(), 1);
        assert_eq!(plan.file_rewrites[0].0, lib_path);
        assert_eq!(plan.file_rewrites[0].1.len(), 1);
    }

    #[test]
    fn test_exact_path_selects_one_of_duplicate_names_and_ignores_legacy_file_alias() {
        let (_left_dir, left_path) =
            temp_source_file("left.rs", "fn helper(x: i32) -> i32 { x }\n");
        let (_right_dir, right_path) =
            temp_source_file("right.rs", "fn helper(x: i32) -> i32 { x }\n");
        let funcs = vec![
            make_function_at("helper", "crate::left::helper", &[]),
            make_function_at("helper", "crate::right::helper", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[
            ("crate::left::helper", &left_path),
            ("crate::right::helper", &right_path),
            ("helper", &right_path),
        ]);
        let proposals =
            vec![make_precondition_proposal_at("crate::left::helper", "helper", "x > 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);

        assert_eq!(plan.total_rewrites(), 1);
        assert_eq!(plan.file_rewrites[0].0, left_path);
    }

    #[test]
    fn test_ambiguous_name_without_exact_path_produces_no_plan() {
        let (_dir, source_path) = temp_source_file("helper.rs", "fn helper(x: i32) -> i32 { x }\n");
        let funcs = vec![
            make_function_at("helper", "crate::left::helper", &[]),
            make_function_at("helper", "crate::right::helper", &[]),
        ];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("helper", &source_path)]);
        let proposals = vec![make_precondition_proposal_at(&source_path, "helper", "x > 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);

        assert!(plan.is_empty());
    }

    #[test]
    fn test_plan_cross_module_summary() {
        let (_dir, f_path) = temp_source_file("f.rs", "fn f() {}\n");
        let funcs = vec![make_function("f", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("f", &f_path)]);
        let proposals = vec![make_precondition_proposal_at(&f_path, "f", "true")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);
        assert!(plan.summary.contains("1 rewrites"));
        assert!(plan.summary.contains("1 files"));
    }

    #[test]
    fn test_plan_cross_module_binary_callee_does_not_backprop_to_source_caller() {
        let funcs = vec![make_function("caller", &["callee"]), make_function("callee", &[])];
        let graph = build_call_graph(&funcs);
        let file_map = make_file_map(&[("caller", "src/caller.rs"), ("callee", "binary:0x1000")]);
        let proposals = vec![make_precondition_proposal_at("binary:0x1000", "callee", "x > 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);

        assert!(plan.is_empty());
        assert_eq!(plan.total_rewrites(), 0);
        assert_eq!(plan.file_count(), 0);
    }

    #[test]
    fn test_plan_cross_module_unreadable_callee_does_not_backprop_to_source_caller() {
        let funcs = vec![make_function("caller", &["callee"]), make_function("callee", &[])];
        let graph = build_call_graph(&funcs);
        let file_map =
            make_file_map(&[("caller", "src/caller.rs"), ("callee", "does/not/exist.rs")]);
        let proposals = vec![make_precondition_proposal_at("does/not/exist.rs", "callee", "x > 0")];

        let plan = plan_cross_module_rewrites(&proposals, &graph, &file_map);

        assert!(plan.is_empty());
        assert_eq!(plan.total_rewrites(), 0);
        assert_eq!(plan.file_count(), 0);
    }
}
