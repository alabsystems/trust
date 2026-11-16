//! Trust: optional diagnostic observations of explicit HIR call expressions.
//! These are neither a runtime call graph nor evidence of acquisition/body completeness.

use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Expr, ExprKind};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::{FileName, SourceFileHashAlgorithm, Span};
use serde_json::{Value, json};

// Trust: offsets refer to the original loaded bytes, not normalized source or a
// later disk read. A macro expansion's span and its callsite are separate facts.
fn raw_span(tcx: TyCtxt<'_>, span: Span) -> Value {
    if span.is_dummy() {
        return Value::Null;
    }
    let map = tcx.sess.source_map();
    let lo = map.lookup_source_file(span.lo());
    let hi = map.lookup_source_file(span.hi());
    if lo.start_pos != hi.start_pos || lo.src.is_none() {
        return Value::Null;
    }
    let FileName::Real(real) = &lo.name else { return Value::Null };
    let Some(path) =
        real.local_path().and_then(|p| super::trust_body_census::absolute_path(p).ok())
    else {
        return Value::Null;
    };
    let Some(hash) = lo.checksum_hash.filter(|h| h.kind == SourceFileHashAlgorithm::Sha256) else {
        return Value::Null;
    };
    json!({
        "file": path,
        "sha256": hash.to_string().strip_prefix("sha256=").unwrap(),
        "lo": lo.original_relative_byte_pos(span.lo()).0,
        "hi": lo.original_relative_byte_pos(span.hi()).0,
    })
}

fn definition(tcx: TyCtxt<'_>, def: DefId) -> Value {
    json!({
        "crate_name": tcx.crate_name(def.krate).to_string(),
        "def_path_hash": format!("{:?}", tcx.def_path_hash(def)),
        "def_path": tcx.def_path_debug_str(def),
        "local": def.is_local(),
        "span_kind": "rustc-def-span",
        "raw_span": raw_span(tcx, tcx.def_span(def)),
    })
}

struct Calls<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    results: &'tcx ty::TypeckResults<'tcx>,
    rows: Vec<Value>,
}

impl<'tcx> Visitor<'tcx> for Calls<'tcx> {
    // Trust: the default nested filter visits no nested bodies/items. Each HIR
    // body owner is visited separately with that owner's own typeck results.
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let tcx = self.tcx;
        let results = self.results;
        let (kind, callee_span, candidate) = match expr.kind {
            ExprKind::Call(callee, _) => {
                let candidate = match results.expr_ty(callee).kind() {
                    ty::FnDef(def, args) => args.no_bound_vars().map(|args| (*def, args)),
                    _ => None,
                };
                ("call", callee.span, candidate)
            }
            ExprKind::MethodCall(segment, ..) => (
                "method_call",
                segment.ident.span,
                results
                    .type_dependent_def_id(expr.hir_id)
                    .map(|def| (def, results.node_args(expr.hir_id))),
            ),
            _ => {
                intravisit::walk_expr(self, expr);
                return;
            }
        };
        let mut target = Value::Null;
        let reason = match candidate {
            None => "indirect_or_unresolved",
            Some((_, args)) if args.has_non_region_param() || args.has_infer() => "generic",
            Some((def, _))
                if tcx.trait_of_assoc(def).is_some() || tcx.trait_item_of(def).is_some() =>
            {
                "trait_dispatch"
            }
            Some((def, _)) => {
                // Trust: a declaration selected by typeck is not a resolved
                // runtime instance. In particular do not call try_resolve:
                // instance selection can demand MIR/post-analysis queries.
                target = definition(tcx, def);
                "static_definition"
            }
        };
        self.rows.push(json!({
            "caller": definition(tcx, self.owner.to_def_id()),
            // HIR local IDs and syntax context distinguish observed occurrences
            // within THIS invocation; they are not compiler-independent IDs.
            "hir_local_id": expr.hir_id.local_id.as_u32(),
            "syntax_context": format!("{:?}", expr.span.ctxt()),
            "from_expansion": expr.span.from_expansion(),
            "raw_span": raw_span(tcx, expr.span),
            "callsite_raw_span": raw_span(tcx, expr.span.source_callsite()),
            "callee_raw_span": raw_span(tcx, callee_span),
            "callee_callsite_raw_span": raw_span(tcx, callee_span.source_callsite()),
            "callee_syntax_context": format!("{:?}", callee_span.ctxt()),
            "kind": kind,
            "declaration": candidate.map(|(def, _)| definition(tcx, def)),
            "resolution": if target.is_null() { "unknown" } else { "static_definition" },
            "reason": reason,
            "target": target,
        }));
        intravisit::walk_expr(self, expr);
    }
}

pub(crate) fn snapshot(tcx: TyCtxt<'_>) -> Value {
    // Trust: erroneous typeck results need not contain every node's type. Do
    // not turn diagnostic observation into an ICE or a claimed zero-site scan.
    if tcx.sess.dcx().has_errors_or_delayed_bugs().is_some() {
        return json!({ "status": "not-observed-typecheck-errors", "input_binding_complete": false });
    }
    let mut owners = tcx.hir_body_owners().collect::<Vec<_>>();
    owners.sort_by_key(|owner| owner.local_def_index.as_u32());
    let mut bodies = Vec::new();
    for owner in owners {
        let mut calls = Calls { tcx, owner, results: tcx.typeck(owner), rows: Vec::new() };
        calls.visit_body(tcx.hir_body_owned_by(owner));
        bodies.push(json!({
            "owner": definition(tcx, owner.to_def_id()),
            "explicit_hir_call_count": calls.rows.len(),
            "calls": calls.rows,
        }));
    }
    json!({
        "status": "observed",
        "scope": "explicit-local-hir-call-and-method-expressions-after-typeck-before-mir-borrowck",
        "authority": "diagnostic-only",
        "input_binding_complete": false,
        "compiler_image_binding": "unmeasured",
        "target_cfg_dependency_binding": "unmeasured",
        "expanded_body_acquisition_completeness": "unmeasured",
        "implicit_calls_drops_desugarings_runtime_targets": "unmeasured",
        "declaration_identity": "invocation-local-diagnostic-not-a-concrete-instance",
        "synthetic_coroutine_bodies_without_hir": "not-visited",
        "body_count": bodies.len(),
        "bodies": bodies,
    })
}
