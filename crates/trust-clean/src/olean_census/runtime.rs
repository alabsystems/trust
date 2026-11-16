//! Captured core declaration content, not executable IR or import authority.
//!
//! Pointer keys are local memoization only and never leave this process. The
//! JSON graph uses deterministic encounter-order IDs and bounded flat tables,
//! avoiding recursive serde expansion of shared Expr/Level DAGs. Captured bytes
//! remain authoritative if conversion or this additional projection is partial.

use std::collections::BTreeMap;
use std::sync::Arc;

use clean_kernel::expr::{BigNat, Expr, ExprKind, Literal};
use clean_kernel::{Level, Name};
use clean_olean::module::{ConstantKind, DefinitionSafety, ReducibilityHintsData};
use clean_olean::{
    RuntimeBody, RuntimeDeclaration, RuntimeFamily, RuntimeOleanInput, RuntimeOleanPart,
    RuntimePartExtraction, RuntimePartIdentity, extract_olean_runtime_parts,
};
use serde_json::{Value, json};

use super::{Captured, names};

const SCHEMA: &str = "trust.lean.olean-declaration-content/v1";

#[derive(Clone, Copy)]
struct Bounds {
    nodes: usize,
    scalar_bytes: usize,
}

impl Default for Bounds {
    fn default() -> Self {
        Self { nodes: 100_000, scalar_bytes: 16 * 1024 * 1024 }
    }
}

enum Pending<'a> {
    Expr(usize, &'a Expr),
    Level(usize, &'a Level),
}

struct Graph<'a> {
    bounds: Bounds,
    scalar_bytes: usize,
    expr_ids: BTreeMap<usize, usize>,
    level_ids: BTreeMap<usize, usize>,
    expressions: Vec<Value>,
    levels: Vec<Value>,
    pending: Vec<Pending<'a>>,
    errors: Vec<String>,
}

impl<'a> Graph<'a> {
    fn new(bounds: Bounds) -> Self {
        Self {
            bounds,
            scalar_bytes: 0,
            expr_ids: BTreeMap::new(),
            level_ids: BTreeMap::new(),
            expressions: Vec::new(),
            levels: Vec::new(),
            pending: Vec::new(),
            errors: Vec::new(),
        }
    }

    fn charge(&mut self, bytes: usize) -> Result<(), String> {
        self.scalar_bytes = self.scalar_bytes.checked_add(bytes).ok_or("scalar byte overflow")?;
        if self.scalar_bytes > self.bounds.scalar_bytes {
            return Err("declaration-content scalar byte bound exceeded".into());
        }
        Ok(())
    }

    fn name(&mut self, name: &Name) -> Result<Value, String> {
        // The direct reader has its own typed-name limits. Check again for this
        // projection, which is also exercised with independently constructed Exprs.
        let mut cursor = name;
        let mut segments = Vec::new();
        loop {
            use clean_kernel::name::NameInner;
            if segments.len() > 256 {
                return Err("content Name segment bound exceeded".into());
            }
            match cursor.inner() {
                NameInner::Anon => break,
                NameInner::Str(prefix, segment) => {
                    self.charge(segment.len())?;
                    segments.push(json!({"kind":"str", "value":segment.as_ref()}));
                    cursor = prefix;
                }
                NameInner::Num(prefix, value) => {
                    self.charge(8)?;
                    segments.push(json!({"kind":"num", "value":value}));
                    cursor = prefix;
                }
            }
        }
        segments.reverse();
        Ok(json!(segments))
    }

    fn names(&mut self, values: &[Name]) -> Result<Value, String> {
        values.iter().map(|n| self.name(n)).collect::<Result<Vec<_>, _>>().map(Value::Array)
    }

    fn capacity(&self) -> Result<(), String> {
        if self.expressions.len() + self.levels.len() >= self.bounds.nodes {
            Err("declaration-content graph node bound exceeded".into())
        } else {
            Ok(())
        }
    }

    fn expr(&mut self, expr: &'a Expr) -> Result<usize, String> {
        let key = expr as *const Expr as usize;
        if let Some(id) = self.expr_ids.get(&key) {
            return Ok(*id);
        }
        self.capacity()?;
        let id = self.expressions.len();
        self.expr_ids.insert(key, id);
        self.expressions.push(json!({"kind":"pending"}));
        self.pending.push(Pending::Expr(id, expr));
        Ok(id)
    }

    fn level(&mut self, level: &'a Level) -> Result<usize, String> {
        let key = level as *const Level as usize;
        if let Some(id) = self.level_ids.get(&key) {
            return Ok(*id);
        }
        self.capacity()?;
        let id = self.levels.len();
        self.level_ids.insert(key, id);
        self.levels.push(json!({"kind":"pending"}));
        self.pending.push(Pending::Level(id, level));
        Ok(id)
    }

    fn expression_node(&mut self, expr: &'a Expr) -> Result<Value, String> {
        Ok(match expr.kind() {
            ExprKind::BVar(index) => json!({"kind":"bvar", "index":index}),
            ExprKind::Sort(level) => json!({"kind":"sort", "level":self.level(level)?}),
            ExprKind::Const(name, levels) => json!({"kind":"const", "name":self.name(name)?,
                "levels":levels.iter().map(|l| self.level(l)).collect::<Result<Vec<_>, _>>()?}),
            ExprKind::App(fun, arg) => {
                json!({"kind":"app", "fun":self.expr(fun)?, "arg":self.expr(arg)?})
            }
            ExprKind::Lam(binder, type_, body) | ExprKind::Pi(binder, type_, body) => {
                json!({"kind":if matches!(expr.kind(), ExprKind::Lam(..)) {"lam"} else {"pi"},
                    "binder":binder, "type":self.expr(type_)?, "body":self.expr(body)?})
            }
            ExprKind::Let(name, type_, value, body, nondep) => json!({"kind":"let",
                "name":self.name(name)?, "type":self.expr(type_)?, "value":self.expr(value)?,
                "body":self.expr(body)?, "nondep":nondep}),
            ExprKind::Proj(name, index, value) => json!({"kind":"proj", "name":self.name(name)?,
                "index":index, "value":self.expr(value)?}),
            ExprKind::Lit(Literal::Nat(value)) => {
                // Explicit little-endian u64 limbs preserve arbitrary precision;
                // do not route through as_u64, display, or a floating JSON number.
                let limbs: &[u64] = match value {
                    BigNat::Small(n) => std::slice::from_ref(n),
                    BigNat::Big(v) => v,
                };
                self.charge(limbs.len().checked_mul(8).ok_or("Nat limb size overflow")?)?;
                json!({"kind":"nat", "limbs_le_u64":limbs})
            }
            ExprKind::Lit(Literal::String(value)) => {
                self.charge(value.len())?;
                json!({"kind":"str", "value":value.as_ref()})
            }
            ExprKind::MData(_, value) => {
                json!({"kind":"mdata-unmeasured", "value":self.expr(value)?})
            }
            _ => {
                return Err(
                    "non-imported core Expr variant is unsupported by content projection".into()
                );
            }
        })
    }

    fn level_node(&mut self, level: &'a Level) -> Result<Value, String> {
        Ok(match level {
            Level::Zero => json!({"kind":"zero"}),
            Level::Succ(inner) => json!({"kind":"succ", "inner":self.level(inner)?}),
            Level::Max(left, right) | Level::IMax(left, right) => json!({
                "kind":if matches!(level, Level::Max(..)) {"max"} else {"imax"},
                "left":self.level(left)?, "right":self.level(right)?}),
            Level::Param(name) => json!({"kind":"param", "name":self.name(name)?}),
        })
    }

    fn root(&mut self, expr: &'a Result<Expr, String>) -> Value {
        let result = expr.as_ref().map_err(Clone::clone).and_then(|expr| self.expr(expr));
        while let Some(pending) = self.pending.pop() {
            let (is_expr, id, node) = match pending {
                Pending::Expr(id, expr) => (true, id, self.expression_node(expr)),
                Pending::Level(id, level) => (false, id, self.level_node(level)),
            };
            let node = node.unwrap_or_else(|error| {
                self.errors.push(error.clone());
                json!({"kind":"unrepresented", "error":error})
            });
            if is_expr {
                self.expressions[id] = node;
            } else {
                self.levels[id] = node;
            }
        }
        match result {
            Ok(id) if self.errors.is_empty() => json!({"status":"projected", "root":id}),
            // Conservative across roots: a memoized node may contain a previous
            // failed child. Never re-label it projected just because no new work
            // was enqueued for the repeated reference.
            Ok(id) => json!({"status":"partial", "root":id,
                "graph_error_count":self.errors.len(), "errors_at":"core_graph.errors"}),
            Err(error) => {
                let index = self.errors.len();
                self.errors.push(error.clone());
                json!({"status":"unrepresented", "error":error, "graph_error_index":index})
            }
        }
    }

    fn family(&mut self, family: &'a RuntimeFamily) -> Result<Value, String> {
        Ok(match family {
            RuntimeFamily::None => json!({"kind":"none"}),
            RuntimeFamily::UnsupportedQuotientMetadata => {
                json!({"kind":"quotient-metadata-unmeasured"})
            }
            RuntimeFamily::Inductive {
                all,
                constructors,
                num_params,
                num_indices,
                num_nested,
                is_nested,
                is_recursive,
                is_unsafe,
                is_reflexive,
            } => json!({"kind":"inductive",
                    "all":self.names(all)?, "constructors":self.names(constructors)?,
                    "num_params":num_params, "num_indices":num_indices, "num_nested":num_nested,
                    "is_nested":is_nested, "is_recursive":is_recursive, "is_unsafe":is_unsafe,
                    "is_reflexive":is_reflexive}),
            RuntimeFamily::Constructor { inductive, index, num_params, num_fields, is_unsafe } => {
                json!({"kind":"constructor", "inductive":self.name(inductive)?, "index":index,
                    "num_params":num_params, "num_fields":num_fields, "is_unsafe":is_unsafe})
            }
            RuntimeFamily::Recursor {
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                k,
                is_unsafe,
                rules,
            } => {
                let mut encoded = Vec::new();
                for rule in rules {
                    encoded.push(json!({"constructor":self.name(&rule.constructor)?,
                        "num_fields":rule.num_fields, "rhs":self.root(&rule.rhs)}));
                }
                json!({"kind":"recursor", "all":self.names(all)?, "num_params":num_params,
                    "num_indices":num_indices, "num_motives":num_motives, "num_minors":num_minors,
                    "k":k, "is_unsafe":is_unsafe, "rules":encoded})
            }
        })
    }
}

fn part_index(part: RuntimeOleanPart) -> usize {
    match part {
        RuntimeOleanPart::Base => 0,
        RuntimeOleanPart::Server => 1,
        RuntimeOleanPart::Private => 2,
    }
}

fn identity(identity: &RuntimePartIdentity, captured: &[Captured]) -> Value {
    let index = part_index(identity.part);
    json!({"part_index":index, "label":identity.label, "byte_count":identity.byte_count,
        "blake3":identity.blake3.iter().map(|b| format!("{b:02x}")).collect::<String>(),
        "capture_sha256":captured[index].record["sha256"], "capture_path":captured[index].record["path"]})
}

fn declaration<'a>(row: &'a RuntimeDeclaration, graph: &mut Graph<'a>) -> Result<Value, String> {
    let kind = match row.kind {
        ConstantKind::Axiom => "axiom",
        ConstantKind::Definition => "definition",
        ConstantKind::Theorem => "theorem",
        ConstantKind::Opaque => "opaque",
        ConstantKind::Quot => "quotient",
        ConstantKind::Inductive => "inductive",
        ConstantKind::Constructor => "constructor",
        ConstantKind::Recursor => "recursor",
        _ => return Err("unknown declaration kind".into()),
    };
    let safety = match row.declaration_safety {
        None => None,
        Some(DefinitionSafety::Safe) => Some("safe"),
        Some(DefinitionSafety::Unsafe) => Some("unsafe"),
        Some(DefinitionSafety::Partial) => Some("partial"),
        _ => return Err("unknown declaration safety".into()),
    };
    let hints = row.hints.map(|h| match h {
        ReducibilityHintsData::Opaque => json!({"kind":"opaque"}),
        ReducibilityHintsData::Abbrev => json!({"kind":"abbrev"}),
        ReducibilityHintsData::Regular(height) => json!({"kind":"regular", "height":height}),
    });
    let body = match &row.body {
        RuntimeBody::Stored(expr) => json!({"status":"stored", "expression":graph.root(expr)}),
        RuntimeBody::NoStoredValueForKind => {
            json!({"status":"no-stored-value-for-kind", "stub_resolution":"unmeasured"})
        }
        RuntimeBody::MissingRequiredValue => json!({"status":"missing-required-value"}),
    };
    Ok(
        json!({"name":graph.name(&row.name)?, "kind":kind, "level_params":graph.names(&row.level_params)?,
        "safety":safety, "hints":hints, "mutual_declarations":row.mutual_declarations.as_ref().map(|n| graph.names(n)).transpose()?,
        "type":graph.root(&row.type_), "body":body, "family":graph.family(&row.family)?,
        "dependencies":row.dependencies.iter().map(|n| graph.name(n)).collect::<Result<Vec<_>,_>>()?,
        "extractor_represented_fields_complete":row.represented_fields_complete, "extractor_issues":row.issues}),
    )
}

fn part_report(part: &RuntimePartExtraction, captured: &[Captured], bounds: Bounds) -> Value {
    let mut graph = Graph::new(bounds);
    let mut rows = Vec::new();
    for row in &part.rows {
        let decoded_name = row.declaration.as_ref().ok().map(|d| graph.name(&d.name));
        let identity_projected = matches!(decoded_name, Some(Ok(_)));
        let projected =
            row.declaration.as_ref().map_err(Clone::clone).and_then(|d| declaration(d, &mut graph));
        let mut record =
            json!({"index":row.index, "authority":"diagnostic-only-no-import-admission"});
        // Exact decoded Names are bounded too. Never bypass the scalar budget
        // by copying the same large shared Name once per failed declaration.
        // Captured part/prefix/index remains available if identity projection
        // is unavailable; the independent raw witness is left unchanged.
        record["decoded_name"] = match decoded_name {
            Some(Ok(name)) => name,
            Some(Err(error)) => {
                record["identity_projection_error"] = json!(error);
                Value::Null
            }
            None => Value::Null,
        };
        match projected {
            Ok(value) => {
                record["projection_graph_complete"] =
                    json!(identity_projected && graph.errors.is_empty());
                record["declaration"] = value;
            }
            Err(error) => {
                record["projection_graph_complete"] = json!(false);
                record["projection_error"] = json!(error);
            }
        }
        rows.push(record);
    }
    json!({"schema":SCHEMA, "status":if part.error.is_some() {"part-decode-failed"} else {"observed"},
        "authority":"diagnostic-only-no-import-admission", "identity":identity(&part.identity,captured),
        "borrowed_prefix":part.borrowed_prefix.iter().map(|p|identity(p,captured)).collect::<Vec<_>>(),
        "source_row_count":part.source_row_count, "rows":rows, "part_error":part.error,
        "core_graph":{"schema":"trust.lean.captured-core-dag/v1", "expressions":graph.expressions,
            "levels":graph.levels, "errors":graph.errors, "node_limit":bounds.nodes,
            "scalar_byte_limit":bounds.scalar_bytes, "scalar_bytes_attempted":graph.scalar_bytes},
        "runtime_body_universe":"unmeasured", "dependency_closure":"unmeasured",
        "limitations":["core declarations are not executable Lean IR or Trust-IR",
            "cumulative part occurrences are retained, not deduplicated or admitted",
            "MData payloads and original binder display names are not reconstructed",
            "projection bounds are not a process memory limit; extraction uses Clean's existing bounded direct reader",
            "imports, extensions, native code, source refinement and kernel authority are separate"]})
}

/// Called once per candidate over the same captured bytes as the old witnesses.
pub(super) fn observe(captured: &[Captured]) -> Vec<Value> {
    let mut output: Vec<Value> = (0..4)
        .map(|index| {
            json!({"schema":SCHEMA,
        "status":if index == 3 {"not-a-kernel-module-part"} else {"not-captured"},
        "authority":"diagnostic-only-no-import-admission", "rows":[]})
        })
        .collect();
    let input = |index: usize| {
        captured[index].bytes.as_ref().map(|bytes| RuntimeOleanInput {
            label: format!("captured-part-{index}"),
            bytes: Arc::from(bytes.as_slice()),
        })
    };
    let Some(base) = input(0) else {
        for index in 1..3 {
            if captured[index].bytes.is_some() {
                output[index]["status"] = json!("missing-captured-base");
            }
        }
        return output;
    };
    match std::panic::catch_unwind(|| extract_olean_runtime_parts(base, input(1), input(2))) {
        Ok(parts) => {
            for part in &parts {
                output[part_index(part.identity.part)] =
                    part_report(part, captured, Bounds::default());
            }
        }
        Err(_) => {
            for index in 0..3 {
                if captured[index].bytes.is_some() {
                    output[index]["status"] = json!("extractor-panicked");
                }
            }
        }
    }
    output
}

pub(super) fn reconcile(report: &mut Value, witness: &names::Witness) {
    let mut errors = Vec::new();
    if !witness.errors.is_empty() {
        errors.push("independent raw witness is incomplete".to_string());
    }
    if report["source_row_count"].as_u64() != Some(witness.constants.len() as u64) {
        errors.push("content/raw constants-array counts do not agree or are unavailable".into());
    }
    let rows = report["rows"].as_array();
    if rows.map(Vec::len) != Some(witness.constants.len()) {
        errors.push(
            "content row population is unavailable or differs from raw constants array".into(),
        );
    }
    for raw in &witness.constants {
        let expected = raw.name.as_ref().map(|n| json!(n));
        let content = rows.and_then(|rows| rows.get(raw.index));
        if raw.error.is_some()
            || expected.is_none()
            || content.is_none_or(|c| {
                c["index"].as_u64() != Some(raw.index as u64)
                    || Some(&c["decoded_name"]) != expected.as_ref()
            })
        {
            errors.push(format!(
                "constant row {} has unresolved or mismatched typed identity",
                raw.index
            ));
        }
        let kind = raw.constant_tag.and_then(|tag| {
            [
                "axiom",
                "definition",
                "theorem",
                "opaque",
                "quotient",
                "inductive",
                "constructor",
                "recursor",
            ]
            .get(tag as usize)
            .copied()
        });
        if kind.is_none() || content.and_then(|c| c["declaration"]["kind"].as_str()) != kind {
            errors.push(format!("constant row {} has unresolved or mismatched kind", raw.index));
        }
    }
    report["raw_witness_reconciliation"] = json!({"status":if errors.is_empty() {"exact-row-identities-agree"} else {"incomplete-or-disagrees"},
        "errors":errors, "meaning":"part-local array identity only; no admission or body-faithfulness evidence"});
}

#[cfg(test)]
mod tests;
