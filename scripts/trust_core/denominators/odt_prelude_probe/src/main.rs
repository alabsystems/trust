// The ODT census's prelude probe: every declaration of Clean's island prelude
// (`Environment::with_prelude()`, what CleanIslandSession::new builds), with its
// kernel terms, as one deterministic JSON document on stdout.
//
// scripts/trust_core/denominators/odt.py --probe-prelude builds this against a
// `git archive` export of the PINNED first-party/clean tree and publishes the
// output (gzip, fixed header) as docs/trust-core/denominators/odt-prelude-decls.json.gz.
// odt.py then classifies every prelude inductive into E2.5.6's rows from these
// terms with the same code that classifies the Lean 4.8 oleans, and re-derives
// D0.5's structural type hashes from them as a control.
//
// Output (keys sorted, one object):
//   exprs   the expression DAG, interned STRUCTURALLY (a node's id depends only on
//           its structure, never on pointer sharing), in first-visit post-order over
//           the declarations sorted by name. A node is a JSON array:
//             ["B", idx] ["F", debug] ["S", level] ["C", name, [level...]]
//             ["A", f, a] ["L", binder_info, ty, body] ["P", binder_info, ty, body]
//             ["Z", name, ty, value, body] ["N", "decimal"] ["T", string]
//             ["J", struct_name, idx, e] ["?", debug-of-other-variant]
//           where f, a, ty, ... are node ids. MData is transparent (its inner node).
//   levels  inline: ["0"] ["+", l] ["max", a, b] ["imax", a, b] ["p", name]
//   decls   one per name, sorted: form (D0.5's form_of order: inductive,
//           constructor, recursor, quot, else the constant kind), lparams, type
//           (the type D0.5's facts_of hashes: the constant table's when the name is
//           in it, else the form's own), value (definitions and opaques only), and
//           the form's kernel facts.
//
// No verdict, no authority: a measurement tool.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::io::Write as _;

use clean_kernel::quot::QuotKind;
use clean_kernel::{ConstantKind, Environment, Expr, ExprKind, Level, Literal, Name};

/// A JSON string literal.
fn js(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn level(l: &Level) -> String {
    match l {
        Level::Zero => "[\"0\"]".to_string(),
        Level::Succ(a) => format!("[\"+\",{}]", level(a)),
        Level::Max(a, b) => format!("[\"max\",{},{}]", level(a), level(b)),
        Level::IMax(a, b) => format!("[\"imax\",{},{}]", level(a), level(b)),
        Level::Param(n) => format!("[\"p\",{}]", js(&n.to_string())),
    }
}

struct Interner {
    by_ptr: HashMap<*const Expr, usize>,
    by_node: HashMap<String, usize>,
    nodes: Vec<String>,
}

impl Interner {
    fn new() -> Self {
        Self { by_ptr: HashMap::new(), by_node: HashMap::new(), nodes: Vec::new() }
    }

    fn intern(&mut self, node: String) -> usize {
        if let Some(id) = self.by_node.get(&node) {
            return *id;
        }
        let id = self.nodes.len();
        self.by_node.insert(node.clone(), id);
        self.nodes.push(node);
        id
    }

    /// The id of `e`, interning its subterms first (iteratively: prelude terms can be deep). The
    /// pointer memo lives for one call only, so an address reused between calls (a temporary) can
    /// never alias another term: ids come from the structural table, which outlives the call.
    fn expr(&mut self, root: &Expr) -> usize {
        let id = self.expr_inner(root);
        self.by_ptr.clear();
        id
    }

    fn expr_inner(&mut self, root: &Expr) -> usize {
        enum Step<'a> {
            Visit(&'a Expr),
            Build(&'a Expr),
        }
        let mut stack = vec![Step::Visit(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Visit(e) => {
                    if self.by_ptr.contains_key(&(e as *const Expr)) {
                        continue;
                    }
                    stack.push(Step::Build(e));
                    // Children pushed in reverse so they are interned left to right.
                    let kids: Vec<&Expr> = match e.kind() {
                        ExprKind::App(f, a) => vec![f, a],
                        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => vec![t, b],
                        ExprKind::Let(_, t, v, b, _) => vec![t, v, b],
                        ExprKind::Proj(_, _, x) => vec![x],
                        ExprKind::MData(_, x) => vec![x],
                        _ => vec![],
                    };
                    for k in kids.into_iter().rev() {
                        stack.push(Step::Visit(k));
                    }
                }
                Step::Build(e) => {
                    let key = e as *const Expr;
                    if self.by_ptr.contains_key(&key) {
                        continue;
                    }
                    let id_of = |this: &Self, x: &Expr| this.by_ptr[&(x as *const Expr)];
                    let id = match e.kind() {
                        ExprKind::MData(_, x) => id_of(self, x),
                        kind => {
                            let node = match kind {
                                ExprKind::BVar(i) => format!("[\"B\",{i}]"),
                                ExprKind::FVar(id) => format!("[\"F\",{}]", js(&format!("{id:?}"))),
                                ExprKind::Sort(l) => format!("[\"S\",{}]", level(l)),
                                ExprKind::Const(n, ls) => format!(
                                    "[\"C\",{},[{}]]",
                                    js(&n.to_string()),
                                    ls.iter().map(level).collect::<Vec<_>>().join(",")
                                ),
                                ExprKind::App(f, a) => {
                                    format!("[\"A\",{},{}]", id_of(self, f), id_of(self, a))
                                }
                                ExprKind::Lam(bd, t, b) => format!(
                                    "[\"L\",{},{},{}]",
                                    js(&format!("{:?}", bd.info)),
                                    id_of(self, t),
                                    id_of(self, b)
                                ),
                                ExprKind::Pi(bd, t, b) => format!(
                                    "[\"P\",{},{},{}]",
                                    js(&format!("{:?}", bd.info)),
                                    id_of(self, t),
                                    id_of(self, b)
                                ),
                                ExprKind::Let(n, t, v, b, _) => format!(
                                    "[\"Z\",{},{},{},{}]",
                                    js(&n.to_string()),
                                    id_of(self, t),
                                    id_of(self, v),
                                    id_of(self, b)
                                ),
                                ExprKind::Lit(Literal::Nat(n)) => {
                                    format!("[\"N\",{}]", js(&n.to_string()))
                                }
                                ExprKind::Lit(Literal::String(s)) => format!("[\"T\",{}]", js(s)),
                                ExprKind::Proj(n, i, x) => {
                                    format!(
                                        "[\"J\",{},{},{}]",
                                        js(&n.to_string()),
                                        i,
                                        id_of(self, x)
                                    )
                                }
                                other => format!("[\"?\",{}]", js(&format!("{other:?}"))),
                            };
                            self.intern(node)
                        }
                    };
                    self.by_ptr.insert(key, id);
                }
            }
        }
        self.by_ptr[&(root as *const Expr)]
    }
}

fn names(ns: &[Name]) -> String {
    format!("[{}]", ns.iter().map(|n| js(&n.to_string())).collect::<Vec<_>>().join(","))
}

fn form_of(env: &Environment, name: &Name) -> Option<&'static str> {
    if env.get_inductive(name).is_some() {
        return Some("inductive");
    }
    if env.get_constructor(name).is_some() {
        return Some("constructor");
    }
    if env.get_recursor(name).is_some() {
        return Some("recursor");
    }
    if env.get_quot(name).is_some() {
        return Some("quot");
    }
    let c = env.get_const(name)?;
    Some(match c.kind {
        ConstantKind::Definition => "definition",
        ConstantKind::Theorem => "theorem",
        ConstantKind::Opaque => "opaque",
        ConstantKind::Axiom => "axiom",
    })
}

fn main() {
    let env = Environment::with_prelude();
    let mut all: BTreeMap<String, Name> = BTreeMap::new();
    for c in env.constants() {
        all.insert(c.name.to_string(), c.name.clone());
    }
    for i in env.inductives() {
        all.insert(i.name.to_string(), i.name.clone());
    }
    for c in env.constructors() {
        all.insert(c.name.to_string(), c.name.clone());
    }
    for r in env.recursors() {
        all.insert(r.name.to_string(), r.name.clone());
    }
    for q in env.quotients() {
        all.insert(q.name.to_string(), q.name.clone());
    }

    let mut interner = Interner::new();
    let mut decls: Vec<String> = Vec::new();
    for (key, name) in &all {
        let Some(form) = form_of(&env, name) else {
            eprintln!("odt-prelude-probe: {key} has no form");
            std::process::exit(2);
        };
        let konst = env.get_const(name);
        // The type D0.5's facts_of hashes: the constant table's when present.
        let (lparams, ty): (&[Name], &Expr) = if let Some(c) = konst {
            (&c.level_params, &c.type_)
        } else if let Some(i) = env.get_inductive(name) {
            (&i.level_params, &i.type_)
        } else if let Some(c) = env.get_constructor(name) {
            (&c.level_params, &c.type_)
        } else if let Some(r) = env.get_recursor(name) {
            (&r.level_params, &r.type_)
        } else if let Some(q) = env.get_quot(name) {
            (&q.level_params, &q.type_)
        } else {
            eprintln!("odt-prelude-probe: {key} has a form but no type");
            std::process::exit(2);
        };
        let ty_id = interner.expr(ty);
        let value_id = match (form, konst.and_then(|c| c.value.as_ref())) {
            ("definition" | "opaque", Some(v)) => Some(interner.expr(v)),
            _ => None,
        };
        let mut fields: BTreeMap<&str, String> = BTreeMap::new();
        fields.insert("name", js(key));
        fields.insert("form", js(form));
        fields.insert("lparams", names(lparams));
        fields.insert("type", ty_id.to_string());
        fields.insert("in_constant_table", konst.is_some().to_string());
        if let Some(v) = value_id {
            fields.insert("value", v.to_string());
        }
        if let Some(i) = env.get_inductive(name) {
            // The inductive's own recorded type, when the constant table's differs.
            let own = interner.expr(&i.type_);
            fields.insert("inductive_type", own.to_string());
            fields.insert("nparams", i.num_params.to_string());
            fields.insert("nindices", i.num_indices.to_string());
            fields.insert("all", names(&i.all_names));
            fields.insert("ctors", names(&i.constructor_names));
            fields.insert("is_rec", i.is_recursive.to_string());
            fields.insert("is_reflexive", i.is_reflexive.to_string());
            fields.insert("is_nested", i.is_nested.to_string());
            fields.insert("is_large_elim", i.is_large_elim.to_string());
            let sf = env.get_structure_field_names(name);
            fields.insert("structure", sf.is_some().to_string());
            if let Some(sf) = sf {
                fields.insert("structure_fields", names(sf));
            }
            fields.insert("class", env.is_class(name).to_string());
        }
        if let Some(c) = env.get_constructor(name) {
            let own = interner.expr(&c.type_);
            fields.insert("constructor_type", own.to_string());
            fields.insert("induct", js(&c.inductive_name.to_string()));
            fields.insert("cidx", c.constructor_idx.to_string());
            fields.insert("nparams", c.num_params.to_string());
            fields.insert("nfields", c.num_fields.to_string());
        }
        if let Some(r) = env.get_recursor(name) {
            fields.insert("induct", js(&r.inductive_name.to_string()));
            fields.insert("nparams", r.num_params.to_string());
            fields.insert("nindices", r.num_indices.to_string());
            fields.insert("nmotives", r.num_motives.to_string());
            fields.insert("nminors", r.num_minors.to_string());
            fields.insert("nrules", r.rules.len().to_string());
            fields.insert("k", r.is_k.to_string());
        }
        if let Some(q) = env.get_quot(name) {
            let k = match q.kind {
                QuotKind::Type => "type",
                QuotKind::Mk => "mk",
                QuotKind::Lift => "lift",
                QuotKind::Ind => "ind",
                QuotKind::Sound => "sound",
            };
            fields.insert("quot_kind", js(k));
        }
        let body =
            fields.iter().map(|(k, v)| format!("{}:{}", js(k), v)).collect::<Vec<_>>().join(",");
        decls.push(format!("{{{body}}}"));
    }

    let classes: BTreeSet<String> =
        all.iter().filter(|(_, n)| env.is_class(n)).map(|(k, _)| k.clone()).collect();
    let mut out = String::new();
    out.push_str("{\"classes\":[");
    out.push_str(&classes.iter().map(|c| js(c)).collect::<Vec<_>>().join(","));
    out.push_str("],\n\"decls\":[\n");
    out.push_str(&decls.join(",\n"));
    out.push_str("\n],\n\"exprs\":[\n");
    out.push_str(&interner.nodes.join(",\n"));
    out.push_str("\n]}\n");
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    if lock.write_all(out.as_bytes()).and_then(|()| lock.flush()).is_err() {
        std::process::exit(2);
    }
}
