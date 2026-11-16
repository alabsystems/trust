//! Lexical identifier diagnostics for decoded syntax, not a Lean IR type,
//! effect, refcount, lifetime, linking or refinement checker.
use std::collections::BTreeMap;

use serde_json::{Value, json};

type R<T> = Result<T, String>;
type Scope = BTreeMap<u64, usize>;
type Joins = BTreeMap<u64, (usize, usize)>;

struct Audit {
    seen: Scope,
    definitions: Vec<Value>,
    references: Vec<Value>,
    calls: Vec<Value>,
    effects: Vec<Value>,
    budget: usize,
}

fn identifier(value: &Value) -> R<u64> {
    value
        .as_u64()
        .filter(|n| *n <= i64::MAX as u64)
        .ok_or_else(|| "unsupported identifier value".into())
}

fn array(value: &Value) -> R<&[Value]> {
    let values = value.as_array().ok_or("expected array")?;
    if values.len() > 10_000 {
        return Err("identifier array population bound".into());
    }
    Ok(values)
}

fn node<'a>(value: &'a Value, shapes: &[(&str, usize)]) -> R<(&'a str, &'a [Value])> {
    let object = value.as_object().ok_or("expected AST node")?;
    if object.len() != 2 {
        return Err("noncanonical AST node keys".into());
    }
    let kind = value["kind"].as_str().ok_or("missing node kind")?;
    let args = array(&value["args"])?;
    if !shapes.iter().any(|(k, n)| *k == kind && *n == args.len()) {
        return Err(format!("unknown AST node/arity: {kind}/{}", args.len()));
    }
    Ok((kind, args))
}

impl Audit {
    fn tick(&mut self, depth: usize) -> R<()> {
        self.budget = self.budget.checked_sub(1).ok_or("identifier traversal resource bound")?;
        if depth >= 256 {
            return Err("identifier traversal depth bound".into());
        }
        Ok(())
    }

    fn define(&mut self, value: &Value, kind: &str, path: &str, ty: &Value) -> R<(u64, usize)> {
        self.tick(0)?;
        let id = identifier(value)?;
        if self.seen.contains_key(&id) {
            return Err(format!("duplicate variable/join ID {id}"));
        }
        let index = self.definitions.len();
        self.definitions.push(json!({"id":id,"kind":kind,"path":path,"type":ty}));
        self.seen.insert(id, index);
        Ok((id, index))
    }

    fn reference(&mut self, value: &Value, scope: &Scope, path: &str) -> R<()> {
        self.tick(0)?;
        let id = identifier(value)?;
        let index = scope
            .get(&id)
            .ok_or_else(|| format!("undefined/out-of-scope variable {id} at {path}"))?;
        self.references.push(json!({"id":id,"kind":"variable","path":path,"definition_path":self.definitions[*index]["path"]}));
        Ok(())
    }

    fn params(&mut self, values: &Value, scope: &Scope, path: &str) -> R<Scope> {
        let mut result = scope.clone();
        for (i, param) in array(values)?.iter().enumerate() {
            let object = param.as_object().ok_or("malformed parameter")?;
            if object.len() != 3 || !object.contains_key("ty") || !param["borrow"].is_boolean() {
                return Err("malformed parameter".into());
            }
            let (id, index) =
                self.define(&param["x"], "parameter", &format!("{path}/{i}"), &param["ty"])?;
            result.insert(id, index);
        }
        Ok(result)
    }

    fn arg(&mut self, value: &Value, scope: &Scope, path: &str) -> R<()> {
        self.tick(0)?;
        let (kind, args) = node(value, &[("var", 1), ("erased", 0)])?;
        if kind == "var" {
            self.reference(&args[0], scope, path)?;
        }
        Ok(())
    }

    fn args(&mut self, values: &Value, scope: &Scope, path: &str) -> R<()> {
        for (i, arg) in array(values)?.iter().enumerate() {
            self.arg(arg, scope, &format!("{path}/{i}"))?;
        }
        Ok(())
    }

    fn expression(&mut self, value: &Value, scope: &Scope, path: &str) -> R<()> {
        self.tick(0)?;
        let (kind, a) = node(
            value,
            &[
                ("ctor", 2),
                ("reset", 2),
                ("reuse", 4),
                ("proj", 2),
                ("uproj", 2),
                ("sproj", 3),
                ("fap", 2),
                ("pap", 2),
                ("ap", 2),
                ("box", 2),
                ("unbox", 1),
                ("lit", 1),
                ("isShared", 1),
            ],
        )?;
        match kind {
            "ctor" => self.args(&a[1], scope, &format!("{path}/ctor_args"))?,
            "reset" => self.reference(&a[1], scope, &format!("{path}/reset"))?,
            "reuse" => {
                self.reference(&a[0], scope, &format!("{path}/reuse"))?;
                self.args(&a[3], scope, &format!("{path}/reuse_args"))?;
            }
            "proj" | "uproj" | "box" => self.reference(&a[1], scope, &format!("{path}/{kind}"))?,
            "sproj" => self.reference(&a[2], scope, &format!("{path}/sproj"))?,
            "fap" | "pap" => {
                self.args(&a[1], scope, &format!("{path}/call_args"))?;
                self.calls.push(json!({"path":path,"kind":kind,"callee":a[0],"arguments":a[1],
                    "binding":"typed name retained; transitive body/effect contract not established"}));
            }
            "ap" => {
                self.reference(&a[0], scope, &format!("{path}/function"))?;
                self.args(&a[1], scope, &format!("{path}/call_args"))?;
                self.calls.push(json!({"path":path,"kind":kind,"function_value":a[0],"arguments":a[1],"binding":"indirect target unmeasured"}));
            }
            "unbox" | "isShared" => self.reference(&a[0], scope, &format!("{path}/{kind}"))?,
            "lit" => {
                node(&a[0], &[("num", 1), ("str", 1)])?;
            }
            _ => return Err("unknown expression".into()),
        }
        if matches!(
            kind,
            "ctor" | "reset" | "reuse" | "proj" | "uproj" | "sproj" | "box" | "unbox" | "isShared"
        ) {
            self.effects.push(
                json!({"path":path,"kind":kind,"semantics":"unmeasured; operation not erased"}),
            );
        }
        Ok(())
    }

    fn body(
        &mut self,
        value: &Value,
        scope: &Scope,
        joins: &Joins,
        path: &str,
        depth: usize,
    ) -> R<()> {
        self.tick(depth)?;
        let (kind, a) = node(
            value,
            &[
                ("vdecl", 4),
                ("jdecl", 4),
                ("set", 4),
                ("setTag", 3),
                ("uset", 4),
                ("sset", 6),
                ("inc", 5),
                ("dec", 5),
                ("del", 2),
                ("case", 4),
                ("ret", 1),
                ("jmp", 2),
                ("unreachable", 0),
            ],
        )?;
        match kind {
            "vdecl" => {
                // A local is not in scope in its own initializer.
                self.expression(&a[2], scope, &format!("{path}/expr"))?;
                let mut next = scope.clone();
                let (id, index) = self.define(&a[0], "local", &format!("{path}/bind"), &a[1])?;
                next.insert(id, index);
                self.body(&a[3], &next, joins, &format!("{path}/then"), depth + 1)?;
            }
            "jdecl" => {
                let arity = array(&a[1])?.len();
                let (id, index) =
                    self.define(&a[0], "join", &format!("{path}/join"), &Value::Null)?;
                self.definitions[index]["arity"] = json!(arity);
                let inside = self.params(&a[1], scope, &format!("{path}/join_params"))?;
                // Match pinned Lean IR Checker: a join is not in scope in its
                // own body, and its parameters do not leak to continuation.
                self.body(&a[2], &inside, joins, &format!("{path}/join_body"), depth + 1)?;
                let mut next_joins = joins.clone();
                next_joins.insert(id, (index, arity));
                self.body(&a[3], scope, &next_joins, &format!("{path}/then"), depth + 1)?;
            }
            "case" => {
                self.reference(&a[1], scope, &format!("{path}/scrutinee"))?;
                for (i, alt) in array(&a[3])?.iter().enumerate() {
                    let (_, args) = node(alt, &[("ctor", 2), ("default", 1)])?;
                    let child = args.last().ok_or("alternative has no body")?;
                    self.body(child, scope, joins, &format!("{path}/alt/{i}"), depth + 1)?;
                }
            }
            "ret" => self.arg(&a[0], scope, &format!("{path}/return"))?,
            "jmp" => {
                let id = identifier(&a[0])?;
                let (index, arity) = joins
                    .get(&id)
                    .ok_or_else(|| format!("undefined/out-of-scope join {id} at {path}"))?;
                self.references.push(json!({"id":id,"kind":"join","path":format!("{path}/target"),"definition_path":self.definitions[*index]["path"]}));
                self.args(&a[1], scope, &format!("{path}/jump_args"))?;
                if array(&a[1])?.len() != *arity {
                    return Err("join argument arity mismatch".into());
                }
            }
            "unreachable" => {}
            "set" | "setTag" | "uset" | "sset" | "inc" | "dec" | "del" => {
                self.reference(&a[0], scope, &format!("{path}/{kind}_target"))?;
                match kind {
                    "set" => self.arg(&a[2], scope, &format!("{path}/stored"))?,
                    "uset" => self.reference(&a[2], scope, &format!("{path}/stored"))?,
                    "sset" => self.reference(&a[3], scope, &format!("{path}/stored"))?,
                    "inc" | "dec" if !a[2].is_boolean() || !a[3].is_boolean() => {
                        return Err("noncanonical RC flags".into());
                    }
                    _ => {}
                }
                self.effects.push(json!({"path":path,"kind":kind,"semantics":"unmeasured; no refcount/lifetime proof"}));
                self.body(
                    a.last().ok_or("missing continuation")?,
                    scope,
                    joins,
                    &format!("{path}/then"),
                    depth + 1,
                )?;
            }
            _ => return Err("unknown body".into()),
        }
        Ok(())
    }
}

pub(super) fn audit(declaration: &Value) -> Value {
    let mut audit = Audit {
        seen: Scope::new(),
        definitions: Vec::new(),
        references: Vec::new(),
        calls: Vec::new(),
        effects: Vec::new(),
        budget: 100_000,
    };
    let result = (|| -> R<()> {
        let scope = audit.params(&declaration["params"], &Scope::new(), "params")?;
        match declaration["kind"].as_str() {
            Some("fdecl") => audit.body(&declaration["body_ast"], &scope, &Joins::new(), "body", 0),
            Some("extern") => Ok(()),
            _ => Err("unknown declaration kind".into()),
        }
    })();
    let errors: Vec<String> = result.err().into_iter().collect();
    json!({"owner":declaration["name"], "status":if errors.is_empty() {"identifier-bindings-resolved-only"} else {"unmeasured"},
        "definitions":audit.definitions,"references":audit.references,"calls":audit.calls,"effects":audit.effects,"errors":errors,
        "type_or_lifetime_or_refinement_authority":false})
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(kind: &str, args: Vec<Value>) -> Value {
        json!({"kind":kind,"args":args})
    }
    fn ret(id: u64) -> Value {
        n("ret", vec![n("var", vec![json!(id)])])
    }
    fn param(id: u64) -> Value {
        json!({"x":id,"ty":"uint8","borrow":false})
    }
    fn decl(body: Value) -> Value {
        json!({"kind":"fdecl","name":[{"kind":"str","value":"Quoted.fn"}],"params":[param(0)],"body_ast":body})
    }
    fn failed(body: Value, message: &str) {
        let result = audit(&decl(body));
        assert_eq!(result["status"], "unmeasured");
        assert!(result["errors"][0].as_str().unwrap().contains(message), "{result}");
        assert_eq!(result["type_or_lifetime_or_refinement_authority"], false);
    }
    fn join(body: Value, continuation: Value) -> Value {
        n("jdecl", vec![json!(1), json!([param(2)]), body, continuation])
    }
    fn jump(id: u64, count: usize) -> Value {
        n("jmp", vec![json!(id), json!(vec![n("erased", vec![]); count])])
    }

    #[test]
    fn joins_resolve_parameters_and_continuation_without_claiming_types() {
        let result = audit(&decl(join(ret(2), jump(1, 1))));
        assert_eq!(result["status"], "identifier-bindings-resolved-only");
        assert_eq!(result["definitions"].as_array().unwrap().len(), 3);
        assert_eq!(result["references"][1]["kind"], "join");
        assert_eq!(result["type_or_lifetime_or_refinement_authority"], false);
    }
    #[test]
    fn undefined_and_future_local_reads_refuse() {
        failed(ret(9), "out-of-scope variable");
        failed(
            n("vdecl", vec![json!(1), json!("uint8"), n("unbox", vec![json!(1)]), ret(1)]),
            "out-of-scope variable",
        );
    }
    #[test]
    fn duplicated_ids_across_roles_refuse() {
        failed(
            n("vdecl", vec![json!(0), json!("uint8"), n("unbox", vec![json!(0)]), ret(0)]),
            "duplicate",
        );
        failed(n("jdecl", vec![json!(0), json!([]), ret(0), ret(0)]), "duplicate");
        let mut d = decl(ret(0));
        d["params"] = json!([param(0), param(0)]);
        assert_eq!(audit(&d)["status"], "unmeasured");
    }
    #[test]
    fn join_self_reference_and_wrong_arity_refuse() {
        failed(join(jump(1, 1), jump(1, 1)), "out-of-scope join");
        failed(join(ret(2), jump(1, 0)), "arity mismatch");
        failed(jump(99, 0), "out-of-scope join");
    }
    #[test]
    fn join_parameters_do_not_leak() {
        failed(join(ret(2), ret(2)), "out-of-scope variable");
    }
    #[test]
    fn branch_local_does_not_leak_and_branch_ids_remain_unique() {
        let local = n("vdecl", vec![json!(1), json!("uint8"), n("unbox", vec![json!(0)]), ret(1)]);
        let case = |right| {
            n(
                "case",
                vec![
                    json!([]),
                    json!(0),
                    json!("uint8"),
                    json!([n("default", vec![local.clone()]), n("default", vec![right])]),
                ],
            )
        };
        failed(case(ret(1)), "out-of-scope variable");
        failed(case(local.clone()), "duplicate");
    }
    #[test]
    fn retained_calls_and_memory_operations_do_not_grant_effect_authority() {
        let call = n(
            "fap",
            vec![
                json!([{"kind":"str","value":"callee.with.dot"}]),
                json!([n("var", vec![json!(0)])]),
            ],
        );
        let body = n(
            "vdecl",
            vec![
                json!(1),
                json!("uint8"),
                call,
                n("set", vec![json!(1), json!(0), n("var", vec![json!(0)]), ret(1)]),
            ],
        );
        let result = audit(&decl(body));
        assert_eq!(result["status"], "identifier-bindings-resolved-only");
        assert_eq!(result["calls"][0]["callee"][0]["value"], "callee.with.dot");
        assert_eq!(result["effects"][0]["kind"], "set");
        assert_eq!(result["type_or_lifetime_or_refinement_authority"], false);
    }
    #[test]
    fn unknown_nodes_malformed_flags_and_stored_reads_refuse() {
        failed(n("future-body", vec![]), "unknown AST");
        failed(n("inc", vec![json!(0), json!(1), json!(2), json!(false), ret(0)]), "RC flags");
        failed(
            n("set", vec![json!(0), json!(0), n("var", vec![json!(99)]), ret(0)]),
            "out-of-scope variable",
        );
    }
    #[test]
    fn ids_and_traversal_are_bounded() {
        failed(ret(u64::MAX), "unsupported identifier");
        let mut body = ret(0);
        for _ in 0..256 {
            body = n("inc", vec![json!(0), json!(1), json!(true), json!(false), body]);
        }
        failed(body, "depth bound");
    }
}
