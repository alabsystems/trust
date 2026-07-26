// Private class elements: the runtime half of the private-name web. The
// PARSER owns the static-semantics early errors (undeclared references up the
// nested-class PrivateEnvironment chain and in class heritage, duplicate
// names, `delete`/out-of-class use → SyntaxError), so every private AST node
// that reaches evaluation is a resolved reference; this module implements the
// runtime PrivateEnvironment (lexical name → identity), the per-object
// [[PrivateElements]] side table (invisible to enumeration/reflection/
// projection by construction), and PrivateGet/PrivateSet/PrivateElementFind/
// HasPrivateElement plus the field/method/accessor add operations.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use std::collections::HashMap;
use trust_js_value::{EnvId, JsValue, ObjId};

/// A resolved private-name identity (unique per class-element declaration).
pub(crate) type PrivName = u32;
/// A PrivateEnvironment handle (index into `Interp::priv_envs`).
pub(crate) type PrivEnvId = u32;

/// One PrivateEnvironment: the private names a class body declares, plus the
/// enclosing environment (nested classes / class methods).
pub(crate) struct PrivEnvData {
    pub parent: Option<PrivEnvId>,
    pub names: HashMap<String, PrivName>,
}

/// A [[PrivateElements]] entry: a field (per-instance value), a method (shared
/// function identity), or an accessor pair.
#[derive(Debug, Clone)]
pub(crate) enum PrivElem {
    Field(JsValue),
    Method(ObjId),
    Accessor {
        get: Option<ObjId>,
        set: Option<ObjId>,
    },
}

impl Interp {
    /// NewPrivateEnvironment(outer).
    pub(crate) fn new_priv_env(&mut self, parent: Option<PrivEnvId>) -> PrivEnvId {
        let id = u32::try_from(self.priv_envs.len()).expect("priv envs bounded by caps");
        self.priv_envs.push(PrivEnvData {
            parent,
            names: HashMap::new(),
        });
        id
    }

    /// Bind a private name in a PrivateEnvironment, returning its identity
    /// (idempotent: a `get`/`set` pair for one name shares an identity).
    pub(crate) fn priv_env_bind(&mut self, penv: PrivEnvId, name: &str) -> PrivName {
        if let Some(id) = self.priv_envs[penv as usize].names.get(name) {
            return *id;
        }
        let id = self.next_priv_name;
        self.next_priv_name += 1;
        self.priv_envs[penv as usize]
            .names
            .insert(name.to_string(), id);
        id
    }

    /// The nearest PrivateEnvironment for a lexical environment chain.
    pub(crate) fn nearest_priv_env(&self, env: EnvId) -> Option<PrivEnvId> {
        let mut cur = Some(env);
        while let Some(e) = cur {
            if let Some(p) = self.priv_env_of.get(&e) {
                return Some(*p);
            }
            cur = self.heap.env(e).parent;
        }
        None
    }

    /// ResolvePrivateIdentifier: a private-name string to its identity through
    /// the lexical PrivateEnvironment chain.
    pub(crate) fn resolve_priv(&self, env: EnvId, name: &str) -> Option<PrivName> {
        let mut cur = self.nearest_priv_env(env);
        while let Some(p) = cur {
            let data = &self.priv_envs[p as usize];
            if let Some(id) = data.names.get(name) {
                return Some(*id);
            }
            cur = data.parent;
        }
        None
    }

    /// Resolve or refuse (the parser guarantees resolution — a miss is an
    /// interpreter bug, refused rather than mis-evaluated).
    pub(crate) fn resolve_priv_or_fatal(&self, env: EnvId, name: &str) -> Result<PrivName, Abrupt> {
        self.resolve_priv(env, name).ok_or_else(|| {
            Abrupt::Fatal(format!(
                "unresolved private name #{name} (parser should have early-errored)"
            ))
        })
    }

    /// PrivateElementFind: index of a private element on an object.
    fn priv_index(&self, oid: ObjId, name: PrivName) -> Option<usize> {
        self.priv_elements
            .get(&oid)
            .and_then(|els| els.iter().position(|(n, _)| *n == name))
    }

    /// HasPrivateElement (the `#x in obj` observable).
    pub(crate) fn priv_has(&self, oid: ObjId, name: PrivName) -> bool {
        self.priv_index(oid, name).is_some()
    }

    /// PrivateFieldAdd / PrivateMethodOrAccessorAdd: append, or TypeError when
    /// the object already carries the brand (re-adding a private element).
    pub(crate) fn priv_add(
        &mut self,
        oid: ObjId,
        name: PrivName,
        elem: PrivElem,
    ) -> Result<(), Abrupt> {
        if self.priv_index(oid, name).is_some() {
            return Err(self.throw_type_error());
        }
        self.priv_elements.entry(oid).or_default().push((name, elem));
        Ok(())
    }

    /// PrivateGet(O, P).
    pub(crate) fn private_get(&mut self, base: &JsValue, name: PrivName) -> ERes {
        let JsValue::Obj(oid) = base else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        let Some(i) = self.priv_index(oid, name) else {
            return Err(self.throw_type_error());
        };
        match self.priv_elements[&oid][i].1.clone() {
            PrivElem::Field(v) => Ok(v),
            PrivElem::Method(f) => Ok(JsValue::Obj(f)),
            PrivElem::Accessor { get, .. } => match get {
                Some(g) => self.call_value(&JsValue::Obj(g), base.clone(), vec![]),
                None => Err(self.throw_type_error()),
            },
        }
    }

    /// PrivateSet(O, P, value).
    pub(crate) fn private_set(
        &mut self,
        base: &JsValue,
        name: PrivName,
        v: JsValue,
    ) -> Result<(), Abrupt> {
        let JsValue::Obj(oid) = base else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        let Some(i) = self.priv_index(oid, name) else {
            return Err(self.throw_type_error());
        };
        match self.priv_elements[&oid][i].1.clone() {
            PrivElem::Field(_) => {
                if let PrivElem::Field(slot) = &mut self.priv_elements.get_mut(&oid).expect("present")[i].1 {
                    *slot = v;
                }
                Ok(())
            }
            PrivElem::Method(_) => Err(self.throw_type_error()),
            PrivElem::Accessor { set, .. } => match set {
                Some(s) => {
                    self.call_value(&JsValue::Obj(s), base.clone(), vec![v])?;
                    Ok(())
                }
                None => Err(self.throw_type_error()),
            },
        }
    }

    /// The `#name in rval` relational operator (13.10.1): TypeError on a
    /// non-object right operand, else HasPrivateElement.
    pub(crate) fn private_brand_check(&mut self, name: PrivName, rval: &JsValue) -> ERes {
        let JsValue::Obj(oid) = rval else {
            return Err(self.throw_type_error());
        };
        Ok(JsValue::Bool(self.priv_has(*oid, name)))
    }
}
