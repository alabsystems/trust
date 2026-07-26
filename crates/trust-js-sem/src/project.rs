// The deep-print projection: a byte-for-byte mirror of js/trace_driver.mjs
// (projectValue / projectObject / projectThrown / escapeString / numberRepr).
// Fresh id-state per projected top-level value; pre-order ids; caps
// depth 8 / keys 64 / nodes 4096 / string 4096. Accessors are recorded
// WITHOUT being invoked (and without an enumerability wrapper, exactly like
// the driver). Anything whose projection would expose engine-divergent
// surface (intrinsic infrastructure, native error instances with engine
// `stack` props, synthetic message text) is a refusal, never a guess.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::Interp;
use crate::number::projection_number_repr;
use crate::value::{ObjId, ObjKind, PropVal, Value};
use std::collections::HashMap;
use trust_js_trace::{ProjectedValue, PropKey, ThrownProjection};

pub const MAX_DEPTH: u32 = 8;
pub const MAX_KEYS: usize = 64;
pub const MAX_NODES: u32 = 4096;
pub const MAX_STRING: usize = 4096;

/// A projection outcome that is not a value.
#[derive(Debug, Clone)]
pub enum ProjErr {
    /// Out of the modeled slice / engine-divergent surface → the case is a
    /// sound `NoCoverage`.
    NoCoverage(String),
    /// Projecting a BigInt: the frozen `trace_driver.mjs` projects a bigint via
    /// `Number.prototype.toString.apply(v, [])`, which throws a TypeError for a
    /// BigInt receiver. So EVERY projection site — a `console.log` argument, the
    /// completion witness, a thrown primitive, or a bigint nested inside a
    /// projected object — actually throws TypeError under the real driver, and
    /// the sem reproduces that exactly rather than emitting the (unreachable)
    /// `{t:"bigint"}` form. Verified end-to-end against the Node driver.
    BigIntTypeError,
}

type P<T> = Result<T, ProjErr>; // Err = projection refusal OR a BigInt throw

fn refuse<T>(msg: impl Into<String>) -> P<T> {
    Err(ProjErr::NoCoverage(msg.into()))
}

struct ProjState {
    seen: HashMap<ObjId, u64>,
    next_id: u64,
    depth: u32,
    nodes: u32,
}

/// Mirror of the driver's `escapeString`, over UTF-16 code units.
#[must_use]
pub fn escape_units(u: &[u16]) -> String {
    let n = u.len().min(MAX_STRING);
    let mut out = String::new();
    for &c in &u[..n] {
        if c == 0x5c {
            out.push_str("\\\\");
        } else if c == 0x22 {
            out.push_str("\\\"");
        } else if (0x20..=0x7e).contains(&c) {
            out.push(char::from(u8::try_from(c).expect("ascii range")));
        } else {
            out.push_str(&format!("\\u{c:04x}"));
        }
    }
    if u.len() > MAX_STRING {
        out.push_str(&format!("\\u2026[truncated:{}]", u.len()));
    }
    out
}

/// Project one top-level value with fresh id-state (one console.log argument,
/// or the completion value).
pub fn project(it: &Interp, v: &Value) -> P<ProjectedValue> {
    let mut st = ProjState {
        seen: HashMap::new(),
        next_id: 0,
        depth: 0,
        nodes: 0,
    };
    project_value(it, v, &mut st)
}

fn project_value(it: &Interp, v: &Value, st: &mut ProjState) -> P<ProjectedValue> {
    st.nodes += 1;
    if st.nodes > MAX_NODES {
        return Ok(ProjectedValue::Nodecap);
    }
    match v {
        Value::Undefined => Ok(ProjectedValue::Undefined),
        Value::Null => Ok(ProjectedValue::Null),
        Value::Bool(b) => Ok(ProjectedValue::Bool { v: *b }),
        Value::Num(n) => Ok(ProjectedValue::Num {
            v: projection_number_repr(*n),
        }),
        // The driver's projectValue does `Number.prototype.toString.apply(v, [])`
        // for a bigint, which throws TypeError — so reaching a bigint under the
        // deep-print walk is a throw, not a value.
        Value::BigInt(_) => Err(ProjErr::BigIntTypeError),
        Value::Str(s) => Ok(ProjectedValue::Str {
            v: escape_units(s),
        }),
        Value::Sym(s) => Ok(crate::symbol::project_symbol(it.sym_data(*s))),
        Value::Obj(id) => {
            // Array.prototype is ObjKind::Array (spec: an Array exotic
            // object), but it is still intrinsic infrastructure whose real
            // engine own-property surface we do not model — refuse by
            // identity, same as IntrinsicOpaque.
            if *id == it.intr.array_proto
                || *id == it.intr.generator_proto
                || *id == it.intr.generator_function_proto
                || *id == it.intr.iterator_proto
                || *id == it.intr.array_iterator_proto
                || *id == it.intr.string_iterator_proto
                || *id == it.intr.symbol_proto
                || *id == it.intr.date_proto
                || *id == it.intr.regexp_proto
                || *id == it.intr.regexp_string_iterator_proto
                || *id == it.intr.promise_proto
                || *id == it.intr.async_function_proto
                || *id == it.intr.map_proto
                || *id == it.intr.set_proto
                || *id == it.intr.weakmap_proto
                || *id == it.intr.weakset_proto
                || *id == it.intr.map_iterator_proto
                || *id == it.intr.set_iterator_proto
                || it.intr.is_binary_proto(*id)
            {
                // Ordinary objects, but with an unmodeled @@toStringTag (and
                // engine-divergent surface): refuse by identity, like
                // Array.prototype.
                return refuse(
                    "projection of intrinsic infrastructure object (engine-divergent surface)",
                );
            }
            let obj = it.obj(*id);
            match &obj.kind {
                ObjKind::Function(_) => {
                    // Own `name` DATA descriptor only; never the prototype's.
                    let name = obj
                        .props
                        .get(&crate::value::units_from_str("name"))
                        .and_then(|p| match &p.val {
                            PropVal::Data {
                                value: Value::Str(s),
                                ..
                            } => Some(escape_units(s)),
                            _ => None,
                        });
                    Ok(ProjectedValue::Fun { name })
                }
                ObjKind::IntrinsicOpaque => refuse(
                    "projection of intrinsic infrastructure object (engine-divergent surface)",
                ),
                // A proxy reaching the deep-print would have its ownKeys /
                // getOwnPropertyDescriptor traps invoked by the projection —
                // unreproducible from a pure read, so refuse soundly.
                ObjKind::Proxy { .. } => {
                    refuse("projection of a Proxy (deep-print would invoke its traps)")
                }
                ObjKind::Error => {
                    refuse("projection of native error instance (engines add own `stack`)")
                }
                // A generator instance is observationally an ordinary object
                // (no own properties; cls resolves to "Object" through the
                // chain), so it projects like a plain object.
                ObjKind::Plain
                | ObjKind::Array
                | ObjKind::Arguments(_)
                | ObjKind::StringObj(_)
                | ObjKind::NumberObj(_)
                | ObjKind::BoolObj(_)
                // A Symbol wrapper (cls "Symbol") / Date (cls "Date") carry no
                // own enumerable string properties; they project like ordinary
                // objects through the chain.
                | ObjKind::SymbolObj(_)
                | ObjKind::DateObj(_)
                | ObjKind::Generator(_)
                // A RegExp object's only own property is `lastIndex` (fully
                // modeled); cls "RegExp" resolves through the chain (Node
                // prints e.g. `/a/g` but the STRUCTURED projection is the
                // ordinary-object form: one non-enumerable `lastIndex`).
                | ObjKind::RegExpObj(_)
                // A RegExp String Iterator has no own properties and cls
                // resolves to "Object" through the chain (Node prints
                // `Object [RegExp String Iterator] {}`).
                | ObjKind::RegExpStringIterator { .. }
                // An array iterator / string iterator has no own properties and
                // its cls resolves to "Object" through the chain — it projects
                // like a plain object (Node: `[].values()` prints `{}`,
                // `"ab"[Symbol.iterator]()` prints `Object [String Iterator] {}`
                // whose STRUCTURED form is the ordinary `{cls:"Object",props:[]}`).
                | ObjKind::ArrayIterator { .. }
                | ObjKind::StringIterator { .. }
                // An ArrayBuffer (cls "ArrayBuffer") / DataView (cls "DataView")
                // has no own enumerable string surface; a typed array (cls
                // "Object" through the chain) projects its element indices as
                // ordinary own data properties — all handled by project_object
                // over `ordered_own_keys_full` + the synthesized element props.
                | ObjKind::ArrayBuffer(_)
                | ObjKind::DataView { .. }
                | ObjKind::TypedArray { .. }
                // A Map/Set/WeakMap/WeakSet instance keeps its entries in an
                // internal slot (no own properties); cls "Map"/"Set"/... resolves
                // through the chain, so it projects like a plain object with that
                // class tag. A Map/Set iterator has no own properties and cls
                // "Object" through the chain.
                | ObjKind::Map(_)
                | ObjKind::Set(_)
                | ObjKind::WeakMap(_)
                | ObjKind::WeakSet(_)
                | ObjKind::MapIterator { .. }
                | ObjKind::SetIterator { .. }
                // A BigInt wrapper (from Object(1n)) has no own enumerable
                // surface; cls "BigInt" resolves through the chain, so it
                // projects like a plain object.
                | ObjKind::BigIntObj(_)
                // A Promise instance has no own enumerable properties and cls
                // "Promise" resolves through the chain (Node prints
                // `Promise { <state> }`, but the STRUCTURED projection is the
                // ordinary-object form: `{ t: obj, cls: "Promise", props: [] }`).
                | ObjKind::Promise(_) => project_object(it, *id, st),
            }
        }
    }
}

fn project_object(it: &Interp, oid: ObjId, st: &mut ProjState) -> P<ProjectedValue> {
    if let Some(&prev) = st.seen.get(&oid) {
        return Ok(ProjectedValue::Circ { target: prev });
    }
    let id = st.next_id;
    st.next_id += 1;
    st.seen.insert(oid, id);
    if st.depth >= MAX_DEPTH {
        return Ok(ProjectedValue::Depthcap { id });
    }
    let obj = it.obj(oid);
    let cls = it.class_tag(oid);
    let keys = it.ordered_own_keys_full(oid);
    // Symbol keys, in enumeration order (after every string key) — the
    // arguments exotic's @@iterator is a real own sym_prop like any other.
    let sym_keys: Vec<crate::value::SymId> = obj.sym_props.keys().copied().collect();
    let total_keys = keys.len() + sym_keys.len();
    let n = keys.len().min(MAX_KEYS);
    let mut props: Vec<(PropKey, ProjectedValue)> = Vec::with_capacity(n);
    st.depth += 1;
    for key in &keys[..n] {
        let key_repr = PropKey::Str(escape_units(key));
        let Some(p) = it.own_prop_resolved(oid, key) else {
            props.push((key_repr, ProjectedValue::Vanished));
            continue;
        };
        if p.synthetic {
            return refuse("projection of engine-specific (synthetic) property text");
        }
        match &p.val {
            PropVal::Data { value, .. } => {
                let pv = project_value(it, value, st)?;
                let entry = if p.enumerable {
                    pv
                } else {
                    ProjectedValue::Nonenum { v: Box::new(pv) }
                };
                props.push((key_repr, entry));
            }
            // Accessors project un-invoked and WITHOUT an enumerability
            // wrapper (the driver pushes them bare).
            PropVal::Accessor { get, set } => {
                props.push((
                    key_repr,
                    ProjectedValue::Accessor {
                        get: get.is_some(),
                        set: set.is_some(),
                    },
                ));
            }
        }
    }
    // Symbol keys fill the remaining MAX_KEYS budget (string keys come first).
    let remaining = MAX_KEYS.saturating_sub(keys.len());
    for sid in sym_keys.iter().take(remaining) {
        // The symbol key itself charges a node in the driver's projectValue.
        let key_pv = project_value(it, &Value::Sym(*sid), st)?;
        let key_repr = PropKey::Sym { sym: Box::new(key_pv) };
        let p = obj.sym_props.get(sid).expect("symbol key present");
        match &p.val {
            PropVal::Data { value, .. } => {
                let pv = project_value(it, value, st)?;
                let entry = if p.enumerable {
                    pv
                } else {
                    ProjectedValue::Nonenum { v: Box::new(pv) }
                };
                props.push((key_repr, entry));
            }
            PropVal::Accessor { get, set } => {
                props.push((
                    key_repr,
                    ProjectedValue::Accessor {
                        get: get.is_some(),
                        set: set.is_some(),
                    },
                ));
            }
        }
    }
    st.depth -= 1;
    Ok(ProjectedValue::Obj {
        id,
        cls,
        props: Some(props),
        unintrospectable: None,
        keycap: if total_keys > MAX_KEYS {
            Some(total_keys as u64)
        } else {
            None
        },
    })
}

/// Mirror of the driver's `projectThrown`: constructor identity + `.name`
/// via the prototype chain (data descriptors only) + proto.constructor.name.
pub fn project_thrown(it: &Interp, v: &Value) -> P<ThrownProjection> {
    let Value::Obj(oid) = v else {
        return Ok(ThrownProjection::Prim {
            v: project(it, v)?,
        });
    };
    // A thrown proxy would have its traps invoked by the driver's deep-print
    // (ctor / name chain walk) — refuse soundly.
    if matches!(it.obj(*oid).kind, ObjKind::Proxy { .. }) {
        return refuse("projection of a thrown Proxy (deep-print would invoke its traps)");
    }
    let ctor = it.class_tag(*oid);
    // .name through the chain, own data descriptors only.
    let mut name: Option<String> = None;
    let name_key = crate::value::units_from_str("name");
    let mut cur = Some(*oid);
    let mut hops = 0;
    while let Some(o) = cur {
        if hops >= 32 {
            break;
        }
        if let Some(p) = it.obj(o).props.get(&name_key) {
            if let PropVal::Data {
                value: Value::Str(s),
                ..
            } = &p.val
            {
                name = Some(escape_units(s));
            }
            break; // any own `name` descriptor stops the walk (accessor → null)
        }
        cur = it.obj(o).proto;
        hops += 1;
    }
    // proto.constructor.name, own data descriptors only.
    let mut ctor_name: Option<String> = None;
    if let Some(proto) = it.obj(*oid).proto {
        let ctor_key = crate::value::units_from_str("constructor");
        if let Some(cp) = it.obj(proto).props.get(&ctor_key) {
            if let PropVal::Data {
                value: Value::Obj(cf),
                ..
            } = &cp.val
            {
                if it.obj(*cf).is_callable() {
                    if let Some(np) = it.obj(*cf).props.get(&name_key) {
                        if let PropVal::Data {
                            value: Value::Str(s),
                            ..
                        } = &np.val
                        {
                            ctor_name = Some(escape_units(s));
                        }
                    }
                }
            }
        }
    }
    Ok(ThrownProjection::Error {
        ctor,
        name,
        ctor_name,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::units_from_str;

    #[test]
    fn escape_vectors() {
        assert_eq!(escape_units(&units_from_str("abc")), "abc");
        assert_eq!(escape_units(&units_from_str("a\"b")), "a\\\"b");
        assert_eq!(escape_units(&units_from_str("a\\b")), "a\\\\b");
        assert_eq!(escape_units(&units_from_str("a\nb")), "a\\u000ab");
        assert_eq!(escape_units(&units_from_str("é")), "\\u00e9");
        assert_eq!(escape_units(&units_from_str("😀")), "\\ud83d\\ude00");
        assert_eq!(escape_units(&[0x0000]), "\\u0000");
        assert_eq!(escape_units(&[0x7e, 0x7f]), "~\\u007f");
        // Truncation: literal … then [truncated:<code-unit len>].
        let long: Vec<u16> = std::iter::repeat_n(0x61, 5000).collect();
        let esc = escape_units(&long);
        assert!(esc.starts_with("aaaa"));
        assert!(esc.ends_with("\\u2026[truncated:5000]"));
        assert_eq!(esc.len(), 4096 + "\\u2026[truncated:5000]".len());
    }
}
