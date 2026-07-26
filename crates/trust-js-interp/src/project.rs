// The deep-print projection: a byte-for-byte mirror of the trace driver
// (js/trace_driver.mjs: projectValue / projectObject / projectThrown /
// escapeString / numberRepr), re-derived independently of trust-js-sem.
// Fresh id-state per projected top-level value; pre-order ids; caps depth 8 /
// keys 64 / nodes 4096 / string 4096; ASCII code-unit escaping (lone
// surrogates survive); accessor non-invocation; Error-class incidental-key
// filtering. Anything whose projection would expose engine-divergent surface
// (intrinsic infrastructure, native error instances, synthetic message text)
// refuses — Err(reason) makes the whole case NoCoverage.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::Interp;
use std::collections::HashMap;
use trust_js_trace::{ProjectedValue, PropKey as TraceKey, ThrownProjection};
use trust_js_value::{
    ordered_own_keys, projection_number_repr, JsValue, ObjId, ObjKind, PropKey, PropValue,
    Property, SymId,
};

pub const MAX_DEPTH: u32 = 8;
pub const MAX_KEYS: usize = 64;
pub const MAX_NODES: u32 = 4096;
pub const MAX_STRING: usize = 4096;

/// Engine-incidental own properties on Error-class objects, filtered by the
/// driver (calibration ruling recorded there).
const ERROR_INCIDENTAL_KEYS: [&str; 6] = [
    "stack",
    "line",
    "column",
    "sourceURL",
    "originalLine",
    "originalColumn",
];

type P<T> = Result<T, String>;

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

/// Project one top-level value with fresh id-state (one console.log
/// argument, or a thrown primitive).
pub fn project(it: &Interp, v: &JsValue) -> P<ProjectedValue> {
    let mut st = ProjState {
        seen: HashMap::new(),
        next_id: 0,
        depth: 0,
        nodes: 0,
    };
    project_value(it, v, &mut st)
}

#[allow(clippy::unnecessary_wraps)]
fn project_sym(it: &Interp, sym: SymId) -> P<ProjectedValue> {
    match sym {
        SymId::WellKnown(wk) => Ok(ProjectedValue::Sym {
            wk: Some(wk.projection_name().to_string()),
            v: None,
        }),
        SymId::User(i) => {
            let desc = it
                .heap
                .symbols
                .get(i as usize)
                .cloned()
                .flatten()
                .map(|d| escape_units(&d));
            Ok(ProjectedValue::Sym { wk: None, v: desc })
        }
    }
}

fn project_value(it: &Interp, v: &JsValue, st: &mut ProjState) -> P<ProjectedValue> {
    st.nodes += 1;
    if st.nodes > MAX_NODES {
        return Ok(ProjectedValue::Nodecap);
    }
    match v {
        JsValue::Undefined => Ok(ProjectedValue::Undefined),
        JsValue::Null => Ok(ProjectedValue::Null),
        JsValue::Bool(b) => Ok(ProjectedValue::Bool { v: *b }),
        JsValue::Num(n) => Ok(ProjectedValue::Num {
            v: projection_number_repr(*n),
        }),
        JsValue::Str(s) => Ok(ProjectedValue::Str { v: escape_units(s) }),
        JsValue::Sym(sym) => project_sym(it, *sym),
        JsValue::BigInt(b) => Ok(ProjectedValue::Bigint {
            v: trust_js_value::bigint_to_decimal(b),
        }),
        JsValue::Obj(oid) => {
            let obj = it.heap.obj(*oid);
            match &obj.kind {
                ObjKind::Function(_) => {
                    // Own `name` DATA descriptor only; a non-string or
                    // accessor name projects as null. A SYNTHETIC name (the
                    // paren-ambiguous assignment inference) refuses.
                    let name = match obj.props.get(&PropKey::from_str("name")) {
                        Some(Property {
                            v: PropValue::Data { value: JsValue::Str(s), .. },
                            synthetic,
                            ..
                        }) => {
                            if *synthetic {
                                return Err(
                                    "projection of an ambiguously-inferred function name"
                                        .to_string(),
                                );
                            }
                            Some(escape_units(s))
                        }
                        _ => None,
                    };
                    Ok(ProjectedValue::Fun { name })
                }
                ObjKind::IntrinsicHost => Err(
                    "projection of intrinsic infrastructure (engine-divergent own surface)"
                        .to_string(),
                ),
                ObjKind::Generator => Err(
                    "projection of a generator object (engine-divergent own surface)".to_string(),
                ),
                ObjKind::AsyncGenerator => Err(
                    "projection of an async generator object (engine-divergent own surface)"
                        .to_string(),
                ),
                ObjKind::ArrayBuffer(_) => Err(
                    "projection of an ArrayBuffer (engine-divergent own surface)".to_string(),
                ),
                ObjKind::DataView(_) => {
                    Err("projection of a DataView (engine-divergent own surface)".to_string())
                }
                ObjKind::TypedArray(_) => Err(
                    "projection of a typed array (integer-indexed exotic own surface)".to_string(),
                ),
                // The driver's deep-print invokes the ownKeys +
                // getOwnPropertyDescriptor traps on a proxy; the pure `&Interp`
                // projection cannot run those (they mutate / can throw / have
                // side effects), so a proxy that reaches the projection refuses
                // (NoCoverage). Trap-invocation / invariant tests assert
                // synchronously and never log the proxy, so they still cover.
                ObjKind::Proxy(_) => Err(
                    "projection of a Proxy exotic object (deep-print would invoke its \
                     ownKeys/getOwnPropertyDescriptor traps)"
                        .to_string(),
                ),
                ObjKind::Error => {
                    Err("projection of a native error instance (engine `stack` surface)"
                        .to_string())
                }
                // A module namespace exotic deep-prints engine-specifically
                // (Node renders `[Module: null prototype] { … }`); rather than
                // model the driver's exact rendering, refuse projecting it
                // (sound NoCoverage). Namespace tests assert on `ns.x` /
                // descriptors and never log the namespace, so they still cover.
                ObjKind::ModuleNamespace => Err(
                    "projection of a Module Namespace exotic object (engine-divergent deep-print)"
                        .to_string(),
                ),
                // A built-in iterator object has NO own properties (its state
                // is in the side table, not the heap object), so it deep-prints
                // as an ordinary empty object with class tag "Object" — its
                // @@toStringTag lives on the prototype and the driver tags by
                // intrinsic-prototype identity, never seeing it. A user-added
                // own property still projects (ordinary [[Set]] applies).
                ObjKind::Iterator
                | ObjKind::Plain
                | ObjKind::Array
                | ObjKind::Arguments(_)
                | ObjKind::Wrapper(_)
                | ObjKind::Date(_)
                | ObjKind::Regex(_)
                | ObjKind::MapObj(_)
                | ObjKind::SetObj(_)
                | ObjKind::WeakMapObj(_)
                | ObjKind::WeakSetObj(_)
                // A Promise projects as an ordinary object: its class tag is
                // "Promise" (via the prototype chain) and its own enumerable
                // surface is whatever the user attached — the internal state
                // lives in the reactor, never as own properties. Matches the
                // driver, which deep-prints a Promise as `{cls:'Promise'}` with
                // no engine-incidental own keys.
                | ObjKind::Promise(_) => {
                    if *oid == it.intr.array_proto {
                        return Err(
                            "projection of %Array.prototype% (engine-divergent own surface)"
                                .to_string(),
                        );
                    }
                    project_object(it, *oid, st)
                }
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
    let cls = it.class_tag(oid);
    let mut keys = ordered_own_keys(it.heap.obj(oid));
    // The driver filters engine-incidental keys from Error-class objects.
    if cls.as_deref().is_some_and(|c| c.starts_with("Error:")) {
        keys.retain(|k| match k {
            PropKey::Str(u) => {
                let name = trust_js_value::units_to_lossy(u);
                !ERROR_INCIDENTAL_KEYS.contains(&name.as_str())
            }
            PropKey::Sym(_) => true,
        });
    }
    let total = keys.len();
    let n = total.min(MAX_KEYS);
    let mut props: Vec<(TraceKey, ProjectedValue)> = Vec::with_capacity(n);
    st.depth += 1;
    for key in keys.into_iter().take(n) {
        let key_repr = match &key {
            PropKey::Str(u) => TraceKey::Str(escape_units(u)),
            PropKey::Sym(s) => TraceKey::Sym {
                sym: Box::new(project_sym(it, *s)?),
            },
        };
        // own_prop merges the arguments parameter map, mirroring the
        // driver's getOwnPropertyDescriptor view.
        let Some(p) = it.own_prop(oid, &key) else {
            props.push((key_repr, ProjectedValue::Vanished));
            continue;
        };
        match &p.v {
            PropValue::Data { value, .. } => {
                if p.synthetic {
                    return Err("projection of engine-specific synthetic text".to_string());
                }
                let pv = project_value(it, value, st)?;
                let entry = if p.enumerable {
                    pv
                } else {
                    ProjectedValue::Nonenum { v: Box::new(pv) }
                };
                props.push((key_repr, entry));
            }
            PropValue::Accessor { get, set } => {
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
        keycap: if total > MAX_KEYS {
            Some(total as u64)
        } else {
            None
        },
    })
}

/// Mirror of the driver's `projectThrown`: constructor identity + `.name`
/// via the prototype chain (own DATA descriptors only) +
/// proto.constructor.name.
pub fn project_thrown(it: &Interp, v: &JsValue) -> P<ThrownProjection> {
    let JsValue::Obj(oid) = v else {
        return Ok(ThrownProjection::Prim { v: project(it, v)? });
    };
    // A thrown proxy's constructor/name walk would invoke its traps; refuse.
    if matches!(it.heap.obj(*oid).kind, ObjKind::Proxy(_)) {
        return Err("thrown value is a Proxy exotic object (trap-invoking projection)".to_string());
    }
    let ctor = it.class_tag(*oid);
    let name_key = PropKey::from_str("name");
    let mut name: Option<String> = None;
    let mut cur = Some(*oid);
    let mut hops = 0;
    while let Some(o) = cur {
        if hops >= 32 {
            break;
        }
        match it.own_prop(o, &name_key) {
            Some(p) => {
                if let PropValue::Data { value: JsValue::Str(s), .. } = &p.v {
                    if p.synthetic {
                        return Err("thrown `.name` is synthetic text".to_string());
                    }
                    name = Some(escape_units(s));
                }
                break; // any own `name` descriptor stops the walk
            }
            None => {
                if let Some(gap) = it.own_miss_gap(o, &name_key) {
                    return Err(format!("thrown `.name` walk: {gap}"));
                }
            }
        }
        cur = it.heap.obj(o).proto;
        hops += 1;
    }
    // proto.constructor.name, own DATA descriptors only.
    let ctor_key = PropKey::from_str("constructor");
    let mut ctor_name: Option<String> = None;
    if let Some(proto) = it.heap.obj(*oid).proto {
        match it.own_prop(proto, &ctor_key) {
            Some(cp) => {
                if let PropValue::Data { value: JsValue::Obj(cf), .. } = &cp.v {
                    if it.heap.obj(*cf).is_callable() {
                        if let Some(np) = it.own_prop(*cf, &name_key) {
                            if np.synthetic {
                                return Err(
                                    "thrown ctor `.name` is ambiguously inferred".to_string()
                                );
                            }
                            if let PropValue::Data { value: JsValue::Str(s), .. } = &np.v {
                                ctor_name = Some(escape_units(s));
                            }
                        } else if let Some(gap) = it.own_miss_gap(*cf, &name_key) {
                            return Err(format!("thrown ctor `.name`: {gap}"));
                        }
                    }
                }
            }
            None => {
                if let Some(gap) = it.own_miss_gap(proto, &ctor_key) {
                    return Err(format!("thrown proto `.constructor`: {gap}"));
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
    use trust_js_value::units_from_str;

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
        assert_eq!(escape_units(&[0xd800]), "\\ud800"); // lone surrogate
        let long: Vec<u16> = std::iter::repeat_n(0x61, 5000).collect();
        let esc = escape_units(&long);
        assert!(esc.starts_with("aaaa"));
        assert!(esc.ends_with("\\u2026[truncated:5000]"));
        assert_eq!(esc.len(), 4096 + "\\u2026[truncated:5000]".len());
    }
}
