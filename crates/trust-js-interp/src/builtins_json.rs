// JSON (S1c): full JSON.parse (25.5.1) with the reviver walk and the
// json-parse-with-source context BOTH ENGINES ship (adversarially verified:
// the reviver receives a third argument — `{ source }` for a primitive
// position whose value is still SameValue-equal to what was parsed there,
// `{}` otherwise), and full JSON.stringify (25.5.2) with replacer
// function/array, space, toJSON, wrapper unwrapping, exact key ordering and
// cycle detection. Serialization walks only fully-modeled own surfaces —
// anything touching an unmodeled exotic refuses.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp, MAX_STRING_UNITS};
use crate::props::PartialDesc;
use std::rc::Rc;
use trust_js_value::{
    js_number_to_string, to_integer_or_infinity, units_from_str, ErrKind, JsValue, ObjId,
    ObjKind, PropKey, Property, Units, WrapperPrim,
};

// ---------------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------------

/// Snapshot of one parsed position, for the reviver's source context.
pub(crate) enum JNode {
    Prim {
        v: JsValue,
        /// The exact source text slice of this literal.
        src: Units,
    },
    Arr {
        oid: ObjId,
        elems: Vec<JNode>,
    },
    Obj {
        oid: ObjId,
        /// Last-wins per key (duplicate keys overwrite, spec
        /// CreateDataProperty order).
        props: Vec<(Units, JNode)>,
    },
}

impl JNode {
    fn child_index(&self, i: usize) -> Option<&JNode> {
        match self {
            JNode::Arr { elems, .. } => elems.get(i),
            _ => None,
        }
    }

    fn child_key(&self, key: &Units) -> Option<&JNode> {
        match self {
            JNode::Obj { props, .. } => props
                .iter()
                .rev()
                .find(|(k, _)| k == key)
                .map(|(_, n)| n),
            _ => None,
        }
    }
}

struct JParser<'a, 'it> {
    s: &'a [u16],
    i: usize,
    it: &'it mut Interp,
    depth: u32,
}

impl JParser<'_, '_> {
    fn err(&mut self) -> Abrupt {
        self.it.throw_native_syntax()
    }

    fn ws(&mut self) {
        while let Some(&c) = self.s.get(self.i) {
            if matches!(c, 0x09 | 0x0a | 0x0d | 0x20) {
                self.i += 1;
            } else {
                break;
            }
        }
    }

    fn parse_value(&mut self) -> Result<JNode, Abrupt> {
        self.depth += 1;
        if self.depth > 512 {
            return Err(Abrupt::Fatal("JSON nesting cap exceeded".to_string()));
        }
        let r = self.parse_value_inner();
        self.depth -= 1;
        r
    }

    #[allow(clippy::too_many_lines)]
    fn parse_value_inner(&mut self) -> Result<JNode, Abrupt> {
        self.ws();
        let start = self.i;
        let Some(&c) = self.s.get(self.i) else {
            return Err(self.err());
        };
        match c {
            0x7b => {
                // '{'
                self.i += 1;
                let oid = self.it.new_plain()?;
                let mut props: Vec<(Units, JNode)> = Vec::new();
                self.ws();
                if self.s.get(self.i) == Some(&0x7d) {
                    self.i += 1;
                    return Ok(JNode::Obj { oid, props });
                }
                loop {
                    self.it.charge_loop()?;
                    self.ws();
                    if self.s.get(self.i) != Some(&0x22) {
                        return Err(self.err());
                    }
                    let key = self.parse_string_body()?;
                    self.ws();
                    if self.s.get(self.i) != Some(&0x3a) {
                        return Err(self.err());
                    }
                    self.i += 1;
                    let node = self.parse_value()?;
                    let v = node_value(&node);
                    let ok = self.it.define_own(
                        oid,
                        &PropKey::Str(key.clone()),
                        PartialDesc::full_data(v, true, true, true),
                    )?;
                    if !ok {
                        return Err(self.it.throw_type_error());
                    }
                    props.push((key, node));
                    self.ws();
                    match self.s.get(self.i) {
                        Some(&0x2c) => {
                            self.i += 1;
                        }
                        Some(&0x7d) => {
                            self.i += 1;
                            return Ok(JNode::Obj { oid, props });
                        }
                        _ => return Err(self.err()),
                    }
                }
            }
            0x5b => {
                // '['
                self.i += 1;
                let oid = self.it.new_array(0)?;
                let mut elems: Vec<JNode> = Vec::new();
                self.ws();
                if self.s.get(self.i) == Some(&0x5d) {
                    self.i += 1;
                    return Ok(JNode::Arr { oid, elems });
                }
                loop {
                    self.it.charge_loop()?;
                    let node = self.parse_value()?;
                    let v = node_value(&node);
                    let idx = elems.len().to_string();
                    self.it
                        .heap
                        .obj_mut(oid)
                        .props
                        .insert(PropKey::Str(units_from_str(&idx)), Property::data(v));
                    elems.push(node);
                    self.ws();
                    match self.s.get(self.i) {
                        Some(&0x2c) => {
                            self.i += 1;
                        }
                        Some(&0x5d) => {
                            self.i += 1;
                            #[allow(clippy::cast_precision_loss)]
                            self.it.set_array_length_raw(oid, elems.len() as f64);
                            return Ok(JNode::Arr { oid, elems });
                        }
                        _ => return Err(self.err()),
                    }
                }
            }
            0x22 => {
                // '"'
                let v = self.parse_string_body()?;
                let src = self.s[start..self.i].to_vec();
                Ok(JNode::Prim {
                    v: JsValue::Str(Rc::new(v)),
                    src,
                })
            }
            0x74 => {
                // true
                self.expect_word(&[0x74, 0x72, 0x75, 0x65])?;
                Ok(JNode::Prim {
                    v: JsValue::Bool(true),
                    src: self.s[start..self.i].to_vec(),
                })
            }
            0x66 => {
                // false
                self.expect_word(&[0x66, 0x61, 0x6c, 0x73, 0x65])?;
                Ok(JNode::Prim {
                    v: JsValue::Bool(false),
                    src: self.s[start..self.i].to_vec(),
                })
            }
            0x6e => {
                // null
                self.expect_word(&[0x6e, 0x75, 0x6c, 0x6c])?;
                Ok(JNode::Prim {
                    v: JsValue::Null,
                    src: self.s[start..self.i].to_vec(),
                })
            }
            _ => {
                let n = self.parse_number()?;
                Ok(JNode::Prim {
                    v: JsValue::Num(n),
                    src: self.s[start..self.i].to_vec(),
                })
            }
        }
    }

    fn expect_word(&mut self, w: &[u16]) -> Result<(), Abrupt> {
        if self.s.len() >= self.i + w.len() && &self.s[self.i..self.i + w.len()] == w {
            self.i += w.len();
            Ok(())
        } else {
            Err(self.err())
        }
    }

    /// Parse a JSON string starting at the opening quote; returns code units.
    fn parse_string_body(&mut self) -> Result<Units, Abrupt> {
        debug_assert_eq!(self.s.get(self.i), Some(&0x22));
        self.i += 1;
        let mut out: Units = Vec::new();
        loop {
            let Some(&c) = self.s.get(self.i) else {
                return Err(self.err());
            };
            self.i += 1;
            match c {
                0x22 => return Ok(out),
                0x5c => {
                    let Some(&e) = self.s.get(self.i) else {
                        return Err(self.err());
                    };
                    self.i += 1;
                    match e {
                        0x22 | 0x5c | 0x2f => out.push(e),
                        0x62 => out.push(0x08),
                        0x66 => out.push(0x0c),
                        0x6e => out.push(0x0a),
                        0x72 => out.push(0x0d),
                        0x74 => out.push(0x09),
                        0x75 => {
                            let mut v: u16 = 0;
                            for _ in 0..4 {
                                let Some(&h) = self.s.get(self.i) else {
                                    return Err(self.err());
                                };
                                self.i += 1;
                                let d = match h {
                                    0x30..=0x39 => h - 0x30,
                                    0x41..=0x46 => h - 0x41 + 10,
                                    0x61..=0x66 => h - 0x61 + 10,
                                    _ => return Err(self.err()),
                                };
                                v = (v << 4) | d;
                            }
                            out.push(v);
                        }
                        _ => return Err(self.err()),
                    }
                }
                c if c < 0x20 => return Err(self.err()),
                c => out.push(c),
            }
            if out.len() > MAX_STRING_UNITS {
                return Err(Abrupt::Fatal("JSON string cap exceeded".to_string()));
            }
        }
    }

    fn parse_number(&mut self) -> Result<f64, Abrupt> {
        let start = self.i;
        if self.s.get(self.i) == Some(&0x2d) {
            self.i += 1;
        }
        // Int part: 0 | [1-9][0-9]*
        match self.s.get(self.i) {
            Some(&0x30) => {
                self.i += 1;
            }
            Some(&c) if (0x31..=0x39).contains(&c) => {
                while matches!(self.s.get(self.i), Some(c) if (0x30..=0x39).contains(c)) {
                    self.i += 1;
                }
            }
            _ => return Err(self.err()),
        }
        if self.s.get(self.i) == Some(&0x2e) {
            self.i += 1;
            if !matches!(self.s.get(self.i), Some(c) if (0x30..=0x39).contains(c)) {
                return Err(self.err());
            }
            while matches!(self.s.get(self.i), Some(c) if (0x30..=0x39).contains(c)) {
                self.i += 1;
            }
        }
        if matches!(self.s.get(self.i), Some(&0x65 | &0x45)) {
            self.i += 1;
            if matches!(self.s.get(self.i), Some(&0x2b | &0x2d)) {
                self.i += 1;
            }
            if !matches!(self.s.get(self.i), Some(c) if (0x30..=0x39).contains(c)) {
                return Err(self.err());
            }
            while matches!(self.s.get(self.i), Some(c) if (0x30..=0x39).contains(c)) {
                self.i += 1;
            }
        }
        let text: String = self.s[start..self.i]
            .iter()
            .map(|&c| char::from(u8::try_from(c).expect("ascii number chars")))
            .collect();
        text.parse::<f64>()
            .map_err(|e| Abrupt::Fatal(format!("JSON number parse: {e}")))
    }
}

fn node_value(n: &JNode) -> JsValue {
    match n {
        JNode::Prim { v, .. } => v.clone(),
        JNode::Arr { oid, .. } | JNode::Obj { oid, .. } => JsValue::Obj(*oid),
    }
}

impl Interp {
    fn throw_native_syntax(&mut self) -> Abrupt {
        self.throw_native(ErrKind::Syntax)
    }

    pub(crate) fn json_parse(&mut self, args: &[JsValue]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        let text = self.to_string_units(&arg(0))?;
        let root = {
            let mut p = JParser {
                s: &text,
                i: 0,
                it: self,
                depth: 0,
            };
            let root = p.parse_value()?;
            p.ws();
            if p.i != p.s.len() {
                return Err(p.err());
            }
            root
        };
        let reviver = arg(1);
        let reviver_callable =
            matches!(&reviver, JsValue::Obj(f) if self.heap.obj(*f).is_callable());
        if !reviver_callable {
            return Ok(node_value(&root));
        }
        // Root wrapper: OrdinaryObjectCreate(%Object.prototype%) with "".
        let wrapper = self.new_plain()?;
        let ok = self.define_own(
            wrapper,
            &PropKey::from_str(""),
            PartialDesc::full_data(node_value(&root), true, true, true),
        )?;
        if !ok {
            return Err(self.throw_type_error());
        }
        self.internalize(wrapper, &units_from_str(""), Some(&root), &reviver, 0)
    }

    /// InternalizeJSONProperty with the shipped source-context extension.
    fn internalize(
        &mut self,
        holder: ObjId,
        name: &Units,
        snap: Option<&JNode>,
        reviver: &JsValue,
        depth: u32,
    ) -> ERes {
        self.charge_loop()?;
        if depth > 600 {
            // Reviver-injected nesting beyond the parse cap: engines fail
            // with an implementation-defined stack RangeError — refuse.
            return Err(Abrupt::Fatal(
                "JSON reviver walk nesting cap exceeded".to_string(),
            ));
        }
        let key = PropKey::Str(name.clone());
        let val = self.get_from_object(holder, &key, JsValue::Obj(holder))?;
        // Snapshot applies only while the value at this position is still
        // the parsed one (identity for containers, SameValue for
        // primitives) — engine-verified drop semantics.
        let snap = snap.filter(|n| match n {
            JNode::Prim { v, .. } => {
                !val.is_object() && crate::ops::same_value(v, &val)
            }
            JNode::Arr { oid, .. } | JNode::Obj { oid, .. } => {
                matches!(&val, JsValue::Obj(o) if o == oid)
            }
        });
        if let JsValue::Obj(vo) = &val {
            let vo = *vo;
            if self.heap.obj(vo).is_array() {
                let len = self.length_of_array_like(vo)?;
                for i in 0..len {
                    self.charge_loop()?;
                    let iname = units_from_str(&i.to_string());
                    let child = snap.and_then(|n| {
                        usize::try_from(i).ok().and_then(|ix| n.child_index(ix))
                    });
                    let newel = self.internalize(vo, &iname, child, reviver, depth + 1)?;
                    let ikey = PropKey::Str(iname);
                    if matches!(newel, JsValue::Undefined) {
                        self.delete_prop(vo, &ikey)?;
                    } else {
                        self.define_own(
                            vo,
                            &ikey,
                            PartialDesc::full_data(newel, true, true, true),
                        )?;
                    }
                }
            } else {
                if !self.own_surface_complete(vo) {
                    return Err(Abrupt::Fatal(
                        "JSON reviver walk over an object with unmodeled own surface"
                            .to_string(),
                    ));
                }
                let keys: Vec<Units> = trust_js_value::ordered_own_keys(self.heap.obj(vo))
                    .into_iter()
                    .filter_map(|k| match k {
                        PropKey::Str(u) => {
                            let enumerable = self
                                .heap
                                .obj(vo)
                                .props
                                .get(&PropKey::Str(u.clone()))
                                .is_some_and(|p| p.enumerable);
                            enumerable.then_some(u)
                        }
                        PropKey::Sym(_) => None,
                    })
                    .collect();
                for p in keys {
                    self.charge_loop()?;
                    let child = snap.and_then(|n| n.child_key(&p));
                    let newel = self.internalize(vo, &p, child, reviver, depth + 1)?;
                    let pkey = PropKey::Str(p);
                    if matches!(newel, JsValue::Undefined) {
                        self.delete_prop(vo, &pkey)?;
                    } else {
                        self.define_own(
                            vo,
                            &pkey,
                            PartialDesc::full_data(newel, true, true, true),
                        )?;
                    }
                }
            }
        }
        // Context object: { source } for still-pristine primitives, else {}.
        let context = self.new_plain()?;
        if let Some(JNode::Prim { src, .. }) = snap {
            let src = src.clone();
            self.heap.obj_mut(context).props.insert(
                PropKey::from_str("source"),
                Property::data(JsValue::Str(Rc::new(src))),
            );
        }
        self.call_value(
            &reviver.clone(),
            JsValue::Obj(holder),
            vec![
                JsValue::Str(Rc::new(name.clone())),
                val,
                JsValue::Obj(context),
            ],
        )
    }

    // -----------------------------------------------------------------------
    // Stringify
    // -----------------------------------------------------------------------

    #[allow(clippy::too_many_lines)]
    pub(crate) fn json_stringify(&mut self, args: &[JsValue]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        let replacer = arg(1);
        let mut replacer_fn: Option<JsValue> = None;
        let mut property_list: Option<Vec<Units>> = None;
        if let JsValue::Obj(ro) = &replacer {
            if self.heap.obj(*ro).is_callable() {
                replacer_fn = Some(replacer.clone());
            // IsArray recurses through a proxy target (revoked → TypeError);
            // a proxy replacer array is a valid PropertyList source.
            } else if self.is_array_exotic(*ro)? {
                let len = self.length_of_array_like(*ro)?;
                let mut list: Vec<Units> = Vec::new();
                for k in 0..len {
                    self.charge_loop()?;
                    let key = PropKey::Str(units_from_str(&k.to_string()));
                    let v = self.get_from_object(*ro, &key, JsValue::Obj(*ro))?;
                    let item: Option<Units> = match &v {
                        JsValue::Str(s) => Some(s.as_ref().clone()),
                        JsValue::Num(n) => Some(units_from_str(&js_number_to_string(*n))),
                        JsValue::Obj(o) => match &self.heap.obj(*o).kind {
                            ObjKind::Wrapper(WrapperPrim::Str(_))
                            | ObjKind::Wrapper(WrapperPrim::Num(_)) => {
                                Some(self.to_string_units(&v)?)
                            }
                            _ => None,
                        },
                        _ => None,
                    };
                    if let Some(u) = item {
                        if !list.contains(&u) {
                            list.push(u);
                        }
                    }
                }
                property_list = Some(list);
            }
        }
        let space = arg(2);
        let space = match &space {
            JsValue::Obj(o) => match &self.heap.obj(*o).kind {
                ObjKind::Wrapper(WrapperPrim::Num(_)) => JsValue::Num(self.to_number(&space)?),
                ObjKind::Wrapper(WrapperPrim::Str(_)) => {
                    JsValue::Str(Rc::new(self.to_string_units(&space)?))
                }
                _ => space.clone(),
            },
            _ => space.clone(),
        };
        let gap: Units = match &space {
            JsValue::Num(n) => {
                let sp = to_integer_or_infinity(*n).min(10.0);
                if sp >= 1.0 {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    let n = sp as usize;
                    vec![0x20; n]
                } else {
                    Vec::new()
                }
            }
            JsValue::Str(s) => s.iter().copied().take(10).collect(),
            _ => Vec::new(),
        };
        let wrapper = self.new_plain()?;
        let ok = self.define_own(
            wrapper,
            &PropKey::from_str(""),
            PartialDesc::full_data(arg(0), true, true, true),
        )?;
        if !ok {
            return Err(self.throw_type_error());
        }
        let mut st = SerState {
            stack: Vec::new(),
            indent: Vec::new(),
            gap,
            replacer_fn,
            property_list,
            depth: 0,
        };
        match self.serialize_property(&mut st, &units_from_str(""), wrapper)? {
            Some(u) => Ok(JsValue::Str(Rc::new(u))),
            None => Ok(JsValue::Undefined),
        }
    }

    /// SerializeJSONProperty (25.5.2.1); None = undefined (omitted).
    fn serialize_property(
        &mut self,
        st: &mut SerState,
        key: &Units,
        holder: ObjId,
    ) -> Result<Option<Units>, Abrupt> {
        self.charge_loop()?;
        if st.depth > 600 {
            // Engines fail deep nesting with an implementation-defined stack
            // RangeError — refuse rather than guess the depth.
            return Err(Abrupt::Fatal(
                "JSON.stringify nesting cap exceeded".to_string(),
            ));
        }
        st.depth += 1;
        let r = self.serialize_property_inner(st, key, holder);
        st.depth -= 1;
        r
    }

    fn serialize_property_inner(
        &mut self,
        st: &mut SerState,
        key: &Units,
        holder: ObjId,
    ) -> Result<Option<Units>, Abrupt> {
        let kp = PropKey::Str(key.clone());
        let mut value = self.get_from_object(holder, &kp, JsValue::Obj(holder))?;
        if matches!(value, JsValue::Obj(_) | JsValue::BigInt(_)) {
            let to_json = self.get_prop(&value, &PropKey::from_str("toJSON"))?;
            if matches!(&to_json, JsValue::Obj(f) if self.heap.obj(*f).is_callable()) {
                value = self.call_value(
                    &to_json,
                    value.clone(),
                    vec![JsValue::Str(Rc::new(key.clone()))],
                )?;
            }
        }
        if let Some(rf) = st.replacer_fn.clone() {
            value = self.call_value(
                &rf,
                JsValue::Obj(holder),
                vec![JsValue::Str(Rc::new(key.clone())), value],
            )?;
        }
        if let JsValue::Obj(vo) = &value {
            match self.heap.obj(*vo).kind.clone() {
                ObjKind::Wrapper(WrapperPrim::Num(_)) => {
                    value = JsValue::Num(self.to_number(&value)?);
                }
                ObjKind::Wrapper(WrapperPrim::Str(_)) => {
                    value = JsValue::Str(Rc::new(self.to_string_units(&value)?));
                }
                ObjKind::Wrapper(WrapperPrim::Bool(b)) => {
                    value = JsValue::Bool(b);
                }
                ObjKind::Wrapper(WrapperPrim::BigInt(b)) => {
                    value = JsValue::BigInt(b);
                }
                _ => {}
            }
        }
        match &value {
            JsValue::Null => Ok(Some(units_from_str("null"))),
            JsValue::Bool(b) => Ok(Some(units_from_str(if *b { "true" } else { "false" }))),
            JsValue::Str(s) => Ok(Some(crate::builtins::json_quote_units(s))),
            JsValue::Num(n) => Ok(Some(units_from_str(&if n.is_finite() {
                js_number_to_string(*n)
            } else {
                "null".to_string()
            }))),
            JsValue::BigInt(_) => Err(self.throw_type_error()),
            JsValue::Obj(vo) => {
                let vo = *vo;
                if self.heap.obj(vo).is_callable() {
                    return Ok(None);
                }
                if self.heap.obj(vo).is_array() {
                    self.serialize_array(st, vo).map(Some)
                } else {
                    self.serialize_object(st, vo).map(Some)
                }
            }
            JsValue::Undefined | JsValue::Sym(_) => Ok(None),
        }
    }

    fn serialize_object(&mut self, st: &mut SerState, vo: ObjId) -> Result<Units, Abrupt> {
        if st.stack.contains(&vo) {
            return Err(self.throw_type_error());
        }
        st.stack.push(vo);
        let stepback = st.indent.clone();
        st.indent.extend_from_slice(&st.gap);
        let keys: Vec<Units> = match &st.property_list {
            Some(list) => list.clone(),
            None => {
                if !self.own_surface_complete(vo) {
                    return Err(Abrupt::Fatal(
                        "JSON.stringify over an object with unmodeled own surface".to_string(),
                    ));
                }
                trust_js_value::ordered_own_keys(self.heap.obj(vo))
                    .into_iter()
                    .filter_map(|k| match k {
                        PropKey::Str(u) => {
                            let enumerable = self
                                .heap
                                .obj(vo)
                                .props
                                .get(&PropKey::Str(u.clone()))
                                .is_some_and(|p| p.enumerable);
                            enumerable.then_some(u)
                        }
                        PropKey::Sym(_) => None,
                    })
                    .collect()
            }
        };
        let mut partial: Vec<Units> = Vec::new();
        for p in keys {
            let str_p = self.serialize_property(st, &p, vo)?;
            if let Some(sp) = str_p {
                let mut member = crate::builtins::json_quote_units(&p);
                member.push(0x3a);
                if !st.gap.is_empty() {
                    member.push(0x20);
                }
                member.extend_from_slice(&sp);
                partial.push(member);
            }
        }
        let out = wrap_members(&partial, &st.gap, &st.indent, &stepback, 0x7b, 0x7d);
        if out.len() > MAX_STRING_UNITS {
            return Err(Abrupt::Fatal("JSON.stringify output cap exceeded".to_string()));
        }
        st.stack.pop();
        st.indent = stepback;
        Ok(out)
    }

    fn serialize_array(&mut self, st: &mut SerState, vo: ObjId) -> Result<Units, Abrupt> {
        if st.stack.contains(&vo) {
            return Err(self.throw_type_error());
        }
        st.stack.push(vo);
        let stepback = st.indent.clone();
        st.indent.extend_from_slice(&st.gap);
        let len = self.length_of_array_like(vo)?;
        let mut partial: Vec<Units> = Vec::new();
        for i in 0..len {
            self.charge_loop()?;
            let str_p = self.serialize_property(st, &units_from_str(&i.to_string()), vo)?;
            partial.push(str_p.unwrap_or_else(|| units_from_str("null")));
        }
        let out = wrap_members(&partial, &st.gap, &st.indent, &stepback, 0x5b, 0x5d);
        if out.len() > MAX_STRING_UNITS {
            return Err(Abrupt::Fatal("JSON.stringify output cap exceeded".to_string()));
        }
        st.stack.pop();
        st.indent = stepback;
        Ok(out)
    }
}

struct SerState {
    stack: Vec<ObjId>,
    indent: Units,
    gap: Units,
    replacer_fn: Option<JsValue>,
    property_list: Option<Vec<Units>>,
    depth: u32,
}

fn wrap_members(
    partial: &[Units],
    gap: &Units,
    indent: &Units,
    stepback: &Units,
    open: u16,
    close: u16,
) -> Units {
    let mut out: Units = vec![open];
    if partial.is_empty() {
        out.push(close);
        return out;
    }
    if gap.is_empty() {
        for (i, m) in partial.iter().enumerate() {
            if i > 0 {
                out.push(0x2c);
            }
            out.extend_from_slice(m);
        }
    } else {
        for (i, m) in partial.iter().enumerate() {
            if i > 0 {
                out.push(0x2c);
            }
            out.push(0x0a);
            out.extend_from_slice(indent);
            out.extend_from_slice(m);
        }
        out.push(0x0a);
        out.extend_from_slice(stepback);
    }
    out.push(close);
    out
}
