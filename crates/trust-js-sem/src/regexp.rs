// RegExp (22.2): the %RegExp% constructor, %RegExp.prototype% (exec/test/
// toString, the flag accessors, and the @@match/@@matchAll/@@replace/@@search/
// @@split protocols), RegExpBuiltinExec with the exact result-array shape
// (index/input/groups/indices), and %RegExpStringIterator%. The pattern
// grammar and matching semantics are delegated ENTIRELY to the frozen,
// independently-validated trust-js-regexp engine (a spec-exact §22.2 matcher):
// a CompileError::Syntax is a real SyntaxError, a CompileError::Unsupported or
// an ExecError is a sound NoCoverage refusal — never a guessed match. The
// interpreter owns only the object model, lastIndex bookkeeping, the global/
// sticky loops, and the result shaping.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::builtins::{to_length_u64, WK_MATCH, WK_SPECIES};
use crate::interp::{Abrupt, ERes, Interp};
use crate::value::{
    units_from_str, NativeErrorKind, ObjId, ObjKind, Object, Prop, RegExpFlag, RegExpProtoOp,
    Units, Value,
};
use std::rc::Rc;
use trust_js_regexp::{CompileError, ExecError, Pattern};

/// The runtime record behind a RegExp object: the compiled matcher
/// ([[RegExpMatcher]]) plus [[OriginalSource]] and [[OriginalFlags]] (the
/// source/flags code units as given, WITHOUT the enclosing slashes).
#[derive(Debug, Clone)]
pub struct RegExpData {
    pub pattern: Pattern,
    pub source: Units,
    pub flags: Units,
}

/// ToIntegerOrInfinity clamped into a usize range for a known-finite,
/// non-negative match index (the `index` field of an exec result).
fn to_index_clamped(n: f64, max: usize) -> usize {
    if n.is_nan() || n <= 0.0 {
        0
    } else if n >= max as f64 {
        max
    } else {
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        {
            n.trunc() as usize
        }
    }
}

/// AdvanceStringIndex (22.2.7.3): +1 in non-Unicode mode; skip a full
/// surrogate pair in Unicode mode.
fn advance_string_index(s: &[u16], index: usize, unicode: bool) -> usize {
    if !unicode || index + 1 >= s.len() {
        return index + 1;
    }
    let first = s[index];
    if (0xd800..=0xdbff).contains(&first) && (0xdc00..=0xdfff).contains(&s[index + 1]) {
        index + 2
    } else {
        index + 1
    }
}

fn has_flag(flags: &[u16], c: char) -> bool {
    flags.contains(&(c as u16))
}

/// EscapeRegExpPattern (22.2.3.2.5): the `source` string form — a Pattern that
/// between `/` delimiters behaves identically. Escapes unescaped `/` outside a
/// character class and every line terminator; empty → "(?:)". Mirrors V8's
/// behavior (verified against Node 24).
pub(crate) fn escape_regexp_pattern(p: &[u16]) -> Units {
    if p.is_empty() {
        return units_from_str("(?:)");
    }
    let mut out: Units = Vec::with_capacity(p.len());
    let mut escaped = false;
    let mut in_class = false;
    for &c in p {
        if escaped {
            push_lt_escaped(&mut out, c);
            escaped = false;
            continue;
        }
        match c {
            0x5c => {
                out.push(0x5c);
                escaped = true;
            }
            0x2f if !in_class => {
                out.push(0x5c);
                out.push(0x2f);
            }
            0x5b => {
                in_class = true;
                out.push(c);
            }
            0x5d => {
                in_class = false;
                out.push(c);
            }
            0x0a | 0x0d | 0x2028 | 0x2029 => push_lt_escaped(&mut out, c),
            _ => out.push(c),
        }
    }
    out
}

/// Emit one code unit, escaping line terminators (the delimiters would
/// otherwise break the single-line `/…/` form).
fn push_lt_escaped(out: &mut Units, c: u16) {
    match c {
        0x0a => out.extend_from_slice(&[0x5c, 0x6e]),           // \n
        0x0d => out.extend_from_slice(&[0x5c, 0x72]),           // \r
        0x2028 => out.extend_from_slice(&units_from_str("\\u2028")),
        0x2029 => out.extend_from_slice(&units_from_str("\\u2029")),
        _ => out.push(c),
    }
}

impl Interp {
    // -- construction --------------------------------------------------------

    /// Evaluate a regular-expression literal (12.9.5): a fresh RegExp object on
    /// %RegExp.prototype% each evaluation. Pattern validity was already checked
    /// at parse; a re-compile failure here is a sound refusal.
    pub(crate) fn eval_regex_literal(&mut self, body: &Units, flags: &Units) -> ERes {
        let proto = self.intr.regexp_proto;
        let oid = self.regexp_from_source(body, flags, proto)?;
        Ok(Value::Obj(oid))
    }

    /// RegExpAlloc + RegExpInitialize (22.2.3.2.x) over already-string source
    /// and flags: compile via trust-js-regexp and materialize the object.
    fn regexp_from_source(
        &mut self,
        source: &Units,
        flags: &Units,
        proto: ObjId,
    ) -> Result<ObjId, Abrupt> {
        let flags_str = crate::value::units_to_lossy(flags);
        match trust_js_regexp::compile(source, &flags_str) {
            Ok(pattern) => {
                let data = Rc::new(RegExpData {
                    pattern,
                    source: source.clone(),
                    flags: flags.clone(),
                });
                let oid = self.alloc(Object::new(ObjKind::RegExpObj(data), Some(proto)));
                // [[lastIndex]]: writable, non-enumerable, non-configurable, +0.
                self.obj_mut(oid).props.insert(
                    units_from_str("lastIndex"),
                    Prop::with_attrs(Value::Num(0.0), true, false, false),
                );
                Ok(oid)
            }
            Err(CompileError::Syntax(_)) => Err(self.throw_native(NativeErrorKind::SyntaxError)),
            Err(CompileError::Unsupported(m)) => {
                Err(Abrupt::Fatal(format!("regexp pattern unsupported: {m}")))
            }
        }
    }

    /// RegExpCreate(P, F) (22.2.3.3): RegExpAlloc(%RegExp%) + RegExpInitialize.
    /// Used by String.prototype.match/matchAll/search when the argument has no
    /// @@-protocol (the argument becomes the pattern SOURCE, ToString'd).
    pub(crate) fn regexp_create(&mut self, pattern: &Value, flags: &Value) -> ERes {
        let p = if matches!(pattern, Value::Undefined) {
            Vec::new()
        } else {
            self.to_string_units(pattern)?
        };
        let f = if matches!(flags, Value::Undefined) {
            Vec::new()
        } else {
            self.to_string_units(flags)?
        };
        let proto = self.intr.regexp_proto;
        let oid = self.regexp_from_source(&p, &f, proto)?;
        Ok(Value::Obj(oid))
    }

    /// IsRegExp (22.2.7.4): honor a user @@match, else the [[RegExpMatcher]]
    /// slot.
    pub(crate) fn is_regexp_public(&mut self, v: &Value) -> Result<bool, Abrupt> {
        self.is_regexp(v)
    }

    fn is_regexp(&mut self, v: &Value) -> Result<bool, Abrupt> {
        let Value::Obj(o) = v else {
            return Ok(false);
        };
        let matcher = self.get_prop_value_sym(v, self.intr.wk(WK_MATCH))?;
        if !matches!(matcher, Value::Undefined) {
            return Ok(self.to_boolean(&matcher));
        }
        Ok(matches!(self.obj(*o).kind, ObjKind::RegExpObj(_)))
    }

    /// The %RegExp% constructor (22.2.3.1), call + construct.
    pub(crate) fn regexp_ctor(&mut self, args: &[Value], is_new: bool) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        let pattern = arg(0);
        let flags = arg(1);
        let pattern_is_regexp = self.is_regexp(&pattern)?;

        let new_target = if is_new {
            self.pending_new_target.take().unwrap_or(self.intr.regexp_ctor)
        } else {
            // Called as a function: `RegExp(re)` with no flags returns `re`
            // unchanged when its constructor is %RegExp%.
            if pattern_is_regexp && matches!(flags, Value::Undefined) {
                let pc = self.get_prop_value(&pattern, &units_from_str("constructor"))?;
                if matches!(&pc, Value::Obj(id) if *id == self.intr.regexp_ctor) {
                    return Ok(pattern);
                }
            }
            self.intr.regexp_ctor
        };

        // Resolve P and F.
        let (p, f) = if let Value::Obj(o) = &pattern {
            if let ObjKind::RegExpObj(data) = &self.obj(*o).kind {
                let src = data.source.clone();
                let orig_flags = data.flags.clone();
                let f = if matches!(flags, Value::Undefined) {
                    Value::Str(Rc::new(orig_flags))
                } else {
                    flags.clone()
                };
                (Value::Str(Rc::new(src)), f)
            } else if pattern_is_regexp {
                let src = self.get_prop_value(&pattern, &units_from_str("source"))?;
                let f = if matches!(flags, Value::Undefined) {
                    self.get_prop_value(&pattern, &units_from_str("flags"))?
                } else {
                    flags.clone()
                };
                (src, f)
            } else {
                (pattern.clone(), flags.clone())
            }
        } else {
            (pattern.clone(), flags.clone())
        };

        let proto = self.proto_from_new_target(new_target, self.intr.regexp_proto)?;
        let p_units = if matches!(p, Value::Undefined) {
            Vec::new()
        } else {
            self.to_string_units(&p)?
        };
        let f_units = if matches!(f, Value::Undefined) {
            Vec::new()
        } else {
            self.to_string_units(&f)?
        };
        let oid = self.regexp_from_source(&p_units, &f_units, proto)?;
        Ok(Value::Obj(oid))
    }

    // -- dispatch ------------------------------------------------------------

    pub(crate) fn dispatch_regexp_proto(
        &mut self,
        op: RegExpProtoOp,
        this: Value,
        args: &[Value],
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match op {
            RegExpProtoOp::Exec => self.regexp_proto_exec(&this, &arg(0)),
            RegExpProtoOp::Test => self.regexp_proto_test(&this, &arg(0)),
            RegExpProtoOp::ToString => self.regexp_proto_to_string(&this),
            RegExpProtoOp::Match => self.regexp_proto_match(&this, &arg(0)),
            RegExpProtoOp::MatchAll => self.regexp_proto_match_all(&this, &arg(0)),
            RegExpProtoOp::Replace => self.regexp_proto_replace(&this, &arg(0), &arg(1)),
            RegExpProtoOp::Search => self.regexp_proto_search(&this, &arg(0)),
            RegExpProtoOp::Split => self.regexp_proto_split(&this, &arg(0), &arg(1)),
        }
    }

    // -- flag accessors ------------------------------------------------------

    pub(crate) fn regexp_flag_get(&mut self, flag: RegExpFlag, this: &Value) -> ERes {
        if let RegExpFlag::Flags = flag {
            return self.regexp_flags_string(this);
        }
        let Value::Obj(rid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let rid = *rid;
        let data = match &self.obj(rid).kind {
            ObjKind::RegExpObj(d) => Some(d.clone()),
            _ => None,
        };
        let Some(data) = data else {
            // The prototype itself has no [[OriginalFlags]] (special-cased).
            if rid == self.intr.regexp_proto {
                return Ok(match flag {
                    RegExpFlag::Source => Value::str_from("(?:)"),
                    _ => Value::Undefined,
                });
            }
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let f = data.pattern.flags();
        Ok(match flag {
            RegExpFlag::Source => Value::Str(Rc::new(escape_regexp_pattern(&data.source))),
            RegExpFlag::Global => Value::Bool(f.global),
            RegExpFlag::IgnoreCase => Value::Bool(f.ignore_case),
            RegExpFlag::Multiline => Value::Bool(f.multiline),
            RegExpFlag::DotAll => Value::Bool(f.dot_all),
            RegExpFlag::Unicode => Value::Bool(f.unicode),
            RegExpFlag::UnicodeSets => Value::Bool(f.unicode_sets),
            RegExpFlag::Sticky => Value::Bool(f.sticky),
            RegExpFlag::HasIndices => Value::Bool(f.has_indices),
            RegExpFlag::Flags => unreachable!("handled above"),
        })
    }

    /// The generic `get flags` (22.2.6.4): reads the eight boolean flag
    /// accessors via [[Get]] in order and assembles the canonical string.
    fn regexp_flags_string(&mut self, r: &Value) -> ERes {
        if !matches!(r, Value::Obj(_)) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let mut out: Units = Vec::new();
        for (name, ch) in [
            ("hasIndices", 'd'),
            ("global", 'g'),
            ("ignoreCase", 'i'),
            ("multiline", 'm'),
            ("dotAll", 's'),
            ("unicode", 'u'),
            ("unicodeSets", 'v'),
            ("sticky", 'y'),
        ] {
            let v = self.get_prop_value(r, &units_from_str(name))?;
            if self.to_boolean(&v) {
                out.push(ch as u16);
            }
        }
        Ok(Value::Str(Rc::new(out)))
    }

    fn regexp_proto_to_string(&mut self, r: &Value) -> ERes {
        if !matches!(r, Value::Obj(_)) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let source_v = self.get_prop_value(r, &units_from_str("source"))?;
        let source = self.to_string_units(&source_v)?;
        let flags_v = self.get_prop_value(r, &units_from_str("flags"))?;
        let flags = self.to_string_units(&flags_v)?;
        let mut out: Units = Vec::with_capacity(source.len() + flags.len() + 2);
        out.push(u16::from(b'/'));
        out.extend_from_slice(&source);
        out.push(u16::from(b'/'));
        out.extend_from_slice(&flags);
        Ok(Value::Str(Rc::new(out)))
    }

    // -- exec ----------------------------------------------------------------

    fn regexp_proto_exec(&mut self, this: &Value, s_arg: &Value) -> ERes {
        let Value::Obj(rid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let rid = *rid;
        if !matches!(self.obj(rid).kind, ObjKind::RegExpObj(_)) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        let s = self.to_string_units(s_arg)?;
        self.regexp_builtin_exec(rid, &s)
    }

    fn regexp_proto_test(&mut self, this: &Value, s_arg: &Value) -> ERes {
        let Value::Obj(rid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let rid = *rid;
        let s = self.to_string_units(s_arg)?;
        let m = self.regexp_exec(rid, &s)?;
        Ok(Value::Bool(!matches!(m, Value::Null)))
    }

    /// RegExpExec (22.2.7.1): honor a user `exec`, else RegExpBuiltinExec.
    fn regexp_exec(&mut self, rid: ObjId, s: &Units) -> ERes {
        let exec = self.get_from_object(rid, &units_from_str("exec"))?;
        if let Value::Obj(f) = &exec {
            if self.obj(*f).is_callable() {
                let result = self.call_value(
                    &exec,
                    Value::Obj(rid),
                    vec![Value::Str(Rc::new(s.to_vec()))],
                )?;
                if !matches!(result, Value::Obj(_) | Value::Null) {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                return Ok(result);
            }
        }
        if !matches!(self.obj(rid).kind, ObjKind::RegExpObj(_)) {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        }
        self.regexp_builtin_exec(rid, s)
    }

    fn set_last_index(&mut self, rid: ObjId, v: f64) -> Result<(), Abrupt> {
        self.set_prop_value(&Value::Obj(rid), &units_from_str("lastIndex"), Value::Num(v), true)
    }

    /// RegExpBuiltinExec (22.2.7.2): the search + result-array construction.
    fn regexp_builtin_exec(&mut self, rid: ObjId, s: &Units) -> ERes {
        let data = match &self.obj(rid).kind {
            ObjKind::RegExpObj(d) => d.clone(),
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        };
        let length = s.len();
        let last_index_v = self.get_from_object(rid, &units_from_str("lastIndex"))?;
        let mut last_index = to_length_u64(self.to_number(&last_index_v)?) as usize;
        let flags = data.pattern.flags();
        let global = flags.global;
        let sticky = flags.sticky;
        if !global && !sticky {
            last_index = 0;
        }
        if last_index > length {
            if global || sticky {
                self.set_last_index(rid, 0.0)?;
            }
            return Ok(Value::Null);
        }
        let search = if sticky {
            data.pattern.exec_sticky_at(s, last_index)
        } else {
            data.pattern.exec_at(s, last_index)
        };
        let m = match search {
            Ok(m) => m,
            Err(e) => {
                let why = match e {
                    ExecError::Budget => "regexp match step budget exceeded",
                    ExecError::Unsupported(_) => "regexp match unsupported",
                };
                return Err(Abrupt::Fatal(why.to_string()));
            }
        };
        let Some(m) = m else {
            if global || sticky {
                self.set_last_index(rid, 0.0)?;
            }
            return Ok(Value::Null);
        };
        #[allow(clippy::cast_precision_loss)]
        if global || sticky {
            self.set_last_index(rid, m.end as f64)?;
        }
        let n = data.pattern.n_captures();
        let arr = self.new_array(n + 1);
        // Integer keys "0".."n" (whole match then captures).
        let matched: Units = s[m.index..m.end].to_vec();
        self.obj_mut(arr)
            .props
            .insert(units_from_str("0"), Prop::data(Value::Str(Rc::new(matched))));
        // Named groups object (null-prototype), if any.
        let named_groups = data.pattern.group_names();
        let has_groups = !named_groups.is_empty();
        for g in 1..=n {
            let cap = m.captures[g - 1];
            let v = match cap {
                Some((st, en)) => Value::Str(Rc::new(s[st..en].to_vec())),
                None => Value::Undefined,
            };
            self.obj_mut(arr)
                .props
                .insert(units_from_str(&g.to_string()), Prop::data(v));
        }
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(arr, (n + 1) as f64);
        // "index", "input" (spec order after the integer keys, before groups).
        #[allow(clippy::cast_precision_loss)]
        self.obj_mut(arr).props.insert(
            units_from_str("index"),
            Prop::data(Value::Num(m.index as f64)),
        );
        self.obj_mut(arr).props.insert(
            units_from_str("input"),
            Prop::data(Value::Str(Rc::new(s.to_vec()))),
        );
        // "groups".
        let groups_val = if has_groups {
            let groups = self.alloc(Object::new(ObjKind::Plain, None));
            for (name, gnum) in &m.named {
                let g = *gnum;
                let v = match m.captures.get(g - 1).copied().flatten() {
                    Some((st, en)) => Value::Str(Rc::new(s[st..en].to_vec())),
                    None => Value::Undefined,
                };
                let key = units_from_str(name);
                // Duplicate names (ES2025): the participating capture wins.
                let overwrite = !matches!(v, Value::Undefined)
                    || !self.obj(groups).props.contains_key(&key);
                if overwrite {
                    self.obj_mut(groups).props.insert(key, Prop::data(v));
                }
            }
            Value::Obj(groups)
        } else {
            Value::Undefined
        };
        self.obj_mut(arr)
            .props
            .insert(units_from_str("groups"), Prop::data(groups_val.clone()));
        // "indices" (the `d` flag).
        if flags.has_indices {
            let indices = self.make_indices_array(s, &m, groups_val)?;
            self.obj_mut(arr)
                .props
                .insert(units_from_str("indices"), Prop::data(indices));
        }
        Ok(Value::Obj(arr))
    }

    /// MakeMatchIndicesIndexPairArray (22.2.7.6) — the `.indices` array.
    fn make_indices_array(
        &mut self,
        _s: &[u16],
        m: &trust_js_regexp::MatchResult,
        groups_sample: Value,
    ) -> ERes {
        let n = m.captures.len();
        // Build the [start, end] pair (or undefined) for each group ONCE and
        // reuse the SAME object for both `indices[i]` and `indices.groups.name`
        // — engines share the object, so the projection must see a
        // back-reference, not a duplicate.
        let mut group_vals: Vec<Value> = Vec::with_capacity(n + 1);
        group_vals.push(self.index_pair(m.index, m.end));
        for i in 1..=n {
            group_vals.push(match m.captures[i - 1] {
                Some((st, en)) => self.index_pair(st, en),
                None => Value::Undefined,
            });
        }
        let arr = self.new_array(n + 1);
        for (i, v) in group_vals.iter().enumerate() {
            self.obj_mut(arr)
                .props
                .insert(units_from_str(&i.to_string()), Prop::data(v.clone()));
        }
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(arr, (n + 1) as f64);
        // indices.groups mirrors the named groups (or undefined), reusing pairs.
        let groups_val = if matches!(groups_sample, Value::Undefined) {
            Value::Undefined
        } else {
            let groups = self.alloc(Object::new(ObjKind::Plain, None));
            for (name, gnum) in &m.named {
                let v = group_vals.get(*gnum).cloned().unwrap_or(Value::Undefined);
                let key = units_from_str(name);
                let overwrite = !matches!(v, Value::Undefined)
                    || !self.obj(groups).props.contains_key(&key);
                if overwrite {
                    self.obj_mut(groups).props.insert(key, Prop::data(v));
                }
            }
            Value::Obj(groups)
        };
        self.obj_mut(arr)
            .props
            .insert(units_from_str("groups"), Prop::data(groups_val));
        Ok(Value::Obj(arr))
    }

    /// A fresh `[start, end]` two-element Array (a match-index pair).
    fn index_pair(&mut self, st: usize, en: usize) -> Value {
        let a = self.new_array(2);
        #[allow(clippy::cast_precision_loss)]
        self.obj_mut(a)
            .props
            .insert(units_from_str("0"), Prop::data(Value::Num(st as f64)));
        #[allow(clippy::cast_precision_loss)]
        self.obj_mut(a)
            .props
            .insert(units_from_str("1"), Prop::data(Value::Num(en as f64)));
        self.set_array_length_raw(a, 2.0);
        Value::Obj(a)
    }

    // -- @@match / @@search --------------------------------------------------

    fn regexp_proto_match(&mut self, this: &Value, s_arg: &Value) -> ERes {
        let Value::Obj(rid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let rid = *rid;
        let s = self.to_string_units(s_arg)?;
        let flags = self.regexp_read_flags(this)?;
        let global = has_flag(&flags, 'g');
        if !global {
            return self.regexp_exec(rid, &s);
        }
        let full_unicode = has_flag(&flags, 'u') || has_flag(&flags, 'v');
        self.set_last_index(rid, 0.0)?;
        let arr = self.new_array(0);
        let mut n: u64 = 0;
        loop {
            self.charge_loop()?;
            let result = self.regexp_exec(rid, &s)?;
            if matches!(result, Value::Null) {
                if n == 0 {
                    return Ok(Value::Null);
                }
                return Ok(Value::Obj(arr));
            }
            let m0 = self.get_prop_value(&result, &units_from_str("0"))?;
            let match_str = self.to_string_units(&m0)?;
            self.create_array_element(arr, n, Value::Str(Rc::new(match_str.clone())));
            if match_str.is_empty() {
                let li = self.read_last_index(rid)?;
                let nli = advance_string_index(&s, li, full_unicode);
                #[allow(clippy::cast_precision_loss)]
                self.set_last_index(rid, nli as f64)?;
            }
            n += 1;
        }
    }

    fn regexp_proto_search(&mut self, this: &Value, s_arg: &Value) -> ERes {
        let Value::Obj(rid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let rid = *rid;
        let s = self.to_string_units(s_arg)?;
        let previous = self.get_from_object(rid, &units_from_str("lastIndex"))?;
        if !crate::props::same_value(self, &previous, &Value::Num(0.0)) {
            self.set_last_index(rid, 0.0)?;
        }
        let result = self.regexp_exec(rid, &s)?;
        let current = self.get_from_object(rid, &units_from_str("lastIndex"))?;
        if !crate::props::same_value(self, &current, &previous) {
            self.set_prop_value(
                &Value::Obj(rid),
                &units_from_str("lastIndex"),
                previous,
                true,
            )?;
        }
        if matches!(result, Value::Null) {
            return Ok(Value::Num(-1.0));
        }
        self.get_prop_value(&result, &units_from_str("index"))
    }

    // -- @@replace -----------------------------------------------------------

    fn regexp_proto_replace(&mut self, this: &Value, s_arg: &Value, replace_value: &Value) -> ERes {
        let Value::Obj(rid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let rid = *rid;
        let s = self.to_string_units(s_arg)?;
        let length_s = s.len();
        let functional = matches!(replace_value, Value::Obj(f) if self.obj(*f).is_callable());
        let replace_str = if functional {
            Vec::new()
        } else {
            self.to_string_units(replace_value)?
        };
        // NOTE: @@replace reads `global` and (if global) `unicode` DIRECTLY via
        // [[Get]] — NOT the "flags" string. This is the behavior the reference
        // engine (V8) ships and the differential oracle enforces (test262's
        // get-flags-err / get-unicode-error / flags-tostring-error pin it), and
        // it also matches the current ES spec's per-flag reads for @@replace.
        let global_v = self.get_prop_value(this, &units_from_str("global"))?;
        let global = self.to_boolean(&global_v);
        let full_unicode = if global {
            let u = self.get_prop_value(this, &units_from_str("unicode"))?;
            self.to_boolean(&u)
        } else {
            false
        };
        if global {
            self.set_last_index(rid, 0.0)?;
        }
        let mut results: Vec<Value> = Vec::new();
        loop {
            self.charge_loop()?;
            let result = self.regexp_exec(rid, &s)?;
            if matches!(result, Value::Null) {
                break;
            }
            results.push(result.clone());
            if !global {
                break;
            }
            let m0 = self.get_prop_value(&result, &units_from_str("0"))?;
            let match_str = self.to_string_units(&m0)?;
            if match_str.is_empty() {
                let li = self.read_last_index(rid)?;
                let nli = advance_string_index(&s, li, full_unicode);
                #[allow(clippy::cast_precision_loss)]
                self.set_last_index(rid, nli as f64)?;
            }
        }
        let mut accumulated: Units = Vec::new();
        let mut next_source_position: usize = 0;
        for result in &results {
            let len_v = self.get_prop_value(result, &units_from_str("length"))?;
            let n_caps = to_length_u64(self.to_number(&len_v)?).saturating_sub(1);
            let m0 = self.get_prop_value(result, &units_from_str("0"))?;
            let matched = self.to_string_units(&m0)?;
            let match_len = matched.len();
            let pos_v = self.get_prop_value(result, &units_from_str("index"))?;
            let position = to_index_clamped(self.to_number(&pos_v)?, length_s);
            let mut captures: Vec<Option<Units>> = Vec::new();
            for i in 1..=n_caps {
                let cap = self.get_prop_value(result, &units_from_str(&i.to_string()))?;
                if matches!(cap, Value::Undefined) {
                    captures.push(None);
                } else {
                    captures.push(Some(self.to_string_units(&cap)?));
                }
            }
            let named = self.get_prop_value(result, &units_from_str("groups"))?;
            let replacement: Units = if functional {
                let mut cb_args: Vec<Value> = Vec::with_capacity(captures.len() + 3);
                cb_args.push(Value::Str(Rc::new(matched.clone())));
                for cap in &captures {
                    cb_args.push(match cap {
                        Some(u) => Value::Str(Rc::new(u.clone())),
                        None => Value::Undefined,
                    });
                }
                #[allow(clippy::cast_precision_loss)]
                cb_args.push(Value::Num(position as f64));
                cb_args.push(Value::Str(Rc::new(s.clone())));
                if !matches!(named, Value::Undefined) {
                    cb_args.push(named.clone());
                }
                let rv = self.call_value(replace_value, Value::Undefined, cb_args)?;
                self.to_string_units(&rv)?
            } else {
                // Step 14.l.i: if namedCaptures is not undefined, ToObject it —
                // a null `groups` is an EAGER TypeError, independent of whether
                // the replacement template references `$<name>`.
                let named_obj = match &named {
                    Value::Undefined => None,
                    Value::Null => return Err(self.throw_native(NativeErrorKind::TypeError)),
                    Value::Obj(_) => Some(named.clone()),
                    prim => Some(Value::Obj(self.to_object_wrapper(prim)?)),
                };
                self.get_substitution(
                    &matched,
                    &s,
                    position,
                    &captures,
                    named_obj.as_ref(),
                    &replace_str,
                )?
            };
            if position >= next_source_position {
                accumulated.extend_from_slice(&s[next_source_position..position]);
                accumulated.extend_from_slice(&replacement);
                next_source_position = position + match_len;
            }
        }
        if next_source_position < length_s {
            accumulated.extend_from_slice(&s[next_source_position..]);
        }
        Ok(Value::Str(Rc::new(accumulated)))
    }

    /// GetSubstitution (22.1.3.19.1): `$$`, `$&`, `` $` ``, `$'`, `$n`/`$nn`,
    /// `$<name>`.
    pub(crate) fn get_substitution(
        &mut self,
        matched: &[u16],
        s: &[u16],
        position: usize,
        captures: &[Option<Units>],
        named: Option<&Value>,
        replacement: &[u16],
    ) -> Result<Units, Abrupt> {
        let tail_pos = (position + matched.len()).min(s.len());
        let m = captures.len();
        let dollar = u16::from(b'$');
        let mut out: Units = Vec::new();
        let mut i = 0;
        while i < replacement.len() {
            let c = replacement[i];
            if c != dollar || i + 1 >= replacement.len() {
                out.push(c);
                i += 1;
                continue;
            }
            let next = replacement[i + 1];
            match next {
                0x24 => {
                    out.push(dollar);
                    i += 2;
                }
                0x26 => {
                    out.extend_from_slice(matched);
                    i += 2;
                }
                0x60 => {
                    out.extend_from_slice(&s[..position]);
                    i += 2;
                }
                0x27 => {
                    out.extend_from_slice(&s[tail_pos..]);
                    i += 2;
                }
                0x30..=0x39 => {
                    let d1 = usize::from(next - 0x30);
                    let two = if i + 2 < replacement.len()
                        && (0x30..=0x39).contains(&replacement[i + 2])
                    {
                        Some(d1 * 10 + usize::from(replacement[i + 2] - 0x30))
                    } else {
                        None
                    };
                    if let Some(nn) = two {
                        if nn >= 1 && nn <= m {
                            if let Some(cap) = &captures[nn - 1] {
                                out.extend_from_slice(cap);
                            }
                            i += 3;
                            continue;
                        }
                    }
                    if d1 >= 1 && d1 <= m {
                        if let Some(cap) = &captures[d1 - 1] {
                            out.extend_from_slice(cap);
                        }
                        i += 2;
                    } else {
                        out.push(dollar);
                        i += 1;
                    }
                }
                0x3c => {
                    let Some(named_v) = named else {
                        out.push(dollar);
                        i += 1;
                        continue;
                    };
                    if let Some(gt_rel) = replacement[i + 2..].iter().position(|&u| u == 0x3e) {
                        let name_units = replacement[i + 2..i + 2 + gt_rel].to_vec();
                        let cap = self.get_prop_value(named_v, &name_units)?;
                        if !matches!(cap, Value::Undefined) {
                            let cap_str = self.to_string_units(&cap)?;
                            out.extend_from_slice(&cap_str);
                        }
                        i = i + 2 + gt_rel + 1;
                    } else {
                        out.push(dollar);
                        i += 1;
                    }
                }
                _ => {
                    out.push(dollar);
                    i += 1;
                }
            }
        }
        Ok(out)
    }

    // -- @@split -------------------------------------------------------------

    fn regexp_proto_split(&mut self, this: &Value, s_arg: &Value, limit: &Value) -> ERes {
        let Value::Obj(rxid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let rxid = *rxid;
        let s = self.to_string_units(s_arg)?;
        let c = self.regexp_species_constructor(rxid)?;
        if c != self.intr.regexp_ctor {
            return Err(Abrupt::Fatal(
                "RegExp @@split via a non-default species constructor (out of slice)".to_string(),
            ));
        }
        let flags = self.regexp_read_flags(this)?;
        let unicode = has_flag(&flags, 'u') || has_flag(&flags, 'v');
        let new_flags = if has_flag(&flags, 'y') {
            flags.clone()
        } else {
            let mut f = flags.clone();
            f.push(u16::from(b'y'));
            f
        };
        let splitter = self.construct(
            &Value::Obj(c),
            vec![Value::Obj(rxid), Value::Str(Rc::new(new_flags))],
        )?;
        let Value::Obj(spid) = splitter else {
            return Err(Abrupt::Fatal("RegExp @@split splitter not an object".to_string()));
        };
        let arr = self.new_array(0);
        let mut length_a: u64 = 0;
        let lim = if matches!(limit, Value::Undefined) {
            u64::from(u32::MAX)
        } else {
            u64::from(crate::props::to_uint32(self.to_number(limit)?))
        };
        if lim == 0 {
            return Ok(Value::Obj(arr));
        }
        let size = s.len();
        if size == 0 {
            let z = self.regexp_exec(spid, &s)?;
            if !matches!(z, Value::Null) {
                return Ok(Value::Obj(arr));
            }
            self.create_array_element(arr, 0, Value::Str(Rc::new(s.clone())));
            return Ok(Value::Obj(arr));
        }
        let mut p: usize = 0;
        let mut q: usize = 0;
        while q < size {
            self.charge_loop()?;
            #[allow(clippy::cast_precision_loss)]
            self.set_last_index(spid, q as f64)?;
            let z = self.regexp_exec(spid, &s)?;
            if matches!(z, Value::Null) {
                q = advance_string_index(&s, q, unicode);
                continue;
            }
            let e = self.read_last_index(spid)?.min(size);
            if e == p {
                q = advance_string_index(&s, q, unicode);
                continue;
            }
            let t: Units = s[p..q].to_vec();
            self.create_array_element(arr, length_a, Value::Str(Rc::new(t)));
            length_a += 1;
            if length_a == lim {
                return Ok(Value::Obj(arr));
            }
            p = e;
            let len_v = self.get_prop_value(&z, &units_from_str("length"))?;
            let number_of_captures = to_length_u64(self.to_number(&len_v)?).saturating_sub(1);
            for i in 1..=number_of_captures {
                let cap = self.get_prop_value(&z, &units_from_str(&i.to_string()))?;
                self.create_array_element(arr, length_a, cap);
                length_a += 1;
                if length_a == lim {
                    return Ok(Value::Obj(arr));
                }
            }
            q = p;
        }
        let t: Units = s[p..].to_vec();
        self.create_array_element(arr, length_a, Value::Str(Rc::new(t)));
        Ok(Value::Obj(arr))
    }

    // -- @@matchAll + the RegExp String Iterator -----------------------------

    fn regexp_proto_match_all(&mut self, this: &Value, s_arg: &Value) -> ERes {
        let Value::Obj(rid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let rid = *rid;
        let s = self.to_string_units(s_arg)?;
        let c = self.regexp_species_constructor(rid)?;
        if c != self.intr.regexp_ctor {
            return Err(Abrupt::Fatal(
                "RegExp @@matchAll via a non-default species constructor (out of slice)"
                    .to_string(),
            ));
        }
        let flags = self.regexp_read_flags(this)?;
        let matcher = self.construct(
            &Value::Obj(c),
            vec![Value::Obj(rid), Value::Str(Rc::new(flags.clone()))],
        )?;
        let Value::Obj(mid) = matcher else {
            return Err(Abrupt::Fatal("RegExp @@matchAll matcher not an object".to_string()));
        };
        let li = self.read_last_index(rid)?;
        #[allow(clippy::cast_precision_loss)]
        self.set_last_index(mid, li as f64)?;
        let global = has_flag(&flags, 'g');
        let unicode = has_flag(&flags, 'u') || has_flag(&flags, 'v');
        let proto = self.intr.regexp_string_iterator_proto;
        let iter = self.alloc(Object::new(
            ObjKind::RegExpStringIterator {
                regexp: mid,
                string: Rc::new(s),
                global,
                unicode,
                done: false,
            },
            Some(proto),
        ));
        Ok(Value::Obj(iter))
    }

    /// %RegExpStringIteratorPrototype%.next (22.2.9.2.1).
    pub(crate) fn regexp_string_iterator_next(&mut self, this: &Value) -> ERes {
        let Value::Obj(oid) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let oid = *oid;
        let (regexp, s, global, unicode, done) = match &self.obj(oid).kind {
            ObjKind::RegExpStringIterator {
                regexp,
                string,
                global,
                unicode,
                done,
            } => (*regexp, string.clone(), *global, *unicode, *done),
            _ => return Err(self.throw_native(NativeErrorKind::TypeError)),
        };
        if done {
            return Ok(self.iter_result(Value::Undefined, true));
        }
        let m = self.regexp_string_iterator_step(regexp, &s, global, unicode)?;
        match m {
            None => {
                self.set_regexp_iterator_done(oid);
                Ok(self.iter_result(Value::Undefined, true))
            }
            Some(v) => {
                if !global {
                    self.set_regexp_iterator_done(oid);
                }
                Ok(self.iter_result(v, false))
            }
        }
    }

    /// One RegExpExec step for the iterator; None once exhausted. Also drives
    /// the empty-match lastIndex advance in global mode.
    pub(crate) fn regexp_string_iterator_step(
        &mut self,
        regexp: ObjId,
        s: &Units,
        global: bool,
        unicode: bool,
    ) -> Result<Option<Value>, Abrupt> {
        let m = self.regexp_exec(regexp, s)?;
        if matches!(m, Value::Null) {
            return Ok(None);
        }
        if global {
            let m0 = self.get_prop_value(&m, &units_from_str("0"))?;
            let match_str = self.to_string_units(&m0)?;
            if match_str.is_empty() {
                let li = self.read_last_index(regexp)?;
                let nli = advance_string_index(s, li, unicode);
                #[allow(clippy::cast_precision_loss)]
                self.set_last_index(regexp, nli as f64)?;
            }
        }
        Ok(Some(m))
    }

    fn set_regexp_iterator_done(&mut self, oid: ObjId) {
        if let ObjKind::RegExpStringIterator { done, .. } = &mut self.obj_mut(oid).kind {
            *done = true;
        }
    }

    // -- shared helpers ------------------------------------------------------

    /// SpeciesConstructor(rx, %RegExp%) (7.3.22) — the constructor identity.
    fn regexp_species_constructor(&mut self, rx: ObjId) -> Result<ObjId, Abrupt> {
        let c = self.get_from_object(rx, &units_from_str("constructor"))?;
        if matches!(c, Value::Undefined) {
            return Ok(self.intr.regexp_ctor);
        }
        let Value::Obj(cid) = c else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        let species = self.get_prop_value_sym(&Value::Obj(cid), self.intr.wk(WK_SPECIES))?;
        match species {
            Value::Undefined | Value::Null => Ok(self.intr.regexp_ctor),
            Value::Obj(sid) if self.obj(sid).is_callable() => Ok(sid),
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// ToString(Get(R, "flags")) as code units — the generic flags read shared
    /// by the @@-protocols.
    fn regexp_read_flags(&mut self, r: &Value) -> Result<Units, Abrupt> {
        let flags_v = self.get_prop_value(r, &units_from_str("flags"))?;
        self.to_string_units(&flags_v)
    }

    fn read_last_index(&mut self, rid: ObjId) -> Result<usize, Abrupt> {
        let v = self.get_from_object(rid, &units_from_str("lastIndex"))?;
        Ok(to_length_u64(self.to_number(&v)?) as usize)
    }

    /// CreateDataPropertyOrThrow(arr, ToString(i), v) with the array length
    /// bumped to i+1.
    fn create_array_element(&mut self, arr: ObjId, i: u64, v: Value) {
        self.obj_mut(arr)
            .props
            .insert(units_from_str(&i.to_string()), Prop::data(v));
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(arr, (i + 1) as f64);
    }
}
