// RegExp runtime (S1d proper): the RegExp constructor + RegExpInitialize/
// RegExpAlloc, RegExp.prototype.{compile,exec,test,source,flags,toString} and
// the abstract methods @@match/@@replace/@@search/@@split, plus the generic
// RegExpExec/RegExpBuiltinExec, all written from ECMA-262 §22.2. The compiled
// matcher is the frozen, spec-exact `trust-js-regexp` engine: a
// CompileError::Syntax at RegExpInitialize is the exact SyntaxError a
// conforming engine raises; a CompileError::Unsupported (Annex-B /
// resource-extreme) ADMITS the object but marks the [[RegExpMatcher]] a gap so
// every later match refuses (NoCoverage) — never a wrong or null result where
// a real match exists. An ExecError (budget / unsupported) likewise refuses.
//
// @@matchAll and String.prototype.matchAll are DECLARED out of slice: the
// %RegExpStringIterator% they return is iterator machinery (S1e), so they
// refuse (sound). Everything else is spec-exact, adversarially calibrated
// against Node and Bun through the trace driver.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss
)]

use crate::interp::{Abrupt, ERes, Interp, MAX_STRING_UNITS};
use std::collections::HashSet;
use std::rc::Rc;
use trust_js_regexp::{compile, CompileError, MatchResult, Pattern};
use trust_js_value::{
    to_integer_or_infinity, to_length_u64, to_uint32, units_from_str, ErrKind, JsObject, JsValue,
    NativeFn, ObjId, ObjKind, PropKey, Property, RegexData, RegexFlagKind, RegexFlags, SymId, Units,
    WkSym,
};

const DOLLAR: u16 = 0x24;

impl Interp {
    /// Evaluate a regex literal: RegExpCreate with the literal's exact source
    /// text ([[OriginalSource]] verbatim) and parsed flags. The pattern was
    /// already validated by the parser; we compile it into the
    /// [[RegExpMatcher]] side table (Unsupported → matcher gap; a Syntax
    /// disagreement with the parser is a sound refusal, never a wrong trace).
    pub(crate) fn eval_regex_literal(&mut self, pattern: &str, flags: &str) -> ERes {
        let Some(rf) = RegexFlags::from_valid_str(flags) else {
            return Err(Abrupt::Fatal(format!(
                "regex literal flags outside the validated set: `{flags}` (parser bug?)"
            )));
        };
        let source_units = units_from_str(pattern);
        let data = RegexData {
            source: Rc::new(source_units.clone()),
            flags: rf,
        };
        let proto = self.intr.regexp_proto;
        let oid = self.alloc_obj(JsObject::new(ObjKind::Regex(data), Some(proto)))?;
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("lastIndex"),
            Property::with_attrs(JsValue::Num(0.0), true, false, false),
        );
        match compile(&source_units, flags) {
            Ok(pat) => {
                self.regex_patterns.insert(oid, Ok(Rc::new(pat)));
            }
            Err(CompileError::Unsupported(r)) => {
                self.regex_patterns.insert(oid, Err(r));
            }
            Err(CompileError::Syntax(msg)) => {
                return Err(Abrupt::Fatal(format!(
                    "regex literal `/{pattern}/{flags}` compile Syntax \
                     (parser/regexp disagreement): {msg}"
                )));
            }
        }
        Ok(JsValue::Obj(oid))
    }

    fn regex_data(&self, v: &JsValue) -> Option<RegexData> {
        if let JsValue::Obj(oid) = v {
            if let ObjKind::Regex(d) = &self.heap.obj(*oid).kind {
                return Some(d.clone());
            }
        }
        None
    }

    fn is_regexp_obj(&self, oid: ObjId) -> bool {
        matches!(self.heap.obj(oid).kind, ObjKind::Regex(_))
    }

    fn is_regexp_proto(&self, v: &JsValue) -> bool {
        matches!(v, JsValue::Obj(o) if *o == self.intr.regexp_proto)
    }

    /// The compiled [[RegExpMatcher]] for a RegExp instance, or a sound refusal
    /// (the pattern was admitted but is outside the spec-exact matcher surface,
    /// or the instance is unexpectedly absent from the side table).
    fn regex_pattern(&self, oid: ObjId) -> Result<Rc<Pattern>, Abrupt> {
        match self.regex_patterns.get(&oid) {
            Some(Ok(p)) => Ok(Rc::clone(p)),
            Some(Err(reason)) => Err(Abrupt::Fatal(format!(
                "regexp matcher unsupported (S1d refusal): {reason}"
            ))),
            None => Err(Abrupt::Fatal(
                "regexp instance without a compiled matcher (interpreter bug)".to_string(),
            )),
        }
    }

    // -- allocation / initialization ----------------------------------------

    /// RegExpAlloc: OrdinaryCreateFromConstructor(newTarget, %RegExp.prototype%)
    /// with the exotic Regex kind and the `lastIndex` own data slot
    /// {w:true, e:false, c:false}. The RegexData is a placeholder overwritten
    /// by RegExpInitialize before the object escapes.
    fn regexp_alloc(&mut self, nt: &JsValue) -> Result<ObjId, Abrupt> {
        let proto = self.get_prototype_from_constructor(nt, self.intr.regexp_proto)?;
        let data = RegexData {
            source: Rc::new(Vec::new()),
            flags: RegexFlags::default(),
        };
        let oid = self.alloc_obj(JsObject::new(ObjKind::Regex(data), Some(proto)))?;
        self.heap.obj_mut(oid).props.insert(
            PropKey::from_str("lastIndex"),
            Property::with_attrs(JsValue::Num(0.0), true, false, false),
        );
        Ok(oid)
    }

    /// RegExpInitialize(obj, P, F) with P and F already reduced to code units
    /// (undefined mapped to empty by the caller). `throw_syntax` = true for the
    /// constructor / `compile` (a Syntax verdict is the real SyntaxError); the
    /// literal path passes false (a Syntax verdict there is a parser
    /// disagreement → a sound refusal).
    fn regexp_initialize(
        &mut self,
        oid: ObjId,
        source: &[u16],
        flags_units: &[u16],
        throw_syntax: bool,
    ) -> Result<(), Abrupt> {
        let Some(flags) = parse_flags_strict(flags_units) else {
            return if throw_syntax {
                Err(self.throw_native(ErrKind::Syntax))
            } else {
                Err(Abrupt::Fatal(
                    "regex literal flags invalid at initialize (parser disagreement)".to_string(),
                ))
            };
        };
        // All units validated ASCII flag letters — a lossless &str for compile.
        let flags_ascii: String = flags_units.iter().map(|&u| u as u8 as char).collect();
        match compile(source, &flags_ascii) {
            Ok(pat) => {
                self.regex_patterns.insert(oid, Ok(Rc::new(pat)));
            }
            Err(CompileError::Syntax(_)) => {
                return if throw_syntax {
                    Err(self.throw_native(ErrKind::Syntax))
                } else {
                    Err(Abrupt::Fatal(
                        "regex pattern Syntax at initialize (parser disagreement)".to_string(),
                    ))
                };
            }
            Err(CompileError::Unsupported(r)) => {
                self.regex_patterns.insert(oid, Err(r));
            }
        }
        if let ObjKind::Regex(d) = &mut self.heap.obj_mut(oid).kind {
            d.source = Rc::new(source.to_vec());
            d.flags = flags;
        }
        // RegExpInitialize step: Perform ? Set(obj, "lastIndex", +0F, true).
        self.set_prop(
            &JsValue::Obj(oid),
            &PropKey::from_str("lastIndex"),
            JsValue::Num(0.0),
            true,
        )?;
        Ok(())
    }

    /// RegExpCreate(P, F): RegExpAlloc(%RegExp%) then RegExpInitialize (with the
    /// standard ToString of P/F; undefined → empty).
    pub(crate) fn regexp_create(&mut self, pattern: &JsValue, flags: &JsValue) -> Result<ObjId, Abrupt> {
        let nt = JsValue::Obj(self.intr.regexp_ctor);
        let oid = self.regexp_alloc(&nt)?;
        let p = if matches!(pattern, JsValue::Undefined) {
            Vec::new()
        } else {
            self.to_string_units(pattern)?
        };
        let f = if matches!(flags, JsValue::Undefined) {
            Vec::new()
        } else {
            self.to_string_units(flags)?
        };
        self.regexp_initialize(oid, &p, &f, true)?;
        Ok(oid)
    }

    /// The RegExp constructor (22.2.4.1): call and new forms, the
    /// return-the-same-object optimization, and the [[RegExpMatcher]] /
    /// IsRegExp pattern-or-flags extraction.
    fn regexp_construct(
        &mut self,
        new_target: Option<JsValue>,
        pattern: JsValue,
        flags: JsValue,
    ) -> ERes {
        let pattern_is_regexp = self.is_reg_exp(&pattern)?;
        let nt_was_none = new_target.is_none();
        let nt = new_target.unwrap_or(JsValue::Obj(self.intr.regexp_ctor));
        // Call form + patternIsRegExp + flags undefined + same constructor →
        // return pattern unchanged.
        if nt_was_none && pattern_is_regexp && matches!(flags, JsValue::Undefined) {
            let pc = self.get_prop(&pattern, &PropKey::from_str("constructor"))?;
            if crate::ops::same_value(&nt, &pc) {
                return Ok(pattern);
            }
        }
        // Extract P (source units) and F (flags units).
        let (p_units, f_units) = if let Some(d) = self.regex_data(&pattern) {
            let p = d.source.as_ref().clone();
            let f = if matches!(flags, JsValue::Undefined) {
                regex_flags_to_units(&d.flags)
            } else {
                self.to_string_units(&flags)?
            };
            (p, f)
        } else if pattern_is_regexp {
            let src = self.get_prop(&pattern, &PropKey::from_str("source"))?;
            let p = self.to_string_units(&src)?;
            let f = if matches!(flags, JsValue::Undefined) {
                let fl = self.get_prop(&pattern, &PropKey::from_str("flags"))?;
                self.to_string_units(&fl)?
            } else {
                self.to_string_units(&flags)?
            };
            (p, f)
        } else {
            let p = if matches!(pattern, JsValue::Undefined) {
                Vec::new()
            } else {
                self.to_string_units(&pattern)?
            };
            let f = if matches!(flags, JsValue::Undefined) {
                Vec::new()
            } else {
                self.to_string_units(&flags)?
            };
            (p, f)
        };
        let oid = self.regexp_alloc(&nt)?;
        self.regexp_initialize(oid, &p_units, &f_units, true)?;
        Ok(JsValue::Obj(oid))
    }

    // -- dispatch ------------------------------------------------------------

    pub(crate) fn dispatch_regexp(
        &mut self,
        nf: NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        use NativeFn as N;
        match nf {
            N::RegExpCtor => self.regexp_construct(new_target, arg(0), arg(1)),
            N::RegexFlagGetter(kind) => {
                // 22.2.6.4.1 RegExpHasFlag: undefined on %RegExp.prototype%,
                // TypeError on any other non-RegExp receiver.
                if let Some(d) = self.regex_data(&this) {
                    let f = &d.flags;
                    let v = match kind {
                        RegexFlagKind::HasIndices => f.has_indices,
                        RegexFlagKind::Global => f.global,
                        RegexFlagKind::IgnoreCase => f.ignore_case,
                        RegexFlagKind::Multiline => f.multiline,
                        RegexFlagKind::DotAll => f.dot_all,
                        RegexFlagKind::Unicode => f.unicode,
                        RegexFlagKind::UnicodeSets => f.unicode_sets,
                        RegexFlagKind::Sticky => f.sticky,
                    };
                    return Ok(JsValue::Bool(v));
                }
                if self.is_regexp_proto(&this) {
                    return Ok(JsValue::Undefined);
                }
                Err(self.throw_type_error())
            }
            N::RegexSourceGetter => {
                // 22.2.6.13: "(?:)" on %RegExp.prototype%; EscapeRegExpPattern
                // of [[OriginalSource]] on instances.
                if let Some(d) = self.regex_data(&this) {
                    let escaped = escape_regexp_pattern(&d.source, d.flags.unicode_sets);
                    return Ok(JsValue::Str(Rc::new(escaped)));
                }
                if self.is_regexp_proto(&this) {
                    return Ok(JsValue::str_from("(?:)"));
                }
                Err(self.throw_type_error())
            }
            N::RegexFlagsGetter => {
                // 22.2.6.4: reads each flag PROPERTY via Get (observable on
                // arbitrary objects), appending codes in spec order.
                let JsValue::Obj(_) = this else {
                    return Err(self.throw_type_error());
                };
                let mut out: Units = Vec::new();
                for (name, code) in [
                    ("hasIndices", b'd'),
                    ("global", b'g'),
                    ("ignoreCase", b'i'),
                    ("multiline", b'm'),
                    ("dotAll", b's'),
                    ("unicode", b'u'),
                    ("unicodeSets", b'v'),
                    ("sticky", b'y'),
                ] {
                    let v = self.get_prop(&this, &PropKey::from_str(name))?;
                    if self.to_boolean(&v) {
                        out.push(u16::from(code));
                    }
                }
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::RegexToString => {
                // 22.2.6.17: "/" + Get(R,"source") + "/" + Get(R,"flags").
                let JsValue::Obj(_) = this else {
                    return Err(self.throw_type_error());
                };
                let src = self.get_prop(&this, &PropKey::from_str("source"))?;
                let src_u = self.to_string_units(&src)?;
                let fl = self.get_prop(&this, &PropKey::from_str("flags"))?;
                let fl_u = self.to_string_units(&fl)?;
                let mut out: Units = vec![0x2f];
                out.extend_from_slice(&src_u);
                out.push(0x2f);
                out.extend_from_slice(&fl_u);
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::RegexProtoMethod(tag) => match tag {
                "exec" => self.regex_proto_exec(&this, arg(0)),
                "test" => self.regex_proto_test(&this, arg(0)),
                "compile" => self.regex_proto_compile(&this, arg(0), arg(1)),
                "@@match" => self.regexp_symbol_match(&this, &arg(0)),
                "@@search" => self.regexp_symbol_search(&this, &arg(0)),
                "@@replace" => self.regexp_symbol_replace(&this, &arg(0), &arg(1)),
                "@@split" => self.regexp_symbol_split(&this, &arg(0), &arg(1)),
                "@@matchAll" => self.regexp_symbol_match_all(&this, &arg(0)),
                other => Err(Abrupt::Fatal(format!(
                    "unrouted RegExp.prototype method `{other}` (interpreter bug)"
                ))),
            },
            _ => Err(Abrupt::Fatal(
                "unrouted regexp native (interpreter bug)".to_string(),
            )),
        }
    }

    // -- exec / test / compile ----------------------------------------------

    /// RegExp.prototype.exec (22.2.6.9): requires [[RegExpMatcher]], uses
    /// RegExpBuiltinExec directly.
    fn regex_proto_exec(&mut self, this: &JsValue, string: JsValue) -> ERes {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        if !self.is_regexp_obj(oid) {
            return Err(self.throw_type_error());
        }
        let s = self.to_string_units(&string)?;
        self.regexp_builtin_exec(oid, &s)
    }

    /// RegExp.prototype.test (22.2.6.16): requires an Object; RegExpExec
    /// (generic — honors a user "exec").
    fn regex_proto_test(&mut self, this: &JsValue, string: JsValue) -> ERes {
        let JsValue::Obj(_) = this else {
            return Err(self.throw_type_error());
        };
        let s = self.to_string_units(&string)?;
        let m = self.regexp_exec(this, &s)?;
        Ok(JsValue::Bool(!matches!(m, JsValue::Null)))
    }

    /// RegExp.prototype.compile (22.2.6.4 legacy): RegExpInitialize in place.
    fn regex_proto_compile(&mut self, this: &JsValue, pattern: JsValue, flags: JsValue) -> ERes {
        let JsValue::Obj(oid) = this else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        if !self.is_regexp_obj(oid) {
            return Err(self.throw_type_error());
        }
        let (p, f) = if let Some(d) = self.regex_data(&pattern) {
            if !matches!(flags, JsValue::Undefined) {
                return Err(self.throw_type_error());
            }
            (d.source.as_ref().clone(), regex_flags_to_units(&d.flags))
        } else {
            let p = if matches!(pattern, JsValue::Undefined) {
                Vec::new()
            } else {
                self.to_string_units(&pattern)?
            };
            let f = if matches!(flags, JsValue::Undefined) {
                Vec::new()
            } else {
                self.to_string_units(&flags)?
            };
            (p, f)
        };
        self.regexp_initialize(oid, &p, &f, true)?;
        Ok(this.clone())
    }

    // -- RegExpExec / RegExpBuiltinExec -------------------------------------

    /// RegExpExec (22.2.7.1): Get(R,"exec"); if callable, Call and validate the
    /// Object|Null result; else RegExpBuiltinExec against [[RegExpMatcher]].
    pub(crate) fn regexp_exec(&mut self, r: &JsValue, s: &[u16]) -> ERes {
        let JsValue::Obj(oid) = r else {
            return Err(self.throw_type_error());
        };
        let oid = *oid;
        let exec = self.get_prop(r, &PropKey::from_str("exec"))?;
        if let JsValue::Obj(e) = &exec {
            if self.heap.obj(*e).is_callable() {
                let result =
                    self.call_value(&exec, r.clone(), vec![JsValue::Str(Rc::new(s.to_vec()))])?;
                if !matches!(result, JsValue::Obj(_) | JsValue::Null) {
                    return Err(self.throw_type_error());
                }
                return Ok(result);
            }
        }
        if !self.is_regexp_obj(oid) {
            return Err(self.throw_type_error());
        }
        self.regexp_builtin_exec(oid, s)
    }

    /// RegExpBuiltinExec (22.2.7.2): the match array (index/input/groups/
    /// captures/indices) or null. An ExecError from the matcher is a sound
    /// refusal — never null where a real match exists.
    fn regexp_builtin_exec(&mut self, oid: ObjId, s: &[u16]) -> ERes {
        let this_v = JsValue::Obj(oid);
        let pattern = self.regex_pattern(oid)?;
        let flags = match &self.heap.obj(oid).kind {
            ObjKind::Regex(d) => d.flags,
            _ => return Err(self.throw_type_error()),
        };
        let global = flags.global;
        let sticky = flags.sticky;
        let has_indices = flags.has_indices;

        let li_v = self.get_prop(&this_v, &PropKey::from_str("lastIndex"))?;
        let last_index = to_length_u64(self.to_number(&li_v)?);
        let start_u = if global || sticky { last_index } else { 0 };
        let start = usize::try_from(start_u).unwrap_or(usize::MAX);

        let res = if sticky {
            pattern.exec_sticky_at(s, start)
        } else {
            pattern.exec_at(s, start)
        };
        let m = match res {
            Err(_) => {
                return Err(Abrupt::Fatal(
                    "regexp match unsupported/budget (S1d refusal, never a wrong result)"
                        .to_string(),
                ))
            }
            Ok(None) => {
                if global || sticky {
                    self.set_prop(
                        &this_v,
                        &PropKey::from_str("lastIndex"),
                        JsValue::Num(0.0),
                        true,
                    )?;
                }
                return Ok(JsValue::Null);
            }
            Ok(Some(m)) => m,
        };

        let e = m.end;
        if global || sticky {
            self.set_prop(
                &this_v,
                &PropKey::from_str("lastIndex"),
                JsValue::Num(e as f64),
                true,
            )?;
        }

        let n = pattern.n_captures();
        let group_names = group_names_by_index(&pattern, n);
        let has_groups = group_names.iter().any(Option::is_some);

        let a = self.new_array(0)?;
        self.create_data_property_or_throw(a, "index", JsValue::Num(m.index as f64))?;
        self.create_data_property_or_throw(a, "input", JsValue::Str(Rc::new(s.to_vec())))?;
        self.create_data_property_or_throw(
            a,
            "0",
            JsValue::Str(Rc::new(s[m.index..e].to_vec())),
        )?;
        let groups_oid = if has_groups {
            Some(self.alloc_obj(JsObject::new(ObjKind::Plain, None))?)
        } else {
            None
        };
        let groups_val = groups_oid.map_or(JsValue::Undefined, JsValue::Obj);
        self.create_data_property_or_throw(a, "groups", groups_val)?;

        let mut cap_vals: Vec<JsValue> = Vec::with_capacity(n);
        for i in 1..=n {
            let cap_val = match m.captures[i - 1] {
                Some((cs, ce)) => JsValue::Str(Rc::new(s[cs..ce].to_vec())),
                None => JsValue::Undefined,
            };
            self.create_data_property_or_throw(a, &i.to_string(), cap_val.clone())?;
            cap_vals.push(cap_val);
        }
        if let Some(g) = groups_oid {
            self.fill_named(g, &group_names, &cap_vals)?;
        }

        if has_indices {
            let indices_arr = self.make_indices_array(&m, n, &group_names, has_groups)?;
            self.create_data_property_or_throw(a, "indices", JsValue::Obj(indices_arr))?;
        }
        Ok(JsValue::Obj(a))
    }

    /// MakeMatchIndicesIndexPairArray (22.2.7.7). Match Record positions are
    /// already UTF-16 code-unit offsets (the matcher's convention), so S is not
    /// needed to build the pairs.
    fn make_indices_array(
        &mut self,
        m: &MatchResult,
        n: usize,
        group_names: &[Option<String>],
        has_groups: bool,
    ) -> Result<ObjId, Abrupt> {
        let arr = self.new_array(0)?;
        let groups_oid = if has_groups {
            Some(self.alloc_obj(JsObject::new(ObjKind::Plain, None))?)
        } else {
            None
        };
        let groups_val = groups_oid.map_or(JsValue::Undefined, JsValue::Obj);
        self.create_data_property_or_throw(arr, "groups", groups_val)?;
        let mut cap_pairs: Vec<JsValue> = Vec::with_capacity(n);
        for i in 0..=n {
            let pair = if i == 0 {
                Some((m.index, m.end))
            } else {
                m.captures[i - 1]
            };
            let pair_val = match pair {
                Some((ps, pe)) => {
                    let p = self.new_array(0)?;
                    self.create_data_property_or_throw(p, "0", JsValue::Num(ps as f64))?;
                    self.create_data_property_or_throw(p, "1", JsValue::Num(pe as f64))?;
                    JsValue::Obj(p)
                }
                None => JsValue::Undefined,
            };
            self.create_data_property_or_throw(arr, &i.to_string(), pair_val.clone())?;
            if i >= 1 {
                cap_pairs.push(pair_val);
            }
        }
        if let Some(g) = groups_oid {
            self.fill_named(g, group_names, &cap_pairs)?;
        }
        Ok(arr)
    }

    /// Fill a null-prototype groups object: for each named capture in
    /// group-number order, the participating group's value wins and the key
    /// takes its first-occurrence position (ES2025 duplicate named groups).
    fn fill_named(
        &mut self,
        groups_oid: ObjId,
        names: &[Option<String>],
        values: &[JsValue],
    ) -> Result<(), Abrupt> {
        let mut matched: HashSet<&str> = HashSet::new();
        for (i, name_opt) in names.iter().enumerate() {
            let Some(name) = name_opt else { continue };
            if matched.contains(name.as_str()) {
                continue;
            }
            let v = values[i].clone();
            let participated = !matches!(v, JsValue::Undefined);
            self.create_data_property_or_throw(groups_oid, name, v)?;
            if participated {
                matched.insert(name.as_str());
            }
        }
        Ok(())
    }

    // -- @@match / @@search / @@replace / @@split ---------------------------

    /// RegExp.prototype[@@match] (22.2.6.8).
    fn regexp_symbol_match(&mut self, this: &JsValue, string: &JsValue) -> ERes {
        let JsValue::Obj(_) = this else {
            return Err(self.throw_type_error());
        };
        let s = self.to_string_units(string)?;
        let flags_v = self.get_prop(this, &PropKey::from_str("flags"))?;
        let flags = self.to_string_units(&flags_v)?;
        let global = flags.contains(&u16::from(b'g'));
        if !global {
            return self.regexp_exec(this, &s);
        }
        let full_unicode = has_unicode(&flags);
        self.set_prop(this, &PropKey::from_str("lastIndex"), JsValue::Num(0.0), true)?;
        let a = self.new_array(0)?;
        let mut n: u64 = 0;
        loop {
            self.charge_loop()?;
            let result = self.regexp_exec(this, &s)?;
            if matches!(result, JsValue::Null) {
                return if n == 0 {
                    Ok(JsValue::Null)
                } else {
                    Ok(JsValue::Obj(a))
                };
            }
            let JsValue::Obj(res) = result else {
                return Err(self.throw_type_error());
            };
            let match0 = self.get_from_object(res, &PropKey::from_str("0"), result.clone())?;
            let match_str = self.to_string_units(&match0)?;
            self.create_data_property_or_throw(
                a,
                &n.to_string(),
                JsValue::Str(Rc::new(match_str.clone())),
            )?;
            if match_str.is_empty() {
                let li = self.get_prop(this, &PropKey::from_str("lastIndex"))?;
                let this_index = to_length_u64(self.to_number(&li)?);
                let next = advance_string_index(&s, this_index, full_unicode);
                self.set_prop(
                    this,
                    &PropKey::from_str("lastIndex"),
                    JsValue::Num(next as f64),
                    true,
                )?;
            }
            n += 1;
        }
    }

    /// RegExp.prototype[@@search] (22.2.6.14).
    fn regexp_symbol_search(&mut self, this: &JsValue, string: &JsValue) -> ERes {
        let JsValue::Obj(_) = this else {
            return Err(self.throw_type_error());
        };
        let s = self.to_string_units(string)?;
        let previous = self.get_prop(this, &PropKey::from_str("lastIndex"))?;
        if !crate::ops::same_value(&previous, &JsValue::Num(0.0)) {
            self.set_prop(this, &PropKey::from_str("lastIndex"), JsValue::Num(0.0), true)?;
        }
        let result = self.regexp_exec(this, &s)?;
        let current = self.get_prop(this, &PropKey::from_str("lastIndex"))?;
        if !crate::ops::same_value(&current, &previous) {
            self.set_prop(this, &PropKey::from_str("lastIndex"), previous, true)?;
        }
        if matches!(result, JsValue::Null) {
            return Ok(JsValue::Num(-1.0));
        }
        let JsValue::Obj(res) = &result else {
            return Err(self.throw_type_error());
        };
        self.get_from_object(*res, &PropKey::from_str("index"), result.clone())
    }

    /// RegExp.prototype[@@replace] (22.2.6.11): string replacer with the full
    /// $-substitution table (incl. $<name>) and function replacers.
    fn regexp_symbol_replace(
        &mut self,
        this: &JsValue,
        string: &JsValue,
        replace_value: &JsValue,
    ) -> ERes {
        let JsValue::Obj(_) = this else {
            return Err(self.throw_type_error());
        };
        let s = self.to_string_units(string)?;
        let length_s = s.len();
        let functional =
            matches!(replace_value, JsValue::Obj(o) if self.heap.obj(*o).is_callable());
        let repl_units: Option<Units> = if functional {
            None
        } else {
            Some(self.to_string_units(replace_value)?)
        };
        let flags_v = self.get_prop(this, &PropKey::from_str("flags"))?;
        let flags = self.to_string_units(&flags_v)?;
        let global = flags.contains(&u16::from(b'g'));
        let full_unicode = has_unicode(&flags);
        if global {
            self.set_prop(this, &PropKey::from_str("lastIndex"), JsValue::Num(0.0), true)?;
        }
        // Collect the match results.
        let mut results: Vec<ObjId> = Vec::new();
        loop {
            self.charge_loop()?;
            let result = self.regexp_exec(this, &s)?;
            let JsValue::Obj(res) = result else {
                break;
            };
            results.push(res);
            if !global {
                break;
            }
            let m0 = self.get_from_object(res, &PropKey::from_str("0"), JsValue::Obj(res))?;
            let match_str = self.to_string_units(&m0)?;
            if match_str.is_empty() {
                let li = self.get_prop(this, &PropKey::from_str("lastIndex"))?;
                let idx = to_length_u64(self.to_number(&li)?);
                let next = advance_string_index(&s, idx, full_unicode);
                self.set_prop(
                    this,
                    &PropKey::from_str("lastIndex"),
                    JsValue::Num(next as f64),
                    true,
                )?;
            }
        }
        let mut accumulated: Units = Vec::new();
        let mut next_source_pos: usize = 0;
        for res in results {
            self.charge_loop()?;
            let result_len = self.length_of_array_like(res)?;
            let n_captures = result_len.saturating_sub(1);
            let matched_v = self.get_from_object(res, &PropKey::from_str("0"), JsValue::Obj(res))?;
            let matched = self.to_string_units(&matched_v)?;
            let pos_v = self.get_from_object(res, &PropKey::from_str("index"), JsValue::Obj(res))?;
            let pos_f = to_integer_or_infinity(self.to_number(&pos_v)?);
            let position = clamp_index(pos_f, length_s);
            let mut captures: Vec<Option<Units>> = Vec::new();
            let mut i: u64 = 1;
            while i <= n_captures {
                let cap =
                    self.get_from_object(res, &PropKey::Str(units_from_str(&i.to_string())), JsValue::Obj(res))?;
                if matches!(cap, JsValue::Undefined) {
                    captures.push(None);
                } else {
                    captures.push(Some(self.to_string_units(&cap)?));
                }
                i += 1;
            }
            let named = self.get_from_object(res, &PropKey::from_str("groups"), JsValue::Obj(res))?;
            let replacement: Units = if functional {
                let mut fargs: Vec<JsValue> = Vec::with_capacity(captures.len() + 3);
                fargs.push(JsValue::Str(Rc::new(matched.clone())));
                for c in &captures {
                    fargs.push(match c {
                        Some(u) => JsValue::Str(Rc::new(u.clone())),
                        None => JsValue::Undefined,
                    });
                }
                fargs.push(JsValue::Num(position as f64));
                fargs.push(JsValue::Str(Rc::new(s.clone())));
                if !matches!(named, JsValue::Undefined) {
                    fargs.push(named.clone());
                }
                let rv = self.call_value(replace_value, JsValue::Undefined, fargs)?;
                self.to_string_units(&rv)?
            } else {
                let named_obj = if matches!(named, JsValue::Undefined) {
                    None
                } else {
                    Some(self.to_object(&named)?)
                };
                let template = repl_units.as_ref().expect("non-functional path");
                self.get_substitution(&matched, &s, position, &captures, named_obj, template)?
            };
            if position >= next_source_pos {
                accumulated.extend_from_slice(&s[next_source_pos..position]);
                accumulated.extend_from_slice(&replacement);
                next_source_pos = position + matched.len();
                if accumulated.len() > MAX_STRING_UNITS {
                    return Err(Abrupt::Fatal("replace result cap exceeded".to_string()));
                }
            }
        }
        if next_source_pos < length_s {
            accumulated.extend_from_slice(&s[next_source_pos..]);
        }
        Ok(JsValue::Str(Rc::new(accumulated)))
    }

    /// GetSubstitution (22.1.3.19.1) with captures + named captures.
    #[allow(clippy::too_many_arguments)]
    fn get_substitution(
        &mut self,
        matched: &[u16],
        s: &[u16],
        position: usize,
        captures: &[Option<Units>],
        named_obj: Option<ObjId>,
        template: &[u16],
    ) -> Result<Units, Abrupt> {
        let n_caps = captures.len();
        let mut out: Units = Vec::with_capacity(template.len());
        let mut i = 0;
        while i < template.len() {
            let c = template[i];
            if c != DOLLAR || i + 1 >= template.len() {
                out.push(c);
                i += 1;
                continue;
            }
            let next = template[i + 1];
            match next {
                0x24 => {
                    out.push(DOLLAR);
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
                    out.extend_from_slice(&s[position + matched.len()..]);
                    i += 2;
                }
                0x30..=0x39 => {
                    let d1 = (next - 0x30) as usize;
                    let two = if i + 2 < template.len() && (0x30..=0x39).contains(&template[i + 2]) {
                        Some(d1 * 10 + (template[i + 2] - 0x30) as usize)
                    } else {
                        None
                    };
                    if let Some(t) = two {
                        if t >= 1 && t <= n_caps {
                            if let Some(cap) = &captures[t - 1] {
                                out.extend_from_slice(cap);
                            }
                            i += 3;
                            continue;
                        }
                    }
                    if d1 >= 1 && d1 <= n_caps {
                        if let Some(cap) = &captures[d1 - 1] {
                            out.extend_from_slice(cap);
                        }
                        i += 2;
                    } else {
                        out.push(DOLLAR);
                        i += 1;
                    }
                }
                0x3C => {
                    match named_obj {
                        None => {
                            out.push(DOLLAR);
                            i += 1;
                        }
                        Some(nobj) => {
                            let mut j = i + 2;
                            while j < template.len() && template[j] != 0x3E {
                                j += 1;
                            }
                            if j >= template.len() {
                                out.push(DOLLAR);
                                i += 1;
                            } else {
                                let name = template[i + 2..j].to_vec();
                                let ref_v = self.get_from_object(
                                    nobj,
                                    &PropKey::Str(name),
                                    JsValue::Obj(nobj),
                                )?;
                                if !matches!(ref_v, JsValue::Undefined) {
                                    let ru = self.to_string_units(&ref_v)?;
                                    out.extend_from_slice(&ru);
                                }
                                i = j + 1;
                            }
                        }
                    }
                }
                _ => {
                    out.push(DOLLAR);
                    i += 1;
                }
            }
        }
        Ok(out)
    }

    /// RegExp.prototype[@@split] (22.2.6.15): the splitter-clone (Species
    /// Constructor + sticky), limit, and empty-match semantics.
    fn regexp_symbol_split(&mut self, this: &JsValue, string: &JsValue, limit: &JsValue) -> ERes {
        let JsValue::Obj(_) = this else {
            return Err(self.throw_type_error());
        };
        let s = self.to_string_units(string)?;
        let c = self.species_constructor(this, self.intr.regexp_ctor)?;
        let flags_v = self.get_prop(this, &PropKey::from_str("flags"))?;
        let flags = self.to_string_units(&flags_v)?;
        let unicode = has_unicode(&flags);
        let mut new_flags = flags.clone();
        if !flags.contains(&u16::from(b'y')) {
            new_flags.push(u16::from(b'y'));
        }
        let splitter = self.construct(
            &c,
            vec![this.clone(), JsValue::Str(Rc::new(new_flags))],
            None,
        )?;
        let a = self.new_array(0)?;
        let mut length_a: u64 = 0;
        let lim: u64 = if matches!(limit, JsValue::Undefined) {
            0xFFFF_FFFF
        } else {
            u64::from(to_uint32(self.to_number(limit)?))
        };
        if lim == 0 {
            return Ok(JsValue::Obj(a));
        }
        let size = s.len();
        if size == 0 {
            let z = self.regexp_exec(&splitter, &s)?;
            if !matches!(z, JsValue::Null) {
                return Ok(JsValue::Obj(a));
            }
            self.create_data_property_or_throw(a, "0", JsValue::Str(Rc::new(s)))?;
            return Ok(JsValue::Obj(a));
        }
        let mut p: usize = 0;
        let mut q: usize = 0;
        while q < size {
            self.charge_loop()?;
            self.set_prop(
                &splitter,
                &PropKey::from_str("lastIndex"),
                JsValue::Num(q as f64),
                true,
            )?;
            let z = self.regexp_exec(&splitter, &s)?;
            if matches!(z, JsValue::Null) {
                q = advance_string_index(&s, q as u64, unicode) as usize;
                continue;
            }
            let JsValue::Obj(z_oid) = &z else {
                return Err(self.throw_type_error());
            };
            let z_oid = *z_oid;
            let li = self.get_prop(&splitter, &PropKey::from_str("lastIndex"))?;
            let e = to_length_u64(self.to_number(&li)?).min(size as u64) as usize;
            if e == p {
                q = advance_string_index(&s, q as u64, unicode) as usize;
                continue;
            }
            self.create_data_property_or_throw(
                a,
                &length_a.to_string(),
                JsValue::Str(Rc::new(s[p..q].to_vec())),
            )?;
            length_a += 1;
            if length_a == lim {
                return Ok(JsValue::Obj(a));
            }
            p = e;
            let num_captures = self.length_of_array_like(z_oid)?.saturating_sub(1);
            let mut i: u64 = 1;
            while i <= num_captures {
                let next_capture = self.get_from_object(
                    z_oid,
                    &PropKey::Str(units_from_str(&i.to_string())),
                    z.clone(),
                )?;
                self.create_data_property_or_throw(a, &length_a.to_string(), next_capture)?;
                length_a += 1;
                if length_a == lim {
                    return Ok(JsValue::Obj(a));
                }
                i += 1;
            }
            q = p;
        }
        self.create_data_property_or_throw(
            a,
            &length_a.to_string(),
            JsValue::Str(Rc::new(s[p..size].to_vec())),
        )?;
        Ok(JsValue::Obj(a))
    }

    /// RegExp.prototype[@@matchAll] (22.2.6.9): clone the regexp through the
    /// species constructor, carry lastIndex, and return the RegExpStringIterator
    /// closure as a state machine (iterobj.rs).
    fn regexp_symbol_match_all(&mut self, this: &JsValue, string: &JsValue) -> ERes {
        let JsValue::Obj(_) = this else {
            return Err(self.throw_type_error());
        };
        let s = self.to_string_units(string)?;
        let c = self.species_constructor(this, self.intr.regexp_ctor)?;
        let flags_v = self.get_prop(this, &PropKey::from_str("flags"))?;
        let flags = self.to_string_units(&flags_v)?;
        let matcher = self.construct(
            &c,
            vec![this.clone(), JsValue::Str(Rc::new(flags.clone()))],
            None,
        )?;
        let JsValue::Obj(m_oid) = matcher else {
            return Err(self.throw_type_error());
        };
        let li_v = self.get_prop(this, &PropKey::from_str("lastIndex"))?;
        let last_index = to_length_u64(self.to_number(&li_v)?);
        self.set_prop(
            &matcher,
            &PropKey::from_str("lastIndex"),
            JsValue::Num(last_index as f64),
            true,
        )?;
        let global = flags.contains(&u16::from(b'g'));
        let full_unicode = has_unicode(&flags);
        self.make_regexp_string_iterator(m_oid, Rc::new(s), global, full_unicode)
    }

    /// SpeciesConstructor(O, defaultConstructor) (7.3.22).
    fn species_constructor(&mut self, o: &JsValue, default: ObjId) -> ERes {
        let c = self.get_prop(o, &PropKey::from_str("constructor"))?;
        if matches!(c, JsValue::Undefined) {
            return Ok(JsValue::Obj(default));
        }
        let JsValue::Obj(_) = c else {
            return Err(self.throw_type_error());
        };
        let s = self.get_prop(&c, &PropKey::Sym(SymId::WellKnown(WkSym::Species)))?;
        if s.is_nullish() {
            return Ok(JsValue::Obj(default));
        }
        if self.is_constructor(&s) {
            return Ok(s);
        }
        Err(self.throw_type_error())
    }
}

/// The name (if any) of each capturing group 1..=n, indexed by group number.
fn group_names_by_index(pattern: &Pattern, n: usize) -> Vec<Option<String>> {
    let names = pattern.group_names();
    (1..=n as u32)
        .map(|g| {
            names
                .iter()
                .find(|(_, gi)| *gi == g)
                .map(|(name, _)| name.clone())
        })
        .collect()
}

/// AdvanceStringIndex (22.2.7.3), over code units.
pub(crate) fn advance_string_index(s: &[u16], index: u64, unicode: bool) -> u64 {
    if !unicode {
        return index + 1;
    }
    let len = s.len() as u64;
    if index + 1 >= len {
        return index + 1;
    }
    let i = index as usize;
    let first = s[i];
    if !(0xD800..=0xDBFF).contains(&first) {
        return index + 1;
    }
    let second = s[i + 1];
    if (0xDC00..=0xDFFF).contains(&second) {
        index + 2
    } else {
        index + 1
    }
}

/// max(min(pos, len), 0) for a ToIntegerOrInfinity result.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn clamp_index(pos: f64, len: usize) -> usize {
    if pos <= 0.0 {
        0
    } else if pos >= len as f64 {
        len
    } else {
        pos as usize
    }
}

fn has_unicode(flags: &[u16]) -> bool {
    flags.contains(&u16::from(b'u')) || flags.contains(&u16::from(b'v'))
}

/// Parse a flags string (code units) strictly: invalid letter, duplicate, or
/// u+v together → None (a SyntaxError). Mirrors the frozen matcher's
/// Flags::parse so the constructor's validation matches the compiler's.
fn parse_flags_strict(flags: &[u16]) -> Option<RegexFlags> {
    let mut f = RegexFlags::default();
    for &u in flags {
        let slot = match u {
            0x64 => &mut f.has_indices,
            0x67 => &mut f.global,
            0x69 => &mut f.ignore_case,
            0x6D => &mut f.multiline,
            0x73 => &mut f.dot_all,
            0x75 => &mut f.unicode,
            0x76 => &mut f.unicode_sets,
            0x79 => &mut f.sticky,
            _ => return None,
        };
        if *slot {
            return None;
        }
        *slot = true;
    }
    if f.unicode && f.unicode_sets {
        return None;
    }
    Some(f)
}

/// [[OriginalFlags]] as canonical code units (d g i m s u v y). Order is
/// unobservable — the raw string is never exposed, only the canonical `flags`
/// getter — so booleans round-trip losslessly.
fn regex_flags_to_units(f: &RegexFlags) -> Units {
    let mut out: Units = Vec::new();
    if f.has_indices {
        out.push(u16::from(b'd'));
    }
    if f.global {
        out.push(u16::from(b'g'));
    }
    if f.ignore_case {
        out.push(u16::from(b'i'));
    }
    if f.multiline {
        out.push(u16::from(b'm'));
    }
    if f.dot_all {
        out.push(u16::from(b's'));
    }
    if f.unicode {
        out.push(u16::from(b'u'));
    }
    if f.unicode_sets {
        out.push(u16::from(b'v'));
    }
    if f.sticky {
        out.push(u16::from(b'y'));
    }
    out
}

/// EscapeRegExpPattern (22.2.6.13.1): produce a string S such that `/S/F`
/// re-parses to the same pattern. Empty → "(?:)"; `/` escaped to `\/` only
/// outside a character class; LineTerminators always escaped; existing escape
/// sequences (`\x`) copied verbatim. Calibrated exact against Node and Bun.
fn escape_regexp_pattern(src: &[u16], v_mode: bool) -> Units {
    if src.is_empty() {
        return units_from_str("(?:)");
    }
    let mut out: Units = Vec::with_capacity(src.len());
    let mut depth: u32 = 0;
    let mut i = 0;
    while i < src.len() {
        let c = src[i];
        if c == 0x5C {
            // Backslash: copy it and the escaped code unit verbatim.
            out.push(c);
            if i + 1 < src.len() {
                out.push(src[i + 1]);
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        match c {
            0x5B => {
                // `[`
                if v_mode {
                    depth += 1;
                } else if depth == 0 {
                    depth = 1;
                }
                out.push(c);
            }
            0x5D => {
                // `]`
                out.push(c);
                if v_mode {
                    depth = depth.saturating_sub(1);
                } else {
                    depth = 0;
                }
            }
            0x2F if depth == 0 => {
                out.push(0x5C);
                out.push(0x2F);
            }
            0x0A => {
                out.push(0x5C);
                out.push(u16::from(b'n'));
            }
            0x0D => {
                out.push(0x5C);
                out.push(u16::from(b'r'));
            }
            0x2028 => out.extend_from_slice(&units_from_str("\\u2028")),
            0x2029 => out.extend_from_slice(&units_from_str("\\u2029")),
            _ => out.push(c),
        }
        i += 1;
    }
    out
}
