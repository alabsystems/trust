// String statics (fromCharCode/fromCodePoint/raw) and the S1b prototype
// surface: at/codePointAt/lastIndexOf/includes/startsWith/endsWith/slice/
// substring/split/case (ASCII-exact)/trim*/repeat/pad*/concat/replace(all)/
// isWellFormed/toWellFormed — written from ECMA-262 over code units.
// Locale-dependent surface (localeCompare, toLocale*) stays danger-listed.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp, MAX_STRING_UNITS};
use std::rc::Rc;
use trust_js_value::{
    to_integer_or_infinity, to_length_u64, to_uint32, units_from_str, ErrKind, JsValue, NativeFn,
    PropKey, SymId, Units, WkSym,
};

/// ECMA-262 WhiteSpace ∪ LineTerminator, over code units.
fn is_ws_unit(c: u16) -> bool {
    matches!(
        c,
        0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20 | 0xA0 | 0x1680 | 0x2000..=0x200A | 0x2028
            | 0x2029 | 0x202F | 0x205F | 0x3000 | 0xFEFF
    )
}

/// StringIndexOf over code units; None when absent.
fn find_from(s: &[u16], search: &[u16], start: usize) -> Option<usize> {
    if search.is_empty() {
        return if start <= s.len() { Some(start) } else { None };
    }
    if search.len() > s.len() {
        return None;
    }
    let last = s.len() - search.len();
    let mut i = start;
    while i <= last {
        if &s[i..i + search.len()] == search {
            return Some(i);
        }
        i += 1;
    }
    None
}

impl Interp {
    /// ToString(this) after RequireObjectCoercible — the shared prologue.
    fn this_str(&mut self, this: &JsValue) -> Result<Units, Abrupt> {
        self.require_object_coercible(this)?;
        self.to_string_units(this)
    }

    /// IsRegExp (7.2.6): Get(argument, @@match) decides — real RegExp
    /// instances resolve the modeled %RegExp.prototype[Symbol.match]%
    /// (truthy), user-set @@match is honored, everything else is false.
    pub(crate) fn is_reg_exp(&mut self, v: &JsValue) -> Result<bool, Abrupt> {
        let JsValue::Obj(oid) = v else {
            return Ok(false);
        };
        let oid = *oid;
        let key = PropKey::Sym(SymId::WellKnown(WkSym::Match));
        let matcher = self.get_prop(v, &key)?;
        if !matches!(matcher, JsValue::Undefined) {
            return Ok(self.to_boolean(&matcher));
        }
        // Step 4: a real RegExp instance ([[RegExpMatcher]]) is IsRegExp even
        // with @@match deleted/undefined.
        Ok(matches!(self.heap.obj(oid).kind, trust_js_value::ObjKind::Regex(_)))
    }

    fn clamp_pos(&self, t: f64, len: usize) -> usize {
        if t <= 0.0 {
            0
        } else if t >= len as f64 {
            len
        } else {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            {
                t as usize
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_string(
        &mut self,
        nf: NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        use NativeFn as N;
        match nf {
            N::StringFromCharCode => {
                let mut out: Units = Vec::with_capacity(args.len());
                for a in &args {
                    let n = self.to_number(a)?;
                    // ToUint16.
                    let u = (to_uint32(n) & 0xFFFF) as u16;
                    out.push(u);
                }
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::StringFromCodePoint => {
                let mut out: Units = Vec::new();
                for a in &args {
                    let n = self.to_number(a)?;
                    if n.trunc() != n || !(0.0..=1_114_111.0).contains(&n) {
                        return Err(self.throw_native(ErrKind::Range));
                    }
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    let cp = n as u32;
                    if cp <= 0xFFFF {
                        out.push(cp as u16);
                    } else {
                        let v = cp - 0x10000;
                        out.push(0xD800 + (v >> 10) as u16);
                        out.push(0xDC00 + (v & 0x3FF) as u16);
                    }
                }
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::StringRaw => {
                let template = arg(0);
                let cooked = self.to_object(&template)?;
                let raw_v =
                    self.get_from_object(cooked, &PropKey::from_str("raw"), JsValue::Obj(cooked))?;
                let literals = self.to_object(&raw_v)?;
                let count = self.length_of_array_like(literals)?;
                let mut out: Units = Vec::new();
                let mut i: u64 = 0;
                loop {
                    if i >= count {
                        break;
                    }
                    self.charge_loop()?;
                    let seg_v = self.get_from_object(
                        literals,
                        &PropKey::Str(units_from_str(&i.to_string())),
                        raw_v.clone(),
                    )?;
                    let seg = self.to_string_units(&seg_v)?;
                    out.extend_from_slice(&seg);
                    if out.len() > MAX_STRING_UNITS {
                        return Err(Abrupt::Fatal("String.raw result cap exceeded".to_string()));
                    }
                    i += 1;
                    if i == count {
                        break;
                    }
                    if let Some(sub) = args.get(usize::try_from(i).unwrap_or(usize::MAX)) {
                        let s = self.to_string_units(&sub.clone())?;
                        out.extend_from_slice(&s);
                    }
                }
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::StringAt => {
                let s = self.this_str(&this)?;
                let rel = to_integer_or_infinity(self.to_number(&arg(0))?);
                let len = s.len() as f64;
                let k = if rel >= 0.0 { rel } else { len + rel };
                if k < 0.0 || k >= len {
                    return Ok(JsValue::Undefined);
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let i = k as usize;
                Ok(JsValue::Str(Rc::new(vec![s[i]])))
            }
            N::StringCodePointAt => {
                let s = self.this_str(&this)?;
                let pos = to_integer_or_infinity(self.to_number(&arg(0))?);
                if pos < 0.0 || pos >= s.len() as f64 {
                    return Ok(JsValue::Undefined);
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let i = pos as usize;
                let first = s[i];
                let cp: u32 = if (0xD800..=0xDBFF).contains(&first)
                    && i + 1 < s.len()
                    && (0xDC00..=0xDFFF).contains(&s[i + 1])
                {
                    0x10000 + ((u32::from(first) - 0xD800) << 10) + (u32::from(s[i + 1]) - 0xDC00)
                } else {
                    u32::from(first)
                };
                Ok(JsValue::Num(f64::from(cp)))
            }
            N::StringLastIndexOf => {
                let s = self.this_str(&this)?;
                let search = self.to_string_units(&arg(0))?;
                let num_pos = self.to_number(&arg(1))?;
                let pos = if num_pos.is_nan() {
                    f64::INFINITY
                } else {
                    to_integer_or_infinity(num_pos)
                };
                let start = self.clamp_pos(pos, s.len());
                if search.len() > s.len() {
                    return Ok(JsValue::Num(-1.0));
                }
                let upper = start.min(s.len() - search.len());
                let mut k = upper as i64;
                while k >= 0 {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                    let i = k as usize;
                    if &s[i..i + search.len()] == search.as_slice() {
                        #[allow(clippy::cast_precision_loss)]
                        return Ok(JsValue::Num(k as f64));
                    }
                    k -= 1;
                }
                Ok(JsValue::Num(-1.0))
            }
            N::StringIncludes | N::StringStartsWith | N::StringEndsWith => {
                let s = self.this_str(&this)?;
                let sv = arg(0);
                if self.is_reg_exp(&sv)? {
                    return Err(self.throw_type_error());
                }
                let search = self.to_string_units(&sv)?;
                match nf {
                    N::StringIncludes => {
                        let pos = to_integer_or_infinity(self.to_number(&arg(1))?);
                        let start = self.clamp_pos(pos, s.len());
                        Ok(JsValue::Bool(find_from(&s, &search, start).is_some()))
                    }
                    N::StringStartsWith => {
                        let pos = to_integer_or_infinity(self.to_number(&arg(1))?);
                        let start = self.clamp_pos(pos, s.len());
                        if start + search.len() > s.len() {
                            return Ok(JsValue::Bool(false));
                        }
                        Ok(JsValue::Bool(&s[start..start + search.len()] == search.as_slice()))
                    }
                    _ => {
                        let end = if matches!(arg(1), JsValue::Undefined) {
                            s.len()
                        } else {
                            let p = to_integer_or_infinity(self.to_number(&arg(1))?);
                            self.clamp_pos(p, s.len())
                        };
                        if search.len() > end {
                            return Ok(JsValue::Bool(false));
                        }
                        let start = end - search.len();
                        Ok(JsValue::Bool(&s[start..end] == search.as_slice()))
                    }
                }
            }
            N::StringSlice => {
                let s = self.this_str(&this)?;
                let len = s.len();
                let t_start = to_integer_or_infinity(self.to_number(&arg(0))?);
                let from = if t_start < 0.0 {
                    self.clamp_pos(len as f64 + t_start, len)
                } else {
                    self.clamp_pos(t_start, len)
                };
                let to = if matches!(arg(1), JsValue::Undefined) {
                    len
                } else {
                    let t = to_integer_or_infinity(self.to_number(&arg(1))?);
                    if t < 0.0 {
                        self.clamp_pos(len as f64 + t, len)
                    } else {
                        self.clamp_pos(t, len)
                    }
                };
                if from >= to {
                    return Ok(JsValue::str_from(""));
                }
                Ok(JsValue::Str(Rc::new(s[from..to].to_vec())))
            }
            N::StringSubstring => {
                let s = self.this_str(&this)?;
                let len = s.len();
                let i1 = {
                    let t = to_integer_or_infinity(self.to_number(&arg(0))?);
                    self.clamp_pos(t, len)
                };
                let i2 = if matches!(arg(1), JsValue::Undefined) {
                    len
                } else {
                    let t = to_integer_or_infinity(self.to_number(&arg(1))?);
                    self.clamp_pos(t, len)
                };
                let (from, to) = if i1 <= i2 { (i1, i2) } else { (i2, i1) };
                Ok(JsValue::Str(Rc::new(s[from..to].to_vec())))
            }
            N::StringSplit => self.string_split(&this, &arg(0), &arg(1)),
            N::StringMatch => self.string_match(&this, &arg(0)),
            N::StringMatchAll => self.string_match_all(&this, &arg(0)),
            N::StringSearch => self.string_search(&this, &arg(0)),
            N::StringCase { upper } => {
                let s = self.this_str(&this)?;
                if s.iter().any(|&c| c >= 0x80) {
                    return Err(Abrupt::Fatal(
                        "non-ASCII case conversion (Unicode case data out of slice)".to_string(),
                    ));
                }
                let out: Units = s
                    .iter()
                    .map(|&c| {
                        let b = c as u8;
                        let m = if upper {
                            b.to_ascii_uppercase()
                        } else {
                            b.to_ascii_lowercase()
                        };
                        u16::from(m)
                    })
                    .collect();
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::StringTrim { start, end } => {
                let s = self.this_str(&this)?;
                let mut a = 0usize;
                let mut b = s.len();
                if start {
                    while a < b && is_ws_unit(s[a]) {
                        a += 1;
                    }
                }
                if end {
                    while b > a && is_ws_unit(s[b - 1]) {
                        b -= 1;
                    }
                }
                Ok(JsValue::Str(Rc::new(s[a..b].to_vec())))
            }
            N::StringRepeat => {
                let s = self.this_str(&this)?;
                let n = to_integer_or_infinity(self.to_number(&arg(0))?);
                if n < 0.0 || n == f64::INFINITY {
                    return Err(self.throw_native(ErrKind::Range));
                }
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let count = n as usize;
                // An empty string (or a zero count) repeats to the empty string:
                // short-circuit so `''.repeat(2**31)` is instant, not a
                // multi-billion no-op copy loop (totality — the copy loop below
                // is not charge_loop-bounded).
                if count == 0 || s.is_empty() {
                    return Ok(JsValue::str_from(""));
                }
                if s.len().saturating_mul(count) > MAX_STRING_UNITS {
                    return Err(Abrupt::Fatal("repeat result cap exceeded".to_string()));
                }
                let mut out: Units = Vec::with_capacity(s.len() * count);
                for _ in 0..count {
                    out.extend_from_slice(&s);
                }
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::StringPad { start } => {
                let s = self.this_str(&this)?;
                let int_max = to_length_u64(self.to_number(&arg(0))?);
                if int_max <= s.len() as u64 {
                    return Ok(JsValue::Str(Rc::new(s)));
                }
                let filler: Units = if matches!(arg(1), JsValue::Undefined) {
                    units_from_str(" ")
                } else {
                    self.to_string_units(&arg(1))?
                };
                if filler.is_empty() {
                    return Ok(JsValue::Str(Rc::new(s)));
                }
                let int_max = usize::try_from(int_max)
                    .ok()
                    .filter(|&m| m <= MAX_STRING_UNITS)
                    .ok_or_else(|| Abrupt::Fatal("pad result cap exceeded".to_string()))?;
                let fill_len = int_max - s.len();
                let mut pad: Units = Vec::with_capacity(fill_len);
                while pad.len() < fill_len {
                    let take = (fill_len - pad.len()).min(filler.len());
                    pad.extend_from_slice(&filler[..take]);
                }
                let mut out: Units = Vec::with_capacity(int_max);
                if start {
                    out.extend_from_slice(&pad);
                    out.extend_from_slice(&s);
                } else {
                    out.extend_from_slice(&s);
                    out.extend_from_slice(&pad);
                }
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::StringConcat => {
                let mut out = self.this_str(&this)?;
                for a in &args {
                    let s = self.to_string_units(a)?;
                    if out.len() + s.len() > MAX_STRING_UNITS {
                        return Err(Abrupt::Fatal("concat result cap exceeded".to_string()));
                    }
                    out.extend_from_slice(&s);
                }
                Ok(JsValue::Str(Rc::new(out)))
            }
            N::StringReplace { all } => self.string_replace(&this, &arg(0), &arg(1), all),
            N::StringIsWellFormed => {
                let s = self.this_str(&this)?;
                Ok(JsValue::Bool(well_formed_scan(&s).is_none()))
            }
            N::StringToWellFormed => {
                let mut s = self.this_str(&this)?;
                let mut i = 0;
                while i < s.len() {
                    let c = s[i];
                    if (0xD800..=0xDBFF).contains(&c) {
                        if i + 1 < s.len() && (0xDC00..=0xDFFF).contains(&s[i + 1]) {
                            i += 2;
                            continue;
                        }
                        s[i] = 0xFFFD;
                    } else if (0xDC00..=0xDFFF).contains(&c) {
                        s[i] = 0xFFFD;
                    }
                    i += 1;
                }
                Ok(JsValue::Str(Rc::new(s)))
            }
            _ => Err(Abrupt::Fatal("unrouted String native (interpreter bug)".to_string())),
        }
    }

    /// String.prototype.match (22.1.3.14): dispatch through the argument's
    /// @@match, else RegExpCreate(regexp, undefined) then Invoke(@@match).
    fn string_match(&mut self, this: &JsValue, regexp: &JsValue) -> ERes {
        self.require_object_coercible(this)?;
        if !regexp.is_nullish() {
            let key = PropKey::Sym(SymId::WellKnown(WkSym::Match));
            if let Some(m) = self.get_method(regexp, &key)? {
                return self.call_value(&m, regexp.clone(), vec![this.clone()]);
            }
        }
        let s = self.to_string_units(this)?;
        let rx = self.regexp_create(regexp, &JsValue::Undefined)?;
        let key = PropKey::Sym(SymId::WellKnown(WkSym::Match));
        let m = self.get_prop(&JsValue::Obj(rx), &key)?;
        self.call_value(&m, JsValue::Obj(rx), vec![JsValue::Str(Rc::new(s))])
    }

    /// String.prototype.matchAll (22.1.3.15): if regexp is a global-flagged
    /// (or non-)RegExp, dispatch through its @@matchAll; else RegExpCreate(
    /// regexp, "g") then Invoke(@@matchAll). A non-global RegExp argument is the
    /// exact TypeError a conforming engine raises.
    fn string_match_all(&mut self, this: &JsValue, regexp: &JsValue) -> ERes {
        self.require_object_coercible(this)?;
        if !regexp.is_nullish() {
            if self.is_reg_exp(regexp)? {
                let flags = self.get_prop(regexp, &PropKey::from_str("flags"))?;
                self.require_object_coercible(&flags)?;
                let fs = self.to_string_units(&flags)?;
                if !fs.contains(&u16::from(b'g')) {
                    return Err(self.throw_type_error());
                }
            }
            let key = PropKey::Sym(SymId::WellKnown(WkSym::MatchAll));
            if let Some(matcher) = self.get_method(regexp, &key)? {
                return self.call_value(&matcher, regexp.clone(), vec![this.clone()]);
            }
        }
        let s = self.to_string_units(this)?;
        let rx = self.regexp_create(regexp, &JsValue::str_from("g"))?;
        let key = PropKey::Sym(SymId::WellKnown(WkSym::MatchAll));
        let m = self.get_prop(&JsValue::Obj(rx), &key)?;
        self.call_value(&m, JsValue::Obj(rx), vec![JsValue::Str(Rc::new(s))])
    }

    /// String.prototype.search (22.1.3.15): dispatch through the argument's
    /// @@search, else RegExpCreate(regexp, undefined) then Invoke(@@search).
    fn string_search(&mut self, this: &JsValue, regexp: &JsValue) -> ERes {
        self.require_object_coercible(this)?;
        if !regexp.is_nullish() {
            let key = PropKey::Sym(SymId::WellKnown(WkSym::Search));
            if let Some(m) = self.get_method(regexp, &key)? {
                return self.call_value(&m, regexp.clone(), vec![this.clone()]);
            }
        }
        let s = self.to_string_units(this)?;
        let rx = self.regexp_create(regexp, &JsValue::Undefined)?;
        let key = PropKey::Sym(SymId::WellKnown(WkSym::Search));
        let m = self.get_prop(&JsValue::Obj(rx), &key)?;
        self.call_value(&m, JsValue::Obj(rx), vec![JsValue::Str(Rc::new(s))])
    }

    /// String.prototype.split (22.1.3.23) for string separators; a
    /// user-supplied @@split method is invoked exactly.
    fn string_split(&mut self, this: &JsValue, separator: &JsValue, limit: &JsValue) -> ERes {
        self.require_object_coercible(this)?;
        if !separator.is_nullish() {
            let key = PropKey::Sym(SymId::WellKnown(WkSym::Split));
            if let Some(splitter) = self.get_method(separator, &key)? {
                return self.call_value(&splitter, separator.clone(), vec![this.clone(), limit.clone()]);
            }
        }
        let s = self.to_string_units(this)?;
        let lim: u64 = if matches!(limit, JsValue::Undefined) {
            4_294_967_295
        } else {
            u64::from(to_uint32(self.to_number(limit)?))
        };
        // Engine order (test262-pinned): ToString(separator) runs BEFORE the
        // lim == 0 early return.
        let r_units: Option<Units> = if matches!(separator, JsValue::Undefined) {
            None
        } else {
            Some(self.to_string_units(separator)?)
        };
        let a = self.new_array(0)?;
        if lim == 0 {
            return Ok(JsValue::Obj(a));
        }
        let Some(r) = r_units else {
            self.create_data_property_or_throw(a, "0", JsValue::Str(Rc::new(s)))?;
            self.set_array_length_raw(a, 1.0);
            return Ok(JsValue::Obj(a));
        };
        if r.is_empty() {
            // Split into code units, capped by lim.
            let n = (s.len() as u64).min(lim);
            for i in 0..usize::try_from(n).expect("bounded by string length") {
                self.charge_loop()?;
                self.create_data_property_or_throw(
                    a,
                    &i.to_string(),
                    JsValue::Str(Rc::new(vec![s[i]])),
                )?;
            }
            #[allow(clippy::cast_precision_loss)]
            self.set_array_length_raw(a, n as f64);
            return Ok(JsValue::Obj(a));
        }
        if s.is_empty() {
            self.create_data_property_or_throw(a, "0", JsValue::Str(Rc::new(s)))?;
            self.set_array_length_raw(a, 1.0);
            return Ok(JsValue::Obj(a));
        }
        let mut out_n: u64 = 0;
        let mut i = 0usize;
        loop {
            self.charge_loop()?;
            match find_from(&s, &r, i) {
                Some(j) => {
                    self.create_data_property_or_throw(
                        a,
                        &out_n.to_string(),
                        JsValue::Str(Rc::new(s[i..j].to_vec())),
                    )?;
                    out_n += 1;
                    if out_n == lim {
                        #[allow(clippy::cast_precision_loss)]
                        self.set_array_length_raw(a, out_n as f64);
                        return Ok(JsValue::Obj(a));
                    }
                    i = j + r.len();
                }
                None => {
                    self.create_data_property_or_throw(
                        a,
                        &out_n.to_string(),
                        JsValue::Str(Rc::new(s[i..].to_vec())),
                    )?;
                    out_n += 1;
                    break;
                }
            }
        }
        #[allow(clippy::cast_precision_loss)]
        self.set_array_length_raw(a, out_n as f64);
        Ok(JsValue::Obj(a))
    }

    /// String.prototype.replace / replaceAll (22.1.3.19/20) for string
    /// patterns; user @@replace methods are invoked exactly.
    fn string_replace(
        &mut self,
        this: &JsValue,
        search_value: &JsValue,
        replace_value: &JsValue,
        all: bool,
    ) -> ERes {
        self.require_object_coercible(this)?;
        if !search_value.is_nullish() {
            if all && self.is_reg_exp(search_value)? {
                let flags = self.get_prop(search_value, &PropKey::from_str("flags"))?;
                self.require_object_coercible(&flags)?;
                let fs = self.to_string_units(&flags)?;
                if !fs.contains(&u16::from(b'g')) {
                    return Err(self.throw_type_error());
                }
            }
            let key = PropKey::Sym(SymId::WellKnown(WkSym::Replace));
            if let Some(replacer) = self.get_method(search_value, &key)? {
                return self.call_value(
                    &replacer,
                    search_value.clone(),
                    vec![this.clone(), replace_value.clone()],
                );
            }
        }
        let s = self.to_string_units(this)?;
        let search = self.to_string_units(search_value)?;
        let functional = matches!(replace_value, JsValue::Obj(o) if self.heap.obj(*o).is_callable());
        let template: Option<Units> = if functional {
            None
        } else {
            Some(self.to_string_units(replace_value)?)
        };
        // Match positions.
        let mut positions: Vec<usize> = Vec::new();
        if all {
            let advance = search.len().max(1);
            let mut i = 0usize;
            while let Some(j) = find_from(&s, &search, i) {
                self.charge_loop()?;
                positions.push(j);
                i = j + advance;
                if i > s.len() {
                    break;
                }
            }
        } else if let Some(j) = find_from(&s, &search, 0) {
            positions.push(j);
        }
        if positions.is_empty() {
            return Ok(JsValue::Str(Rc::new(s)));
        }
        let mut out: Units = Vec::new();
        let mut end_of_last = 0usize;
        for &p in &positions {
            self.charge_loop()?;
            out.extend_from_slice(&s[end_of_last..p]);
            let replacement: Units = if functional {
                #[allow(clippy::cast_precision_loss)]
                let rv = self.call_value(
                    replace_value,
                    JsValue::Undefined,
                    vec![
                        JsValue::Str(Rc::new(search.clone())),
                        JsValue::Num(p as f64),
                        JsValue::Str(Rc::new(s.clone())),
                    ],
                )?;
                self.to_string_units(&rv)?
            } else {
                get_substitution(&search, &s, p, template.as_ref().expect("non-functional"))
            };
            out.extend_from_slice(&replacement);
            if out.len() > MAX_STRING_UNITS {
                return Err(Abrupt::Fatal("replace result cap exceeded".to_string()));
            }
            end_of_last = p + search.len();
        }
        out.extend_from_slice(&s[end_of_last..]);
        Ok(JsValue::Str(Rc::new(out)))
    }
}

/// The first lone surrogate index, if any.
fn well_formed_scan(s: &[u16]) -> Option<usize> {
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        if (0xD800..=0xDBFF).contains(&c) {
            if i + 1 < s.len() && (0xDC00..=0xDFFF).contains(&s[i + 1]) {
                i += 2;
                continue;
            }
            return Some(i);
        }
        if (0xDC00..=0xDFFF).contains(&c) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// GetSubstitution (22.1.3.19.1) with no captures ($$, $&, $`, $'; $n and
/// $<...> stay literal without captures/namedCaptures).
fn get_substitution(matched: &[u16], s: &[u16], position: usize, template: &[u16]) -> Units {
    let dollar = u16::from(b'$');
    let mut out: Units = Vec::with_capacity(template.len());
    let mut i = 0;
    while i < template.len() {
        let c = template[i];
        if c != dollar || i + 1 >= template.len() {
            out.push(c);
            i += 1;
            continue;
        }
        let n = template[i + 1];
        match n {
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
                out.extend_from_slice(&s[position + matched.len()..]);
                i += 2;
            }
            _ => {
                out.push(c);
                i += 1;
            }
        }
    }
    out
}
