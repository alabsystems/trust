// Date (21.4): the calendar arithmetic (21.4.1), the %Date% constructor and
// statics, and the exactly-determined getters/setters/toISOString/toJSON/
// @@toPrimitive. The driver firewall pins the clock (TZ=0, FIXED_EPOCH + a
// tick per observation), so local time equals UTC and every field is exact.
// Human-readable string forms (toString/toDateString/toLocaleString/...) carry
// engine-specific timezone names and are refused (unmodeled on Date.prototype).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::expr::Hint;
use crate::interp::{Abrupt, ERes, Interp};
use crate::value::{Builtin, DateOp, NativeErrorKind, ObjKind, Object, Value};

const MS_PER_DAY: f64 = 86_400_000.0;
const MS_PER_HOUR: f64 = 3_600_000.0;
const MS_PER_MINUTE: f64 = 60_000.0;
const MS_PER_SECOND: f64 = 1000.0;
const MAX_TIME: f64 = 8.64e15;

// -- calendar arithmetic (21.4.1) -------------------------------------------

fn day(t: f64) -> f64 {
    (t / MS_PER_DAY).floor()
}

fn time_within_day(t: f64) -> f64 {
    t.rem_euclid(MS_PER_DAY)
}

fn days_in_year(y: f64) -> f64 {
    if y.rem_euclid(4.0) != 0.0 {
        365.0
    } else if y.rem_euclid(100.0) != 0.0 {
        366.0
    } else if y.rem_euclid(400.0) != 0.0 {
        365.0
    } else {
        366.0
    }
}

fn day_from_year(y: f64) -> f64 {
    365.0 * (y - 1970.0) + ((y - 1969.0) / 4.0).floor()
        - ((y - 1901.0) / 100.0).floor()
        + ((y - 1601.0) / 400.0).floor()
}

fn time_from_year(y: f64) -> f64 {
    MS_PER_DAY * day_from_year(y)
}

fn in_leap_year(t: f64) -> bool {
    days_in_year(year_from_time(t)) == 366.0
}

fn year_from_time(t: f64) -> f64 {
    // Estimate then correct (day count ≈ 365.2425/yr).
    let d = day(t);
    let mut y = (1970.0 + d / 365.2425).floor();
    while time_from_year(y) > t {
        y -= 1.0;
    }
    while time_from_year(y + 1.0) <= t {
        y += 1.0;
    }
    y
}

fn day_within_year(t: f64) -> f64 {
    day(t) - day_from_year(year_from_time(t))
}

/// Cumulative days before month `m` (0-based) in a year, with `leap`.
fn days_before_month(m: i64, leap: bool) -> f64 {
    let cum: [i64; 12] = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];
    #[allow(clippy::cast_precision_loss)]
    let base = cum[m.rem_euclid(12) as usize] as f64;
    if leap && m.rem_euclid(12) >= 2 {
        base + 1.0
    } else {
        base
    }
}

fn month_from_time(t: f64) -> f64 {
    let dwy = day_within_year(t);
    let leap = f64::from(in_leap_year(t));
    let bounds: [f64; 13] = [
        0.0,
        31.0,
        59.0 + leap,
        90.0 + leap,
        120.0 + leap,
        151.0 + leap,
        181.0 + leap,
        212.0 + leap,
        243.0 + leap,
        273.0 + leap,
        304.0 + leap,
        334.0 + leap,
        365.0 + leap,
    ];
    for m in 0..12 {
        if dwy >= bounds[m] && dwy < bounds[m + 1] {
            #[allow(clippy::cast_precision_loss)]
            return m as f64;
        }
    }
    0.0
}

fn date_from_time(t: f64) -> f64 {
    let dwy = day_within_year(t);
    let m = month_from_time(t) as i64;
    let leap = in_leap_year(t);
    dwy - days_before_month(m, leap) + 1.0
}

fn week_day(t: f64) -> f64 {
    (day(t) + 4.0).rem_euclid(7.0)
}

fn hours_from_time(t: f64) -> f64 {
    (t / MS_PER_HOUR).floor().rem_euclid(24.0)
}
fn min_from_time(t: f64) -> f64 {
    (t / MS_PER_MINUTE).floor().rem_euclid(60.0)
}
fn sec_from_time(t: f64) -> f64 {
    (t / MS_PER_SECOND).floor().rem_euclid(60.0)
}
fn ms_from_time(t: f64) -> f64 {
    t.rem_euclid(MS_PER_SECOND)
}

fn make_time(h: f64, m: f64, s: f64, ms: f64) -> f64 {
    if !(h.is_finite() && m.is_finite() && s.is_finite() && ms.is_finite()) {
        return f64::NAN;
    }
    h.trunc() * MS_PER_HOUR + m.trunc() * MS_PER_MINUTE + s.trunc() * MS_PER_SECOND + ms.trunc()
}

fn make_day(year: f64, month: f64, date: f64) -> f64 {
    if !(year.is_finite() && month.is_finite() && date.is_finite()) {
        return f64::NAN;
    }
    let y = year.trunc();
    let m = month.trunc();
    let dt = date.trunc();
    let ym = y + (m / 12.0).floor();
    let mm = m.rem_euclid(12.0);
    let leap = days_in_year(ym) == 366.0;
    #[allow(clippy::cast_possible_truncation)]
    let day_of_month_start = day_from_year(ym) + days_before_month(mm as i64, leap);
    day_of_month_start + dt - 1.0
}

fn make_date(day: f64, time: f64) -> f64 {
    if !(day.is_finite() && time.is_finite()) {
        return f64::NAN;
    }
    day * MS_PER_DAY + time
}

/// A finite date field beyond 2^53 makes MakeDate's intermediate products
/// exceed the exact-integer range of f64, and engines diverge on the rounding
/// (V8's Date.UTC ≠ the naive spec formula for such inputs). Refuse rather
/// than emit a value that would only match one engine.
fn fp_unsafe(v: f64) -> bool {
    v.is_finite() && v.abs() > 9_007_199_254_740_992.0
}

fn time_clip(t: f64) -> f64 {
    if !t.is_finite() || t.abs() > MAX_TIME {
        return f64::NAN;
    }
    let t = t.trunc();
    if t == 0.0 {
        0.0 // -0 → +0
    } else {
        t
    }
}

/// Format an ISO year: 4 digits for 0..=9999, else sign + 6 digits.
fn iso_year(y: i64) -> String {
    if (0..=9999).contains(&y) {
        format!("{y:04}")
    } else if y < 0 {
        format!("-{:06}", -y)
    } else {
        format!("+{y:06}")
    }
}

impl Interp {
    /// thisTimeValue (21.4.4): the [[DateValue]] of a Date object.
    fn this_time_value(&mut self, this: &Value) -> Result<f64, Abrupt> {
        match this {
            Value::Obj(o) => match self.obj(*o).kind {
                ObjKind::DateObj(t) => Ok(t),
                _ => Err(self.throw_native(NativeErrorKind::TypeError)),
            },
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    fn set_date_value(&mut self, this: &Value, t: f64) -> Result<f64, Abrupt> {
        let clipped = time_clip(t);
        let Value::Obj(o) = this else {
            return Err(self.throw_native(NativeErrorKind::TypeError));
        };
        match &mut self.obj_mut(*o).kind {
            ObjKind::DateObj(slot) => {
                *slot = clipped;
                Ok(clipped)
            }
            _ => Err(self.throw_native(NativeErrorKind::TypeError)),
        }
    }

    /// Coerce up to `count` provided setter arguments (running valueOf, which
    /// may mutate the receiver). Returns (coerced values, thisTimeValue).
    /// Refuses if a valueOf mutated the receiver's [[DateValue]] during
    /// coercion (spec vs engine read-order latitude) or a field is beyond 2^53.
    fn coerce_setter_args(
        &mut self,
        this: &Value,
        max: usize,
        args: &[Value],
    ) -> Result<(Vec<f64>, f64), Abrupt> {
        let t_before = self.this_time_value(this)?; // RequireInternalSlot, before ToNumber
        let n = args.len().min(max);
        let mut out = Vec::with_capacity(n);
        for a in args.iter().take(n) {
            out.push(self.to_number(a)?);
        }
        let t_after = self.this_time_value(this)?;
        if t_before.to_bits() != t_after.to_bits() {
            return Err(Abrupt::Fatal(
                "Date receiver mutated during setter argument coercion (read-order latitude)"
                    .to_string(),
            ));
        }
        if out.iter().any(|&v| fp_unsafe(v)) {
            return Err(Abrupt::Fatal(
                "Date setter field beyond 2^53 (fp-rounding latitude)".to_string(),
            ));
        }
        Ok((out, t_before))
    }

    /// The %Date% constructor and its statics/methods.
    pub(crate) fn dispatch_date_builtin(
        &mut self,
        b: Builtin,
        this: Value,
        args: &[Value],
        is_new: bool,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match b {
            Builtin::DateCtor => {
                if !is_new {
                    // `Date(...)` as a function returns the current-time STRING
                    // (engine-specific timezone name): out of the exact slice.
                    return Err(Abrupt::Fatal(
                        "Date() called as a function (engine-specific date string)".to_string(),
                    ));
                }
                let t = match args.len() {
                    0 => self.clock_now(),
                    1 => {
                        // If the single argument is itself a Date, copy its
                        // [[DateValue]]; otherwise ToPrimitive → String parse or
                        // ToNumber.
                        if let Value::Obj(o) = &arg(0) {
                            if let ObjKind::DateObj(tv) = self.obj(*o).kind {
                                tv
                            } else {
                                self.date_value_from_primitive(&arg(0))?
                            }
                        } else {
                            self.date_value_from_primitive(&arg(0))?
                        }
                    }
                    _ => {
                        let y = self.to_number(&arg(0))?;
                        let m = self.to_number(&arg(1))?;
                        let dt = if args.len() > 2 { self.to_number(&arg(2))? } else { 1.0 };
                        let h = if args.len() > 3 { self.to_number(&arg(3))? } else { 0.0 };
                        let mi = if args.len() > 4 { self.to_number(&arg(4))? } else { 0.0 };
                        let s = if args.len() > 5 { self.to_number(&arg(5))? } else { 0.0 };
                        let ms = if args.len() > 6 { self.to_number(&arg(6))? } else { 0.0 };
                        if [y, m, dt, h, mi, s, ms].iter().any(|&v| fp_unsafe(v)) {
                            return Err(Abrupt::Fatal(
                                "Date field beyond 2^53 (fp-rounding latitude)".to_string(),
                            ));
                        }
                        let yr = two_digit_year(y);
                        make_date(make_day(yr, m, dt), make_time(h, mi, s, ms))
                        // UTC(finalDate) == finalDate since the offset is 0.
                    }
                };
                // The driver firewall's Date is a wrapper whose construct body
                // is `return new RealDate(...args)` — it DISCARDS a foreign
                // new.target, so even a subclass super() call yields an
                // instance parented on %Date.prototype% (never the subclass's
                // `.prototype`). Mirror that exactly: `sub instanceof Subclass`
                // is false under the oracle. (pending_new_target is cleared by
                // construct_with_target after dispatch.)
                let _ = self.pending_new_target.take();
                let oid = self.alloc(Object::new(
                    ObjKind::DateObj(time_clip(t)),
                    Some(self.intr.date_proto),
                ));
                Ok(Value::Obj(oid))
            }
            Builtin::DateNow => Ok(Value::Num(self.clock_now())),
            Builtin::DateUtc => {
                let y = self.to_number(&arg(0))?;
                let m = if args.len() > 1 { self.to_number(&arg(1))? } else { 0.0 };
                let dt = if args.len() > 2 { self.to_number(&arg(2))? } else { 1.0 };
                let h = if args.len() > 3 { self.to_number(&arg(3))? } else { 0.0 };
                let mi = if args.len() > 4 { self.to_number(&arg(4))? } else { 0.0 };
                let s = if args.len() > 5 { self.to_number(&arg(5))? } else { 0.0 };
                let ms = if args.len() > 6 { self.to_number(&arg(6))? } else { 0.0 };
                if [y, m, dt, h, mi, s, ms].iter().any(|&v| fp_unsafe(v)) {
                    return Err(Abrupt::Fatal(
                        "Date.UTC field beyond 2^53 (fp-rounding latitude)".to_string(),
                    ));
                }
                let yr = two_digit_year(y);
                Ok(Value::Num(time_clip(make_date(
                    make_day(yr, m, dt),
                    make_time(h, mi, s, ms),
                ))))
            }
            Builtin::DateParse => {
                let s = self.to_string_units(&arg(0))?;
                let str = crate::value::units_to_lossy(&s);
                match parse_iso(&str) {
                    ParseResult::Value(v) => Ok(Value::Num(v)),
                    ParseResult::Refuse => Err(Abrupt::Fatal(
                        "Date.parse of a non-ISO-8601 or out-of-range string (engine latitude)"
                            .to_string(),
                    )),
                }
            }
            Builtin::DateMethod(op) => self.dispatch_date_method(op, &this, args),
            _ => Err(Abrupt::Fatal(format!("date dispatch: {b:?}"))),
        }
    }

    fn date_value_from_primitive(&mut self, v: &Value) -> Result<f64, Abrupt> {
        let p = self.to_primitive(v, Hint::Default)?;
        if let Value::Str(s) = &p {
            let str = crate::value::units_to_lossy(s);
            return match parse_iso(&str) {
                ParseResult::Value(v) => Ok(v),
                ParseResult::Refuse => Err(Abrupt::Fatal(
                    "new Date(<non-ISO string>) (engine-specific heuristics)".to_string(),
                )),
            };
        }
        self.to_number(&p)
    }

    #[allow(clippy::too_many_lines)]
    fn dispatch_date_method(&mut self, op: DateOp, this: &Value, args: &[Value]) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(Value::Undefined);
        match op {
            DateOp::GetTime => Ok(Value::Num(self.this_time_value(this)?)),
            DateOp::GetTimezoneOffset => {
                let t = self.this_time_value(this)?;
                Ok(Value::Num(if t.is_nan() { f64::NAN } else { 0.0 }))
            }
            DateOp::GetFullYear
            | DateOp::GetMonth
            | DateOp::GetDate
            | DateOp::GetDay
            | DateOp::GetHours
            | DateOp::GetMinutes
            | DateOp::GetSeconds
            | DateOp::GetMilliseconds => {
                let t = self.this_time_value(this)?;
                if t.is_nan() {
                    return Ok(Value::Num(f64::NAN));
                }
                let v = match op {
                    DateOp::GetFullYear => year_from_time(t),
                    DateOp::GetMonth => month_from_time(t),
                    DateOp::GetDate => date_from_time(t),
                    DateOp::GetDay => week_day(t),
                    DateOp::GetHours => hours_from_time(t),
                    DateOp::GetMinutes => min_from_time(t),
                    DateOp::GetSeconds => sec_from_time(t),
                    DateOp::GetMilliseconds => ms_from_time(t),
                    _ => unreachable!(),
                };
                Ok(Value::Num(v))
            }
            DateOp::SetTime => {
                // RequireInternalSlot([[DateValue]]) precedes ToNumber(time).
                self.this_time_value(this)?;
                let n = self.to_number(&arg(0))?;
                let v = self.set_date_value(this, n)?;
                Ok(Value::Num(v))
            }
            DateOp::SetMilliseconds => {
                let (a, t) = self.coerce_setter_args(this, 1, args)?;
                let time = make_time(hours_from_time(t), min_from_time(t), sec_from_time(t), a.first().copied().unwrap_or(f64::NAN));
                let nd = make_date(day(t), time);
                let v = self.set_date_value(this, nd)?;
                Ok(Value::Num(v))
            }
            DateOp::SetSeconds => {
                let (a, t) = self.coerce_setter_args(this, 2, args)?;
                let ms = a.get(1).copied().unwrap_or_else(|| ms_from_time(t));
                let time = make_time(hours_from_time(t), min_from_time(t), a.first().copied().unwrap_or(f64::NAN), ms);
                let nd = make_date(day(t), time);
                let v = self.set_date_value(this, nd)?;
                Ok(Value::Num(v))
            }
            DateOp::SetMinutes => {
                let (a, t) = self.coerce_setter_args(this, 3, args)?;
                let s = a.get(1).copied().unwrap_or_else(|| sec_from_time(t));
                let ms = a.get(2).copied().unwrap_or_else(|| ms_from_time(t));
                let time = make_time(hours_from_time(t), a.first().copied().unwrap_or(f64::NAN), s, ms);
                let nd = make_date(day(t), time);
                let v = self.set_date_value(this, nd)?;
                Ok(Value::Num(v))
            }
            DateOp::SetHours => {
                let (a, t) = self.coerce_setter_args(this, 4, args)?;
                let m = a.get(1).copied().unwrap_or_else(|| min_from_time(t));
                let s = a.get(2).copied().unwrap_or_else(|| sec_from_time(t));
                let ms = a.get(3).copied().unwrap_or_else(|| ms_from_time(t));
                let time = make_time(a.first().copied().unwrap_or(f64::NAN), m, s, ms);
                let nd = make_date(day(t), time);
                let v = self.set_date_value(this, nd)?;
                Ok(Value::Num(v))
            }
            DateOp::SetDate => {
                let (a, t) = self.coerce_setter_args(this, 1, args)?;
                let nd = make_date(
                    make_day(year_from_time(t), month_from_time(t), a.first().copied().unwrap_or(f64::NAN)),
                    time_within_day(t),
                );
                let v = self.set_date_value(this, nd)?;
                Ok(Value::Num(v))
            }
            DateOp::SetMonth => {
                let (a, t) = self.coerce_setter_args(this, 2, args)?;
                let dt = a.get(1).copied().unwrap_or_else(|| date_from_time(t));
                let nd = make_date(make_day(year_from_time(t), a.first().copied().unwrap_or(f64::NAN), dt), time_within_day(t));
                let v = self.set_date_value(this, nd)?;
                Ok(Value::Num(v))
            }
            DateOp::SetFullYear => {
                // setFullYear resets a NaN time to +0 before recomputing.
                let (a, t0) = self.coerce_setter_args(this, 3, args)?;
                let t = if t0.is_nan() { 0.0 } else { t0 };
                let m = a.get(1).copied().unwrap_or_else(|| month_from_time(t));
                let dt = a.get(2).copied().unwrap_or_else(|| date_from_time(t));
                let nd = make_date(make_day(a.first().copied().unwrap_or(f64::NAN), m, dt), time_within_day(t));
                let v = self.set_date_value(this, nd)?;
                Ok(Value::Num(v))
            }
            DateOp::ToIsoString => {
                let t = self.this_time_value(this)?;
                if !t.is_finite() {
                    return Err(self.throw_native(NativeErrorKind::RangeError));
                }
                Ok(Value::str_from(&iso_string(t)))
            }
            DateOp::ToJson => {
                // 21.4.4.37 (generic, not Date-specific): O = ToObject(this);
                // tv = ToPrimitive(O, number); if tv is a non-finite Number →
                // null; else Invoke(O, "toISOString").
                let oid = match this {
                    Value::Obj(o) => *o,
                    Value::Undefined | Value::Null => {
                        return Err(self.throw_native(NativeErrorKind::TypeError))
                    }
                    Value::Sym(s) => {
                        let s = *s;
                        self.alloc(Object::new(ObjKind::SymbolObj(s), Some(self.intr.symbol_proto)))
                    }
                    _ => self.to_object_wrapper(this)?,
                };
                let o = Value::Obj(oid);
                let tv = self.to_primitive(&o, Hint::Number)?;
                if let Value::Num(n) = &tv {
                    if !n.is_finite() {
                        return Ok(Value::Null);
                    }
                }
                let m = self.get_prop_value(&o, &crate::value::units_from_str("toISOString"))?;
                self.call_value(&m, o, Vec::new())
            }
            DateOp::ToPrimitive => {
                // Date.prototype[@@toPrimitive](hint) (21.4.4.45): O must be an
                // Object; then OrdinaryToPrimitive(O, hint) — so a redefined
                // valueOf/toString is honored.
                if !this.is_object() {
                    return Err(self.throw_native(NativeErrorKind::TypeError));
                }
                match &arg(0) {
                    Value::Str(s) if crate::value::units_eq_ascii(s, "number") => {
                        self.ordinary_to_primitive(this, Hint::Number)
                    }
                    Value::Str(s)
                        if crate::value::units_eq_ascii(s, "string")
                            || crate::value::units_eq_ascii(s, "default") =>
                    {
                        // String/default → OrdinaryToPrimitive(O, string) tries
                        // toString first (unmodeled tz) → refuse.
                        self.ordinary_to_primitive(this, Hint::String)
                    }
                    _ => Err(self.throw_native(NativeErrorKind::TypeError)),
                }
            }
        }
    }
}

/// The two-digit-year rule (0..=99 → 1900 + y).
fn two_digit_year(y: f64) -> f64 {
    if y.is_nan() {
        return f64::NAN;
    }
    let iy = y.trunc();
    if (0.0..=99.0).contains(&iy) {
        1900.0 + iy
    } else {
        y
    }
}

/// ISO 8601 extended-format string for a finite time value.
fn iso_string(t: f64) -> String {
    #[allow(clippy::cast_possible_truncation)]
    let y = year_from_time(t) as i64;
    #[allow(clippy::cast_possible_truncation)]
    let mo = month_from_time(t) as i64 + 1;
    #[allow(clippy::cast_possible_truncation)]
    let d = date_from_time(t) as i64;
    #[allow(clippy::cast_possible_truncation)]
    let h = hours_from_time(t) as i64;
    #[allow(clippy::cast_possible_truncation)]
    let mi = min_from_time(t) as i64;
    #[allow(clippy::cast_possible_truncation)]
    let s = sec_from_time(t) as i64;
    #[allow(clippy::cast_possible_truncation)]
    let ms = ms_from_time(t) as i64;
    format!(
        "{}-{:02}-{:02}T{:02}:{:02}:{:02}.{:03}Z",
        iso_year(y),
        mo,
        d,
        h,
        mi,
        s,
        ms
    )
}

enum ParseResult {
    Value(f64),
    /// Non-conforming, or conforming-but-out-of-range: refuse (never a guessed
    /// value; the NaN cases are engine-corner risk we decline).
    Refuse,
}

/// Parse the ECMA-262 Date Time String Format (21.4.1.18) ONLY. Returns
/// `Value` for conforming, in-range strings; `Refuse` for anything the spec
/// leaves to engine heuristics. Out-of-range conforming fields also refuse
/// (conservative — never a guessed value).
fn parse_iso(s: &str) -> ParseResult {
    let b = s.as_bytes();
    let mut i = 0usize;
    let n = b.len();
    let digit = |c: u8| c.is_ascii_digit();
    let read_n = |b: &[u8], i: &mut usize, k: usize| -> Option<i64> {
        if *i + k > b.len() {
            return None;
        }
        let mut v: i64 = 0;
        for j in 0..k {
            let c = b[*i + j];
            if !c.is_ascii_digit() {
                return None;
            }
            v = v * 10 + i64::from(c - b'0');
        }
        *i += k;
        Some(v)
    };

    // Year: [+-]YYYYYY or YYYY. A time-only form starts with 'T'.
    let year: i64;
    let mut month: i64 = 1;
    let mut date: i64 = 1;
    let mut has_time = false;
    let mut hour: i64 = 0;
    let mut minute: i64 = 0;
    let mut second: i64 = 0;
    let mut milli: i64 = 0;
    let mut tz_present = false;
    let mut tz_offset: i64 = 0; // minutes

    if i < n && (b[i] == b'+' || b[i] == b'-') {
        let sign = if b[i] == b'-' { -1 } else { 1 };
        i += 1;
        match read_n(b, &mut i, 6) {
            // "-000000" (negative zero extended year) is invalid → NaN in
            // conforming engines; refuse rather than compute year 0.
            Some(0) if sign == -1 => return ParseResult::Refuse,
            Some(v) => year = sign * v,
            None => return ParseResult::Refuse,
        }
    } else if i < n && digit(b[i]) {
        match read_n(b, &mut i, 4) {
            Some(v) => year = v,
            None => return ParseResult::Refuse,
        }
    } else if i < n && b[i] == b'T' {
        // time-only: date defaults handled below; but a bare time with no date
        // is not a standard whole-string form → refuse (engine latitude).
        return ParseResult::Refuse;
    } else {
        return ParseResult::Refuse;
    }

    // Optional -MM
    let mut have_month = false;
    let mut have_date = false;
    if i < n && b[i] == b'-' {
        i += 1;
        match read_n(b, &mut i, 2) {
            Some(v) => {
                month = v;
                have_month = true;
            }
            None => return ParseResult::Refuse,
        }
        if i < n && b[i] == b'-' {
            i += 1;
            match read_n(b, &mut i, 2) {
                Some(v) => {
                    date = v;
                    have_date = true;
                }
                None => return ParseResult::Refuse,
            }
        }
    }
    let _ = (have_month, have_date);

    // Optional time: T HH:mm[:ss[.sss]]
    if i < n && b[i] == b'T' {
        has_time = true;
        i += 1;
        match read_n(b, &mut i, 2) {
            Some(v) => hour = v,
            None => return ParseResult::Refuse,
        }
        if !(i < n && b[i] == b':') {
            return ParseResult::Refuse;
        }
        i += 1;
        match read_n(b, &mut i, 2) {
            Some(v) => minute = v,
            None => return ParseResult::Refuse,
        }
        if i < n && b[i] == b':' {
            i += 1;
            match read_n(b, &mut i, 2) {
                Some(v) => second = v,
                None => return ParseResult::Refuse,
            }
            if i < n && b[i] == b'.' {
                i += 1;
                match read_n(b, &mut i, 3) {
                    Some(v) => milli = v,
                    None => return ParseResult::Refuse,
                }
            }
        }
        // Optional timezone.
        if i < n && b[i] == b'Z' {
            tz_present = true;
            i += 1;
        } else if i < n && (b[i] == b'+' || b[i] == b'-') {
            let sign = if b[i] == b'-' { -1 } else { 1 };
            i += 1;
            let th = match read_n(b, &mut i, 2) {
                Some(v) => v,
                None => return ParseResult::Refuse,
            };
            if !(i < n && b[i] == b':') {
                return ParseResult::Refuse;
            }
            i += 1;
            let tm = match read_n(b, &mut i, 2) {
                Some(v) => v,
                None => return ParseResult::Refuse,
            };
            if th > 23 || tm > 59 {
                return ParseResult::Refuse;
            }
            tz_present = true;
            tz_offset = sign * (th * 60 + tm);
        }
    }

    if i != n {
        return ParseResult::Refuse;
    }

    // Range validation (conservative — out of range refuses to NaN, but we
    // only *claim* the value for in-range strings; NaN cases are refused
    // upstream by returning ParseResult::Nan → Node returns NaN too, but to
    // avoid any engine-corner risk we treat those as sound NaN only for the
    // clearly-spec-mandated tz overflow above; field overflow refuses).
    if !(1..=12).contains(&month)
        || !(1..=31).contains(&date)
        || hour > 23
        || minute > 59
        || second > 59
    {
        return ParseResult::Refuse;
    }

    #[allow(clippy::cast_precision_loss)]
    let day_num = make_day(year as f64, (month - 1) as f64, date as f64);
    #[allow(clippy::cast_precision_loss)]
    let time = make_time(hour as f64, minute as f64, second as f64, milli as f64);
    let mut t = make_date(day_num, time);
    // A date-time WITHOUT an explicit timezone is local time (== UTC here);
    // date-only forms are UTC. With an explicit offset, subtract it.
    if has_time && tz_present {
        #[allow(clippy::cast_precision_loss)]
        {
            t -= (tz_offset as f64) * MS_PER_MINUTE;
        }
    }
    ParseResult::Value(time_clip(t))
}
