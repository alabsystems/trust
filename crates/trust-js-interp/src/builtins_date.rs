// Date (S1c), written from ECMA-262 §21.4 with the DRIVER's nondeterminism
// firewall modeled exactly: the global `Date` binding is the driver's
// deterministic wrapper (fixed epoch 1700000000000 advancing 1ms per
// observation, shared by Date.now / new Date() / Date()); the real
// constructor survives only as `Date.prototype.constructor`, whose
// zero-argument forms and `now` touch the real clock and therefore REFUSE.
// The harness pins TZ=UTC (adversarially verified: local == UTC on both
// engines, tz suffix "GMT+0000 (Coordinated Universal Time)" identical), so
// LocalTime/UTC are the identity. Date.parse and the string constructor
// accept EXACTLY the spec Date Time String Format grammar (engines' lenient
// fallback parsing is implementation-defined and refuses).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use trust_js_value::{
    to_integer_or_infinity, DateField, DateSetKind, ErrKind, JsObject, JsValue, NativeFn, ObjId,
    ObjKind, PropKey, Units,
};

pub(crate) const MS_PER_DAY: f64 = 86_400_000.0;
const MS_PER_HOUR: f64 = 3_600_000.0;
const MS_PER_MINUTE: f64 = 60_000.0;
const MS_PER_SECOND: f64 = 1000.0;
const MAX_TIME: f64 = 8.64e15;
const FIXED_EPOCH: f64 = 1_700_000_000_000.0;

// -- fixed-timezone conversions (TZ=UTC pinned by the driver harness) -------
#[inline]
fn local_time(t: f64) -> f64 {
    t
}
#[inline]
fn utc_from_local(t: f64) -> f64 {
    t
}

// -- spec day/time decomposition (finite integral t) ------------------------

fn floor_div(a: i64, b: i64) -> i64 {
    a.div_euclid(b)
}

/// Day(t) over the extended (unclipped) range used by MakeDay lookups.
fn day_i(t: f64) -> i64 {
    #[allow(clippy::cast_possible_truncation)]
    {
        (t / MS_PER_DAY).floor() as i64
    }
}

fn time_within_day(t: f64) -> f64 {
    t.rem_euclid(MS_PER_DAY)
}

fn is_leap(y: i64) -> bool {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
}

fn days_in_year(y: i64) -> i64 {
    if is_leap(y) {
        366
    } else {
        365
    }
}

/// DayFromYear(y): day number of 1 January of year y.
fn day_from_year(y: i64) -> i64 {
    365 * (y - 1970) + floor_div(y - 1969, 4) - floor_div(y - 1901, 100)
        + floor_div(y - 1601, 400)
}

/// YearFromTime as a year number, from a day number.
fn year_from_day(day: i64) -> i64 {
    // Initial estimate, then adjust (the estimate is within ±1).
    let mut y = 1970 + floor_div(day * 400, 146_097);
    loop {
        let d0 = day_from_year(y);
        if day < d0 {
            y -= 1;
        } else if day >= d0 + days_in_year(y) {
            y += 1;
        } else {
            return y;
        }
    }
}

const MONTH_DAYS: [i64; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

/// (month 0-11, date 1-31) from a day number.
fn month_date_from_day(day: i64) -> (i64, i64) {
    let y = year_from_day(day);
    let mut d = day - day_from_year(y);
    for (m, len) in MONTH_DAYS.iter().enumerate() {
        let len = len + i64::from(m == 1 && is_leap(y));
        if d < len {
            #[allow(clippy::cast_possible_wrap)]
            return (m as i64, d + 1);
        }
        d -= len;
    }
    unreachable!("day within year");
}

fn week_day(day: i64) -> i64 {
    (day + 4).rem_euclid(7)
}

// -- spec composition -------------------------------------------------------

/// MakeTime(h, m, s, ms): Number (𝔽) arithmetic per spec.
fn make_time(h: f64, m: f64, s: f64, milli: f64) -> f64 {
    if !h.is_finite() || !m.is_finite() || !s.is_finite() || !milli.is_finite() {
        return f64::NAN;
    }
    let h = to_integer_or_infinity(h);
    let m = to_integer_or_infinity(m);
    let s = to_integer_or_infinity(s);
    let milli = to_integer_or_infinity(milli);
    ((h * MS_PER_HOUR + m * MS_PER_MINUTE) + s * MS_PER_SECOND) + milli
}

/// MakeDay(y, m, dt): day number (may exceed the clipped range — only
/// TimeClip enforces bounds). NaN when out of the representable search
/// range.
fn make_day(y: f64, m: f64, dt: f64) -> f64 {
    if !y.is_finite() || !m.is_finite() || !dt.is_finite() {
        return f64::NAN;
    }
    let y = to_integer_or_infinity(y);
    let m = to_integer_or_infinity(m);
    let dt = to_integer_or_infinity(dt);
    let ym = y + (m / 12.0).floor();
    if !ym.is_finite() || ym.abs() > 1.0e8 {
        // No finite time value with this year: rolls to NaN exactly like the
        // spec's failed lookup (anything this large TimeClips to NaN anyway).
        return f64::NAN;
    }
    let mn = m.rem_euclid(12.0);
    #[allow(clippy::cast_possible_truncation)]
    let (ymi, mni) = (ym as i64, mn as i64);
    let mut day = day_from_year(ymi);
    for mm in 0..mni {
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let len = MONTH_DAYS[mm as usize] + i64::from(mm == 1 && is_leap(ymi));
        day += len;
    }
    #[allow(clippy::cast_precision_loss)]
    {
        day as f64 + dt - 1.0
    }
}

/// MakeDate(day, time) = day × msPerDay + time (Number arithmetic).
fn make_date(day: f64, time: f64) -> f64 {
    day * MS_PER_DAY + time
}

/// TimeClip (21.4.1.31): 𝔽(! ToIntegerOrInfinity(time)) — the MATHEMATICAL
/// zero maps to +0, so a -0-signed truncation (e.g. -1.23e-15) must never
/// survive into [[DateValue]] (caught by the uncapped Date-directory sweep:
/// Date.prototype.valueOf S9.4_A3_T1 asserts SameValue(+0)).
fn time_clip(t: f64) -> f64 {
    if !t.is_finite() || t.abs() > MAX_TIME {
        return f64::NAN;
    }
    to_integer_or_infinity(t) + 0.0
}

/// MakeFullYear (21.4.1.30): 0..=99 maps into 1900..=1999.
fn make_full_year(y: f64) -> f64 {
    if y.is_nan() {
        return f64::NAN;
    }
    let yi = to_integer_or_infinity(y);
    if (0.0..=99.0).contains(&yi) {
        1900.0 + yi
    } else {
        y
    }
}

// -- string formats ---------------------------------------------------------

const WEEKDAYS: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
const MONTHS: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
];

fn pad(n: i64, width: usize) -> String {
    format!("{:0width$}", n, width = width)
}

/// DateString(tv) — "Tue Nov 14 2023".
fn date_string(t: f64) -> String {
    let d = day_i(t);
    let y = year_from_day(d);
    let (m, dt) = month_date_from_day(d);
    let (sign, yv) = if y < 0 { ("-", -y) } else { ("", y) };
    format!(
        "{} {} {} {sign}{}",
        WEEKDAYS[week_day(d) as usize],
        MONTHS[m as usize],
        pad(dt, 2),
        pad(yv, 4)
    )
}

/// TimeString(tv) + TimeZoneString under the pinned zone —
/// "22:13:20 GMT+0000 (Coordinated Universal Time)".
fn time_string_with_zone(t: f64) -> String {
    format!(
        "{}:{}:{} GMT+0000 (Coordinated Universal Time)",
        pad(hour_from(t), 2),
        pad(min_from(t), 2),
        pad(sec_from(t), 2)
    )
}

fn hour_from(t: f64) -> i64 {
    floor_div(day_ms(t), 3_600_000).rem_euclid(24)
}
fn min_from(t: f64) -> i64 {
    floor_div(day_ms(t), 60_000).rem_euclid(60)
}
fn sec_from(t: f64) -> i64 {
    floor_div(day_ms(t), 1000).rem_euclid(60)
}
fn ms_from(t: f64) -> i64 {
    day_ms(t).rem_euclid(1000)
}
fn day_ms(t: f64) -> i64 {
    #[allow(clippy::cast_possible_truncation)]
    {
        time_within_day(t) as i64
    }
}

/// ToDateString(tv) (21.4.4.41.4).
pub(crate) fn to_date_string(tv: f64) -> String {
    if tv.is_nan() {
        return "Invalid Date".to_string();
    }
    let t = local_time(tv);
    format!("{} {}", date_string(t), time_string_with_zone(t))
}

fn iso_year(y: i64) -> Result<String, ()> {
    if (0..=9999).contains(&y) {
        Ok(pad(y, 4))
    } else if y < 0 {
        if y < -271_821 {
            return Err(());
        }
        Ok(format!("-{}", pad(-y, 6)))
    } else {
        if y > 275_760 {
            return Err(());
        }
        Ok(format!("+{}", pad(y, 6)))
    }
}

/// Date.prototype.toISOString body (RangeError on NaN handled by caller).
fn iso_string(t: f64) -> Result<String, ()> {
    let d = day_i(t);
    let y = year_from_day(d);
    let (m, dt) = month_date_from_day(d);
    Ok(format!(
        "{}-{}-{}T{}:{}:{}.{}Z",
        iso_year(y)?,
        pad(m + 1, 2),
        pad(dt, 2),
        pad(hour_from(t), 2),
        pad(min_from(t), 2),
        pad(sec_from(t), 2),
        pad(ms_from(t), 3)
    ))
}

/// Date.prototype.toUTCString — "Tue, 14 Nov 2023 22:13:20 GMT".
fn utc_string(t: f64) -> String {
    let d = day_i(t);
    let y = year_from_day(d);
    let (m, dt) = month_date_from_day(d);
    let (sign, yv) = if y < 0 { ("-", -y) } else { ("", y) };
    format!(
        "{}, {} {} {sign}{} {}:{}:{} GMT",
        WEEKDAYS[week_day(d) as usize],
        pad(dt, 2),
        MONTHS[m as usize],
        pad(yv, 4),
        pad(hour_from(t), 2),
        pad(min_from(t), 2),
        pad(sec_from(t), 2)
    )
}

// -- Date Time String Format parsing (21.4.1.32; exact grammar only) --------

struct P<'a> {
    s: &'a [u16],
    i: usize,
}

impl P<'_> {
    fn digits(&mut self, n: usize) -> Option<i64> {
        let mut v: i64 = 0;
        for _ in 0..n {
            let c = *self.s.get(self.i)?;
            if !(0x30..=0x39).contains(&c) {
                return None;
            }
            v = v * 10 + i64::from(c - 0x30);
            self.i += 1;
        }
        Some(v)
    }

    fn ch(&mut self, c: u16) -> bool {
        if self.s.get(self.i) == Some(&c) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    fn peek(&self) -> Option<u16> {
        self.s.get(self.i).copied()
    }
}

/// Parse EXACTLY the spec Date Time String Format. `Ok(tv)` for grammar
/// matches (including rolled-over MakeDay days — engine-verified), `Err(())`
/// = not in the modeled grammar (implementation-defined fallback; refuse).
fn parse_iso(units: &Units) -> Result<f64, ()> {
    let mut p = P { s: units, i: 0 };
    // Year: YYYY or [+-]YYYYYY.
    let year: i64 = match p.peek() {
        Some(c @ (0x2b | 0x2d)) => {
            p.i += 1;
            let y = p.digits(6).ok_or(())?;
            if c == 0x2d {
                if y == 0 {
                    return Err(()); // -000000 is invalid per grammar
                }
                -y
            } else {
                y
            }
        }
        _ => p.digits(4).ok_or(())?,
    };
    let mut month: i64 = 1;
    let mut day: i64 = 1;
    if p.ch(0x2d) {
        month = p.digits(2).ok_or(())?;
        if !(1..=12).contains(&month) {
            return Err(());
        }
        if p.ch(0x2d) {
            day = p.digits(2).ok_or(())?;
            if !(1..=31).contains(&day) {
                return Err(());
            }
        }
    }
    let mut hour: i64 = 0;
    let mut minute: i64 = 0;
    let mut second: i64 = 0;
    let mut milli: i64 = 0;
    let mut have_time = false;
    let mut offset_ms: Option<i64> = None; // None = date-only or local(=UTC)
    if p.ch(0x54) {
        // 'T'
        have_time = true;
        hour = p.digits(2).ok_or(())?;
        if !p.ch(0x3a) {
            return Err(());
        }
        minute = p.digits(2).ok_or(())?;
        if hour > 24 || minute > 59 {
            return Err(());
        }
        if p.ch(0x3a) {
            second = p.digits(2).ok_or(())?;
            if second > 59 {
                return Err(());
            }
            if p.ch(0x2e) {
                milli = p.digits(3).ok_or(())?;
            }
        }
        // 24:00:00.000 is the only valid hour-24 form.
        if hour == 24 && (minute != 0 || second != 0 || milli != 0) {
            return Err(());
        }
        // Time zone offset.
        match p.peek() {
            Some(0x5a) => {
                p.i += 1;
                offset_ms = Some(0);
            }
            Some(c @ (0x2b | 0x2d)) => {
                p.i += 1;
                let oh = p.digits(2).ok_or(())?;
                if !p.ch(0x3a) {
                    return Err(());
                }
                let om = p.digits(2).ok_or(())?;
                if oh > 23 || om > 59 {
                    return Err(());
                }
                let ms = (oh * 60 + om) * 60_000;
                offset_ms = Some(if c == 0x2d { -ms } else { ms });
            }
            _ => {}
        }
    }
    if p.i != units.len() {
        return Err(());
    }
    #[allow(clippy::cast_precision_loss)]
    let d = make_day(year as f64, (month - 1) as f64, day as f64);
    #[allow(clippy::cast_precision_loss)]
    let t = make_time(hour as f64, minute as f64, second as f64, milli as f64);
    let mut tv = make_date(d, t);
    match offset_ms {
        #[allow(clippy::cast_precision_loss)]
        Some(o) => tv -= o as f64,
        None => {
            if have_time {
                // No offset: local time — identical to UTC under the pinned
                // zone.
                tv = utc_from_local(tv);
            }
        }
    }
    Ok(time_clip(tv))
}

// -- interpreter integration ------------------------------------------------

impl Interp {
    /// The driver's deterministic clock: fixed epoch + 1ms per observation.
    pub(crate) fn tick_now(&mut self) -> f64 {
        self.clock_ticks += 1;
        #[allow(clippy::cast_precision_loss)]
        {
            FIXED_EPOCH + self.clock_ticks as f64
        }
    }

    fn this_date_value(&mut self, this: &JsValue) -> Result<f64, Abrupt> {
        if let JsValue::Obj(oid) = this {
            if let ObjKind::Date(t) = self.heap.obj(*oid).kind {
                return Ok(t);
            }
        }
        Err(self.throw_type_error())
    }

    fn set_date_value(&mut self, this: &JsValue, t: f64) {
        if let JsValue::Obj(oid) = this {
            if let ObjKind::Date(dv) = &mut self.heap.obj_mut(*oid).kind {
                *dv = t;
            }
        }
    }

    fn new_date_obj(&mut self, tv: f64, proto: ObjId) -> Result<ObjId, Abrupt> {
        self.alloc_obj(JsObject::new(ObjKind::Date(tv), Some(proto)))
    }

    /// The 1-arg constructor value path (shared by wrapper and real ctor).
    fn date_value_from_arg(&mut self, v: &JsValue) -> Result<f64, Abrupt> {
        if let JsValue::Obj(oid) = v {
            if let ObjKind::Date(t) = self.heap.obj(*oid).kind {
                return Ok(t);
            }
        }
        let prim = self.to_primitive(v, crate::ops::Hint::Default)?;
        if let JsValue::Str(s) = &prim {
            return match parse_iso(s) {
                Ok(tv) => Ok(tv),
                Err(()) => Err(Abrupt::Fatal(format!(
                    "Date string parse outside the specified ISO grammar: `{}`",
                    trust_js_value::units_to_lossy(s)
                ))),
            };
        }
        Ok(time_clip(self.to_number(&prim)?))
    }

    /// The multi-argument (y, m, d?, h?, min?, s?, ms?) constructor/UTC path.
    fn date_from_fields(&mut self, args: &[JsValue], as_utc: bool) -> Result<f64, Abrupt> {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        let y = self.to_number(&arg(0))?;
        let m = if args.len() > 1 {
            self.to_number(&arg(1))?
        } else {
            0.0
        };
        let dt = if args.len() > 2 {
            self.to_number(&arg(2))?
        } else {
            1.0
        };
        let h = if args.len() > 3 {
            self.to_number(&arg(3))?
        } else {
            0.0
        };
        let min = if args.len() > 4 {
            self.to_number(&arg(4))?
        } else {
            0.0
        };
        let s = if args.len() > 5 {
            self.to_number(&arg(5))?
        } else {
            0.0
        };
        let milli = if args.len() > 6 {
            self.to_number(&arg(6))?
        } else {
            0.0
        };
        let yr = make_full_year(y);
        let final_date = make_date(make_day(yr, m, dt), make_time(h, min, s, milli));
        Ok(if as_utc {
            time_clip(final_date)
        } else {
            time_clip(utc_from_local(final_date))
        })
    }

    #[allow(clippy::too_many_lines)]
    pub(crate) fn dispatch_date(
        &mut self,
        nf: NativeFn,
        this: JsValue,
        args: Vec<JsValue>,
        new_target: Option<&JsValue>,
    ) -> ERes {
        let arg = |i: usize| args.get(i).cloned().unwrap_or(JsValue::Undefined);
        use NativeFn as N;
        match nf {
            N::DateWrapperCtor => {
                // The driver wrapper: as a call (any args) it returns the
                // ToDateString of a ticked instant; as a constructor it
                // ALWAYS produces an instance with %Date.prototype% (the
                // wrapper body constructs the real Date without forwarding
                // new.target — engine-verified).
                if new_target.is_none() {
                    let tv = self.tick_now();
                    return Ok(JsValue::str_from(&to_date_string(tv)));
                }
                let tv = if args.is_empty() {
                    self.tick_now()
                } else if args.len() == 1 {
                    self.date_value_from_arg(&arg(0))?
                } else {
                    self.date_from_fields(&args, false)?
                };
                let proto = self.intr.date_proto;
                let oid = self.new_date_obj(tv, proto)?;
                Ok(JsValue::Obj(oid))
            }
            N::DateRealCtor => {
                // The REAL constructor (Date.prototype.constructor): its
                // zero-argument forms read the real clock — refuse.
                if new_target.is_none() || args.is_empty() {
                    return Err(Abrupt::Fatal(
                        "real Date constructor zero-arg/call form (real clock, \
                         engine-divergent)"
                            .to_string(),
                    ));
                }
                let tv = if args.len() == 1 {
                    self.date_value_from_arg(&arg(0))?
                } else {
                    self.date_from_fields(&args, false)?
                };
                let ntv = new_target.expect("checked above").clone();
                let proto = self.get_prototype_from_constructor(&ntv, self.intr.date_proto)?;
                let oid = self.new_date_obj(tv, proto)?;
                Ok(JsValue::Obj(oid))
            }
            N::DateNow => Ok(JsValue::Num(self.tick_now())),
            N::DateRealNow => Err(Abrupt::Fatal(
                "real Date.now (real clock, engine-divergent)".to_string(),
            )),
            N::DateParse => {
                let s = self.to_string_units(&arg(0))?;
                match parse_iso(&s) {
                    Ok(tv) => Ok(JsValue::Num(tv)),
                    Err(()) => Err(Abrupt::Fatal(format!(
                        "Date.parse outside the specified ISO grammar: `{}`",
                        trust_js_value::units_to_lossy(&s)
                    ))),
                }
            }
            N::DateUtc => {
                if args.is_empty() {
                    // y = ToNumber(undefined) = NaN.
                    return Ok(JsValue::Num(f64::NAN));
                }
                Ok(JsValue::Num(self.date_from_fields(&args, true)?))
            }
            N::DateGetTime | N::DateValueOf => Ok(JsValue::Num(self.this_date_value(&this)?)),
            N::DateGetTimezoneOffset => {
                let t = self.this_date_value(&this)?;
                Ok(JsValue::Num(if t.is_nan() { f64::NAN } else { 0.0 }))
            }
            N::DateSetTime => {
                self.this_date_value(&this)?;
                let n = self.to_number(&arg(0))?;
                let v = time_clip(n);
                self.set_date_value(&this, v);
                Ok(JsValue::Num(v))
            }
            N::DateGetField { field, utc } => {
                let tv = self.this_date_value(&this)?;
                if tv.is_nan() {
                    return Ok(JsValue::Num(f64::NAN));
                }
                let t = if utc { tv } else { local_time(tv) };
                let d = day_i(t);
                #[allow(clippy::cast_precision_loss)]
                let n = match field {
                    DateField::FullYear => year_from_day(d) as f64,
                    DateField::Month => month_date_from_day(d).0 as f64,
                    DateField::Date => month_date_from_day(d).1 as f64,
                    DateField::Day => week_day(d) as f64,
                    DateField::Hours => hour_from(t) as f64,
                    DateField::Minutes => min_from(t) as f64,
                    DateField::Seconds => sec_from(t) as f64,
                    DateField::Milliseconds => ms_from(t) as f64,
                };
                Ok(JsValue::Num(n))
            }
            N::DateSetField { field, utc } => {
                let tv = self.this_date_value(&this)?;
                // Coercions run in argument order BEFORE the NaN short
                // circuit (each ToNumber is observable).
                let mut coerced: Vec<f64> = Vec::with_capacity(args.len());
                let arity: usize = match field {
                    DateSetKind::FullYear => 3,
                    DateSetKind::Month | DateSetKind::Seconds => 2,
                    DateSetKind::Hours => 4,
                    DateSetKind::Minutes => 3,
                    DateSetKind::Date | DateSetKind::Milliseconds => 1,
                };
                for i in 0..args.len().min(arity) {
                    let n = self.to_number(&arg(i))?;
                    coerced.push(n);
                }
                let got = |i: usize| coerced.get(i).copied();
                // setFullYear treats an invalid date as +0; the others
                // return NaN (leaving [[DateValue]] NaN).
                let t = if tv.is_nan() {
                    if matches!(field, DateSetKind::FullYear) {
                        0.0
                    } else {
                        self.set_date_value(&this, f64::NAN);
                        return Ok(JsValue::Num(f64::NAN));
                    }
                } else if utc {
                    tv
                } else {
                    local_time(tv)
                };
                let d = day_i(t);
                #[allow(clippy::cast_precision_loss)]
                let (mut year, mut month, mut date) = {
                    let (m, dt) = month_date_from_day(d);
                    (year_from_day(d) as f64, m as f64, dt as f64)
                };
                #[allow(clippy::cast_precision_loss)]
                let (mut hour, mut min, mut sec, mut milli) = (
                    hour_from(t) as f64,
                    min_from(t) as f64,
                    sec_from(t) as f64,
                    ms_from(t) as f64,
                );
                match field {
                    DateSetKind::FullYear => {
                        year = got(0).unwrap_or(f64::NAN);
                        if let Some(v) = got(1) {
                            month = v;
                        }
                        if let Some(v) = got(2) {
                            date = v;
                        }
                    }
                    DateSetKind::Month => {
                        month = got(0).unwrap_or(f64::NAN);
                        if let Some(v) = got(1) {
                            date = v;
                        }
                    }
                    DateSetKind::Date => {
                        date = got(0).unwrap_or(f64::NAN);
                    }
                    DateSetKind::Hours => {
                        hour = got(0).unwrap_or(f64::NAN);
                        if let Some(v) = got(1) {
                            min = v;
                        }
                        if let Some(v) = got(2) {
                            sec = v;
                        }
                        if let Some(v) = got(3) {
                            milli = v;
                        }
                    }
                    DateSetKind::Minutes => {
                        min = got(0).unwrap_or(f64::NAN);
                        if let Some(v) = got(1) {
                            sec = v;
                        }
                        if let Some(v) = got(2) {
                            milli = v;
                        }
                    }
                    DateSetKind::Seconds => {
                        sec = got(0).unwrap_or(f64::NAN);
                        if let Some(v) = got(1) {
                            milli = v;
                        }
                    }
                    DateSetKind::Milliseconds => {
                        milli = got(0).unwrap_or(f64::NAN);
                    }
                }
                let new_date =
                    make_date(make_day(year, month, date), make_time(hour, min, sec, milli));
                let v = if utc {
                    time_clip(new_date)
                } else {
                    time_clip(utc_from_local(new_date))
                };
                self.set_date_value(&this, v);
                Ok(JsValue::Num(v))
            }
            N::DateToIsoString => {
                let tv = self.this_date_value(&this)?;
                if tv.is_nan() {
                    return Err(self.throw_native(ErrKind::Range));
                }
                match iso_string(tv) {
                    Ok(s) => Ok(JsValue::str_from(&s)),
                    Err(()) => Err(self.throw_native(ErrKind::Range)),
                }
            }
            N::DateToJson => {
                // 21.4.4.37: generic over any receiver.
                let o = self.to_object(&this)?;
                let tv = self.to_primitive(&JsValue::Obj(o), crate::ops::Hint::Number)?;
                if let JsValue::Num(n) = tv {
                    if !n.is_finite() {
                        return Ok(JsValue::Null);
                    }
                }
                let iso = self.get_from_object(
                    o,
                    &PropKey::from_str("toISOString"),
                    JsValue::Obj(o),
                )?;
                self.call_value(&iso, JsValue::Obj(o), vec![])
            }
            N::DateToUtcString => {
                let tv = self.this_date_value(&this)?;
                if tv.is_nan() {
                    return Ok(JsValue::str_from("Invalid Date"));
                }
                Ok(JsValue::str_from(&utc_string(tv)))
            }
            N::DateToString => {
                let tv = self.this_date_value(&this)?;
                Ok(JsValue::str_from(&to_date_string(tv)))
            }
            N::DateToDateString => {
                let tv = self.this_date_value(&this)?;
                if tv.is_nan() {
                    return Ok(JsValue::str_from("Invalid Date"));
                }
                Ok(JsValue::str_from(&date_string(local_time(tv))))
            }
            N::DateToTimeString => {
                let tv = self.this_date_value(&this)?;
                if tv.is_nan() {
                    return Ok(JsValue::str_from("Invalid Date"));
                }
                Ok(JsValue::str_from(&time_string_with_zone(local_time(tv))))
            }
            N::DateToPrimitive => {
                // 21.4.4.45: this must be an Object; hint string maps to
                // OrdinaryToPrimitive order.
                let JsValue::Obj(_) = this else {
                    return Err(self.throw_type_error());
                };
                let JsValue::Str(hint) = arg(0) else {
                    return Err(self.throw_type_error());
                };
                let h = trust_js_value::units_to_lossy(&hint);
                let order: [&str; 2] = match h.as_str() {
                    "default" | "string" => ["toString", "valueOf"],
                    "number" => ["valueOf", "toString"],
                    _ => return Err(self.throw_type_error()),
                };
                for m in order {
                    let mv = self.get_prop(&this, &PropKey::from_str(m))?;
                    if let JsValue::Obj(mid) = &mv {
                        if self.heap.obj(*mid).is_callable() {
                            let r = self.call_value(&mv, this.clone(), vec![])?;
                            if !r.is_object() {
                                return Ok(r);
                            }
                        }
                    }
                }
                Err(self.throw_type_error())
            }
            N::DateGetYear => {
                let tv = self.this_date_value(&this)?;
                if tv.is_nan() {
                    return Ok(JsValue::Num(f64::NAN));
                }
                #[allow(clippy::cast_precision_loss)]
                Ok(JsValue::Num(
                    year_from_day(day_i(local_time(tv))) as f64 - 1900.0,
                ))
            }
            N::DateSetYear => {
                // B.2.3.2.
                let tv = self.this_date_value(&this)?;
                let t = if tv.is_nan() { 0.0 } else { local_time(tv) };
                let y = self.to_number(&arg(0))?;
                if y.is_nan() {
                    self.set_date_value(&this, f64::NAN);
                    return Ok(JsValue::Num(f64::NAN));
                }
                let yi = to_integer_or_infinity(y);
                let yyyy = if (0.0..=99.0).contains(&yi) {
                    yi + 1900.0
                } else {
                    y
                };
                let d = day_i(t);
                let (m, dt) = month_date_from_day(d);
                #[allow(clippy::cast_precision_loss)]
                let day = make_day(yyyy, m as f64, dt as f64);
                let date = utc_from_local(make_date(day, time_within_day(t)));
                let v = time_clip(date);
                self.set_date_value(&this, v);
                Ok(JsValue::Num(v))
            }
            _ => Err(Abrupt::Fatal("unrouted date native (interpreter bug)".to_string())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn day_decomposition_vectors() {
        // 1700000000123 = 2023-11-14T22:13:20.123Z, a Tuesday.
        let t = 1_700_000_000_123.0;
        let d = day_i(t);
        assert_eq!(year_from_day(d), 2023);
        assert_eq!(month_date_from_day(d), (10, 14));
        assert_eq!(week_day(d), 2);
        assert_eq!(hour_from(t), 22);
        assert_eq!(min_from(t), 13);
        assert_eq!(sec_from(t), 20);
        assert_eq!(ms_from(t), 123);
        // Epoch and negative times.
        assert_eq!(year_from_day(day_i(0.0)), 1970);
        assert_eq!(week_day(day_i(0.0)), 4); // Thursday
        let neg = -5e12;
        assert_eq!(year_from_day(day_i(neg)), 1811);
        assert_eq!(month_date_from_day(day_i(neg)), (6, 23));
        // Extremes.
        assert_eq!(year_from_day(day_i(MAX_TIME)), 275_760);
        assert_eq!(month_date_from_day(day_i(MAX_TIME)), (8, 13));
        assert_eq!(year_from_day(day_i(-MAX_TIME)), -271_821);
        assert_eq!(month_date_from_day(day_i(-MAX_TIME)), (3, 20));
    }

    #[test]
    fn make_day_time_clip_vectors() {
        assert_eq!(make_date(make_day(1970.0, 0.0, 1.0), 0.0), 0.0);
        // Rollover: month 13 / day 32 / hour 25 wrap forward.
        let t = make_date(
            make_day(2023.0, 13.0, 32.0),
            make_time(25.0, 61.0, 61.0, 1001.0),
        );
        assert_eq!(iso_string(t).unwrap(), "2024-03-04T02:02:02.001Z");
        assert!(time_clip(MAX_TIME + 1.0).is_nan());
        assert_eq!(time_clip(MAX_TIME), MAX_TIME);
        assert_eq!(time_clip(1.5), 1.0);
        assert_eq!(time_clip(-1.5), -1.0);
        // 𝔽(0) is +0: negative-fraction truncation must not yield -0.
        assert_eq!(time_clip(-1.23e-15).to_bits(), 0.0f64.to_bits());
        assert_eq!(time_clip(-0.0).to_bits(), 0.0f64.to_bits());
        assert!(make_day(f64::NAN, 0.0, 1.0).is_nan());
        assert!(make_day(1.0e9, 0.0, 1.0).is_nan());
        assert_eq!(make_full_year(99.0), 1999.0);
        assert_eq!(make_full_year(100.0), 100.0);
        assert_eq!(make_full_year(-1.0), -1.0);
    }

    #[test]
    fn format_vectors() {
        let t = 1_700_000_000_123.0;
        assert_eq!(
            to_date_string(t),
            "Tue Nov 14 2023 22:13:20 GMT+0000 (Coordinated Universal Time)"
        );
        assert_eq!(utc_string(t), "Tue, 14 Nov 2023 22:13:20 GMT");
        assert_eq!(iso_string(t).unwrap(), "2023-11-14T22:13:20.123Z");
        assert_eq!(to_date_string(f64::NAN), "Invalid Date");
        assert_eq!(
            iso_string(-62_198_755_200_000.0).unwrap(),
            "-000001-01-01T00:00:00.000Z"
        );
        assert_eq!(iso_string(MAX_TIME).unwrap(), "+275760-09-13T00:00:00.000Z");
    }

    #[test]
    fn parse_iso_vectors() {
        let u = trust_js_value::units_from_str;
        let p = |s: &str| parse_iso(&u(s));
        assert_eq!(p("2023-11-14T22:13:20.123Z").unwrap(), 1_700_000_000_123.0);
        assert_eq!(p("2023-11-14").unwrap(), 1_699_920_000_000.0);
        assert_eq!(p("2023-11-14T22:13:20").unwrap(), 1_700_000_000_000.0);
        assert_eq!(p("2023-11-14T22:13:20+05:30").unwrap(), 1_699_980_200_000.0);
        // In-grammar day overflow rolls (engine-verified).
        assert_eq!(p("2023-02-29").unwrap(), 1_677_628_800_000.0);
        assert_eq!(p("2023-11-14T24:00:00").unwrap(), 1_700_006_400_000.0);
        assert_eq!(p("+275760-09-13T00:00:00.000Z").unwrap(), MAX_TIME);
        assert_eq!(p("-271821-04-20T00:00:00.000Z").unwrap(), -MAX_TIME);
        assert_eq!(p("2023").unwrap(), 1_672_531_200_000.0);
        assert_eq!(p("2023-11").unwrap(), 1_698_796_800_000.0);
        assert_eq!(p("2023-11-14T22:13").unwrap(), 1_699_999_980_000.0);
        // Outside the exact grammar: refuse (never guess).
        for bad in [
            "2023-13-01", "2023-00-01", "2023-01-00", "2023-11-14T25:00:00",
            "2023-11-14T24:30:00", "2023-11-14T23:59:60", "2023-11-14 22:13:20",
            "2023-11-14T22:13:20.1Z", "nonsense", "", "-000000", "2023-11-14t22:13",
            "2023-11-14T22:13:20z", " 2023", "2023 ",
        ] {
            assert!(p(bad).is_err(), "should refuse: {bad}");
        }
    }
}
