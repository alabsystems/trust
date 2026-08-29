// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! TOML's four date/time forms (TOML v1.0.0 §"Offset Date-Time" .. §"Local
//! Time"), and nothing else.
//!
//! # This type is deliberately inert
//!
//! Measured over the 1360-file TOML corpus in this repository: **zero
//! datetimes**. Not "few" — none. So the requirement here is not a calendar
//! library, it is that a datetime *round-trips*: parse it, hold it, print it
//! back. There is no arithmetic, no timezone database, no `chrono`-shaped API,
//! and there must not be. Anything more is surface that nothing exercises and
//! that a future reader would reasonably assume is tested.
//!
//! # Round-tripping is value-lossless, not byte-lossless
//!
//! `07:32:00.100` prints back as `07:32:00.1`. Trailing zeros in the fractional
//! second are not preserved, because the fraction is stored as a `u32`
//! nanosecond count. **This is exactly what the incumbent does**
//! (`toml_datetime` formats `{:09}` and then `trim_end_matches('0')`), and
//! matching the incumbent is the priority — a difference here would be a real
//! disagreement on the acceptance gate, whereas this is not.
//!
//! Fractions finer than a nanosecond are truncated, again as the incumbent
//! truncates them.
//!
//! # One place this is STRICTER than the incumbent, stated at the site
//!
//! [`Date::validate`] rejects a day that does not exist in its month —
//! `2026-02-30` is an error here. The incumbent's range check is looser. This
//! cannot show up on the corpus differential (zero datetimes), and rejecting an
//! impossible date is the behaviour a reader of a *verifying* toolchain should
//! get. If a future corpus file does carry an out-of-range date and the gate
//! reports a rejection disagreement, this comment is the explanation, and the
//! fix is a decision about which behaviour is wanted — not a silent loosening.

use std::fmt;

use crate::error::Error;

/// The struct name this crate and the incumbent both use to smuggle a datetime
/// through serde's data model.
///
/// serde has no datetime type, so a self-describing format that has one has to
/// encode it as something serde does understand. The convention `toml`
/// established is a one-entry map under a reserved key that cannot collide with
/// a real TOML key (a bare key cannot contain `$`, and a quoted key spelling
/// this exact string is not something any real document contains).
///
/// **The spelling is copied from the incumbent on purpose.** Keeping it
/// identical means a type written against `toml_datetime`'s `Deserialize` impl
/// deserializes from this crate unchanged, and vice versa. Changing it would be
/// a silent wire-format fork.
pub(crate) const DATETIME_PRIVATE_NAME: &str = "$__toml_private_Datetime";

/// The reserved field name inside that map.
pub(crate) const DATETIME_PRIVATE_FIELD: &str = "$__toml_private_datetime";

/// A TOML date and/or time.
///
/// Exactly one of the four TOML forms, distinguished by which parts are
/// present:
///
/// | form | `date` | `time` | `offset` |
/// |---|---|---|---|
/// | offset date-time | yes | yes | yes |
/// | local date-time  | yes | yes | no  |
/// | local date       | yes | no  | no  |
/// | local time       | no  | yes | no  |
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Datetime {
    /// The calendar date, absent only for a local time.
    pub date: Option<Date>,
    /// The wall-clock time, absent only for a local date.
    pub time: Option<Time>,
    /// The UTC offset; present only for an offset date-time.
    pub offset: Option<Offset>,
}

/// A calendar date.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Date {
    /// Four-digit year.
    pub year: u16,
    /// 1-12.
    pub month: u8,
    /// 1-31, and no larger than the month allows.
    pub day: u8,
}

/// A wall-clock time.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Time {
    /// 0-23.
    pub hour: u8,
    /// 0-59.
    pub minute: u8,
    /// 0-60. Sixty is allowed: TOML's ABNF defers to the leap-second rules.
    pub second: u8,
    /// 0-999_999_999.
    pub nanosecond: u32,
}

/// A UTC offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Offset {
    /// `Z` — zero offset, explicitly UTC.
    ///
    /// Distinct from `Custom { minutes: 0 }` because `+00:00` and `Z` are
    /// different spellings and the round-trip must preserve which was written.
    Z,
    /// Signed minutes east of UTC.
    Custom {
        /// Minutes; negative is west of UTC.
        minutes: i16,
    },
}

impl Date {
    fn validate(self, line: usize, column: usize) -> Result<Self, Error> {
        if self.month < 1 || self.month > 12 {
            return Err(Error::at(
                format!("month `{}` is out of range 01-12", self.month),
                line,
                column,
            ));
        }
        let limit = days_in_month(self.year, self.month);
        if self.day < 1 || self.day > limit {
            // See the module header: this per-month check is stricter than the
            // incumbent's. It is stated there and here rather than only in a
            // commit message.
            return Err(Error::at(
                format!(
                    "day `{}` is out of range 01-{limit:02} for {:04}-{:02}",
                    self.day, self.year, self.month
                ),
                line,
                column,
            ));
        }
        Ok(self)
    }
}

fn is_leap_year(year: u16) -> bool {
    (year % 4 == 0 && year % 100 != 0) || year % 400 == 0
}

fn days_in_month(year: u16, month: u8) -> u8 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year(year) => 29,
        2 => 28,
        _ => 0,
    }
}

impl fmt::Display for Date {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:04}-{:02}-{:02}", self.year, self.month, self.day)
    }
}

impl fmt::Display for Time {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:02}:{:02}:{:02}", self.hour, self.minute, self.second)?;
        if self.nanosecond != 0 {
            // Identical to the incumbent: nine digits, then trailing zeros
            // trimmed. See the module header for why this is value-lossless
            // rather than byte-lossless.
            let digits = format!("{:09}", self.nanosecond);
            write!(f, ".{}", digits.trim_end_matches('0'))?;
        }
        Ok(())
    }
}

impl fmt::Display for Offset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Z => f.write_str("Z"),
            Self::Custom { minutes } => {
                let (sign, magnitude) =
                    if *minutes < 0 { ('-', -i32::from(*minutes)) } else { ('+', i32::from(*minutes)) };
                write!(f, "{sign}{:02}:{:02}", magnitude / 60, magnitude % 60)
            }
        }
    }
}

impl fmt::Display for Datetime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(date) = self.date {
            write!(f, "{date}")?;
        }
        if let Some(time) = self.time {
            if self.date.is_some() {
                f.write_str("T")?;
            }
            write!(f, "{time}")?;
        }
        if let Some(offset) = self.offset {
            write!(f, "{offset}")?;
        }
        Ok(())
    }
}

/// Parse a datetime from the exact text of a TOML datetime token.
///
/// The tokenizer has already decided that this run of bytes IS a datetime (see
/// `parser::looks_like_datetime`); this function's job is to accept the four
/// forms and reject everything else with a located error.
pub(crate) fn parse(text: &str, line: usize, column: usize) -> Result<Datetime, Error> {
    let bytes = text.as_bytes();
    let bad = |what: &str| Error::at(format!("invalid datetime `{text}`: {what}"), line, column);

    // Local time: `HH:MM:SS[.frac]`, distinguished by a colon in position 2.
    if bytes.len() >= 3 && bytes[2] == b':' {
        let (time, rest) = parse_time(text, line, column)?;
        if !rest.is_empty() {
            return Err(bad("trailing characters after a local time"));
        }
        return Ok(Datetime { date: None, time: Some(time), offset: None });
    }

    if bytes.len() < 10 {
        return Err(bad("expected a date of the form YYYY-MM-DD"));
    }
    let date = parse_date(&text[..10], line, column)?;
    let rest = &text[10..];
    if rest.is_empty() {
        return Ok(Datetime { date: Some(date), time: None, offset: None });
    }

    // TOML permits `T`, `t` or a single space as the date/time separator.
    let separator = rest.as_bytes()[0];
    if !matches!(separator, b'T' | b't' | b' ') {
        return Err(bad("expected `T`, `t` or a space between the date and the time"));
    }
    let (time, rest) = parse_time(&rest[1..], line, column)?;

    let offset = if rest.is_empty() {
        None
    } else {
        Some(parse_offset(rest, line, column)?)
    };
    Ok(Datetime { date: Some(date), time: Some(time), offset })
}

fn parse_date(text: &str, line: usize, column: usize) -> Result<Date, Error> {
    let bytes = text.as_bytes();
    let bad = |what: &str| Error::at(format!("invalid date `{text}`: {what}"), line, column);
    if bytes.len() != 10 || bytes[4] != b'-' || bytes[7] != b'-' {
        return Err(bad("expected YYYY-MM-DD"));
    }
    let digits = |slice: &str| -> Result<u32, Error> {
        if slice.bytes().all(|byte| byte.is_ascii_digit()) {
            Ok(slice.parse::<u32>().unwrap_or(u32::MAX))
        } else {
            Err(Error::at(format!("invalid date `{text}`: expected digits"), line, column))
        }
    };
    let year = digits(&text[0..4])?;
    let month = digits(&text[5..7])?;
    let day = digits(&text[8..10])?;
    Date {
        year: u16::try_from(year).map_err(|_| bad("year out of range"))?,
        month: u8::try_from(month).map_err(|_| bad("month out of range"))?,
        day: u8::try_from(day).map_err(|_| bad("day out of range"))?,
    }
    .validate(line, column)
}

/// Parse `HH:MM:SS[.frac]`, returning the remainder (offset, if any).
fn parse_time<'a>(text: &'a str, line: usize, column: usize) -> Result<(Time, &'a str), Error> {
    let bad = |what: &str| Error::at(format!("invalid time `{text}`: {what}"), line, column);
    let bytes = text.as_bytes();
    if bytes.len() < 8 || bytes[2] != b':' || bytes[5] != b':' {
        return Err(bad("expected HH:MM:SS"));
    }
    let field = |slice: &str, what: &'static str| -> Result<u8, Error> {
        if slice.len() == 2 && slice.bytes().all(|byte| byte.is_ascii_digit()) {
            Ok(slice.parse::<u8>().unwrap_or(u8::MAX))
        } else {
            Err(Error::at(
                format!("invalid time `{text}`: expected two digits for the {what}"),
                line,
                column,
            ))
        }
    };
    let hour = field(&text[0..2], "hour")?;
    let minute = field(&text[3..5], "minute")?;
    let second = field(&text[6..8], "second")?;
    if hour > 23 {
        return Err(bad("hour out of range 00-23"));
    }
    if minute > 59 {
        return Err(bad("minute out of range 00-59"));
    }
    // 60 is deliberate: TOML's ABNF defers `time-second` to the leap-second
    // rules, so `23:59:60` is a valid TOML time.
    if second > 60 {
        return Err(bad("second out of range 00-60"));
    }

    let mut rest = &text[8..];
    let mut nanosecond = 0u32;
    if rest.starts_with('.') {
        let fraction: String =
            rest[1..].chars().take_while(char::is_ascii_digit).collect();
        if fraction.is_empty() {
            return Err(bad("a fractional second needs at least one digit"));
        }
        rest = &rest[1 + fraction.len()..];
        // Nine digits of precision, truncating the rest — as the incumbent
        // does. See the module header.
        for (index, digit) in fraction.bytes().take(9).enumerate() {
            let place = 10u32.pow(8 - u32::try_from(index).expect("index < 9"));
            nanosecond += u32::from(digit - b'0') * place;
        }
    }
    Ok((Time { hour, minute, second, nanosecond }, rest))
}

fn parse_offset(text: &str, line: usize, column: usize) -> Result<Offset, Error> {
    let bad = |what: &str| Error::at(format!("invalid UTC offset `{text}`: {what}"), line, column);
    if text == "Z" || text == "z" {
        return Ok(Offset::Z);
    }
    let bytes = text.as_bytes();
    if bytes.len() != 6 || !matches!(bytes[0], b'+' | b'-') || bytes[3] != b':' {
        return Err(bad("expected `Z` or `+HH:MM` / `-HH:MM`"));
    }
    let field = |slice: &str| -> Result<i16, Error> {
        if slice.bytes().all(|byte| byte.is_ascii_digit()) {
            Ok(slice.parse::<i16>().unwrap_or(i16::MAX))
        } else {
            Err(Error::at(format!("invalid UTC offset `{text}`: expected digits"), line, column))
        }
    };
    let hours = field(&text[1..3])?;
    let minutes = field(&text[4..6])?;
    if hours > 23 {
        return Err(bad("offset hours out of range 00-23"));
    }
    if minutes > 59 {
        return Err(bad("offset minutes out of range 00-59"));
    }
    let total = hours * 60 + minutes;
    Ok(Offset::Custom { minutes: if bytes[0] == b'-' { -total } else { total } })
}

// ---------------------------------------------------------------------------
// serde
// ---------------------------------------------------------------------------

impl serde::Serialize for Datetime {
    /// Serialize through the reserved one-entry map, so a datetime survives a
    /// round-trip through any self-describing format.
    ///
    /// Note that this crate ships no TOML *serializer* (slice 1 is the read
    /// path). This impl exists so `Datetime` is usable as a field of a type the
    /// caller serializes to some other format, and so the encoding is stated in
    /// one place next to the matching `Deserialize`.
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct as _;
        let mut entry = serializer.serialize_struct(DATETIME_PRIVATE_NAME, 1)?;
        entry.serialize_field(DATETIME_PRIVATE_FIELD, &self.to_string())?;
        entry.end()
    }
}

impl<'de> serde::Deserialize<'de> for Datetime {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_struct(
            DATETIME_PRIVATE_NAME,
            &[DATETIME_PRIVATE_FIELD],
            DatetimeVisitor,
        )
    }
}

struct DatetimeVisitor;

impl<'de> serde::de::Visitor<'de> for DatetimeVisitor {
    type Value = Datetime;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a TOML datetime")
    }

    fn visit_map<A: serde::de::MapAccess<'de>>(self, mut map: A) -> Result<Datetime, A::Error> {
        use serde::de::Error as _;
        let key: Option<DatetimeKey> = map.next_key()?;
        if key.is_none() {
            return Err(A::Error::custom("expected a TOML datetime"));
        }
        let text: String = map.next_value()?;
        if map.next_key::<DatetimeKey>()?.is_some() {
            return Err(A::Error::custom("expected exactly one datetime field"));
        }
        // Position 1:1 is a placeholder: this path is reached from an arbitrary
        // Deserializer, which may be another format entirely, so there is no
        // TOML position to report. When the source IS this crate's parser the
        // datetime was already validated at parse time and cannot fail here.
        parse(&text, 1, 1).map_err(|error| A::Error::custom(error.message()))
    }
}

/// Accepts only the reserved field name, so a two-entry map or a differently
/// named key is a clean error rather than a silent misread.
struct DatetimeKey;

impl<'de> serde::Deserialize<'de> for DatetimeKey {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct KeyVisitor;

        impl serde::de::Visitor<'_> for KeyVisitor {
            type Value = DatetimeKey;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a TOML datetime field")
            }

            fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<DatetimeKey, E> {
                if value == DATETIME_PRIVATE_FIELD {
                    Ok(DatetimeKey)
                } else {
                    Err(E::custom("expected the reserved TOML datetime field"))
                }
            }
        }

        deserializer.deserialize_identifier(KeyVisitor)
    }
}
