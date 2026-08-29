// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A JSON number.
//!
//! The three-way split (`u64` / `i64` / `f64`) is not an implementation detail
//! that can be simplified: the tree's digests depend on it. `100` must
//! serialize as `100` and `100.0` as `100.0`, so an integer that arrived as an
//! integer has to STAY an integer through a parse/serialize round trip. A
//! single `f64` carrier would silently rewrite every integer in every proof
//! bundle.
//!
//! `Number` cannot hold NaN or an infinity: [`Number::from_f64`] returns `None`
//! for them, matching the incumbent, and `Value::from(f64::NAN)` is therefore
//! `Value::Null`.

use crate::ser::float::FloatBuffer;
use crate::ser::int::IntBuffer;
use core::fmt::{self, Debug, Display};
use core::hash::{Hash, Hasher};

/// Represents a JSON number, whether integer or floating point.
#[derive(Clone, PartialEq, Eq)]
pub struct Number {
    pub(crate) n: N,
}

#[derive(Copy, Clone, Debug)]
pub(crate) enum N {
    PosInt(u64),
    NegInt(i64),
    Float(f64),
}

impl PartialEq for N {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (N::PosInt(a), N::PosInt(b)) => a == b,
            (N::NegInt(a), N::NegInt(b)) => a == b,
            // `-0.0 == 0.0` is true in IEEE and true here, matching the
            // incumbent. The Hash impl below normalises to keep the
            // Eq/Hash contract.
            (N::Float(a), N::Float(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for N {}

impl Hash for N {
    fn hash<H: Hasher>(&self, h: &mut H) {
        match *self {
            N::PosInt(i) => i.hash(h),
            N::NegInt(i) => i.hash(h),
            N::Float(f) => {
                if f == 0.0f64 {
                    // 0.0 and -0.0 compare equal, so they must hash equal.
                    0.0f64.to_bits().hash(h);
                } else {
                    f.to_bits().hash(h);
                }
            }
        }
    }
}

impl Hash for Number {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.n.hash(h);
    }
}

impl Number {
    /// Returns true if the number is an integer between `i64::MIN` and
    /// `i64::MAX`.
    #[must_use]
    pub fn is_i64(&self) -> bool {
        match self.n {
            N::PosInt(v) => v <= i64::MAX as u64,
            N::NegInt(_) => true,
            N::Float(_) => false,
        }
    }

    /// Returns true if the number is an integer between zero and `u64::MAX`.
    #[must_use]
    pub fn is_u64(&self) -> bool {
        matches!(self.n, N::PosInt(_))
    }

    /// Returns true if the number can be represented by `f64`.
    #[must_use]
    pub fn is_f64(&self) -> bool {
        matches!(self.n, N::Float(_))
    }

    /// Represents the number as `i64` if possible.
    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        match self.n {
            N::PosInt(n) => {
                if n <= i64::MAX as u64 {
                    Some(n as i64)
                } else {
                    None
                }
            }
            N::NegInt(n) => Some(n),
            N::Float(_) => None,
        }
    }

    /// Represents the number as `u64` if possible.
    #[must_use]
    pub fn as_u64(&self) -> Option<u64> {
        match self.n {
            N::PosInt(n) => Some(n),
            N::NegInt(_) | N::Float(_) => None,
        }
    }

    /// Represents the number as `f64` if possible. Integers are converted
    /// lossily, exactly as the incumbent does.
    #[must_use]
    pub fn as_f64(&self) -> Option<f64> {
        match self.n {
            N::PosInt(n) => Some(n as f64),
            N::NegInt(n) => Some(n as f64),
            N::Float(n) => Some(n),
        }
    }

    /// Converts a finite `f64` to a `Number`. Infinite or NaN input returns
    /// `None` — a JSON document has no spelling for them.
    #[must_use]
    pub fn from_f64(f: f64) -> Option<Number> {
        if f.is_finite() {
            Some(Number { n: N::Float(f) })
        } else {
            None
        }
    }
}

impl Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.n {
            N::PosInt(u) => f.write_str(IntBuffer::new().format_u64(u)),
            N::NegInt(i) => f.write_str(IntBuffer::new().format_i64(i)),
            N::Float(v) => f.write_str(FloatBuffer::new().format_finite_f64(v)),
        }
    }
}

impl Debug for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Number({self})")
    }
}

macro_rules! from_unsigned {
    ($($ty:ty)*) => {$(
        impl From<$ty> for Number {
            fn from(u: $ty) -> Self {
                Number { n: N::PosInt(u as u64) }
            }
        }
    )*};
}

macro_rules! from_signed {
    ($($ty:ty)*) => {$(
        impl From<$ty> for Number {
            fn from(i: $ty) -> Self {
                let i = i as i64;
                if i < 0 {
                    Number { n: N::NegInt(i) }
                } else {
                    Number { n: N::PosInt(i as u64) }
                }
            }
        }
    )*};
}

from_unsigned!(u8 u16 u32 u64 usize);
from_signed!(i8 i16 i32 i64 isize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn non_finite_has_no_number() {
        assert!(Number::from_f64(f64::NAN).is_none());
        assert!(Number::from_f64(f64::INFINITY).is_none());
        assert!(Number::from_f64(f64::NEG_INFINITY).is_none());
    }

    #[test]
    fn negative_zero_keeps_its_sign_in_display() {
        // The sign of zero is observable in the output and must survive.
        assert_eq!(Number::from_f64(-0.0).unwrap().to_string(), "-0.0");
        assert_eq!(Number::from_f64(0.0).unwrap().to_string(), "0.0");
    }

    #[test]
    fn integers_stay_integers() {
        assert_eq!(Number::from(100u8).to_string(), "100");
        assert_eq!(Number::from(-1i64).to_string(), "-1");
        assert_eq!(Number::from(u64::MAX).to_string(), "18446744073709551615");
        assert_eq!(Number::from(i64::MIN).to_string(), "-9223372036854775808");
        assert!(Number::from(u64::MAX).is_u64());
        assert!(!Number::from(u64::MAX).is_i64());
        assert!(Number::from(i64::MIN).is_i64());
    }
}
