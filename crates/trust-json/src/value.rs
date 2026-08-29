// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The JSON tree.

use crate::map::Map;
use crate::number::Number;
use core::fmt::{self, Debug, Display};

/// Represents any valid JSON value.
#[derive(Clone, PartialEq, Eq, Default)]
pub enum Value {
    /// `null`.
    #[default]
    Null,
    /// `true` or `false`.
    Bool(bool),
    /// A number, integer or floating point.
    Number(Number),
    /// A string.
    String(String),
    /// An array.
    Array(Vec<Value>),
    /// An object. Key-sorted — see [`crate::map`].
    Object(Map<String, Value>),
}

impl Value {
    #[must_use]
    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }
    #[must_use]
    pub fn is_boolean(&self) -> bool {
        matches!(self, Value::Bool(_))
    }
    #[must_use]
    pub fn is_number(&self) -> bool {
        matches!(self, Value::Number(_))
    }
    #[must_use]
    pub fn is_string(&self) -> bool {
        matches!(self, Value::String(_))
    }
    #[must_use]
    pub fn is_array(&self) -> bool {
        matches!(self, Value::Array(_))
    }
    #[must_use]
    pub fn is_object(&self) -> bool {
        matches!(self, Value::Object(_))
    }
    #[must_use]
    pub fn is_i64(&self) -> bool {
        matches!(self, Value::Number(n) if n.is_i64())
    }
    #[must_use]
    pub fn is_u64(&self) -> bool {
        matches!(self, Value::Number(n) if n.is_u64())
    }
    #[must_use]
    pub fn is_f64(&self) -> bool {
        matches!(self, Value::Number(n) if n.is_f64())
    }

    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::String(s) => Some(s),
            _ => None,
        }
    }
    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Value::Number(n) => n.as_i64(),
            _ => None,
        }
    }
    #[must_use]
    pub fn as_u64(&self) -> Option<u64> {
        match self {
            Value::Number(n) => n.as_u64(),
            _ => None,
        }
    }
    #[must_use]
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Value::Number(n) => n.as_f64(),
            _ => None,
        }
    }
    #[must_use]
    pub fn as_array(&self) -> Option<&Vec<Value>> {
        match self {
            Value::Array(a) => Some(a),
            _ => None,
        }
    }
    pub fn as_array_mut(&mut self) -> Option<&mut Vec<Value>> {
        match self {
            Value::Array(a) => Some(a),
            _ => None,
        }
    }
    #[must_use]
    pub fn as_object(&self) -> Option<&Map<String, Value>> {
        match self {
            Value::Object(o) => Some(o),
            _ => None,
        }
    }
    pub fn as_object_mut(&mut self) -> Option<&mut Map<String, Value>> {
        match self {
            Value::Object(o) => Some(o),
            _ => None,
        }
    }

    /// Index into a JSON array or object; returns `None` for the wrong shape
    /// or a missing key, never panicking.
    #[must_use]
    pub fn get<I: Index>(&self, index: I) -> Option<&Value> {
        index.index_into(self)
    }

    pub fn get_mut<I: Index>(&mut self, index: I) -> Option<&mut Value> {
        index.index_into_mut(self)
    }

    /// Takes the value out, leaving `Null` in its place.
    pub fn take(&mut self) -> Value {
        core::mem::replace(self, Value::Null)
    }
}

/// A type that can index into a [`Value`].
pub trait Index {
    #[doc(hidden)]
    fn index_into<'v>(&self, v: &'v Value) -> Option<&'v Value>;
    #[doc(hidden)]
    fn index_into_mut<'v>(&self, v: &'v mut Value) -> Option<&'v mut Value>;
}

impl Index for usize {
    fn index_into<'v>(&self, v: &'v Value) -> Option<&'v Value> {
        match v {
            Value::Array(a) => a.get(*self),
            _ => None,
        }
    }
    fn index_into_mut<'v>(&self, v: &'v mut Value) -> Option<&'v mut Value> {
        match v {
            Value::Array(a) => a.get_mut(*self),
            _ => None,
        }
    }
}

impl Index for str {
    fn index_into<'v>(&self, v: &'v Value) -> Option<&'v Value> {
        match v {
            Value::Object(o) => o.get(self),
            _ => None,
        }
    }
    fn index_into_mut<'v>(&self, v: &'v mut Value) -> Option<&'v mut Value> {
        match v {
            Value::Object(o) => o.get_mut(self),
            _ => None,
        }
    }
}

impl Index for String {
    fn index_into<'v>(&self, v: &'v Value) -> Option<&'v Value> {
        self.as_str().index_into(v)
    }
    fn index_into_mut<'v>(&self, v: &'v mut Value) -> Option<&'v mut Value> {
        self.as_str().index_into_mut(v)
    }
}

impl<T> Index for &T
where
    T: ?Sized + Index,
{
    fn index_into<'v>(&self, v: &'v Value) -> Option<&'v Value> {
        (**self).index_into(v)
    }
    fn index_into_mut<'v>(&self, v: &'v mut Value) -> Option<&'v mut Value> {
        (**self).index_into_mut(v)
    }
}

impl<I> core::ops::Index<I> for Value
where
    I: Index,
{
    type Output = Value;
    /// Missing entries read as `Null`, matching the incumbent.
    fn index(&self, index: I) -> &Value {
        static NULL: Value = Value::Null;
        index.index_into(self).unwrap_or(&NULL)
    }
}

/// `Display` is the compact serialization; `{:#}` is the pretty one. Same as
/// the incumbent.
impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = if f.alternate() {
            crate::ser::to_string_pretty(self)
        } else {
            crate::ser::to_string(self)
        };
        match s {
            Ok(s) => f.write_str(&s),
            Err(_) => Err(fmt::Error),
        }
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Null => f.write_str("Null"),
            Value::Bool(b) => write!(f, "Bool({b})"),
            Value::Number(n) => Debug::fmt(n, f),
            Value::String(s) => write!(f, "String({s:?})"),
            Value::Array(a) => {
                f.write_str("Array ")?;
                Debug::fmt(a, f)
            }
            Value::Object(o) => {
                f.write_str("Object ")?;
                Debug::fmt(o, f)
            }
        }
    }
}

macro_rules! from_number {
    ($($ty:ty)*) => {$(
        impl From<$ty> for Value {
            fn from(n: $ty) -> Self { Value::Number(n.into()) }
        }
    )*};
}
from_number!(u8 u16 u32 u64 usize i8 i16 i32 i64 isize);

impl From<f64> for Value {
    /// A non-finite float becomes `Null`, matching the incumbent.
    fn from(f: f64) -> Self {
        Number::from_f64(f).map_or(Value::Null, Value::Number)
    }
}

impl From<f32> for Value {
    fn from(f: f32) -> Self {
        Value::from(f64::from(f))
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::String(s)
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::String(s.to_owned())
    }
}

impl From<Number> for Value {
    fn from(n: Number) -> Self {
        Value::Number(n)
    }
}

impl From<Map<String, Value>> for Value {
    fn from(m: Map<String, Value>) -> Self {
        Value::Object(m)
    }
}

impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(v: Vec<T>) -> Self {
        Value::Array(v.into_iter().map(Into::into).collect())
    }
}

impl<T: Clone + Into<Value>> From<&[T]> for Value {
    fn from(v: &[T]) -> Self {
        Value::Array(v.iter().cloned().map(Into::into).collect())
    }
}

impl<T: Into<Value>> From<Option<T>> for Value {
    fn from(o: Option<T>) -> Self {
        o.map_or(Value::Null, Into::into)
    }
}

impl<T: Into<Value>> FromIterator<T> for Value {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Value::Array(iter.into_iter().map(Into::into).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn non_finite_floats_become_null() {
        assert_eq!(Value::from(f64::NAN), Value::Null);
        assert_eq!(Value::from(f64::INFINITY), Value::Null);
    }

    #[test]
    fn display_is_compact_alternate_is_pretty() {
        let v = Value::Array(vec![Value::from(1u8), Value::from(2u8)]);
        assert_eq!(format!("{v}"), "[1,2]");
        assert_eq!(format!("{v:#}"), "[\n  1,\n  2\n]");
    }
}
