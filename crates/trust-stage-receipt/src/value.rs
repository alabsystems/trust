//! Lossless receipt data, independent of Cargo's globally unified serde features.
//!
//! Numbers retain their validated JSON tokens. Objects retain insertion order
//! and use a separate logarithmic lookup index. No tree operation recurses on
//! the caller's stack, including destruction of accepted or rejected metadata.

use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Index, IndexMut};

/// An actual lexical JSON number. An object or string cannot construct one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Number(String);

impl Number {
    pub(crate) fn from_validated_token(token: &str) -> Self {
        Self(token.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
    pub fn is_integer(&self) -> bool {
        !self.0.bytes().any(|b| matches!(b, b'.' | b'e' | b'E'))
    }
    pub fn as_u64(&self) -> Option<u64> {
        self.is_integer().then(|| self.0.parse().ok()).flatten()
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A duplicate-free JSON object with original insertion order.
#[derive(Default)]
pub struct Object {
    entries: Vec<(String, Value)>,
    positions: BTreeMap<String, usize>,
}

impl Object {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    pub fn contains_key(&self, key: &str) -> bool {
        self.positions.contains_key(key)
    }
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.positions.get(key).map(|&index| &self.entries[index].1)
    }
    pub fn get_mut(&mut self, key: &str) -> Option<&mut Value> {
        self.positions.get(key).map(|&index| &mut self.entries[index].1)
    }
    /// Replace an existing key in place; the strict parser rejects duplicates
    /// before insertion. Programmatic diagnostic edits preserve key order.
    pub fn insert(&mut self, key: String, value: Value) -> Option<Value> {
        if let Some(&index) = self.positions.get(&key) {
            return Some(std::mem::replace(&mut self.entries[index].1, value));
        }
        self.positions.insert(key.clone(), self.entries.len());
        self.entries.push((key, value));
        None
    }
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.entries.iter())
    }
    pub fn keys(&self) -> impl DoubleEndedIterator<Item = &String> {
        self.entries.iter().map(|(key, _)| key)
    }
}

pub struct Iter<'a>(std::slice::Iter<'a, (String, Value)>);
impl<'a> Iterator for Iter<'a> {
    type Item = (&'a String, &'a Value);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(key, value)| (key, value))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl DoubleEndedIterator for Iter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(key, value)| (key, value))
    }
}
impl ExactSizeIterator for Iter<'_> {}
impl<'a> IntoIterator for &'a Object {
    type Item = (&'a String, &'a Value);
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Native JSON values. This data model carries no writer or proof authority.
#[derive(Default)]
pub enum Value {
    #[default]
    Null,
    Bool(bool),
    Number(Number),
    String(String),
    Array(Vec<Value>),
    Object(Object),
}

impl Value {
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }
    pub fn is_object(&self) -> bool {
        matches!(self, Self::Object(_))
    }
    pub fn is_string(&self) -> bool {
        matches!(self, Self::String(_))
    }
    pub fn is_number(&self) -> bool {
        matches!(self, Self::Number(_))
    }
    pub fn as_str(&self) -> Option<&str> {
        if let Self::String(value) = self { Some(value) } else { None }
    }
    pub fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(value) = self { Some(*value) } else { None }
    }
    pub fn as_u64(&self) -> Option<u64> {
        if let Self::Number(value) = self { value.as_u64() } else { None }
    }
    pub fn as_array(&self) -> Option<&Vec<Value>> {
        if let Self::Array(value) = self { Some(value) } else { None }
    }
    pub fn as_object(&self) -> Option<&Object> {
        if let Self::Object(value) = self { Some(value) } else { None }
    }
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.as_object().and_then(|value| value.get(key))
    }
    pub fn is_empty_array(&self) -> bool {
        self.as_array().is_some_and(Vec::is_empty)
    }
}

impl Drop for Value {
    fn drop(&mut self) {
        fn detach(value: &mut Value, pending: &mut Vec<Value>) {
            match value {
                Value::Array(values) => pending.append(values),
                Value::Object(values) => {
                    pending.extend(std::mem::take(&mut values.entries).into_iter().map(|(_, v)| v));
                }
                _ => {}
            }
        }
        let mut pending = Vec::new();
        detach(self, &mut pending);
        while let Some(mut value) = pending.pop() {
            detach(&mut value, &mut pending);
            // Its children are detached; its own Drop sees an empty container.
        }
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        enum Copy<'a> {
            Value(&'a Value),
            Array(usize),
            Object(&'a Object),
        }
        let mut pending = vec![Copy::Value(self)];
        let mut done = Vec::new();
        while let Some(step) = pending.pop() {
            match step {
                Copy::Value(value) => match value {
                    Self::Null => done.push(Self::Null),
                    Self::Bool(value) => done.push(Self::Bool(*value)),
                    Self::Number(value) => done.push(Self::Number(value.clone())),
                    Self::String(value) => done.push(Self::String(value.clone())),
                    Self::Array(values) => {
                        pending.push(Copy::Array(values.len()));
                        pending.extend(values.iter().rev().map(Copy::Value));
                    }
                    Self::Object(values) => {
                        pending.push(Copy::Object(values));
                        pending.extend(values.iter().rev().map(|(_, value)| Copy::Value(value)));
                    }
                },
                Copy::Array(count) => {
                    let values = done.split_off(done.len() - count);
                    done.push(Self::Array(values));
                }
                Copy::Object(original) => {
                    let values = done.split_off(done.len() - original.len());
                    let mut object = Object::new();
                    for ((key, _), value) in original.iter().zip(values) {
                        object.insert(key.clone(), value);
                    }
                    done.push(Self::Object(object));
                }
            }
        }
        done.pop().expect("cloned root value")
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            match (left, right) {
                (Self::Null, Self::Null) => {}
                (Self::Bool(a), Self::Bool(b)) if a == b => {}
                (Self::Number(a), Self::Number(b)) if a == b => {}
                (Self::String(a), Self::String(b)) if a == b => {}
                (Self::Array(a), Self::Array(b)) if a.len() == b.len() => {
                    pending.extend(a.iter().zip(b))
                }
                (Self::Object(a), Self::Object(b)) if a.len() == b.len() => {
                    for (key, value) in a {
                        let Some(other) = b.get(key) else { return false };
                        pending.push((value, other));
                    }
                }
                _ => return false,
            }
        }
        true
    }
}
impl Eq for Value {}

impl PartialEq<str> for Value {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == Some(other)
    }
}
impl PartialEq<&str> for Value {
    fn eq(&self, other: &&str) -> bool {
        self == *other
    }
}
impl PartialEq<bool> for Value {
    fn eq(&self, other: &bool) -> bool {
        self.as_bool() == Some(*other)
    }
}
impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&crate::json::encode(self, false))
    }
}
impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
impl Index<&str> for Value {
    type Output = Value;
    fn index(&self, key: &str) -> &Self::Output {
        static NULL: Value = Value::Null;
        self.get(key).unwrap_or(&NULL)
    }
}
impl Index<usize> for Value {
    type Output = Value;
    fn index(&self, index: usize) -> &Self::Output {
        static NULL: Value = Value::Null;
        self.as_array().and_then(|values| values.get(index)).unwrap_or(&NULL)
    }
}
impl IndexMut<&str> for Value {
    fn index_mut(&mut self, key: &str) -> &mut Self::Output {
        if self.is_null() {
            *self = Self::Object(Object::new());
        }
        let Self::Object(values) = self else { panic!("indexed value is not an object") };
        if !values.contains_key(key) {
            values.insert(key.into(), Self::Null);
        }
        values.get_mut(key).expect("inserted object key")
    }
}
