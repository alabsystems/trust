// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A JSON object: `String` keys to [`Value`]s.
//!
//! # The ordering contract, which is load-bearing
//!
//! The incumbent has two backings selected by the `preserve_order` feature:
//! `BTreeMap` (key-sorted iteration) without it, `IndexMap` (insertion order)
//! with it. `crates/Cargo.toml` enables it nowhere, but the ROOT workspace does
//! — `first-party/trust-mc/trust-mc-driver/Cargo.toml` asks for it, and Cargo
//! unifies features across a workspace — so the same crates genuinely build
//! both ways, and `crates/trust-types/src/digest.rs:11-25` documents that a
//! `Value`-derived digest would otherwise differ between the two lockfiles.
//!
//! The defence already in the tree is
//! `trust_types::digest::canonicalize_json_in_place`, which rebuilds every
//! object in key order so both backings emit identical bytes. It relies on a
//! property this map must therefore keep:
//!
//! > inserting keys in sorted order yields sorted iteration.
//!
//! A `BTreeMap` satisfies it unconditionally, which is why that is the backing
//! chosen here, and why there is no `preserve_order` switch to get wrong.

use crate::value::Value;
use core::fmt::{self, Debug};
use core::ops::{Index, IndexMut};
use std::collections::{BTreeMap, btree_map};

/// Represents a JSON key/value map.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct Map<K, V> {
    map: BTreeMap<K, V>,
}

impl Map<String, Value> {
    #[must_use]
    pub fn new() -> Self {
        Map {
            map: BTreeMap::new(),
        }
    }

    /// Provided for source compatibility with the incumbent. A `BTreeMap` has
    /// no capacity, so the hint is ignored.
    #[must_use]
    pub fn with_capacity(_capacity: usize) -> Self {
        Map::new()
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&Value>
    where
        String: core::borrow::Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.map.get(key)
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        String: core::borrow::Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.map.contains_key(key)
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut Value>
    where
        String: core::borrow::Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.map.get_mut(key)
    }

    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&String, &Value)>
    where
        String: core::borrow::Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.map.get_key_value(key)
    }

    pub fn insert(&mut self, k: String, v: Value) -> Option<Value> {
        self.map.insert(k, v)
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<Value>
    where
        String: core::borrow::Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.map.remove(key)
    }

    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(String, Value)>
    where
        String: core::borrow::Borrow<Q>,
        Q: ?Sized + Ord,
    {
        self.map.remove_entry(key)
    }

    pub fn append(&mut self, other: &mut Self) {
        self.map.append(&mut other.map);
    }

    pub fn entry<S>(&mut self, key: S) -> btree_map::Entry<'_, String, Value>
    where
        S: Into<String>,
    {
        self.map.entry(key.into())
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn iter(&self) -> btree_map::Iter<'_, String, Value> {
        self.map.iter()
    }

    pub fn iter_mut(&mut self) -> btree_map::IterMut<'_, String, Value> {
        self.map.iter_mut()
    }

    pub fn keys(&self) -> btree_map::Keys<'_, String, Value> {
        self.map.keys()
    }

    pub fn values(&self) -> btree_map::Values<'_, String, Value> {
        self.map.values()
    }

    pub fn values_mut(&mut self) -> btree_map::ValuesMut<'_, String, Value> {
        self.map.values_mut()
    }

    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&String, &mut Value) -> bool,
    {
        self.map.retain(f);
    }
}

impl Debug for Map<String, Value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.map.fmt(f)
    }
}

impl<Q> Index<&Q> for Map<String, Value>
where
    String: core::borrow::Borrow<Q>,
    Q: ?Sized + Ord + fmt::Display,
{
    type Output = Value;
    fn index(&self, index: &Q) -> &Value {
        self.map
            .get(index)
            .unwrap_or_else(|| panic!("no entry found for key {index}"))
    }
}

impl<Q> IndexMut<&Q> for Map<String, Value>
where
    String: core::borrow::Borrow<Q>,
    Q: ?Sized + Ord + fmt::Display,
{
    fn index_mut(&mut self, index: &Q) -> &mut Value {
        self.map
            .get_mut(index)
            .unwrap_or_else(|| panic!("no entry found for key {index}"))
    }
}

impl<'a> IntoIterator for &'a Map<String, Value> {
    type Item = (&'a String, &'a Value);
    type IntoIter = btree_map::Iter<'a, String, Value>;
    fn into_iter(self) -> Self::IntoIter {
        self.map.iter()
    }
}

impl<'a> IntoIterator for &'a mut Map<String, Value> {
    type Item = (&'a String, &'a mut Value);
    type IntoIter = btree_map::IterMut<'a, String, Value>;
    fn into_iter(self) -> Self::IntoIter {
        self.map.iter_mut()
    }
}

impl IntoIterator for Map<String, Value> {
    type Item = (String, Value);
    type IntoIter = btree_map::IntoIter<String, Value>;
    fn into_iter(self) -> Self::IntoIter {
        self.map.into_iter()
    }
}

impl FromIterator<(String, Value)> for Map<String, Value> {
    fn from_iter<T: IntoIterator<Item = (String, Value)>>(iter: T) -> Self {
        Map {
            map: BTreeMap::from_iter(iter),
        }
    }
}

impl Extend<(String, Value)> for Map<String, Value> {
    fn extend<T: IntoIterator<Item = (String, Value)>>(&mut self, iter: T) {
        self.map.extend(iter);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iteration_is_key_sorted_regardless_of_insertion_order() {
        let mut m = Map::new();
        for k in ["z", "a", "m", "b"] {
            m.insert(k.to_owned(), Value::Null);
        }
        let ks: Vec<&str> = m.keys().map(String::as_str).collect();
        assert_eq!(ks, ["a", "b", "m", "z"]);
    }

    #[test]
    fn sorted_insertion_stays_sorted() {
        // The property `canonicalize_json_in_place` relies on.
        let mut m = Map::new();
        for k in ["a", "b", "m", "z"] {
            m.insert(k.to_owned(), Value::Null);
        }
        let ks: Vec<&str> = m.keys().map(String::as_str).collect();
        assert_eq!(ks, ["a", "b", "m", "z"]);
    }
}
