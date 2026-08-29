// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The table representation: an ordered string-keyed map.
//!
//! # Why this is a newtype and not a bare `BTreeMap`
//!
//! The incumbent spells a table `toml::map::Map<String, Value>` and re-exports
//! it as `toml::Table`. Consumers in this tree name `toml::Table` in function
//! signatures (`crates/trust-deps/src/lib.rs:1600,1613`), so the name has to
//! exist and has to be a distinct type they can name. A `pub type Table =
//! BTreeMap<String, Value>` would also compile today, but it would export
//! `BTreeMap`'s entire surface as this crate's public API and make any later
//! change of backing store a breaking change for consumers.
//!
//! # Iteration order is part of the contract
//!
//! The backing store is [`BTreeMap`], so iteration is **key-sorted**, always.
//!
//! This matches the incumbent as this workspace actually resolves it. The
//! incumbent's ordering is conditional: `toml`'s `preserve_order` feature swaps
//! its map for an insertion-ordered `IndexMap`. Measured across every manifest
//! in this repository, `preserve_order` is enabled **nowhere** for `toml`
//! (`crates/Cargo.toml:468` takes `toml = "0.8"` with default features, which
//! resolve to `['default', 'display', 'parse']`), so the incumbent is
//! BTreeMap-backed here too and the two agree.
//!
//! The conditionality is not hypothetical elsewhere: the sibling
//! `first-party/trust-mc/trust-mc-driver/Cargo.toml:30` enables
//! `preserve_order` on `serde_json`, and Cargo unifies features across a
//! workspace, so the same `crates/` code genuinely builds both ways in the root
//! lockfile — which is exactly why `crates/trust-types/src/digest.rs` carries a
//! `canonicalize_json_in_place`. **This crate takes the unconditional branch on
//! purpose**: a digest taken over a `trust_toml::Table` cannot change meaning
//! because some unrelated crate turned a feature on. If you ever add a
//! `preserve_order` feature here, you reintroduce that hazard.

use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::collections::btree_map;
use std::fmt;
use std::iter::FromIterator;
use std::ops::Index;

/// A string-keyed map with key-sorted iteration. See the module docs.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Map<K, V> {
    inner: BTreeMap<K, V>,
}

impl<K, V> Map<K, V> {
    /// An empty map.
    #[must_use]
    pub const fn new() -> Self {
        Self { inner: BTreeMap::new() }
    }

    /// Number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Whether the map holds no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Entries in key order.
    pub fn iter(&self) -> btree_map::Iter<'_, K, V> {
        self.inner.iter()
    }

    /// Entries in key order, values mutable.
    pub fn iter_mut(&mut self) -> btree_map::IterMut<'_, K, V> {
        self.inner.iter_mut()
    }

    /// Keys in order.
    pub fn keys(&self) -> btree_map::Keys<'_, K, V> {
        self.inner.keys()
    }

    /// Values in key order.
    pub fn values(&self) -> btree_map::Values<'_, K, V> {
        self.inner.values()
    }

    /// Drop every entry.
    pub fn clear(&mut self) {
        self.inner.clear();
    }
}

impl<K: Ord, V> Map<K, V> {
    /// The value for `key`, or `None`.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.get(key)
    }

    /// The value for `key`, mutable.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.get_mut(key)
    }

    /// Whether `key` is present.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.contains_key(key)
    }

    /// Insert, returning any displaced value.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.inner.insert(key, value)
    }

    /// Remove, returning the value if it was present.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.inner.remove(key)
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for Map<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Print like a map literal, not like `Map { inner: {...} }`. Consumers
        // format values with `{:?}` in error paths (`trust-deps/src/lib.rs:1643`)
        // and the newtype wrapper is noise there.
        self.inner.fmt(f)
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for Map<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self { inner: BTreeMap::from_iter(iter) }
    }
}

impl<K: Ord, V> Extend<(K, V)> for Map<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        self.inner.extend(iter);
    }
}

impl<K, V> IntoIterator for Map<K, V> {
    type Item = (K, V);
    type IntoIter = btree_map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a Map<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = btree_map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut Map<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = btree_map::IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter_mut()
    }
}

impl<K, Q, V> Index<&Q> for Map<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord + ?Sized + fmt::Debug,
{
    type Output = V;

    /// # Panics
    ///
    /// If `key` is absent — matching the incumbent, and matching `BTreeMap`.
    fn index(&self, key: &Q) -> &V {
        self.get(key).unwrap_or_else(|| panic!("no entry found for key {key:?}"))
    }
}

// ---------------------------------------------------------------------------
// serde
// ---------------------------------------------------------------------------
//
// The incumbent's `Map` implements both directions, so a consumer can name
// `toml::Table` as a field of a `#[derive(Serialize, Deserialize)]` struct.
// Under a Cargo dependency rename that has to keep compiling, so both are here.
// Neither is derived: this crate does not depend on `serde_derive`.

impl<K: serde::Serialize, V: serde::Serialize> serde::Serialize for Map<K, V> {
    /// As a map, in this map's iteration order — which is key order. See the
    /// module docs: that order is part of the contract, not an accident of the
    /// backing store.
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap as _;
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (key, value) in self {
            map.serialize_entry(key, value)?;
        }
        map.end()
    }
}

impl<'de, K, V> serde::Deserialize<'de> for Map<K, V>
where
    K: Ord + serde::Deserialize<'de>,
    V: serde::Deserialize<'de>,
{
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(MapVisitor(std::marker::PhantomData))
    }
}

struct MapVisitor<K, V>(std::marker::PhantomData<fn() -> (K, V)>);

impl<'de, K, V> serde::de::Visitor<'de> for MapVisitor<K, V>
where
    K: Ord + serde::Deserialize<'de>,
    V: serde::Deserialize<'de>,
{
    type Value = Map<K, V>;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a table")
    }

    fn visit_map<A: serde::de::MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut map = Map::new();
        // A duplicate key overwrites, matching `BTreeMap::insert` and the
        // incumbent. This crate's own parser rejects a duplicate key before it
        // ever reaches here (TOML forbids redefining one), so this arm is only
        // reachable when a `Map` is built from some other format.
        while let Some((key, value)) = access.next_entry()? {
            map.insert(key, value);
        }
        Ok(map)
    }
}
