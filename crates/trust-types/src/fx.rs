// Trust: Deterministic hash collections for compilation reproducibility
//
// Re-exports `rustc-hash` based types matching the compiler's `rustc_data_structures::fx`.
// Use these instead of `std::collections::HashMap/HashSet` to ensure deterministic
// hashing across compilation runs.
//
// - `FxHashMap`/`FxHashSet`: Deterministic hash, unordered iteration.
//   Use for lookup-only maps where iteration order does not affect output.
//
// - `FxIndexMap`/`FxIndexSet`: Deterministic hash + insertion-order iteration.
//   Use when iteration order matters (output generation, VC ordering, etc.)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet, FxHasher};

/// Deterministic insertion-ordered map (FxHash + IndexMap).
pub type FxIndexMap<K, V> = indexmap::IndexMap<K, V, FxBuildHasher>;

/// Deterministic insertion-ordered set (FxHash + IndexSet).
pub type FxIndexSet<V> = indexmap::IndexSet<V, FxBuildHasher>;
