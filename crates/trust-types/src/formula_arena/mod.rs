// trust-types/formula_arena/mod.rs: Arena-allocated formula representation
//
// Replaces Box<Formula> heap allocations with index-based
// arena allocation. Formula trees are built once and read many times,
// making arena allocation ideal: O(1) bump allocation, contiguous memory
// layout for cache-friendly traversal, and copy-free sharing via indices.
//
// The existing `Formula` enum is preserved for backward compatibility.
// `FormulaArena` is a parallel representation for performance-critical paths.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod arena;
mod builder;
mod query;
mod structural;
mod transform;
mod types;

#[cfg(test)]
mod tests;

// Re-export all public items at the module root for backward compatibility.
pub use arena::{FormulaArena, HashConsMetrics};
pub use types::{FormulaNode, FormulaRef};
