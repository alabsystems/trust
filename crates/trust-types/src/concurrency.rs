// trust-types/concurrency.rs: thread-model types for happens-before analysis
//
// The thread-model vocabulary trust-vcgen's happens-before lane builds on
// (`MemoryLocationId`, `HappensBeforeEdgeKind`, `ConcurrencyPoint`), and the
// spelled fallback of std thread-spawn recognition. The spawn census itself
// lives in the compiler (trust-mir-extract's MIR adapter over trust-ir's
// reachability engine, design 2026-09-29-spawn-census-by-construction).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::BlockId;

// ---------------------------------------------------------------------------
// Thread model types for happens-before analysis
// ---------------------------------------------------------------------------

/// Canonical identity for a memory location accessed by multiple threads.
///
/// Used to determine whether two accesses in different threads refer to the
/// same memory location. Conservative: unknown locations may-alias with
/// anything of the same type.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryLocationId {
    /// A global `static` variable, identified by its def_path.
    Global { def_path: String },
    /// A direct `&AtomicT` function parameter.
    Parameter { function: String, param_index: usize },
    /// An `Arc<T>` captured by a spawn closure, traced back to its allocation.
    ArcCapture { source_def_path: String },
    /// Could not determine the memory location identity.
    Unknown { description: String },
}

impl std::fmt::Display for MemoryLocationId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemoryLocationId::Global { def_path } => write!(f, "global:{def_path}"),
            MemoryLocationId::Parameter { function, param_index } => {
                write!(f, "param:{function}[{param_index}]")
            }
            MemoryLocationId::ArcCapture { source_def_path } => {
                write!(f, "arc:{source_def_path}")
            }
            MemoryLocationId::Unknown { description } => write!(f, "unknown:{description}"),
        }
    }
}

/// The kind of happens-before edge in the concurrency graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HappensBeforeEdgeKind {
    /// Intra-thread program order: sequential statements within one thread.
    ProgramOrder,
    /// Thread spawn: the spawn call HB the first operation of the child thread.
    Spawn,
    /// Thread join: the last operation of the child thread HB the join return.
    Join,
    /// Release-acquire synchronization on an atomic variable.
    SyncWith,
    /// Lock acquisition after an unlock on the same mutex.
    LockUnlock,
    /// Atomic fence-based synchronization.
    Fence,
}

/// A program point: a specific location in a specific function and thread.
///
/// This is the node type in the happens-before graph. Two program points
/// are ordered if there exists a path of HB edges between them.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ConcurrencyPoint {
    /// The function containing this point.
    pub function: String,
    /// The basic block within the function.
    pub block: BlockId,
    /// The thread this point executes in (empty string = main thread).
    pub thread_id: String,
}

impl ConcurrencyPoint {
    /// Create a new program point.
    #[must_use]
    pub fn new(function: impl Into<String>, block: BlockId, thread_id: impl Into<String>) -> Self {
        Self { function: function.into(), block, thread_id: thread_id.into() }
    }
}

impl std::fmt::Display for ConcurrencyPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}::bb{}@{}", self.function, self.block.0, self.thread_id)
    }
}

/// Spelled std thread-creation callee paths, the FALLBACK half of spawn
/// recognition. The primary half is the compiler-minted
/// [`crate::CalleeKey`] tag ([`crate::STD_THREAD_SPAWN_ITEMS`]), minted from
/// std's diagnostic items by the same classifier as the compiler's spawn
/// census; see [`call_is_std_thread_spawn`]. These strings serve bodies with no
/// key (synthetic MIR, pre-carrier artifacts) and can only ADD a match.
///
/// The first block is what the extractor ACTUALLY renders (untrimmed
/// `def_path_str_with_args`), measured 2026-09-28 with `-Ztrust-dump=mir-only`
/// on `trustc 1.99.0-dev (56c474d6e)`: before that measurement this table
/// named none of the three `Builder` spellings, so a `Builder::spawn`,
/// `spawn_unchecked` or `spawn_scoped` call with no callee key reached the
/// router unrefused. The second block keeps the re-export/source spellings and
/// older renderings. A row matches the path exactly or followed by a turbofish
/// (`::<`), never as a substring: `my::std::thread::spawn` and
/// `std::thread::spawn_worker` are not spawns.
pub const THREAD_SPAWN_PATTERNS: &[&str] = &[
    // Measured extractor renderings.
    "std::thread::functions::spawn",
    "std::thread::builder::Builder::spawn",
    "std::thread::builder::Builder::spawn_unchecked",
    "std::thread::scoped::Scope::<'_, '_>::spawn",
    "std::thread::scoped::<impl std::thread::builder::Builder>::spawn_scoped",
    // Re-export / source / older renderings.
    "std::thread::spawn",
    "std::thread::Builder::spawn",
    "std::thread::Builder::spawn_unchecked",
    "std::thread::builder::<impl Builder>::spawn",
    "std::thread::builder::<impl Builder>::spawn_unchecked",
    "std::thread::Builder::spawn_scoped",
    "std::thread::Scope::spawn",
    "std::thread::Scope::<'_, '_>::spawn",
    "std::thread::scoped::<impl Builder>::spawn_scoped",
];

/// Check whether a rendered MIR Call func path is a std thread spawn: an exact
/// [`THREAD_SPAWN_PATTERNS`] row, optionally followed by a turbofish. This is
/// the spelled fallback only; prefer [`call_is_std_thread_spawn`], which also
/// reads the compiler-minted callee key.
#[must_use]
pub fn is_thread_spawn(func_path: &str) -> bool {
    THREAD_SPAWN_PATTERNS.iter().any(|base| {
        func_path == *base
            || func_path.strip_prefix(base).is_some_and(|suffix| suffix.starts_with("::<"))
    })
}

/// Whether a call is a std thread spawn: its compiler-minted key carries a
/// [`crate::STD_THREAD_SPAWN_ITEMS`] tag (the diagnostic-item verdict), or its
/// rendered path is a spelled [`THREAD_SPAWN_PATTERNS`] row. For refusal and
/// happens-before bookkeeping only; never proof authority.
#[must_use]
pub fn call_is_std_thread_spawn(func_path: &str, key: Option<&crate::CalleeKey>) -> bool {
    crate::CalleeKey::opt_is_one_of(key, crate::STD_THREAD_SPAWN_ITEMS)
        || is_thread_spawn(func_path)
}

/// How many causes the SC-8 row disclosure ([`sc8_row_disclosure`]) names before it counts
/// the rest.
pub const SC8_ROW_NAMED_CAUSES: usize = 2;
/// The opener of the SC-8 back-reference a spawn-census row carries when the unclosed
/// pools decide it (SC-8 (c), trust-mir-extract's `unclosed_row_suffix`):
/// [`sc8_row_disclosure`] writes it, then the first [`SC8_ROW_NAMED_CAUSES`] causes, a
/// count of the rest, and [`SC8_ROW_DISCLOSURE_CLOSE`]. The census lists the causes in the
/// order of a hash of their principals' types, so which ones a row names, and in what
/// order, follows the `StableCrateId`s of the crates those types name. The elision audit
/// therefore reads a disclosure by these constants and compares only its count of causes
/// (`audit_ledger::build_independent`; T3 L4, L4-AUDIT-7).
pub const SC8_ROW_DISCLOSURE_OPEN: &str = " [pools unclosed because: ";
/// The separator between two causes of the SC-8 row disclosure, and before its count of
/// the causes it does not name (`+<n> more`).
pub const SC8_ROW_DISCLOSURE_SEPARATOR: &str = "; ";
/// The end of the SC-8 row disclosure ([`SC8_ROW_DISCLOSURE_OPEN`]).
pub const SC8_ROW_DISCLOSURE_CLOSE: &str = "; see the crate's SC-8 root-cause note]";

/// The SC-8 row disclosure ([`SC8_ROW_DISCLOSURE_OPEN`]) of `causes`: the first
/// [`SC8_ROW_NAMED_CAUSES`] of them, then `+<n> more` when there are more.
#[must_use]
pub fn sc8_row_disclosure(causes: &[String]) -> String {
    let named = causes
        .iter()
        .take(SC8_ROW_NAMED_CAUSES)
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join(SC8_ROW_DISCLOSURE_SEPARATOR);
    let more = causes.len().saturating_sub(SC8_ROW_NAMED_CAUSES);
    let more = if more > 0 {
        format!("{SC8_ROW_DISCLOSURE_SEPARATOR}+{more} more")
    } else {
        String::new()
    };
    format!("{SC8_ROW_DISCLOSURE_OPEN}{named}{more}{SC8_ROW_DISCLOSURE_CLOSE}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_sc8_row_disclosure_is_the_census_spelling() {
        // The bytes trust-mir-extract wrote before the spelling moved here (T3 L4, C06a).
        let causes = |n: usize| (0..n).map(|i| format!("cause {i}")).collect::<Vec<_>>();
        assert_eq!(
            sc8_row_disclosure(&causes(1)),
            " [pools unclosed because: cause 0; see the crate's SC-8 root-cause note]"
        );
        assert_eq!(
            sc8_row_disclosure(&causes(2)),
            " [pools unclosed because: cause 0; cause 1; see the crate's SC-8 root-cause note]"
        );
        assert_eq!(
            sc8_row_disclosure(&causes(5)),
            " [pools unclosed because: cause 0; cause 1; +3 more; see the crate's SC-8 \
             root-cause note]"
        );
    }

    #[test]
    fn test_is_thread_spawn() {
        // The spellings the extractor renders today (measured; see
        // `THREAD_SPAWN_PATTERNS`), with their turbofish.
        for measured in [
            "std::thread::functions::spawn::<{closure@p4.rs:1:41: 1:43}, ()>",
            "std::thread::builder::Builder::spawn::<{closure@p4.rs:2:56: 2:58}, ()>",
            "std::thread::builder::Builder::spawn_unchecked::<{closure@p4.rs:3:75: 3:77}, ()>",
            "std::thread::scoped::Scope::<'_, '_>::spawn::<{closure@p4.rs:4:47: 4:49}, ()>",
            "std::thread::scoped::<impl std::thread::builder::Builder>::spawn_scoped::<'_, {closure@p4.rs:5:91: 5:93}, ()>",
        ] {
            assert!(is_thread_spawn(measured), "{measured}");
        }
        for near_miss in [
            "std::thread::builder::Builder::spawn_worker",
            "my::std::thread::spawn",
            "std::thread::spawnx",
            "std::thread::scoped::<impl std::thread::builder::Builder>::spawn_scoped_helper",
        ] {
            assert!(!is_thread_spawn(near_miss), "{near_miss}");
        }
        assert!(is_thread_spawn("std::thread::spawn"));
        assert!(is_thread_spawn("std::thread::spawn::<closure>"));
        assert!(is_thread_spawn("std::thread::Builder::spawn"));
        assert!(!is_thread_spawn("tokio::spawn"));
        assert!(!is_thread_spawn("std::sync::Mutex::lock"));
        assert!(!is_thread_spawn("my_module::spawn_worker"));
    }

    #[test]
    fn test_memory_location_id_display() {
        let global = MemoryLocationId::Global { def_path: "my_mod::COUNTER".to_string() };
        assert_eq!(global.to_string(), "global:my_mod::COUNTER");

        let param = MemoryLocationId::Parameter { function: "worker".to_string(), param_index: 0 };
        assert_eq!(param.to_string(), "param:worker[0]");

        let arc = MemoryLocationId::ArcCapture { source_def_path: "main::data".to_string() };
        assert_eq!(arc.to_string(), "arc:main::data");

        let unknown = MemoryLocationId::Unknown { description: "indirect".to_string() };
        assert_eq!(unknown.to_string(), "unknown:indirect");
    }

    #[test]
    fn test_memory_location_id_eq_hash() {
        use crate::fx::FxHashSet;
        let a = MemoryLocationId::Global { def_path: "x".to_string() };
        let b = MemoryLocationId::Global { def_path: "x".to_string() };
        let c = MemoryLocationId::Global { def_path: "y".to_string() };

        assert_eq!(a, b);
        assert_ne!(a, c);

        let mut set = FxHashSet::default();
        set.insert(a.clone());
        set.insert(b);
        assert_eq!(set.len(), 1);
        set.insert(c);
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_program_point_display() {
        let pp = ConcurrencyPoint::new("my_fn", BlockId(3), "thread_1");
        assert_eq!(pp.to_string(), "my_fn::bb3@thread_1");
    }

    #[test]
    fn test_happens_before_edge_kind_values() {
        // Ensure all variants are distinct
        let kinds = [
            HappensBeforeEdgeKind::ProgramOrder,
            HappensBeforeEdgeKind::Spawn,
            HappensBeforeEdgeKind::Join,
            HappensBeforeEdgeKind::SyncWith,
            HappensBeforeEdgeKind::LockUnlock,
            HappensBeforeEdgeKind::Fence,
        ];
        for (i, a) in kinds.iter().enumerate() {
            for (j, b) in kinds.iter().enumerate() {
                if i == j {
                    assert_eq!(a, b);
                } else {
                    assert_ne!(a, b);
                }
            }
        }
    }
}
