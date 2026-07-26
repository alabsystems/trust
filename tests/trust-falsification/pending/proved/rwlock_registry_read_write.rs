// T1 regression (ffi-name-collision over-refutation, 2026-07-06): method calls
// named `read`/`write` on std::sync::RwLock must NOT bind the POSIX read(2)/
// write(2) FFI summaries by bare terminal name. ffi_vcgen::is_extern_call's
// Pattern 3 matched the callee path's LAST `::`-segment against the builtin
// summary table, so `std::sync::RwLock::<T>::write` bound builtin_write() —
// demanding an fd-range on a lock acquisition and refuting zero-unsafe,
// zero-FFI registry code (38 obligations in aterm-types registry.rs).
// `is_foreign` (tcx.is_foreign_item) is the authoritative FFI signal; a
// qualified Rust path must never route into the FFI lane on name alone.
// This file must PROVE (exit 0). Flips RED if the last-segment binding returns.
#![crate_type = "lib"]

use std::collections::HashMap;
use std::sync::{PoisonError, RwLock};

pub struct Registry {
    domains: RwLock<HashMap<u32, u32>>,
}

impl Registry {
    #[must_use]
    pub fn new() -> Self {
        Self {
            domains: RwLock::new(HashMap::new()),
        }
    }

    /// `.write()` — terminal path segment collides with POSIX write(2).
    pub fn register(&self, key: u32, value: u32) {
        let mut guard = self
            .domains
            .write()
            .unwrap_or_else(PoisonError::into_inner);
        guard.insert(key, value);
    }

    /// `.read()` — terminal path segment collides with POSIX read(2).
    #[must_use]
    pub fn get(&self, key: u32) -> Option<u32> {
        let guard = self.domains.read().unwrap_or_else(PoisonError::into_inner);
        guard.get(&key).copied()
    }
}

impl Default for Registry {
    fn default() -> Self {
        Self::new()
    }
}
