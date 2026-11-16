//! Type-erased per-owner memo slots that live and die with a context (D-VC-6).
//!
//! trust-types depends on no trust-ir and its ay bindings are optional, so it cannot name
//! the lowering memo's or the certify memo's types. Each owner keeps its own type in its
//! slot: trust-vcgen its block-def recipe counts (from C08), the compiler its row-key
//! identity oracle's context (from C09), trust-router the lowering memo (from C10),
//! trust-certify the certify memo (from C10c). A slot is created on first
//! use and dropped with the context, never earlier and never shared with another context.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::any::Any;
use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Mutex, PoisonError};

/// Who owns a memo slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum MemoSlot {
    /// trust-vcgen's block-def recipe counts: the rows that were block-def conjunctions,
    /// and which became Spine rows (C08).
    Recipes,
    /// trust-router's lowering memo (C10).
    Lowering,
    /// trust-certify's certify memo (C10c).
    Certify,
    /// The compiler's row-key identity oracle: the context its exact sites' keys of this
    /// body are identified in (C09, `rustc_mir_transform`'s `trust_verify::row_key`).
    RowKeys,
}

/// The memo slots of one context, behind one lock (L4-CTX-1).
#[derive(Default)]
pub struct ContextMemos {
    slots: Mutex<BTreeMap<MemoSlot, Box<dyn Any + Send>>>,
}

impl fmt::Debug for ContextMemos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slots = self.slots.lock().unwrap_or_else(PoisonError::into_inner);
        f.debug_struct("ContextMemos").field("slots", &slots.keys().collect::<Vec<_>>()).finish()
    }
}

impl ContextMemos {
    /// Run `work` on `slot`'s value, created with `T::default()` on first use. `None`, and
    /// `work` does not run, when the slot already holds a value of another type.
    pub fn with<T, R>(&self, slot: MemoSlot, work: impl FnOnce(&mut T) -> R) -> Option<R>
    where
        T: Any + Send + Default,
    {
        let mut slots = self.slots.lock().unwrap_or_else(PoisonError::into_inner);
        let value = slots.entry(slot).or_insert_with(|| Box::new(T::default()));
        value.downcast_mut::<T>().map(work)
    }

    /// Whether `slot` holds a value.
    #[must_use]
    pub fn contains(&self, slot: MemoSlot) -> bool {
        self.slots.lock().unwrap_or_else(PoisonError::into_inner).contains_key(&slot)
    }
}
