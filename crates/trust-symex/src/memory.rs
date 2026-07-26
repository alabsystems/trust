// trust-symex symbolic memory model
//
// Object-based symbolic memory following KLEE's memory model
// (refs/klee/lib/Core/Executor.cpp). Tracks stack, heap, and global
// memory regions with lazy initialization for unread addresses.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use trust_types::BinOp;

use crate::state::SymbolicValue;

/// Identifies a region of memory.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryRegion {
    /// Stack-allocated memory at a given frame offset.
    Stack(u64),
    /// Heap-allocated memory with a unique allocation id and byte offset.
    Heap(u64, u64),
    /// Global/static memory identified by name.
    Global(String),
}

impl std::fmt::Display for MemoryRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Stack(offset) => write!(f, "stack[{offset}]"),
            Self::Heap(id, offset) => write!(f, "heap[{id}+{offset}]"),
            Self::Global(name) => write!(f, "global[{name}]"),
        }
    }
}

/// An address in symbolic memory: region + byte offset within that region.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MemoryAddress {
    pub region: MemoryRegion,
    pub offset: u64,
}

impl MemoryAddress {
    /// Create a new memory address.
    #[must_use]
    pub fn new(region: MemoryRegion, offset: u64) -> Self {
        Self { region, offset }
    }
}

/// Errors arising from memory operations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum MemoryError {
    /// Access to an address outside allocated bounds.
    OutOfBounds { addr: MemoryAddress, region_size: u64 },
    /// Read/write to freed memory.
    UseAfterFree { addr: MemoryAddress },
    /// Freeing memory that was already freed.
    DoubleFree { region: MemoryRegion },
    /// Reading from memory that was never written.
    UninitializedRead { addr: MemoryAddress },
    /// Freeing a region that was not heap-allocated.
    InvalidFree { region: MemoryRegion },
}

impl std::fmt::Display for MemoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfBounds { addr, region_size } => {
                write!(
                    f,
                    "out of bounds access at {}.{} (region size {region_size})",
                    addr.region, addr.offset
                )
            }
            Self::UseAfterFree { addr } => {
                write!(f, "use after free at {}.{}", addr.region, addr.offset)
            }
            Self::DoubleFree { region } => write!(f, "double free of {region}"),
            Self::UninitializedRead { addr } => {
                write!(f, "uninitialized read at {}.{}", addr.region, addr.offset)
            }
            Self::InvalidFree { region } => {
                write!(f, "invalid free of non-heap region {region}")
            }
        }
    }
}

impl std::error::Error for MemoryError {}

/// Metadata for an allocated memory object.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct AllocationMeta {
    /// Size in bytes.
    pub(crate) size: u64,
    /// Whether this allocation has been freed.
    pub(crate) freed: bool,
}

/// A snapshot of the symbolic memory state, used for path forking.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemorySnapshot {
    cells: BTreeMap<MemoryAddress, SymbolicValue>,
    allocations: BTreeMap<MemoryRegion, AllocationMeta>,
    freed_regions: BTreeSet<MemoryRegion>,
    next_alloc_id: u64,
    next_stack_offset: u64,
}

/// Symbolic memory model with region-based addressing.
///
/// Follows KLEE's object-based memory model: each allocation creates
/// a named region, and loads/stores are resolved within that region.
/// Uninitialized reads return a fresh symbolic value (lazy init).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolicMemory {
    /// Mapping from addresses to symbolic values.
    cells: BTreeMap<MemoryAddress, SymbolicValue>,
    /// Metadata for each allocated region.
    allocations: BTreeMap<MemoryRegion, AllocationMeta>,
    /// Regions that have been freed (for use-after-free detection).
    freed_regions: BTreeSet<MemoryRegion>,
    /// Counter for generating unique heap allocation IDs.
    next_alloc_id: u64,
    /// Counter for generating unique stack frame offsets.
    next_stack_offset: u64,
    /// Whether to lazily initialize unread memory (true) or error (false).
    lazy_init: bool,
}

/// Maximum byte size that fits in our i128 concrete values.
const MAX_VALUE_BYTES: u64 = 16;

/// Compute a bitmask for the given number of bytes.
///
/// Returns `None` if `size_bytes` is 0 or >= `MAX_VALUE_BYTES` (the full
/// value width), meaning no masking is needed.
fn byte_mask(size_bytes: u64) -> Option<i128> {
    if size_bytes == 0 || size_bytes >= MAX_VALUE_BYTES {
        return None;
    }
    let bits = size_bytes * 8;
    // (1 << bits) - 1: e.g. size=1 -> 0xFF, size=2 -> 0xFFFF, size=4 -> 0xFFFFFFFF
    Some((1i128 << bits) - 1)
}

/// Mask a symbolic value to the given byte width.
///
/// For concrete values the mask is applied directly. For symbolic/compound
/// values, a `BitAnd` node is emitted so the solver sees the constraint.
///
/// NOTE: When the value is symbolic and no bit-width information is available
/// at this layer, the mask expression models the constraint symbolically.
/// A full byte-array memory model would track per-byte symbolic cells
/// instead; this is a pragmatic middle ground.
// Trust: #777 -- size-aware masking for sub-object store/load
fn mask_value(value: SymbolicValue, size_bytes: u64) -> SymbolicValue {
    let Some(mask) = byte_mask(size_bytes) else {
        return value;
    };
    match &value {
        SymbolicValue::Concrete(v) => SymbolicValue::Concrete(v & mask),
        // Symbolic or compound: wrap in BitAnd so the expression tree
        // carries the size constraint for the solver.
        _ => SymbolicValue::bin_op(value, BinOp::BitAnd, SymbolicValue::Concrete(mask)),
    }
}

impl Default for SymbolicMemory {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolicMemory {
    /// Create a new empty symbolic memory with lazy initialization enabled.
    #[must_use]
    pub fn new() -> Self {
        Self {
            cells: BTreeMap::new(),
            allocations: BTreeMap::default(),
            freed_regions: BTreeSet::new(),
            next_alloc_id: 0,
            next_stack_offset: 0,
            lazy_init: true,
        }
    }

    /// Create a new symbolic memory with explicit lazy-init setting.
    #[must_use]
    pub fn with_lazy_init(lazy_init: bool) -> Self {
        Self { lazy_init, ..Self::new() }
    }

    /// Allocate a new heap region of the given size.
    ///
    /// Returns the base `MemoryRegion` for the allocation.
    pub fn allocate(&mut self, size: u64) -> MemoryRegion {
        let id = self.next_alloc_id;
        self.next_alloc_id += 1;
        let region = MemoryRegion::Heap(id, 0);
        self.allocations.insert(region.clone(), AllocationMeta { size, freed: false });
        region
    }

    /// Allocate a stack region of the given size.
    #[must_use]
    pub fn allocate_stack(&mut self, size: u64) -> MemoryRegion {
        let offset = self.next_stack_offset;
        self.next_stack_offset += size;
        let region = MemoryRegion::Stack(offset);
        self.allocations.insert(region.clone(), AllocationMeta { size, freed: false });
        region
    }

    /// Register a global memory region.
    pub fn register_global(&mut self, name: impl Into<String>, size: u64) -> MemoryRegion {
        let region = MemoryRegion::Global(name.into());
        self.allocations.insert(region.clone(), AllocationMeta { size, freed: false });
        region
    }

    /// Deallocate a heap region. Returns an error on double-free or
    /// freeing a non-heap region.
    pub fn deallocate(&mut self, region: &MemoryRegion) -> Result<(), MemoryError> {
        // Only heap regions can be deallocated.
        if !matches!(region, MemoryRegion::Heap(_, _)) {
            return Err(MemoryError::InvalidFree { region: region.clone() });
        }

        if self.freed_regions.contains(region) {
            return Err(MemoryError::DoubleFree { region: region.clone() });
        }

        if let Some(meta) = self.allocations.get_mut(region) {
            if meta.freed {
                return Err(MemoryError::DoubleFree { region: region.clone() });
            }
            meta.freed = true;
        }

        self.freed_regions.insert(region.clone());
        Ok(())
    }

    /// Store a symbolic value at the given address.
    ///
    /// If `size` is smaller than the full value width (16 bytes / i128),
    /// the stored value is masked to the requested byte width. This models
    /// partial (sub-object) stores where only the low `size` bytes are
    /// written.
    // Trust: #777 -- store now respects the size parameter
    pub fn store(
        &mut self,
        addr: &MemoryAddress,
        size: u64,
        value: SymbolicValue,
    ) -> Result<(), MemoryError> {
        // Check use-after-free.
        if self.freed_regions.contains(&addr.region) {
            return Err(MemoryError::UseAfterFree { addr: addr.clone() });
        }

        // (P1-17): Check bounds including access size, not just offset.
        // A store of `size` bytes at `offset` requires offset + size <= region_size.
        if let Some(meta) = self.allocations.get(&addr.region)
            && addr.offset.checked_add(size).is_none_or(|end| end > meta.size)
        {
            return Err(MemoryError::OutOfBounds { addr: addr.clone(), region_size: meta.size });
        }

        // Mask the value to the requested byte width so that partial
        // stores do not silently carry high bits from the source value.
        let masked = mask_value(value, size);
        self.cells.insert(addr.clone(), masked);
        Ok(())
    }

    /// Load a symbolic value from the given address.
    ///
    /// If `size` is smaller than the full value width (16 bytes / i128),
    /// the returned value is masked to extract only the low `size` bytes.
    /// This models partial (sub-object) loads.
    ///
    /// If `lazy_init` is enabled and the address has never been written,
    /// a fresh symbolic variable is created and stored. If `lazy_init`
    /// is disabled, an `UninitializedRead` error is returned.
    // Trust: #777 -- load now respects the size parameter
    pub fn load(&mut self, addr: &MemoryAddress, size: u64) -> Result<SymbolicValue, MemoryError> {
        // Check use-after-free.
        if self.freed_regions.contains(&addr.region) {
            return Err(MemoryError::UseAfterFree { addr: addr.clone() });
        }

        // (P1-17): Check bounds including access size, not just offset.
        // A load of `size` bytes at `offset` requires offset + size <= region_size.
        if let Some(meta) = self.allocations.get(&addr.region)
            && addr.offset.checked_add(size).is_none_or(|end| end > meta.size)
        {
            return Err(MemoryError::OutOfBounds { addr: addr.clone(), region_size: meta.size });
        }

        if let Some(val) = self.cells.get(addr) {
            // Mask the loaded value to the requested byte width so that
            // sub-object reads do not expose high bits from a wider store.
            return Ok(mask_value(val.clone(), size));
        }

        // Lazy initialization: create a fresh symbol for uninitialized memory.
        if self.lazy_init {
            let sym_name = format!("mem_{}_{}", addr.region, addr.offset);
            let val = SymbolicValue::Symbol(sym_name);
            self.cells.insert(addr.clone(), val.clone());
            // Mask the lazy-init symbol to the requested width.
            Ok(mask_value(val, size))
        } else {
            Err(MemoryError::UninitializedRead { addr: addr.clone() })
        }
    }

    /// Take a snapshot of the current memory state for path forking.
    #[must_use]
    pub fn snapshot(&self) -> MemorySnapshot {
        MemorySnapshot {
            cells: self.cells.clone(),
            allocations: self.allocations.clone(),
            freed_regions: self.freed_regions.clone(),
            next_alloc_id: self.next_alloc_id,
            next_stack_offset: self.next_stack_offset,
        }
    }

    /// Restore memory from a previous snapshot.
    pub fn restore(&mut self, snapshot: MemorySnapshot) {
        self.cells = snapshot.cells;
        self.allocations = snapshot.allocations;
        self.freed_regions = snapshot.freed_regions;
        self.next_alloc_id = snapshot.next_alloc_id;
        self.next_stack_offset = snapshot.next_stack_offset;
    }

    /// Returns the number of cells (address-value pairs) in memory.
    #[must_use]
    pub fn cell_count(&self) -> usize {
        self.cells.len()
    }

    /// Returns the number of active (non-freed) allocations.
    #[must_use]
    pub fn active_allocation_count(&self) -> usize {
        self.allocations.values().filter(|m| !m.freed).count()
    }

    /// Check whether a region has been freed.
    #[must_use]
    pub fn is_freed(&self, region: &MemoryRegion) -> bool {
        self.freed_regions.contains(region)
    }

    /// Iterate over all stored cells.
    pub fn cells(&self) -> impl Iterator<Item = (&MemoryAddress, &SymbolicValue)> {
        self.cells.iter()
    }
}

/// Compute the set of addresses that differ between two memory states.
#[must_use]
pub fn diff_memories(a: &SymbolicMemory, b: &SymbolicMemory) -> BTreeSet<MemoryAddress> {
    let mut differing = BTreeSet::new();

    // Addresses in a but not b, or with different values.
    for (addr, val_a) in &a.cells {
        match b.cells.get(addr) {
            Some(val_b) if val_a == val_b => {}
            _ => {
                differing.insert(addr.clone());
            }
        }
    }

    // Addresses in b but not a.
    for addr in b.cells.keys() {
        if !a.cells.contains_key(addr) {
            differing.insert(addr.clone());
        }
    }

    differing
}

#[cfg(test)]
mod tests {
    use trust_types::BinOp;

    use super::*;

    // --- Basic load/store ---

    #[test]
    fn test_memory_store_and_load() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(16);
        let addr = MemoryAddress::new(region, 0);
        // Concrete(42) fits in 4 bytes, so masking is transparent.
        mem.store(&addr, 4, SymbolicValue::Concrete(42)).expect("store should succeed");
        let val = mem.load(&addr, 4).expect("load should succeed");
        assert_eq!(val, SymbolicValue::Concrete(42));
    }

    #[test]
    fn test_memory_load_lazy_init() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        let addr = MemoryAddress::new(region, 0);
        let val = mem.load(&addr, 4).expect("lazy load should succeed");
        // With size-aware loading, the lazy-init symbol is masked to 4 bytes:
        // BinOp(Symbol("mem_..."), BitAnd, Concrete(0xFFFF_FFFF))
        match &val {
            SymbolicValue::BinOp(inner, BinOp::BitAnd, mask) => {
                match (inner.as_ref(), mask.as_ref()) {
                    (SymbolicValue::Symbol(name), SymbolicValue::Concrete(m)) => {
                        assert!(name.starts_with("mem_"));
                        assert_eq!(*m, 0xFFFF_FFFF);
                    }
                    other => panic!("expected (Symbol, Concrete mask), got {other:?}"),
                }
            }
            other => panic!("expected BinOp(Symbol, BitAnd, mask), got {other:?}"),
        }
    }

    #[test]
    fn test_memory_load_lazy_init_disabled() {
        let mut mem = SymbolicMemory::with_lazy_init(false);
        let region = mem.allocate(8);
        let addr = MemoryAddress::new(region, 0);
        let err = mem.load(&addr, 4).expect_err("should fail without lazy init");
        assert!(matches!(err, MemoryError::UninitializedRead { .. }));
    }

    #[test]
    fn test_memory_lazy_init_is_idempotent() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        let addr = MemoryAddress::new(region, 0);
        let val1 = mem.load(&addr, 4).expect("first load");
        let val2 = mem.load(&addr, 4).expect("second load");
        assert_eq!(val1, val2, "lazy-init should return same value on re-read");
    }

    // --- Allocation ---

    #[test]
    fn test_memory_allocate_unique_ids() {
        let mut mem = SymbolicMemory::new();
        let r1 = mem.allocate(8);
        let r2 = mem.allocate(16);
        assert_ne!(r1, r2);
    }

    #[test]
    fn test_memory_allocate_stack() {
        let mut mem = SymbolicMemory::new();
        let r = mem.allocate_stack(32);
        assert!(matches!(r, MemoryRegion::Stack(_)));
        assert_eq!(mem.active_allocation_count(), 1);
    }

    #[test]
    fn test_memory_register_global() {
        let mut mem = SymbolicMemory::new();
        let r = mem.register_global("MY_GLOBAL", 64);
        assert_eq!(r, MemoryRegion::Global("MY_GLOBAL".into()));
        let addr = MemoryAddress::new(r, 0);
        mem.store(&addr, 8, SymbolicValue::Concrete(100)).expect("store to global");
        let val = mem.load(&addr, 8).expect("load from global");
        assert_eq!(val, SymbolicValue::Concrete(100));
    }

    // --- Error detection ---

    #[test]
    fn test_memory_out_of_bounds_store() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(4);
        let addr = MemoryAddress::new(region, 10); // offset 10 > size 4
        let err =
            mem.store(&addr, 4, SymbolicValue::Concrete(0)).expect_err("should be out of bounds");
        assert!(matches!(err, MemoryError::OutOfBounds { region_size: 4, .. }));
    }

    #[test]
    fn test_memory_out_of_bounds_load() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(4);
        let addr = MemoryAddress::new(region, 5);
        let err = mem.load(&addr, 4).expect_err("should be out of bounds");
        assert!(matches!(err, MemoryError::OutOfBounds { .. }));
    }

    #[test]
    fn test_memory_use_after_free_store() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        mem.deallocate(&region).expect("free should succeed");
        let addr = MemoryAddress::new(region, 0);
        let err = mem
            .store(&addr, 4, SymbolicValue::Concrete(0))
            .expect_err("should detect use-after-free");
        assert!(matches!(err, MemoryError::UseAfterFree { .. }));
    }

    #[test]
    fn test_memory_use_after_free_load() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        let addr = MemoryAddress::new(region.clone(), 0);
        mem.store(&addr, 4, SymbolicValue::Concrete(1)).expect("store before free");
        mem.deallocate(&region).expect("free should succeed");
        let err = mem.load(&addr, 4).expect_err("should detect use-after-free");
        assert!(matches!(err, MemoryError::UseAfterFree { .. }));
    }

    #[test]
    fn test_memory_double_free() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        mem.deallocate(&region).expect("first free ok");
        let err = mem.deallocate(&region).expect_err("should detect double free");
        assert!(matches!(err, MemoryError::DoubleFree { .. }));
    }

    #[test]
    fn test_memory_invalid_free_stack() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate_stack(16);
        let err = mem.deallocate(&region).expect_err("should reject non-heap free");
        assert!(matches!(err, MemoryError::InvalidFree { .. }));
    }

    #[test]
    fn test_memory_invalid_free_global() {
        let mut mem = SymbolicMemory::new();
        let region = mem.register_global("g", 8);
        let err = mem.deallocate(&region).expect_err("should reject non-heap free");
        assert!(matches!(err, MemoryError::InvalidFree { .. }));
    }

    // --- Snapshot/restore ---

    #[test]
    fn test_memory_snapshot_restore() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(16);
        let addr = MemoryAddress::new(region, 0);
        mem.store(&addr, 4, SymbolicValue::Concrete(10)).expect("store");

        let snap = mem.snapshot();

        // Modify memory after snapshot.
        mem.store(&addr, 4, SymbolicValue::Concrete(20)).expect("overwrite");
        assert_eq!(mem.load(&addr, 4).expect("load"), SymbolicValue::Concrete(20));

        // Restore should bring back original value.
        mem.restore(snap);
        assert_eq!(mem.load(&addr, 4).expect("load after restore"), SymbolicValue::Concrete(10));
    }

    #[test]
    fn test_memory_snapshot_preserves_freed_state() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);

        let snap = mem.snapshot();

        mem.deallocate(&region).expect("free");
        assert!(mem.is_freed(&region));

        mem.restore(snap);
        assert!(!mem.is_freed(&region), "restore should undo free");
    }

    #[test]
    fn test_memory_snapshot_preserves_alloc_counter() {
        let mut mem = SymbolicMemory::new();
        mem.allocate(4); // id 0

        let snap = mem.snapshot();

        let r2 = mem.allocate(8); // id 1
        assert_eq!(r2, MemoryRegion::Heap(1, 0));

        mem.restore(snap);
        let r3 = mem.allocate(8); // should be id 1 again
        assert_eq!(r3, MemoryRegion::Heap(1, 0));
    }

    // --- diff_memories ---

    #[test]
    fn test_diff_memories_identical() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        let addr = MemoryAddress::new(region, 0);
        mem.store(&addr, 4, SymbolicValue::Concrete(1)).expect("store");
        let diff = diff_memories(&mem, &mem);
        assert!(diff.is_empty());
    }

    #[test]
    fn test_diff_memories_different_values() {
        let mut a = SymbolicMemory::new();
        let region_a = a.allocate(8);
        let addr = MemoryAddress::new(region_a, 0);
        a.store(&addr, 4, SymbolicValue::Concrete(1)).expect("store a");

        let mut b = SymbolicMemory::new();
        let region_b = b.allocate(8);
        let addr_b = MemoryAddress::new(region_b, 0);
        b.store(&addr_b, 4, SymbolicValue::Concrete(2)).expect("store b");

        let diff = diff_memories(&a, &b);
        assert!(!diff.is_empty());
    }

    #[test]
    fn test_diff_memories_asymmetric() {
        let mut a = SymbolicMemory::new();
        let r = a.allocate(8);
        let addr = MemoryAddress::new(r, 0);
        a.store(&addr, 4, SymbolicValue::Concrete(5)).expect("store");

        let b = SymbolicMemory::new();
        let diff = diff_memories(&a, &b);
        assert_eq!(diff.len(), 1);
    }

    // --- Misc ---

    #[test]
    fn test_memory_cell_count() {
        let mut mem = SymbolicMemory::new();
        assert_eq!(mem.cell_count(), 0);
        let region = mem.allocate(16);
        let a0 = MemoryAddress::new(region.clone(), 0);
        let a1 = MemoryAddress::new(region, 4);
        mem.store(&a0, 4, SymbolicValue::Concrete(1)).expect("s1");
        mem.store(&a1, 4, SymbolicValue::Concrete(2)).expect("s2");
        assert_eq!(mem.cell_count(), 2);
    }

    #[test]
    fn test_memory_active_allocation_count() {
        let mut mem = SymbolicMemory::new();
        let r1 = mem.allocate(8);
        mem.allocate(8);
        assert_eq!(mem.active_allocation_count(), 2);
        mem.deallocate(&r1).expect("free");
        assert_eq!(mem.active_allocation_count(), 1);
    }

    #[test]
    fn test_memory_default() {
        let mem = SymbolicMemory::default();
        assert_eq!(mem.cell_count(), 0);
        assert_eq!(mem.active_allocation_count(), 0);
    }

    #[test]
    fn test_memory_store_overwrite() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        let addr = MemoryAddress::new(region, 0);
        mem.store(&addr, 4, SymbolicValue::Concrete(1)).expect("s1");
        mem.store(&addr, 4, SymbolicValue::Concrete(2)).expect("s2");
        let val = mem.load(&addr, 4).expect("load");
        assert_eq!(val, SymbolicValue::Concrete(2));
    }

    #[test]
    fn test_memory_symbolic_store_and_load() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        let addr = MemoryAddress::new(region, 0);
        let sym = SymbolicValue::Symbol("input_x".into());
        mem.store(&addr, 4, sym.clone()).expect("store");
        let val = mem.load(&addr, 4).expect("load");
        // Both store and load apply the 4-byte mask to symbolic values.
        let mask_4b = SymbolicValue::Concrete(0xFFFF_FFFF);
        let stored = SymbolicValue::bin_op(sym, BinOp::BitAnd, mask_4b.clone());
        let expected = SymbolicValue::bin_op(stored, BinOp::BitAnd, mask_4b);
        assert_eq!(val, expected);
    }

    #[test]
    fn test_memory_region_display() {
        assert_eq!(MemoryRegion::Stack(0).to_string(), "stack[0]");
        assert_eq!(MemoryRegion::Heap(3, 0).to_string(), "heap[3+0]");
        assert_eq!(MemoryRegion::Global("foo".into()).to_string(), "global[foo]");
    }

    // --- Size-aware store/load ---

    #[test]
    fn test_store_concrete_masks_to_size() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(16);
        let addr = MemoryAddress::new(region, 0);
        // Store a value with high bits set, but only 1-byte size.
        mem.store(&addr, 1, SymbolicValue::Concrete(0x1234)).expect("store");
        // Only the low byte (0x34) should survive.
        let val = mem.load(&addr, 16).expect("load full width");
        assert_eq!(val, SymbolicValue::Concrete(0x34));
    }

    #[test]
    fn test_load_concrete_masks_to_size() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(16);
        let addr = MemoryAddress::new(region, 0);
        // Store a wide value at full width.
        mem.store(&addr, 16, SymbolicValue::Concrete(0xDEAD_BEEF)).expect("store");
        // Load only 2 bytes -- should get low 2 bytes.
        let val = mem.load(&addr, 2).expect("load 2 bytes");
        assert_eq!(val, SymbolicValue::Concrete(0xBEEF));
    }

    #[test]
    fn test_store_load_full_width_no_mask() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(16);
        let addr = MemoryAddress::new(region, 0);
        let sym = SymbolicValue::Symbol("x".into());
        // Full width (16 bytes) should not mask.
        mem.store(&addr, 16, sym.clone()).expect("store");
        let val = mem.load(&addr, 16).expect("load");
        assert_eq!(val, sym);
    }

    #[test]
    fn test_store_symbolic_masks_with_binop() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(16);
        let addr = MemoryAddress::new(region, 0);
        let sym = SymbolicValue::Symbol("y".into());
        mem.store(&addr, 2, sym.clone()).expect("store 2 bytes");
        // Load at full width to see what was actually stored.
        let val = mem.load(&addr, 16).expect("load full");
        let expected = SymbolicValue::bin_op(sym, BinOp::BitAnd, SymbolicValue::Concrete(0xFFFF));
        assert_eq!(val, expected);
    }

    #[test]
    fn test_load_symbolic_lazy_init_masked() {
        let mut mem = SymbolicMemory::new();
        let region = mem.allocate(8);
        let addr = MemoryAddress::new(region, 0);
        // Lazy-init load at 1 byte should produce masked symbol.
        let val = mem.load(&addr, 1).expect("load 1 byte");
        match &val {
            SymbolicValue::BinOp(inner, BinOp::BitAnd, mask) => {
                assert!(matches!(inner.as_ref(), SymbolicValue::Symbol(_)));
                assert_eq!(mask.as_ref(), &SymbolicValue::Concrete(0xFF));
            }
            other => panic!("expected masked symbol, got {other:?}"),
        }
    }

    #[test]
    fn test_byte_mask_helper() {
        assert_eq!(byte_mask(0), None); // 0 means no mask
        assert_eq!(byte_mask(1), Some(0xFF));
        assert_eq!(byte_mask(2), Some(0xFFFF));
        assert_eq!(byte_mask(4), Some(0xFFFF_FFFF));
        assert_eq!(byte_mask(8), Some(0xFFFF_FFFF_FFFF_FFFF));
        assert_eq!(byte_mask(16), None); // full width, no mask
        assert_eq!(byte_mask(20), None); // beyond full width, no mask
    }

    #[test]
    fn test_mask_value_concrete() {
        let v = mask_value(SymbolicValue::Concrete(0xABCD), 1);
        assert_eq!(v, SymbolicValue::Concrete(0xCD));
    }

    #[test]
    fn test_mask_value_full_width_passthrough() {
        let sym = SymbolicValue::Symbol("z".into());
        let v = mask_value(sym.clone(), 16);
        assert_eq!(v, sym, "full-width mask should be identity");
    }
}
