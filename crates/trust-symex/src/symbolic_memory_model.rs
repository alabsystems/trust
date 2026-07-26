// trust-symex symbolic memory model with copy-on-write
//
// Lazy symbolic memory model with copy-on-write for efficient state
// forking during symbolic execution. Complements the existing memory.rs
// with a higher-level model that tracks symbolic pointers, access logs,
// and alias analysis.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// A symbolic pointer: base name + offset + region id.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SymbolicPointer {
    /// Symbolic base name (e.g., "x", "heap_0").
    pub base: String,
    /// Byte offset from base.
    pub offset: i64,
    /// Region this pointer belongs to.
    pub region_id: usize,
}

impl SymbolicPointer {
    /// Create a new symbolic pointer.
    #[must_use]
    pub fn new(base: &str, offset: i64, region_id: usize) -> Self {
        Self { base: base.to_owned(), offset, region_id }
    }
}

/// A single cell in symbolic memory.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryCell {
    /// Symbolic or concrete value stored in this cell.
    pub value: String,
    /// Whether the value is symbolic (true) or concrete (false).
    pub symbolic: bool,
    /// Number of times this cell has been written.
    pub write_count: usize,
}

impl MemoryCell {
    /// Create a new memory cell.
    #[must_use]
    pub fn new(value: &str, symbolic: bool) -> Self {
        Self { value: value.to_owned(), symbolic, write_count: 0 }
    }
}

/// A contiguous region of symbolic memory.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryRegionModel {
    /// Unique region identifier.
    pub id: usize,
    /// Human-readable name.
    pub name: String,
    /// Sparse cell storage: offset -> cell.
    pub cells: BTreeMap<i64, MemoryCell>,
    /// Maximum size in cells.
    pub size: usize,
}

impl MemoryRegionModel {
    /// Create a new memory region.
    #[must_use]
    pub fn new(id: usize, name: &str, size: usize) -> Self {
        Self { id, name: name.to_owned(), cells: BTreeMap::default(), size }
    }

    /// Check whether an offset is within bounds.
    #[must_use]
    pub fn in_bounds(&self, offset: i64) -> bool {
        offset >= 0 && (offset as usize) < self.size
    }
}

/// Kind of memory access.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum AccessKind {
    /// Read access.
    Read,
    /// Write access.
    Write,
}

/// A logged memory access.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryAccess {
    /// Pointer used for this access.
    pub pointer: SymbolicPointer,
    /// Kind of access (read or write).
    pub kind: AccessKind,
    /// Value written (None for reads).
    pub value: Option<String>,
    /// Logical timestamp of the access.
    pub timestamp: u64,
}

/// Configuration for the memory model.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemoryModelConfig {
    /// Maximum number of regions.
    pub max_regions: usize,
    /// Maximum size of each region in cells.
    pub max_region_size: usize,
    /// Whether to use copy-on-write for fork().
    pub enable_cow: bool,
}

impl Default for MemoryModelConfig {
    fn default() -> Self {
        Self { max_regions: 256, max_region_size: 4096, enable_cow: true }
    }
}

/// Errors from memory model operations.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum MemoryModelError {
    /// Access out of region bounds.
    #[error("out of bounds access: pointer '{ptr}' in region {region}")]
    OutOfBounds {
        /// String representation of the pointer.
        ptr: String,
        /// Region id.
        region: usize,
    },
    /// Null pointer dereference.
    #[error("null pointer dereference")]
    NullDereference,
    /// Use after free.
    #[error("use after free: region {0}")]
    UseAfterFree(usize),
    /// Double free.
    #[error("double free: region {0}")]
    DoubleFree(usize),
    /// Unknown region.
    #[error("unknown region: {0}")]
    UnknownRegion(usize),
    /// Region limit exceeded.
    #[error("region limit exceeded: max {0}")]
    RegionLimitExceeded(usize),
}

/// Lazy symbolic memory model with copy-on-write semantics.
#[derive(Debug, Clone)]
pub struct MemoryModel {
    /// Configuration.
    config: MemoryModelConfig,
    /// Active memory regions.
    regions: BTreeMap<usize, MemoryRegionModel>,
    /// Freed region ids.
    freed: BTreeSet<usize>,
    /// Next region id to allocate.
    next_region_id: usize,
    /// Access log for the current execution path.
    log: Vec<MemoryAccess>,
    /// Logical clock for access ordering.
    clock: u64,
}

impl MemoryModel {
    /// Create a new memory model with the given configuration.
    #[must_use]
    pub fn new(config: MemoryModelConfig) -> Self {
        Self {
            config,
            regions: BTreeMap::default(),
            freed: BTreeSet::default(),
            next_region_id: 0,
            log: Vec::new(),
            clock: 0,
        }
    }

    /// Allocate a new memory region and return a pointer to its base.
    pub fn allocate(
        &mut self,
        name: &str,
        size: usize,
    ) -> Result<SymbolicPointer, MemoryModelError> {
        if self.regions.len() >= self.config.max_regions {
            return Err(MemoryModelError::RegionLimitExceeded(self.config.max_regions));
        }
        let effective_size = size.min(self.config.max_region_size);
        let id = self.next_region_id;
        self.next_region_id += 1;
        let region = MemoryRegionModel::new(id, name, effective_size);
        self.regions.insert(id, region);
        Ok(SymbolicPointer::new(name, 0, id))
    }

    /// Read a memory cell at the given symbolic pointer.
    pub fn read(&self, ptr: &SymbolicPointer) -> Result<&MemoryCell, MemoryModelError> {
        self.check_pointer(ptr)?;
        let region = self
            .regions
            .get(&ptr.region_id)
            .ok_or(MemoryModelError::UnknownRegion(ptr.region_id))?;
        region.cells.get(&ptr.offset).ok_or(MemoryModelError::OutOfBounds {
            ptr: format!("{}+{}", ptr.base, ptr.offset),
            region: ptr.region_id,
        })
    }

    /// Read a cell, logging the access. Returns a clone of the cell.
    pub fn read_logged(&mut self, ptr: &SymbolicPointer) -> Result<MemoryCell, MemoryModelError> {
        let cell = self.read(ptr)?.clone();
        self.log.push(MemoryAccess {
            pointer: ptr.clone(),
            kind: AccessKind::Read,
            value: None,
            timestamp: self.clock,
        });
        self.clock += 1;
        Ok(cell)
    }

    /// Write a value to the memory cell at the given symbolic pointer.
    pub fn write(&mut self, ptr: &SymbolicPointer, value: &str) -> Result<(), MemoryModelError> {
        self.check_pointer(ptr)?;
        let region = self
            .regions
            .get_mut(&ptr.region_id)
            .ok_or(MemoryModelError::UnknownRegion(ptr.region_id))?;
        if !region.in_bounds(ptr.offset) {
            return Err(MemoryModelError::OutOfBounds {
                ptr: format!("{}+{}", ptr.base, ptr.offset),
                region: ptr.region_id,
            });
        }
        let cell =
            region.cells.entry(ptr.offset).or_insert_with(|| MemoryCell::new("uninit", false));
        cell.value = value.to_owned();
        cell.symbolic = true;
        cell.write_count += 1;
        self.log.push(MemoryAccess {
            pointer: ptr.clone(),
            kind: AccessKind::Write,
            value: Some(value.to_owned()),
            timestamp: self.clock,
        });
        self.clock += 1;
        Ok(())
    }

    /// Free a memory region.
    pub fn free(&mut self, region_id: usize) -> Result<(), MemoryModelError> {
        if self.freed.contains(&region_id) {
            return Err(MemoryModelError::DoubleFree(region_id));
        }
        if !self.regions.contains_key(&region_id) {
            return Err(MemoryModelError::UnknownRegion(region_id));
        }
        self.regions.remove(&region_id);
        self.freed.insert(region_id);
        Ok(())
    }

    /// Fork the memory model (copy-on-write clone).
    #[must_use]
    pub fn fork(&self) -> MemoryModel {
        // In COW mode, we still clone the region map but each region's cells
        // are independently owned. A true COW implementation would use
        // Rc<RefCell<>> or similar, but clone is correct and simple.
        Self {
            config: self.config.clone(),
            regions: self.regions.clone(),
            freed: self.freed.clone(),
            next_region_id: self.next_region_id,
            log: self.log.clone(),
            clock: self.clock,
        }
    }

    /// Number of active (non-freed) regions.
    #[must_use]
    pub fn region_count(&self) -> usize {
        self.regions.len()
    }

    /// Access log for this execution path.
    #[must_use]
    pub fn access_log(&self) -> &[MemoryAccess] {
        &self.log
    }

    /// Check if two symbolic pointers may alias (point to the same cell).
    #[must_use]
    pub fn is_alias(&self, a: &SymbolicPointer, b: &SymbolicPointer) -> bool {
        a.region_id == b.region_id && a.offset == b.offset
    }

    /// Return the set of region ids that a pointer could refer to.
    ///
    /// For concrete pointers, this is a singleton. For symbolic pointers
    /// with an unknown base, this could include multiple regions.
    #[must_use]
    pub fn points_to_set(&self, ptr: &SymbolicPointer) -> Vec<usize> {
        // Exact match: the pointer's region_id is known.
        if self.regions.contains_key(&ptr.region_id) {
            return vec![ptr.region_id];
        }
        // Symbolic: find all regions whose name matches the base.
        self.regions.values().filter(|r| r.name == ptr.base).map(|r| r.id).collect()
    }

    /// Validate a pointer before access.
    fn check_pointer(&self, ptr: &SymbolicPointer) -> Result<(), MemoryModelError> {
        if ptr.base == "null" || (ptr.base.is_empty() && ptr.offset == 0) {
            return Err(MemoryModelError::NullDereference);
        }
        if self.freed.contains(&ptr.region_id) {
            return Err(MemoryModelError::UseAfterFree(ptr.region_id));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn default_config() -> MemoryModelConfig {
        MemoryModelConfig { max_regions: 16, max_region_size: 1024, enable_cow: true }
    }

    #[test]
    fn test_memory_model_allocate_returns_base_pointer() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("stack0", 64).expect("should allocate");
        assert_eq!(ptr.base, "stack0");
        assert_eq!(ptr.offset, 0);
        assert_eq!(model.region_count(), 1);
    }

    #[test]
    fn test_memory_model_write_then_read() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("heap0", 128).expect("should allocate");
        model.write(&ptr, "sym_val_0").expect("should write");
        let cell = model.read(&ptr).expect("should read");
        assert_eq!(cell.value, "sym_val_0");
        assert!(cell.symbolic);
        assert_eq!(cell.write_count, 1);
    }

    #[test]
    fn test_memory_model_write_increments_count() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("r", 16).expect("should allocate");
        model.write(&ptr, "a").expect("first write");
        model.write(&ptr, "b").expect("second write");
        let cell = model.read(&ptr).expect("should read");
        assert_eq!(cell.write_count, 2);
        assert_eq!(cell.value, "b");
    }

    #[test]
    fn test_memory_model_read_uninitialized_errors() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("r", 16).expect("should allocate");
        // Reading offset 5 that was never written should error.
        let read_ptr = SymbolicPointer::new("r", 5, ptr.region_id);
        let result = model.read(&read_ptr);
        assert!(result.is_err());
    }

    #[test]
    fn test_memory_model_out_of_bounds_write() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("r", 4).expect("should allocate");
        let oob = SymbolicPointer::new("r", 10, ptr.region_id);
        let result = model.write(&oob, "bad");
        assert!(matches!(result, Err(MemoryModelError::OutOfBounds { .. })));
    }

    #[test]
    fn test_memory_model_negative_offset_out_of_bounds() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("r", 4).expect("should allocate");
        let neg = SymbolicPointer::new("r", -1, ptr.region_id);
        let result = model.write(&neg, "bad");
        assert!(matches!(result, Err(MemoryModelError::OutOfBounds { .. })));
    }

    #[test]
    fn test_memory_model_free_region() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("heap1", 32).expect("should allocate");
        assert_eq!(model.region_count(), 1);
        model.free(ptr.region_id).expect("should free");
        assert_eq!(model.region_count(), 0);
    }

    #[test]
    fn test_memory_model_double_free_errors() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("heap2", 32).expect("should allocate");
        model.free(ptr.region_id).expect("first free");
        let result = model.free(ptr.region_id);
        assert!(matches!(result, Err(MemoryModelError::DoubleFree(_))));
    }

    #[test]
    fn test_memory_model_use_after_free_errors() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("heap3", 32).expect("should allocate");
        model.write(&ptr, "val").expect("should write");
        model.free(ptr.region_id).expect("should free");
        let result = model.read(&ptr);
        assert!(matches!(result, Err(MemoryModelError::UseAfterFree(_))));
    }

    #[test]
    fn test_memory_model_null_deref_errors() {
        let model = MemoryModel::new(default_config());
        let null_ptr = SymbolicPointer::new("null", 0, 0);
        let result = model.read(&null_ptr);
        assert!(matches!(result, Err(MemoryModelError::NullDereference)));
    }

    #[test]
    fn test_memory_model_fork_isolation() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("shared", 64).expect("should allocate");
        model.write(&ptr, "original").expect("should write");

        let mut forked = model.fork();
        forked.write(&ptr, "modified").expect("should write in fork");

        let original_cell = model.read(&ptr).expect("read original");
        let forked_cell = forked.read(&ptr).expect("read forked");
        assert_eq!(original_cell.value, "original");
        assert_eq!(forked_cell.value, "modified");
    }

    #[test]
    fn test_memory_model_fork_preserves_log() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("r", 8).expect("should allocate");
        model.write(&ptr, "v").expect("should write");
        let forked = model.fork();
        assert_eq!(forked.access_log().len(), model.access_log().len());
    }

    #[test]
    fn test_memory_model_access_log_records_writes() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("log_test", 8).expect("should allocate");
        model.write(&ptr, "val1").expect("should write");
        model.write(&ptr, "val2").expect("should write");
        let log = model.access_log();
        assert_eq!(log.len(), 2);
        assert_eq!(log[0].kind, AccessKind::Write);
        assert_eq!(log[0].value.as_deref(), Some("val1"));
        assert_eq!(log[1].timestamp, 1);
    }

    #[test]
    fn test_memory_model_read_logged_records_access() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("r", 8).expect("should allocate");
        model.write(&ptr, "v").expect("should write");
        let _cell = model.read_logged(&ptr).expect("should read");
        let log = model.access_log();
        assert_eq!(log.len(), 2);
        assert_eq!(log[1].kind, AccessKind::Read);
    }

    #[test]
    fn test_memory_model_is_alias_same_cell() {
        let model = MemoryModel::new(default_config());
        let a = SymbolicPointer::new("x", 4, 0);
        let b = SymbolicPointer::new("y", 4, 0);
        assert!(model.is_alias(&a, &b));
    }

    #[test]
    fn test_memory_model_is_alias_different_offset() {
        let model = MemoryModel::new(default_config());
        let a = SymbolicPointer::new("x", 0, 0);
        let b = SymbolicPointer::new("x", 4, 0);
        assert!(!model.is_alias(&a, &b));
    }

    #[test]
    fn test_memory_model_points_to_set_known_region() {
        let mut model = MemoryModel::new(default_config());
        let ptr = model.allocate("heap", 32).expect("should allocate");
        let pts = model.points_to_set(&ptr);
        assert_eq!(pts, vec![ptr.region_id]);
    }

    #[test]
    fn test_memory_model_points_to_set_by_name() {
        let mut model = MemoryModel::new(default_config());
        let p1 = model.allocate("buf", 16).expect("should allocate");
        let _p2 = model.allocate("buf", 16).expect("should allocate");
        // Query with a non-existent region id but matching name.
        let query = SymbolicPointer::new("buf", 0, 999);
        let pts = model.points_to_set(&query);
        assert_eq!(pts.len(), 2);
        assert!(pts.contains(&p1.region_id));
    }

    #[test]
    fn test_memory_model_region_limit_exceeded() {
        let config = MemoryModelConfig { max_regions: 2, max_region_size: 8, enable_cow: false };
        let mut model = MemoryModel::new(config);
        model.allocate("a", 4).expect("first");
        model.allocate("b", 4).expect("second");
        let result = model.allocate("c", 4);
        assert!(matches!(result, Err(MemoryModelError::RegionLimitExceeded(2))));
    }

    #[test]
    fn test_memory_model_unknown_region_free() {
        let mut model = MemoryModel::new(default_config());
        let result = model.free(999);
        assert!(matches!(result, Err(MemoryModelError::UnknownRegion(999))));
    }

    #[test]
    fn test_memory_model_multiple_regions_independent() {
        let mut model = MemoryModel::new(default_config());
        let p1 = model.allocate("r1", 16).expect("alloc r1");
        let p2 = model.allocate("r2", 16).expect("alloc r2");
        model.write(&p1, "val1").expect("write r1");
        model.write(&p2, "val2").expect("write r2");
        let c1 = model.read(&p1).expect("read r1");
        let c2 = model.read(&p2).expect("read r2");
        assert_eq!(c1.value, "val1");
        assert_eq!(c2.value, "val2");
    }

    #[test]
    fn test_memory_model_default_config() {
        let config = MemoryModelConfig::default();
        assert_eq!(config.max_regions, 256);
        assert_eq!(config.max_region_size, 4096);
        assert!(config.enable_cow);
    }

    #[test]
    fn test_symbolic_pointer_new() {
        let ptr = SymbolicPointer::new("test_base", 42, 7);
        assert_eq!(ptr.base, "test_base");
        assert_eq!(ptr.offset, 42);
        assert_eq!(ptr.region_id, 7);
    }

    #[test]
    fn test_memory_cell_new() {
        let cell = MemoryCell::new("concrete_42", false);
        assert_eq!(cell.value, "concrete_42");
        assert!(!cell.symbolic);
        assert_eq!(cell.write_count, 0);
    }

    #[test]
    fn test_memory_region_model_in_bounds() {
        let region = MemoryRegionModel::new(0, "test", 8);
        assert!(region.in_bounds(0));
        assert!(region.in_bounds(7));
        assert!(!region.in_bounds(8));
        assert!(!region.in_bounds(-1));
    }
}
