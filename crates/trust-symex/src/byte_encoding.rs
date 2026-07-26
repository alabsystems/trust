// trust-symex flat byte-level memory encoding (Layer 3)
//
// Single flat byte array as physical memory model. Each byte is either
// concrete (known u8) or symbolic (SMT bitvector of width 8). Multi-byte
// loads/stores handle endianness via byte concatenation.
//
// This layer is used for:
// - Translation validation against LLVM IR / machine code
// - Binary analysis integration (Ghidra P-code, angr VEX)
// - Modeling `ptr::read_unaligned`, `transmute`, union access
//
// Design: Issue #150, VISION.md Section 9 (Memory Abstraction)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// Endianness
// ---------------------------------------------------------------------------

/// Byte ordering for multi-byte operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Endian {
    /// Least significant byte at lowest address (x86, ARM default).
    Little,
    /// Most significant byte at lowest address (network byte order).
    Big,
}

impl std::fmt::Display for Endian {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Little => write!(f, "little-endian"),
            Self::Big => write!(f, "big-endian"),
        }
    }
}

// ---------------------------------------------------------------------------
// Symbolic byte
// ---------------------------------------------------------------------------

/// A single byte in the flat memory model.
///
/// Either a concrete `u8` value or a symbolic 8-bit bitvector.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SymbolicByte {
    /// A known concrete byte value.
    Concrete(u8),
    /// A symbolic byte represented as an SMT formula (BitVec(8)).
    Symbolic(Formula),
}

impl SymbolicByte {
    /// Returns `true` if this byte is concrete.
    #[must_use]
    pub fn is_concrete(&self) -> bool {
        matches!(self, Self::Concrete(_))
    }

    /// Try to extract a concrete value.
    #[must_use]
    pub fn as_concrete(&self) -> Option<u8> {
        match self {
            Self::Concrete(v) => Some(*v),
            Self::Symbolic(_) => None,
        }
    }

    /// Convert to an SMT formula (BitVec(8)).
    #[must_use]
    pub fn to_formula(&self) -> Formula {
        match self {
            Self::Concrete(v) => Formula::BitVec { value: i128::from(*v), width: 8 },
            Self::Symbolic(f) => f.clone(),
        }
    }
}

impl std::fmt::Display for SymbolicByte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Concrete(v) => write!(f, "0x{v:02x}"),
            Self::Symbolic(formula) => write!(f, "sym({formula:?})"),
        }
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from byte-level memory operations.
#[derive(Debug, Clone, Error, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ByteMemoryError {
    #[error("uninitialized read at address {address} (size {size})")]
    UninitializedRead { address: u64, size: u64 },

    #[error("address overflow: base {base} + offset {offset} overflows")]
    AddressOverflow { base: u64, offset: u64 },

    #[error("zero-width access at address {address}")]
    ZeroWidthAccess { address: u64 },
}

// ---------------------------------------------------------------------------
// ByteMemory
// ---------------------------------------------------------------------------

/// Flat byte-level memory model.
///
/// Maps addresses (u64) to symbolic bytes. Uninitialized bytes can either
/// return fresh symbolic values (lazy init) or error.
///
/// The SMT encoding uses `(Array (_ BitVec 64) (_ BitVec 8))`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ByteMemory {
    /// Mapping from address to symbolic byte.
    cells: BTreeMap<u64, SymbolicByte>,
    /// Whether to lazily create symbolic bytes for uninitialized reads.
    lazy_init: bool,
    /// Counter for generating unique symbolic byte names.
    next_sym_id: u64,
    /// Default endianness for multi-byte operations.
    endian: Endian,
}

impl Default for ByteMemory {
    fn default() -> Self {
        Self::new(Endian::Little)
    }
}

impl ByteMemory {
    /// Create a new byte memory with the given endianness.
    #[must_use]
    pub fn new(endian: Endian) -> Self {
        Self { cells: BTreeMap::new(), lazy_init: true, endian, next_sym_id: 0 }
    }

    /// Create a new byte memory with lazy init disabled (strict mode).
    #[must_use]
    pub fn strict(endian: Endian) -> Self {
        Self { cells: BTreeMap::new(), lazy_init: false, endian, next_sym_id: 0 }
    }

    /// Returns the endianness.
    #[must_use]
    pub fn endian(&self) -> Endian {
        self.endian
    }

    /// Returns the number of initialized bytes.
    #[must_use]
    pub fn initialized_byte_count(&self) -> usize {
        self.cells.len()
    }

    // -----------------------------------------------------------------------
    // Single-byte operations
    // -----------------------------------------------------------------------

    /// Store a single byte at an address.
    pub fn store_byte(&mut self, address: u64, byte: SymbolicByte) {
        self.cells.insert(address, byte);
    }

    /// Load a single byte from an address.
    ///
    /// If lazy_init is enabled and the byte was never written, returns a
    /// fresh symbolic byte. Otherwise returns an error.
    pub fn load_byte(&mut self, address: u64) -> Result<SymbolicByte, ByteMemoryError> {
        if let Some(byte) = self.cells.get(&address) {
            return Ok(byte.clone());
        }

        if self.lazy_init {
            let sym_name = format!("mem_byte_{}", self.next_sym_id);
            self.next_sym_id += 1;
            let byte = SymbolicByte::Symbolic(Formula::Var(sym_name, Sort::BitVec(8)));
            self.cells.insert(address, byte.clone());
            Ok(byte)
        } else {
            Err(ByteMemoryError::UninitializedRead { address, size: 1 })
        }
    }

    // -----------------------------------------------------------------------
    // Multi-byte operations
    // -----------------------------------------------------------------------

    /// Store a multi-byte value using the memory's endianness.
    ///
    /// `bytes` are stored starting at `address`. The byte at index 0 is
    /// the least significant byte for little-endian, most significant for big.
    pub fn store_bytes(&mut self, address: u64, bytes: &[SymbolicByte]) {
        self.store_bytes_endian(address, bytes, self.endian);
    }

    /// Store a multi-byte value with explicit endianness.
    pub fn store_bytes_endian(&mut self, address: u64, bytes: &[SymbolicByte], endian: Endian) {
        match endian {
            Endian::Little => {
                // bytes[0] = LSB goes to lowest address.
                for (i, byte) in bytes.iter().enumerate() {
                    self.cells.insert(address + i as u64, byte.clone());
                }
            }
            Endian::Big => {
                // bytes[0] = MSB goes to lowest address.
                for (i, byte) in bytes.iter().enumerate() {
                    self.cells.insert(address + i as u64, byte.clone());
                }
            }
        }
    }

    /// Load a multi-byte value using the memory's endianness.
    ///
    /// Returns bytes in value order: index 0 is LSB for little-endian,
    /// MSB for big-endian.
    pub fn load_bytes(
        &mut self,
        address: u64,
        size: u64,
    ) -> Result<Vec<SymbolicByte>, ByteMemoryError> {
        self.load_bytes_endian(address, size, self.endian)
    }

    /// Load a multi-byte value with explicit endianness.
    pub fn load_bytes_endian(
        &mut self,
        address: u64,
        size: u64,
        _endian: Endian,
    ) -> Result<Vec<SymbolicByte>, ByteMemoryError> {
        if size == 0 {
            return Err(ByteMemoryError::ZeroWidthAccess { address });
        }

        let mut result = Vec::with_capacity(size as usize);
        for i in 0..size {
            let addr = address
                .checked_add(i)
                .ok_or(ByteMemoryError::AddressOverflow { base: address, offset: i })?;
            result.push(self.load_byte(addr)?);
        }

        Ok(result)
    }

    // -----------------------------------------------------------------------
    // Concrete value helpers
    // -----------------------------------------------------------------------

    /// Store a concrete u32 at an address using the memory's endianness.
    pub fn store_u32(&mut self, address: u64, value: u32) {
        let bytes = match self.endian {
            Endian::Little => value.to_le_bytes(),
            Endian::Big => value.to_be_bytes(),
        };
        for (i, &b) in bytes.iter().enumerate() {
            self.cells.insert(address + i as u64, SymbolicByte::Concrete(b));
        }
    }

    /// Store a concrete u64 at an address using the memory's endianness.
    pub fn store_u64(&mut self, address: u64, value: u64) {
        let bytes = match self.endian {
            Endian::Little => value.to_le_bytes(),
            Endian::Big => value.to_be_bytes(),
        };
        for (i, &b) in bytes.iter().enumerate() {
            self.cells.insert(address + i as u64, SymbolicByte::Concrete(b));
        }
    }

    /// Load a concrete u32 from an address. Returns `None` if any byte is symbolic.
    pub fn load_concrete_u32(&mut self, address: u64) -> Result<Option<u32>, ByteMemoryError> {
        let bytes = self.load_bytes(address, 4)?;
        let concrete: Option<Vec<u8>> = bytes.iter().map(|b| b.as_concrete()).collect();
        let Some(raw) = concrete else {
            return Ok(None);
        };
        let arr: [u8; 4] = [raw[0], raw[1], raw[2], raw[3]];
        Ok(Some(match self.endian {
            Endian::Little => u32::from_le_bytes(arr),
            Endian::Big => u32::from_be_bytes(arr),
        }))
    }

    /// Load a concrete u64 from an address. Returns `None` if any byte is symbolic.
    pub fn load_concrete_u64(&mut self, address: u64) -> Result<Option<u64>, ByteMemoryError> {
        let bytes = self.load_bytes(address, 8)?;
        let concrete: Option<Vec<u8>> = bytes.iter().map(|b| b.as_concrete()).collect();
        let Some(raw) = concrete else {
            return Ok(None);
        };
        let arr: [u8; 8] = [raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6], raw[7]];
        Ok(Some(match self.endian {
            Endian::Little => u64::from_le_bytes(arr),
            Endian::Big => u64::from_be_bytes(arr),
        }))
    }

    // -----------------------------------------------------------------------
    // SMT encoding
    // -----------------------------------------------------------------------

    /// Encode a multi-byte load as an SMT formula.
    ///
    /// For a `width`-bit load at `address`, produces a bitvector concatenation
    /// of individual bytes, respecting endianness.
    #[must_use]
    pub fn encode_load_formula(&self, base_name: &str, address: u64, width_bytes: u64) -> Formula {
        if width_bytes == 0 {
            return Formula::BitVec { value: 0, width: 0 };
        }

        if width_bytes == 1 {
            if let Some(byte) = self.cells.get(&address) {
                return byte.to_formula();
            }
            return Formula::Var(format!("{base_name}_{address:#x}"), Sort::BitVec(8));
        }

        // Build concatenation based on endianness.
        // For little-endian: byte at highest address is MSB.
        // For big-endian: byte at lowest address is MSB.
        let byte_formulas: Vec<Formula> = (0..width_bytes)
            .map(|i| {
                let addr = address + i;
                if let Some(byte) = self.cells.get(&addr) {
                    byte.to_formula()
                } else {
                    Formula::Var(format!("{base_name}_{addr:#x}"), Sort::BitVec(8))
                }
            })
            .collect();

        // Concatenate bytes into a single bitvector.
        // For little-endian: reverse so MSB is first in concat (SMT convention).
        // For big-endian: already in MSB-first order.
        let ordered: Vec<Formula> = match self.endian {
            Endian::Little => byte_formulas.into_iter().rev().collect(),
            Endian::Big => byte_formulas,
        };

        // Build a left-folded concat tree.
        let mut result = ordered[0].clone();
        for byte in &ordered[1..] {
            result = Formula::BvConcat(Box::new(result), Box::new(byte.clone()));
        }

        result
    }

    /// Encode a multi-byte store as an SMT formula.
    ///
    /// Given a memory array formula and a value to store, produces the
    /// updated array with individual byte stores.
    #[must_use]
    pub fn encode_store_formula(
        &self,
        array: &Formula,
        address: u64,
        value: &Formula,
        width_bytes: u64,
    ) -> Formula {
        if width_bytes == 0 {
            return array.clone();
        }

        let mut result = array.clone();

        for i in 0..width_bytes {
            let addr = address + i;
            let addr_formula = Formula::BitVec { value: addr as i128, width: 64 };

            // Extract the appropriate byte from the value.
            let byte_formula = match self.endian {
                Endian::Little => {
                    // Byte i is bits [i*8 + 7 : i*8].
                    let low = (i * 8) as u32;
                    let high = low + 7;
                    Formula::BvExtract { inner: Box::new(value.clone()), high, low }
                }
                Endian::Big => {
                    // Byte i is bits [(width_bytes - 1 - i)*8 + 7 : (width_bytes - 1 - i)*8].
                    let byte_idx = width_bytes - 1 - i;
                    let low = (byte_idx * 8) as u32;
                    let high = low + 7;
                    Formula::BvExtract { inner: Box::new(value.clone()), high, low }
                }
            };

            result =
                Formula::Store(Box::new(result), Box::new(addr_formula), Box::new(byte_formula));
        }

        result
    }
}

// ---------------------------------------------------------------------------
// ByteMemoryRegion
// ---------------------------------------------------------------------------

/// A contiguous region of byte memory with a base address and size.
///
/// Useful for modeling stack frames, heap allocations, or mmapped regions
/// as bounded byte arrays.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ByteMemoryRegion {
    /// Human-readable name for this region.
    name: String,
    /// Base address of the region.
    base: u64,
    /// Size in bytes.
    size: u64,
    /// The bytes in this region (offset from base -> byte).
    bytes: BTreeMap<u64, SymbolicByte>,
}

impl ByteMemoryRegion {
    /// Create a new uninitialized region.
    #[must_use]
    pub fn new(name: impl Into<String>, base: u64, size: u64) -> Self {
        Self { name: name.into(), base, size, bytes: BTreeMap::new() }
    }

    /// Returns the region name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the base address.
    #[must_use]
    pub fn base(&self) -> u64 {
        self.base
    }

    /// Returns the size in bytes.
    #[must_use]
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Returns the number of initialized bytes in this region.
    #[must_use]
    pub fn initialized_count(&self) -> usize {
        self.bytes.len()
    }

    /// Store a byte at an offset within the region.
    ///
    /// Returns an error if the offset is out of bounds.
    pub fn store(&mut self, offset: u64, byte: SymbolicByte) -> Result<(), ByteMemoryError> {
        if offset >= self.size {
            return Err(ByteMemoryError::AddressOverflow { base: self.base, offset });
        }
        self.bytes.insert(offset, byte);
        Ok(())
    }

    /// Load a byte from an offset within the region.
    ///
    /// Returns a fresh symbolic byte for uninitialized offsets.
    #[must_use]
    pub fn load(&self, offset: u64) -> SymbolicByte {
        if offset >= self.size {
            // Out of bounds -- return symbolic.
            return SymbolicByte::Symbolic(Formula::Var(
                format!("{}_oob_{offset:#x}", self.name),
                Sort::BitVec(8),
            ));
        }
        self.bytes.get(&offset).cloned().unwrap_or_else(|| {
            SymbolicByte::Symbolic(Formula::Var(
                format!("{}_{offset:#x}", self.name),
                Sort::BitVec(8),
            ))
        })
    }

    /// Check if an address falls within this region.
    #[must_use]
    pub fn contains(&self, address: u64) -> bool {
        address >= self.base && address < self.base + self.size
    }

    /// Convert an absolute address to a region-relative offset.
    #[must_use]
    pub fn to_offset(&self, address: u64) -> Option<u64> {
        if self.contains(address) { Some(address - self.base) } else { None }
    }

    /// Generate an SMT formula asserting that all initialized bytes match.
    ///
    /// Useful for translation validation: assert region contents equal
    /// expected values.
    #[must_use]
    pub fn equality_formula(&self, array_name: &str) -> Formula {
        let array = Formula::Var(
            array_name.to_owned(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );

        let mut conjuncts = Vec::new();
        for (&offset, byte) in &self.bytes {
            let addr = Formula::BitVec { value: (self.base + offset) as i128, width: 64 };
            let selected = Formula::Select(Box::new(array.clone()), Box::new(addr));
            let expected = byte.to_formula();
            conjuncts.push(Formula::Eq(Box::new(selected), Box::new(expected)));
        }

        if conjuncts.is_empty() {
            Formula::Bool(true)
        } else if conjuncts.len() == 1 {
            // SAFETY: len == 1 guarantees .next() returns Some.
            conjuncts
                .into_iter()
                .next()
                .expect("invariant: len == 1 guarantees .next() returns Some")
        } else {
            Formula::And(conjuncts)
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // --- SymbolicByte ---

    #[test]
    fn test_symbolic_byte_concrete() {
        let byte = SymbolicByte::Concrete(0xAB);
        assert!(byte.is_concrete());
        assert_eq!(byte.as_concrete(), Some(0xAB));
    }

    #[test]
    fn test_symbolic_byte_symbolic() {
        let byte = SymbolicByte::Symbolic(Formula::Var("b0".into(), Sort::BitVec(8)));
        assert!(!byte.is_concrete());
        assert_eq!(byte.as_concrete(), None);
    }

    #[test]
    fn test_symbolic_byte_to_formula_concrete() {
        let byte = SymbolicByte::Concrete(42);
        let f = byte.to_formula();
        assert_eq!(f, Formula::BitVec { value: 42, width: 8 });
    }

    #[test]
    fn test_symbolic_byte_to_formula_symbolic() {
        let var = Formula::Var("x".into(), Sort::BitVec(8));
        let byte = SymbolicByte::Symbolic(var.clone());
        assert_eq!(byte.to_formula(), var);
    }

    #[test]
    fn test_symbolic_byte_display() {
        assert_eq!(SymbolicByte::Concrete(0xFF).to_string(), "0xff");
        assert_eq!(SymbolicByte::Concrete(0x00).to_string(), "0x00");
    }

    // --- ByteMemory single byte ---

    #[test]
    fn test_store_and_load_byte() {
        let mut mem = ByteMemory::new(Endian::Little);
        mem.store_byte(0x100, SymbolicByte::Concrete(0x42));
        let byte = mem.load_byte(0x100).expect("load ok");
        assert_eq!(byte, SymbolicByte::Concrete(0x42));
    }

    #[test]
    fn test_load_uninitialized_lazy_init() {
        let mut mem = ByteMemory::new(Endian::Little);
        let byte = mem.load_byte(0x200).expect("lazy init");
        assert!(!byte.is_concrete());
    }

    #[test]
    fn test_load_uninitialized_strict_errors() {
        let mut mem = ByteMemory::strict(Endian::Little);
        let err = mem.load_byte(0x200).expect_err("strict mode");
        assert!(matches!(err, ByteMemoryError::UninitializedRead { .. }));
    }

    // --- ByteMemory multi-byte ---

    #[test]
    fn test_store_u32_little_endian() {
        let mut mem = ByteMemory::new(Endian::Little);
        mem.store_u32(0x100, 0xDEAD_BEEF);

        // Little-endian: lowest address has LSB.
        assert_eq!(mem.load_byte(0x100).unwrap(), SymbolicByte::Concrete(0xEF));
        assert_eq!(mem.load_byte(0x101).unwrap(), SymbolicByte::Concrete(0xBE));
        assert_eq!(mem.load_byte(0x102).unwrap(), SymbolicByte::Concrete(0xAD));
        assert_eq!(mem.load_byte(0x103).unwrap(), SymbolicByte::Concrete(0xDE));
    }

    #[test]
    fn test_store_u32_big_endian() {
        let mut mem = ByteMemory::new(Endian::Big);
        mem.store_u32(0x100, 0xDEAD_BEEF);

        // Big-endian: lowest address has MSB.
        assert_eq!(mem.load_byte(0x100).unwrap(), SymbolicByte::Concrete(0xDE));
        assert_eq!(mem.load_byte(0x101).unwrap(), SymbolicByte::Concrete(0xAD));
        assert_eq!(mem.load_byte(0x102).unwrap(), SymbolicByte::Concrete(0xBE));
        assert_eq!(mem.load_byte(0x103).unwrap(), SymbolicByte::Concrete(0xEF));
    }

    #[test]
    fn test_load_concrete_u32_little_endian() {
        let mut mem = ByteMemory::new(Endian::Little);
        mem.store_u32(0x0, 0x1234_5678);
        let val = mem.load_concrete_u32(0x0).expect("load ok").expect("concrete");
        assert_eq!(val, 0x1234_5678);
    }

    #[test]
    fn test_load_concrete_u32_big_endian() {
        let mut mem = ByteMemory::new(Endian::Big);
        mem.store_u32(0x0, 0x1234_5678);
        let val = mem.load_concrete_u32(0x0).expect("load ok").expect("concrete");
        assert_eq!(val, 0x1234_5678);
    }

    #[test]
    fn test_load_concrete_u32_returns_none_for_symbolic() {
        let mut mem = ByteMemory::new(Endian::Little);
        mem.store_byte(0x0, SymbolicByte::Concrete(0x01));
        mem.store_byte(0x1, SymbolicByte::Symbolic(Formula::Var("x".into(), Sort::BitVec(8))));
        mem.store_byte(0x2, SymbolicByte::Concrete(0x03));
        mem.store_byte(0x3, SymbolicByte::Concrete(0x04));
        let result = mem.load_concrete_u32(0x0).expect("load ok");
        assert!(result.is_none());
    }

    #[test]
    fn test_store_and_load_u64() {
        let mut mem = ByteMemory::new(Endian::Little);
        mem.store_u64(0x0, 0x0102_0304_0506_0708);
        let val = mem.load_concrete_u64(0x0).expect("load ok").expect("concrete");
        assert_eq!(val, 0x0102_0304_0506_0708);
    }

    // --- Multi-byte store/load ---

    #[test]
    fn test_store_bytes_and_load_bytes() {
        let mut mem = ByteMemory::new(Endian::Little);
        let bytes = vec![
            SymbolicByte::Concrete(0x11),
            SymbolicByte::Concrete(0x22),
            SymbolicByte::Concrete(0x33),
        ];
        mem.store_bytes(0x10, &bytes);
        let loaded = mem.load_bytes(0x10, 3).expect("load ok");
        assert_eq!(loaded, bytes);
    }

    #[test]
    fn test_load_bytes_zero_width_errors() {
        let mut mem = ByteMemory::new(Endian::Little);
        let err = mem.load_bytes(0x0, 0).expect_err("zero width");
        assert!(matches!(err, ByteMemoryError::ZeroWidthAccess { .. }));
    }

    // --- Endian display ---

    #[test]
    fn test_endian_display() {
        assert_eq!(Endian::Little.to_string(), "little-endian");
        assert_eq!(Endian::Big.to_string(), "big-endian");
    }

    // --- ByteMemory defaults ---

    #[test]
    fn test_byte_memory_default() {
        let mem = ByteMemory::default();
        assert_eq!(mem.endian(), Endian::Little);
        assert_eq!(mem.initialized_byte_count(), 0);
    }

    // --- ByteMemoryRegion ---

    #[test]
    fn test_region_basic() {
        let region = ByteMemoryRegion::new("stack0", 0x1000, 256);
        assert_eq!(region.name(), "stack0");
        assert_eq!(region.base(), 0x1000);
        assert_eq!(region.size(), 256);
        assert_eq!(region.initialized_count(), 0);
    }

    #[test]
    fn test_region_store_and_load() {
        let mut region = ByteMemoryRegion::new("heap0", 0x2000, 64);
        region.store(0, SymbolicByte::Concrete(0xAA)).expect("store ok");
        region.store(63, SymbolicByte::Concrete(0xBB)).expect("store end");

        assert_eq!(region.load(0), SymbolicByte::Concrete(0xAA));
        assert_eq!(region.load(63), SymbolicByte::Concrete(0xBB));
        assert_eq!(region.initialized_count(), 2);
    }

    #[test]
    fn test_region_store_out_of_bounds() {
        let mut region = ByteMemoryRegion::new("small", 0x0, 4);
        let err = region.store(4, SymbolicByte::Concrete(0xFF)).expect_err("oob");
        assert!(matches!(err, ByteMemoryError::AddressOverflow { .. }));
    }

    #[test]
    fn test_region_load_uninitialized_returns_symbolic() {
        let region = ByteMemoryRegion::new("test", 0x0, 16);
        let byte = region.load(5);
        assert!(!byte.is_concrete());
    }

    #[test]
    fn test_region_contains() {
        let region = ByteMemoryRegion::new("r", 0x100, 16);
        assert!(region.contains(0x100));
        assert!(region.contains(0x10F));
        assert!(!region.contains(0x110));
        assert!(!region.contains(0x0FF));
    }

    #[test]
    fn test_region_to_offset() {
        let region = ByteMemoryRegion::new("r", 0x100, 16);
        assert_eq!(region.to_offset(0x100), Some(0));
        assert_eq!(region.to_offset(0x108), Some(8));
        assert_eq!(region.to_offset(0x110), None);
    }

    // --- SMT encoding ---

    #[test]
    fn test_encode_load_formula_single_byte() {
        let mut mem = ByteMemory::new(Endian::Little);
        mem.store_byte(0x100, SymbolicByte::Concrete(0x42));
        let f = mem.encode_load_formula("mem", 0x100, 1);
        assert_eq!(f, Formula::BitVec { value: 0x42, width: 8 });
    }

    #[test]
    fn test_encode_load_formula_multi_byte_le() {
        let mut mem = ByteMemory::new(Endian::Little);
        mem.store_byte(0x0, SymbolicByte::Concrete(0x78));
        mem.store_byte(0x1, SymbolicByte::Concrete(0x56));

        let f = mem.encode_load_formula("mem", 0x0, 2);
        // Little-endian: byte[1] (0x56) is MSB, byte[0] (0x78) is LSB.
        // Concat: 0x56 ++ 0x78 = 0x5678.
        match &f {
            Formula::BvConcat(_, _) => {} // correct structure
            other => panic!("expected BvConcat, got {other:?}"),
        }
    }

    #[test]
    fn test_encode_load_formula_uninitialized() {
        let mem = ByteMemory::new(Endian::Little);
        let f = mem.encode_load_formula("mem", 0x0, 1);
        // Should be a variable since the address was never written.
        match &f {
            Formula::Var(_, Sort::BitVec(8)) => {}
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn test_encode_store_formula_single_byte() {
        let mem = ByteMemory::new(Endian::Little);
        let array = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let value = Formula::BitVec { value: 0xFF, width: 8 };
        let f = mem.encode_store_formula(&array, 0x100, &value, 1);
        match &f {
            Formula::Store(_, _, _) => {}
            other => panic!("expected Store, got {other:?}"),
        }
    }

    #[test]
    fn test_encode_store_formula_multi_byte() {
        let mem = ByteMemory::new(Endian::Little);
        let array = Formula::Var(
            "mem".into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        );
        let value = Formula::BitVec { value: 0xDEAD, width: 16 };
        let f = mem.encode_store_formula(&array, 0x0, &value, 2);
        // Should be nested Store(Store(array, addr0, byte0), addr1, byte1).
        match &f {
            Formula::Store(inner, _, _) => match inner.as_ref() {
                Formula::Store(_, _, _) => {}
                other => panic!("expected nested Store, got {other:?}"),
            },
            other => panic!("expected Store, got {other:?}"),
        }
    }

    // --- Equality formula ---

    #[test]
    fn test_region_equality_formula_empty() {
        let region = ByteMemoryRegion::new("test", 0x0, 16);
        let f = region.equality_formula("mem");
        assert_eq!(f, Formula::Bool(true));
    }

    #[test]
    fn test_region_equality_formula_single_byte() {
        let mut region = ByteMemoryRegion::new("test", 0x100, 16);
        region.store(0, SymbolicByte::Concrete(0xAB)).expect("store");
        let f = region.equality_formula("mem");
        match &f {
            Formula::Eq(_, _) => {}
            other => panic!("expected Eq, got {other:?}"),
        }
    }

    #[test]
    fn test_region_equality_formula_multiple_bytes() {
        let mut region = ByteMemoryRegion::new("test", 0x0, 4);
        region.store(0, SymbolicByte::Concrete(0x01)).unwrap();
        region.store(1, SymbolicByte::Concrete(0x02)).unwrap();
        let f = region.equality_formula("mem");
        match &f {
            Formula::And(conjuncts) => assert_eq!(conjuncts.len(), 2),
            other => panic!("expected And, got {other:?}"),
        }
    }

    // --- Address overflow ---

    #[test]
    fn test_load_bytes_address_overflow() {
        let mut mem = ByteMemory::new(Endian::Little);
        let err = mem.load_bytes(u64::MAX, 2).expect_err("should overflow");
        assert!(matches!(err, ByteMemoryError::AddressOverflow { .. }));
    }
}
