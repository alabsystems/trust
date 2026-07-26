// trust-lift: Function boundary detection
//
// Provides function boundary detection from symbol tables (Mach-O gated behind
// the `macho` feature) and a standalone API for pre-extracted boundaries.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(feature = "macho")]
use trust_binary_parse::MachO;

#[cfg(feature = "elf")]
use trust_binary_parse::Elf64;

#[cfg(any(feature = "macho", feature = "elf", test))]
use crate::error::LiftError;

/// A detected function boundary from the symbol table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionBoundary {
    /// Demangled or raw symbol name.
    pub name: String,
    /// Start address (virtual).
    pub start: u64,
    /// Size in bytes (estimated from gap to next symbol if not available).
    pub size: u64,
}

/// Detect function boundaries from a parsed Mach-O binary.
///
/// Extracts defined, non-stab symbols from the symbol table, sorts by address,
/// and estimates each function's size as the gap to the next symbol (or to the
/// end of the text section for the last function).
#[cfg(feature = "macho")]
pub(crate) fn detect_functions(macho: &MachO<'_>) -> Result<Vec<FunctionBoundary>, LiftError> {
    let symbols = macho.symbols()?;
    let text_filter = macho_text_section_filter(macho);

    // Filter to defined (non-external-only) symbols with nonzero addresses,
    // excluding stab debugging symbols. When Mach-O section metadata is
    // available, keep only symbols in executable __TEXT,__text.
    let mut func_addrs: Vec<(String, u64)> = symbols
        .iter()
        .filter(|s| {
            is_macho_function_candidate(
                s.is_stab(),
                s.is_defined_in_section(),
                s.value(),
                s.section_index(),
                text_filter,
            )
        })
        .map(|s| {
            let name = normalize_macho_symbol_name(s.name());
            (name, s.value())
        })
        .collect();

    // Sort by address for gap-based size estimation.
    func_addrs.sort_by_key(|(_, addr)| *addr);
    func_addrs.dedup_by_key(|(_, addr)| *addr);

    // Determine text section end for bounding the last function.
    let text_end = macho.text_section().map(|s| s.addr() + s.size()).unwrap_or(u64::MAX);

    boundaries_from_sorted(&func_addrs, text_end)
}

#[cfg(feature = "macho")]
fn macho_text_section_filter(macho: &MachO<'_>) -> Option<MachOTextSectionFilter> {
    let text = macho.text_section()?;
    if !text.is_executable() {
        return Some(MachOTextSectionFilter {
            section_index: 0,
            start: text.addr(),
            end: text.addr().saturating_add(text.size()),
        });
    }

    let section_index = macho
        .sections()
        .position(|(_, section)| std::ptr::eq(section, text))
        .and_then(|index| u8::try_from(index + 1).ok())?;

    Some(MachOTextSectionFilter {
        section_index,
        start: text.addr(),
        end: text.addr().saturating_add(text.size()),
    })
}

#[cfg(any(feature = "macho", test))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MachOTextSectionFilter {
    section_index: u8,
    start: u64,
    end: u64,
}

#[cfg(any(feature = "macho", test))]
fn is_macho_function_candidate(
    is_stab: bool,
    is_defined_in_section: bool,
    value: u64,
    section_index: u8,
    text_filter: Option<MachOTextSectionFilter>,
) -> bool {
    if is_stab || !is_defined_in_section || value == 0 || section_index == 0 {
        return false;
    }

    match text_filter {
        Some(filter) => {
            section_index == filter.section_index && value >= filter.start && value < filter.end
        }
        None => true,
    }
}

#[cfg(any(feature = "macho", test))]
fn normalize_macho_symbol_name(raw_name: &str) -> String {
    raw_name.strip_prefix('_').unwrap_or(raw_name).to_string()
}

/// Detect function boundaries from a parsed ELF64 binary.
///
/// Extracts STT_FUNC symbols from the symbol table, sorts by address,
/// and estimates each function's size from the symbol's `st_size` field
/// (falling back to gap-based estimation when size is zero).
#[cfg(feature = "elf")]
pub(crate) fn detect_functions_elf(elf: &Elf64<'_>) -> Result<Vec<FunctionBoundary>, LiftError> {
    let func_syms = elf.function_symbols()?;

    // Build sorted (name, address) pairs; use st_size if available.
    let mut func_addrs: Vec<(String, u64, u64)> =
        func_syms.iter().map(|s| (s.name.to_string(), s.st_value, s.st_size)).collect();

    func_addrs.sort_by_key(|(_, addr, _)| *addr);
    func_addrs.dedup_by_key(|(_, addr, _)| *addr);

    // Determine text section end for bounding the last function.
    let text_end = elf
        .text_section()
        .map(|s| s.sh_addr + s.sh_size)
        .or_else(|| {
            // Fall back to first executable segment end
            elf.executable_segments().first().map(|seg| seg.p_vaddr + seg.p_memsz)
        })
        .unwrap_or(u64::MAX);

    // Build boundaries, preferring st_size when nonzero.
    let mut boundaries = Vec::with_capacity(func_addrs.len());
    for (i, (name, start, sym_size)) in func_addrs.iter().enumerate() {
        let size = if *sym_size > 0 {
            *sym_size
        } else {
            // Gap-based estimation
            let next_start = func_addrs.get(i + 1).map(|(_, a, _)| *a).unwrap_or(text_end);
            next_start.saturating_sub(*start)
        };
        boundaries.push(FunctionBoundary { name: name.clone(), start: *start, size });
    }

    Ok(boundaries)
}

/// Build function boundaries from a sorted list of (name, address) pairs.
///
/// This is the core algorithm, usable without Mach-O parsing.
/// `text_end` is the address past the last byte of the code section.
#[cfg(any(feature = "macho", test))]
pub(crate) fn boundaries_from_sorted(
    func_addrs: &[(String, u64)],
    text_end: u64,
) -> Result<Vec<FunctionBoundary>, LiftError> {
    let mut boundaries = Vec::with_capacity(func_addrs.len());
    for (i, (name, start)) in func_addrs.iter().enumerate() {
        let next_start = func_addrs.get(i + 1).map(|(_, a)| *a).unwrap_or(text_end);
        let size = next_start.saturating_sub(*start);
        boundaries.push(FunctionBoundary { name: name.clone(), start: *start, size });
    }
    Ok(boundaries)
}

/// Find the function boundary containing the given address.
pub(crate) fn find_function_at(
    boundaries: &[FunctionBoundary],
    address: u64,
) -> Option<&FunctionBoundary> {
    boundaries.iter().find(|b| address >= b.start && address < b.start + b.size)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_boundaries_from_sorted() {
        let addrs = vec![("foo".to_string(), 0x1000u64), ("bar".to_string(), 0x1100)];
        let boundaries = boundaries_from_sorted(&addrs, 0x1200).expect("should succeed");
        assert_eq!(boundaries.len(), 2);
        assert_eq!(boundaries[0].name, "foo");
        assert_eq!(boundaries[0].start, 0x1000);
        assert_eq!(boundaries[0].size, 0x100);
        assert_eq!(boundaries[1].name, "bar");
        assert_eq!(boundaries[1].start, 0x1100);
        assert_eq!(boundaries[1].size, 0x100);
    }

    #[test]
    fn test_normalize_macho_symbol_name_strips_one_abi_underscore() {
        assert_eq!(normalize_macho_symbol_name("_main"), "main");
        assert_eq!(normalize_macho_symbol_name("already_normal"), "already_normal");
        assert_eq!(normalize_macho_symbol_name("__Z3foov"), "_Z3foov");
        assert_eq!(normalize_macho_symbol_name("_"), "");
    }

    #[test]
    fn test_macho_candidate_without_section_metadata_keeps_defined_symbols() {
        assert!(is_macho_function_candidate(false, true, 0x1000, 1, None));
        assert!(!is_macho_function_candidate(true, true, 0x1000, 1, None));
        assert!(!is_macho_function_candidate(false, false, 0x1000, 1, None));
        assert!(!is_macho_function_candidate(false, true, 0, 1, None));
        assert!(!is_macho_function_candidate(false, true, 0x1000, 0, None));
    }

    #[test]
    fn test_macho_candidate_requires_executable_text_section_metadata() {
        let text_filter = MachOTextSectionFilter { section_index: 2, start: 0x1000, end: 0x1100 };

        assert!(is_macho_function_candidate(false, true, 0x1000, 2, Some(text_filter)));
        assert!(is_macho_function_candidate(false, true, 0x10ff, 2, Some(text_filter)));
        assert!(!is_macho_function_candidate(false, true, 0x1000, 1, Some(text_filter)));
        assert!(!is_macho_function_candidate(false, true, 0x0fff, 2, Some(text_filter)));
        assert!(!is_macho_function_candidate(false, true, 0x1100, 2, Some(text_filter)));
    }

    #[test]
    fn test_macho_candidate_rejects_when_text_section_is_not_executable() {
        let non_executable_text =
            MachOTextSectionFilter { section_index: 0, start: 0x1000, end: 0x1100 };

        assert!(!is_macho_function_candidate(false, true, 0x1000, 1, Some(non_executable_text)));
    }

    #[test]
    fn test_find_function_at_exact_match() {
        let boundaries = vec![
            FunctionBoundary { name: "foo".into(), start: 0x1000, size: 0x100 },
            FunctionBoundary { name: "bar".into(), start: 0x1100, size: 0x80 },
        ];
        let found = find_function_at(&boundaries, 0x1000);
        assert_eq!(found.map(|b| &b.name[..]), Some("foo"));

        let found = find_function_at(&boundaries, 0x1050);
        assert_eq!(found.map(|b| &b.name[..]), Some("foo"));

        let found = find_function_at(&boundaries, 0x1100);
        assert_eq!(found.map(|b| &b.name[..]), Some("bar"));
    }

    #[test]
    fn test_find_function_at_miss() {
        let boundaries = vec![FunctionBoundary { name: "foo".into(), start: 0x1000, size: 0x100 }];
        assert!(find_function_at(&boundaries, 0x2000).is_none());
    }
}
