// trust-binary-parse: Mach-O symbol table parsing
//
// Reference: mach-o/nlist.h — struct nlist_64
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::constants::*;
use crate::error::ParseError;
use crate::read::{Cursor, read_strtab_entry};

/// A parsed nlist_64 symbol table entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol<'a> {
    /// Symbol name from the string table.
    pub(crate) name: &'a str,
    /// n_type field: stab bits, pext, type, ext.
    pub(crate) n_type: u8,
    /// Section number (1-based) or NO_SECT (0).
    pub(crate) n_sect: u8,
    /// Description field (reference type, library ordinal, etc.).
    pub(crate) n_desc: u16,
    /// Value (address for defined symbols).
    pub(crate) n_value: u64,
}

impl Symbol<'_> {
    /// Whether this is a stab debugging symbol.
    #[must_use]
    pub fn is_stab(&self) -> bool {
        (self.n_type & N_STAB) != 0
    }

    /// Whether this symbol is external.
    #[must_use]
    pub fn is_external(&self) -> bool {
        (self.n_type & N_EXT) != 0
    }

    /// Whether this symbol is private external.
    #[must_use]
    pub fn is_private_external(&self) -> bool {
        (self.n_type & N_PEXT) != 0
    }

    /// The N_TYPE field (masked).
    #[must_use]
    pub fn symbol_type(&self) -> u8 {
        self.n_type & N_TYPE_MASK
    }

    /// Whether this is an undefined symbol.
    #[must_use]
    pub fn is_undefined(&self) -> bool {
        self.symbol_type() == N_UNDF
    }

    /// Whether this symbol is defined in a section.
    #[must_use]
    pub fn is_defined_in_section(&self) -> bool {
        self.symbol_type() == N_SECT
    }

    /// Whether this is an absolute symbol.
    #[must_use]
    pub fn is_absolute(&self) -> bool {
        self.symbol_type() == N_ABS
    }

    /// Whether this is an indirect symbol.
    #[must_use]
    pub fn is_indirect(&self) -> bool {
        self.symbol_type() == N_INDR
    }
}

/// Parse the symbol table from the file data, given symtab command info.
pub fn parse_symbols<'a>(
    file_data: &'a [u8],
    symoff: u32,
    nsyms: u32,
    stroff: u32,
    strsize: u32,
    swap: bool,
) -> Result<Vec<Symbol<'a>>, ParseError> {
    let sym_start = symoff as usize;
    let sym_end = sym_start + (nsyms as usize) * NLIST_64_SIZE;
    if sym_end > file_data.len() {
        return Err(ParseError::InvalidSymbolTable { offset: symoff, count: nsyms });
    }

    let str_start = stroff as usize;
    let str_end = str_start + strsize as usize;
    if str_end > file_data.len() {
        return Err(ParseError::InvalidSymbolTable { offset: stroff, count: strsize });
    }
    let strtab = &file_data[str_start..str_end];

    let mut symbols = Vec::with_capacity(nsyms as usize);
    let mut cursor = Cursor::new(file_data, sym_start, swap);

    for _ in 0..nsyms {
        let n_strx = cursor.read_u32()?;
        let n_type = cursor.read_u8()?;
        let n_sect = cursor.read_u8()?;
        let n_desc = cursor.read_u16()?;
        let n_value = cursor.read_u64()?;

        let name = read_strtab_entry(strtab, n_strx)?;

        symbols.push(Symbol { name, n_type, n_sect, n_desc, n_value });
    }

    Ok(symbols)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_flags() {
        let sym =
            Symbol { name: "_main", n_type: N_SECT | N_EXT, n_sect: 1, n_desc: 0, n_value: 0x1000 };
        assert!(sym.is_external());
        assert!(sym.is_defined_in_section());
        assert!(!sym.is_undefined());
        assert!(!sym.is_stab());
        assert!(!sym.is_absolute());
    }

    #[test]
    fn test_undefined_symbol() {
        let sym =
            Symbol { name: "_printf", n_type: N_UNDF | N_EXT, n_sect: 0, n_desc: 0, n_value: 0 };
        assert!(sym.is_external());
        assert!(sym.is_undefined());
        assert!(!sym.is_defined_in_section());
    }

    #[test]
    fn test_stab_symbol() {
        let sym = Symbol {
            name: "debug_info",
            n_type: 0xE0, // N_STAB bits set
            n_sect: 0,
            n_desc: 0,
            n_value: 0,
        };
        assert!(sym.is_stab());
        assert!(!sym.is_external());
    }

    #[test]
    fn test_private_external_symbol() {
        let sym = Symbol {
            name: "_private",
            n_type: N_PEXT | N_SECT | N_EXT,
            n_sect: 1,
            n_desc: 0,
            n_value: 0x2000,
        };
        assert!(sym.is_private_external());
        assert!(sym.is_external());
        assert!(sym.is_defined_in_section());
    }

    #[test]
    fn test_absolute_symbol() {
        let sym = Symbol { name: "_abs", n_type: N_ABS, n_sect: 0, n_desc: 0, n_value: 0x42 };
        assert!(sym.is_absolute());
        assert!(!sym.is_undefined());
        assert!(!sym.is_defined_in_section());
        assert!(!sym.is_indirect());
    }

    #[test]
    fn test_indirect_symbol() {
        let sym = Symbol { name: "_indirect", n_type: N_INDR, n_sect: 0, n_desc: 0, n_value: 0 };
        assert!(sym.is_indirect());
        assert!(!sym.is_absolute());
        assert!(!sym.is_undefined());
    }

    #[test]
    fn test_symbol_type_masking() {
        // N_TYPE_MASK = 0x0E, so only bits 1-3 matter for type
        let sym = Symbol {
            name: "test",
            n_type: N_PEXT | N_SECT | N_EXT, // 0x10 | 0x0E | 0x01 = 0x1F
            n_sect: 1,
            n_desc: 0,
            n_value: 0,
        };
        assert_eq!(sym.symbol_type(), N_SECT);
    }

    #[test]
    fn test_symbol_debug_and_clone() {
        let sym = Symbol { name: "test", n_type: 0, n_sect: 0, n_desc: 0, n_value: 0 };
        let cloned = sym.clone();
        assert_eq!(sym, cloned);
        let _ = format!("{:?}", sym);
    }
}
