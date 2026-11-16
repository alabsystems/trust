// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Stable function symbols for structural Lean declaration names.
//!
//! A display joins components with dots and cannot identify a declaration:
//! `A.b` and `«A.b»` display alike. Keep ordinary ASCII paths readable, and
//! encode every other identity in a reserved, versioned namespace. Components
//! carry distinct tags, exact byte lengths and every UTF-8 byte; no hash or
//! truncated digest stands in for a name.

use std::fmt::Write as _;

use clean_kernel::name::{Name, NameInner};

const PREFIX: &str = "__trust_lean_name_v1_";

/// An injective symbol spelling, independent of lexical quoting or display.
///
/// Bare symbols never start with the escape prefix. Encoded symbols record
/// each structural component, distinguishing string digits from numeric nodes,
/// dots within components from separators, and anonymous from empty strings.
#[must_use]
pub fn declaration_symbol(name: &Name) -> String {
    let mut parts = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            part @ (NameInner::Str(parent, _) | NameInner::Num(parent, _)) => {
                parts.push(part);
                current = parent.as_ref();
            }
        }
    }
    parts.reverse();
    if !parts.is_empty()
        && parts.iter().all(|part| matches!(part, NameInner::Str(_, text) if ascii_identifier(text)))
    {
        let total_len: usize = parts
            .iter()
            .map(|part| match part {
                NameInner::Str(_, text) => text.len(),
                _ => 0,
            })
            .sum::<usize>()
            + parts.len()
            - 1;
        let mut symbol = String::with_capacity(total_len);
        for (idx, part) in parts.iter().enumerate() {
            if idx > 0 {
                symbol.push('.');
            }
            if let NameInner::Str(_, text) = part {
                symbol.push_str(text);
            }
        }
        if !symbol.starts_with(PREFIX) {
            return symbol;
        }
    }
    let mut symbol = PREFIX.to_owned();
    if parts.is_empty() {
        symbol.push('a');
    }
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for part in parts {
        match part {
            NameInner::Anon => {}
            NameInner::Str(_, text) => {
                let _ = write!(symbol, "s{}_", text.len());
                for byte in text.as_bytes() {
                    symbol.push(HEX[(byte >> 4) as usize] as char);
                    symbol.push(HEX[(byte & 15) as usize] as char);
                }
            }
            NameInner::Num(_, number) => {
                let _ = write!(symbol, "n{number}_");
            }
        }
    }
    symbol
}

fn ascii_identifier(text: &str) -> bool {
    let mut bytes = text.bytes();
    matches!(bytes.next(), Some(b) if b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn ordinary_paths_and_versioned_wire_spelling_are_stable() {
        assert_eq!(declaration_symbol(&Name::anon().str("chooseWide")), "chooseWide");
        assert_eq!(declaration_symbol(&Name::anon().str("A").str("b")), "A.b");
        assert_eq!(declaration_symbol(&Name::anon().str("A.b")), "__trust_lean_name_v1_s3_412e62");
        assert_eq!(declaration_symbol(&Name::anon().num(7)), "__trust_lean_name_v1_n7_");
    }

    #[test]
    fn component_boundaries_numeric_nodes_and_escape_lookalikes_do_not_alias() {
        let mut names = vec![Name::anon(), Name::anon().num(0), Name::anon().num(u64::MAX)];
        for text in ["", "A", "b", "A.b", "7", "é", "_", "__trust_lean_name_v1_a"] {
            names.push(Name::anon().str(text));
            names.push(Name::anon().str(text).num(7));
            names.push(Name::anon().num(7).str(text));
            for other in ["", "A", "b", "7", "é", "A.b"] {
                names.push(Name::anon().str(text).str(other));
            }
        }
        let original_symbols: Vec<_> = names.iter().map(declaration_symbol).collect();
        for symbol in &original_symbols {
            if symbol.starts_with(PREFIX) {
                let lookalike = Name::anon().str(symbol);
                if !names.contains(&lookalike) {
                    names.push(lookalike);
                }
            }
        }
        assert_eq!(names.iter().collect::<HashSet<_>>().len(), names.len());
        let symbols: HashSet<_> = names.iter().map(declaration_symbol).collect();
        assert_eq!(symbols.len(), names.len());
    }
}
