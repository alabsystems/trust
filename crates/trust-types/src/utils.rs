// trust-types/utils.rs: Shared utility functions for the verification pipeline
//
// Consolidates helpers that were duplicated across multiple crates.
// Part of #160.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::{Operand, Place};

/// Strip generic parameters from a Rust path for matching, borrowing `path`
/// when it contains no angle brackets.
#[must_use]
pub fn strip_generics_cow(path: &str) -> std::borrow::Cow<'_, str> {
    if !path.contains(['<', '>']) {
        return std::borrow::Cow::Borrowed(path);
    }
    std::borrow::Cow::Owned(strip_generics(path))
}

/// Compare `strip_generics(path)` against `expected` without allocating when
/// `path` has no angle brackets or its leading non-generic prefix already
/// mismatches `expected`.
#[must_use]
pub fn strip_generics_eq(path: &str, expected: &str) -> bool {
    let Some(lt_idx) = path.find('<') else {
        return if path.contains('>') {
            strip_generics(path) == expected
        } else {
            path == expected
        };
    };
    let prefix = &path[..lt_idx];
    if !prefix.contains('>') && !prefix.contains(":::") {
        let stable_prefix = &prefix[..prefix.len().saturating_sub(1)];
        if !expected.starts_with(stable_prefix) {
            return false;
        }
    }
    strip_generics(path) == expected
}

/// Strip generic parameters from a Rust path for matching.
///
/// Converts `std::sync::Mutex::<T>::lock` to `std::sync::Mutex::lock`.
/// Handles nested generics like `HashMap::<K, V>::get`.
pub fn strip_generics(path: &str) -> String {
    if !path.contains(['<', '>']) {
        return path.to_string();
    }
    let mut result = String::with_capacity(path.len());
    let mut depth = 0u32;

    for ch in path.chars() {
        match ch {
            '<' => depth += 1,
            '>' => {
                depth = depth.saturating_sub(1);
            }
            _ if depth > 0 => { /* skip content inside generics */ }
            ':' if result.ends_with(":::") => {
                // Collapse runs of `::::` (from `Mutex::<T>::`) into `::` in-place.
                result.pop();
            }
            _ => result.push(ch),
        }
    }

    result
}

/// Extract the [`Place`] from an [`Operand`], if it refers to one.
///
/// Returns `Some(&place)` for `Copy` and `Move` operands, `None` for constants.
pub fn operand_place(operand: &Operand) -> Option<&Place> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) | Operand::Symbolic(_) | Operand::Unsupported { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strip_generics_simple() {
        assert_eq!(strip_generics("std::vec::Vec::<i32>::push"), "std::vec::Vec::push");
    }

    #[test]
    fn test_strip_generics_nested() {
        assert_eq!(
            strip_generics("std::collections::HashMap::<String, Vec<u8>>::get"),
            "std::collections::HashMap::get"
        );
    }

    #[test]
    fn test_strip_generics_no_generics() {
        assert_eq!(strip_generics("std::io::Read::read"), "std::io::Read::read");
    }

    #[test]
    fn test_strip_generics_empty() {
        assert_eq!(strip_generics(""), "");
    }

    #[test]
    fn test_operand_place_copy() {
        let place = Place::local(1);
        let op = Operand::Copy(place.clone());
        assert_eq!(operand_place(&op), Some(&place));
    }

    #[test]
    fn test_operand_place_move() {
        let place = Place::local(2);
        let op = Operand::Move(place.clone());
        assert_eq!(operand_place(&op), Some(&place));
    }

    #[test]
    fn test_operand_place_constant() {
        let op = Operand::Constant(crate::ConstValue::Bool(true));
        assert_eq!(operand_place(&op), None);
    }
}
