// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Shared by `differential_corpus.rs` and `rejection.rs`: the recursive
//! comparison between an incumbent `toml::Value` tree and a `trust_toml::Value`
//! tree.
//!
//! It lives here rather than being duplicated because the two gates must apply
//! the SAME notion of "equal". A second, slightly different comparator is how a
//! difference gets classified as equal in one gate and unequal in the other,
//! and the one that is wrong is the one nobody re-reads.

#![allow(dead_code)]

use std::collections::BTreeSet;

/// Recursively compare an incumbent tree against ours, accumulating every
/// difference rather than stopping at the first: one run should describe the
/// whole disagreement.
pub fn compare(
    incumbent: &incumbent_toml::Value,
    ours: &trust_toml::Value,
    path: &str,
    out: &mut Vec<String>,
) {
    use incumbent_toml::Value as Theirs;
    use trust_toml::Value as Ours;

    let at = if path.is_empty() { "<root>".to_string() } else { path.to_string() };
    match (incumbent, ours) {
        (Theirs::String(left), Ours::String(right)) => {
            if left != right {
                out.push(format!("{at}: string {left:?} vs {right:?}"));
            }
        }
        (Theirs::Integer(left), Ours::Integer(right)) => {
            if left != right {
                out.push(format!("{at}: integer {left} vs {right}"));
            }
        }
        (Theirs::Float(left), Ours::Float(right)) => {
            // Bit equality, with NaN counted equal to NaN. `==` would report
            // every NaN pair as a disagreement, and would also miss a
            // -0.0/+0.0 difference, which IS observable once a value is
            // re-emitted or digested.
            let same = left.to_bits() == right.to_bits() || (left.is_nan() && right.is_nan());
            if !same {
                out.push(format!("{at}: float {left:?} vs {right:?}"));
            }
        }
        (Theirs::Boolean(left), Ours::Boolean(right)) => {
            if left != right {
                out.push(format!("{at}: boolean {left} vs {right}"));
            }
        }
        (Theirs::Datetime(left), Ours::Datetime(right)) => {
            // Through Display: the two crates have unrelated datetime types,
            // and the canonical text is the observable both must agree on.
            if left.to_string() != right.to_string() {
                out.push(format!("{at}: datetime {left} vs {right}"));
            }
        }
        (Theirs::Array(left), Ours::Array(right)) => {
            if left.len() != right.len() {
                out.push(format!("{at}: array length {} vs {}", left.len(), right.len()));
                return;
            }
            for (index, (left, right)) in left.iter().zip(right).enumerate() {
                compare(left, right, &format!("{at}[{index}]"), out);
            }
        }
        (Theirs::Table(left), Ours::Table(right)) => {
            let left_keys: Vec<&str> = left.keys().map(String::as_str).collect();
            let right_keys: Vec<&str> = right.keys().map(String::as_str).collect();
            if left_keys != right_keys {
                let left_set: BTreeSet<&str> = left_keys.iter().copied().collect();
                let right_set: BTreeSet<&str> = right_keys.iter().copied().collect();
                if left_set == right_set {
                    out.push(format!(
                        "{at}: key ORDER differs — {left_keys:?} vs {right_keys:?}"
                    ));
                } else {
                    out.push(format!(
                        "{at}: keys differ — only incumbent {:?}, only trust-toml {:?}",
                        left_set.difference(&right_set).collect::<Vec<_>>(),
                        right_set.difference(&left_set).collect::<Vec<_>>()
                    ));
                }
                return;
            }
            let prefix = if path.is_empty() { String::new() } else { format!("{path}.") };
            for key in left_keys {
                compare(&left[key], &right[key], &format!("{prefix}{key}"), out);
            }
        }
        (left, right) => out.push(format!(
            "{at}: type differs — incumbent {}, trust-toml {}",
            left.type_str(),
            right.type_str()
        )),
    }
}

/// The same notion of equality, over two **incumbent** trees.
///
/// `serialize_differential.rs` needs this shape: it emits text with `trust-toml`
/// and then reads that text back **with the incumbent**, so both sides of the
/// comparison are `incumbent_toml::Value`. Re-reading with our own parser would
/// be the blind spot the whole gate exists to close — a mis-escape paired with a
/// matching mis-unescape round-trips perfectly through one implementation and is
/// still a corrupt file for every other reader.
///
/// It lives beside [`compare`], and not in that file's caller, for the reason
/// stated at the top: the two gates must apply the same notion of "equal", and a
/// second definition that drifts is how a difference gets classified as equal in
/// one gate and unequal in the other. Keeping them adjacent means a change to
/// one is visibly a change that should touch the other. `incumbent_toml::Value`
/// derives `PartialEq`, so a bare `==` would also compile — and would silently
/// report every `nan` as a disagreement and every `-0.0`/`0.0` pair as a match.
pub fn compare_incumbent(
    left: &incumbent_toml::Value,
    right: &incumbent_toml::Value,
    path: &str,
    out: &mut Vec<String>,
) {
    use incumbent_toml::Value as V;

    let at = if path.is_empty() { "<root>".to_string() } else { path.to_string() };
    match (left, right) {
        (V::Float(left), V::Float(right)) => {
            let same = left.to_bits() == right.to_bits() || (left.is_nan() && right.is_nan());
            if !same {
                out.push(format!("{at}: float {left:?} vs {right:?}"));
            }
        }
        (V::Array(left), V::Array(right)) => {
            if left.len() != right.len() {
                out.push(format!("{at}: array length {} vs {}", left.len(), right.len()));
                return;
            }
            for (index, (left, right)) in left.iter().zip(right).enumerate() {
                compare_incumbent(left, right, &format!("{at}[{index}]"), out);
            }
        }
        (V::Table(left), V::Table(right)) => {
            let left_keys: Vec<&str> = left.keys().map(String::as_str).collect();
            let right_keys: Vec<&str> = right.keys().map(String::as_str).collect();
            if left_keys != right_keys {
                let left_set: BTreeSet<&str> = left_keys.iter().copied().collect();
                let right_set: BTreeSet<&str> = right_keys.iter().copied().collect();
                if left_set == right_set {
                    out.push(format!("{at}: key ORDER differs — {left_keys:?} vs {right_keys:?}"));
                } else {
                    out.push(format!(
                        "{at}: keys differ — only left {:?}, only right {:?}",
                        left_set.difference(&right_set).collect::<Vec<_>>(),
                        right_set.difference(&left_set).collect::<Vec<_>>()
                    ));
                }
                return;
            }
            let prefix = if path.is_empty() { String::new() } else { format!("{path}.") };
            for key in left_keys {
                compare_incumbent(&left[key], &right[key], &format!("{prefix}{key}"), out);
            }
        }
        (left, right) if left == right => {}
        (left, right) => out.push(format!(
            "{at}: {} {left} vs {} {right}",
            left.type_str(),
            right.type_str()
        )),
    }
}

