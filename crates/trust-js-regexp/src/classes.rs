//! CharSet algebra: sorted disjoint code-point ranges + (for v-mode)
//! strings, with the spec's fold operations.
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::unicode::{canonicalize, fold_sources, Fold};

/// A CharSet: sorted, merged ranges of code points, plus (v-mode only)
/// a set of strings (each a code-point sequence of length != 1; length-1
/// strings live in `ranges`). `strings` is sorted by (len desc, lexi) —
/// the spec's matcher preference order (longer strings first; the empty
/// string, if present, sorts last).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CharSet {
    pub ranges: Vec<(u32, u32)>,
    pub strings: Vec<Vec<u32>>,
}

pub const MAX_CP: u32 = 0x10FFFF;

impl CharSet {
    pub fn from_ranges(mut ranges: Vec<(u32, u32)>) -> CharSet {
        normalize(&mut ranges);
        CharSet { ranges, strings: Vec::new() }
    }

    pub fn single(cp: u32) -> CharSet {
        CharSet { ranges: vec![(cp, cp)], strings: Vec::new() }
    }

    pub fn add_range(&mut self, lo: u32, hi: u32) {
        self.ranges.push((lo, hi));
        normalize(&mut self.ranges);
    }

    /// Add a string (v-mode). Length-1 strings fold into `ranges`.
    pub fn add_string(&mut self, s: Vec<u32>) {
        if s.len() == 1 {
            self.add_range(s[0], s[0]);
        } else if !self.strings.contains(&s) {
            self.strings.push(s);
            sort_strings(&mut self.strings);
        }
    }

    pub fn union(&self, other: &CharSet) -> CharSet {
        let mut ranges = self.ranges.clone();
        ranges.extend_from_slice(&other.ranges);
        normalize(&mut ranges);
        let mut strings = self.strings.clone();
        for s in &other.strings {
            if !strings.contains(s) {
                strings.push(s.clone());
            }
        }
        sort_strings(&mut strings);
        CharSet { ranges, strings }
    }

    pub fn intersect(&self, other: &CharSet) -> CharSet {
        let mut out = Vec::new();
        let (mut i, mut j) = (0, 0);
        while i < self.ranges.len() && j < other.ranges.len() {
            let (a1, b1) = self.ranges[i];
            let (a2, b2) = other.ranges[j];
            let lo = a1.max(a2);
            let hi = b1.min(b2);
            if lo <= hi {
                out.push((lo, hi));
            }
            if b1 < b2 { i += 1 } else { j += 1 }
        }
        let strings = self
            .strings
            .iter()
            .filter(|s| other.strings.contains(s))
            .cloned()
            .collect();
        CharSet { ranges: out, strings }
    }

    pub fn subtract(&self, other: &CharSet) -> CharSet {
        let mut out = self.intersect(&CharSet {
            ranges: complement_ranges(&other.ranges, 0, MAX_CP),
            strings: Vec::new(),
        });
        out.strings = self
            .strings
            .iter()
            .filter(|s| !other.strings.contains(s))
            .cloned()
            .collect();
        sort_strings(&mut out.strings);
        out
    }

    /// Complement of the character part within `universe`. Caller must have
    /// ruled out strings (MayContainStrings early errors).
    pub fn complement_within(&self, universe: &[(u32, u32)]) -> CharSet {
        let uni = CharSet { ranges: universe.to_vec(), strings: Vec::new() };
        uni.subtract(&CharSet { ranges: self.ranges.clone(), strings: Vec::new() })
    }

    /// The image of this set under a fold: { canon(c) : c ∈ set }, strings
    /// folded elementwise. Exact and cheap: only fold-source points can map
    /// away from themselves, so the image is (set − sources) ∪
    /// { canon(c) : c ∈ set ∩ sources }.
    pub fn fold_image(&self, fold: Fold) -> CharSet {
        if fold == Fold::None {
            return self.clone();
        }
        let sources = fold_sources(fold);
        let src_set = CharSet { ranges: sources.to_vec(), strings: Vec::new() };
        let me = CharSet { ranges: self.ranges.clone(), strings: Vec::new() };
        let mut out = me.subtract(&src_set);
        let moved = me.intersect(&src_set);
        let mut extra = Vec::new();
        for &(a, b) in &moved.ranges {
            for cp in a..=b {
                extra.push(canonicalize(cp, fold));
            }
        }
        for cp in extra {
            out.ranges.push((cp, cp));
        }
        normalize(&mut out.ranges);
        out.strings = self
            .strings
            .iter()
            .map(|s| s.iter().map(|&c| canonicalize(c, fold)).collect())
            .collect();
        dedup_strings(&mut out.strings);
        out
    }
}

fn normalize(ranges: &mut Vec<(u32, u32)>) {
    ranges.sort_unstable();
    let mut out: Vec<(u32, u32)> = Vec::with_capacity(ranges.len());
    for &(a, b) in ranges.iter() {
        debug_assert!(a <= b);
        if let Some(last) = out.last_mut() {
            if a <= last.1.saturating_add(1) {
                last.1 = last.1.max(b);
                continue;
            }
        }
        out.push((a, b));
    }
    *ranges = out;
}

fn sort_strings(strings: &mut [Vec<u32>]) {
    strings.sort_by(|a, b| b.len().cmp(&a.len()).then_with(|| a.cmp(b)));
}

fn dedup_strings(strings: &mut Vec<Vec<u32>>) {
    sort_strings(strings);
    strings.dedup();
}

pub fn complement_ranges(ranges: &[(u32, u32)], lo: u32, hi: u32) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    let mut cur = lo;
    for &(a, b) in ranges {
        if a > cur {
            out.push((cur, a - 1));
        }
        cur = cur.max(b.saturating_add(1));
        if cur > hi {
            break;
        }
    }
    if cur <= hi {
        out.push((cur, hi));
    }
    out
}
