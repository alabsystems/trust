//! The interval partition (plan §2.3 "Abstraction") over the descriptor
//! numbers a program can tell apart.
//!
//! The model is explored at the REAL constants: every descriptor number, every
//! limit and every `F_DUPFD` floor in a state is the number the program would
//! see, and every platform step is `trust_platform::step` on those numbers.
//! (An earlier scaled instance mapped large constants to small images; it
//! could not represent arithmetic on them, `setrlimit` operands, or
//! allocations that spill between two high intervals, and passed programs
//! that leak.) The partition is used for one thing only: choosing WHERE the
//! RL-INIT environment places a foreign descriptor ([`Partition::positions`]).
//!
//! A program compares descriptor numbers with its constants (and values
//! derived from them by `+ k` and `min`). Two numbers strictly between the same
//! two consecutive points behave alike under those comparisons, so a foreign
//! descriptor is placed at every point `c`, at `c - 1` and `c + 1` (the edges
//! of the neighbouring intervals), at `c + k` for every additive literal `k`
//! of the program, and at the lowest number of the "mid" interval above the
//! small points. This is an argued enumeration of the interesting classes,
//! not a proof that it is exhaustive — which is one reason a pass over a
//! derived model is never admitted (the payload is refutation-only).

use std::collections::BTreeSet;

/// Constants below this are "small": stdio, lane numbers, `F_DUPFD` floors.
pub const SMALL: i64 = 64;

/// The points of the partition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Partition {
    consts: Vec<i64>,
    offsets: Vec<i64>,
    mid_lo: i64,
}

impl Partition {
    /// The partition of `consts` (the program's and environment's constants)
    /// with the program's additive literals `offsets`.
    #[must_use]
    pub fn new(
        consts: impl IntoIterator<Item = i64>,
        offsets: impl IntoIterator<Item = i64>,
    ) -> Partition {
        let consts: BTreeSet<i64> = consts.into_iter().collect();
        let offsets: BTreeSet<i64> = offsets.into_iter().filter(|k| *k != 0).collect();
        let max_small = consts.iter().copied().filter(|v| *v < SMALL).max().unwrap_or(2).max(2);
        Partition {
            consts: consts.into_iter().collect(),
            offsets: offsets.into_iter().collect(),
            mid_lo: max_small + 1,
        }
    }

    /// The lowest number of the interval above the small points (where
    /// RL-INIT packs descriptor arguments that sit "somewhere below the
    /// ceiling").
    #[must_use]
    pub fn mid_lo(&self) -> i64 {
        self.mid_lo
    }

    #[must_use]
    pub fn constants(&self) -> &[i64] {
        &self.consts
    }

    #[must_use]
    pub fn offsets(&self) -> &[i64] {
        &self.offsets
    }

    /// Candidate positions of a foreign descriptor in `[lo, limit)`: every
    /// point and its two neighbours, every point shifted by every additive
    /// literal, and `extra` (the next free mid number of a layout).
    #[must_use]
    pub fn positions(&self, lo: i64, limit: i64, extra: &[i64]) -> Vec<i64> {
        let mut out: BTreeSet<i64> = BTreeSet::new();
        for c in &self.consts {
            for d in [-1, 0, 1] {
                out.insert(c.saturating_add(d));
            }
            for k in &self.offsets {
                out.insert(c.saturating_add(*k));
            }
        }
        out.extend(extra.iter().copied());
        out.into_iter().filter(|p| *p >= lo && *p < limit && *p <= i64::from(i32::MAX)).collect()
    }
}
