/*!
The byte-frequency heuristic that substring searchers use to pick a prefilter.

Upstream this module also carries `Finder` and `Pair`, the "packed pair"
prefilter itself. That prefilter exists to feed candidate offsets to a
vectorised confirmation step; there is no vectorised step in this crate, so the
prefilter has nothing to accelerate and is absent rather than stubbed.

[`HeuristicFrequencyRank`] stays, because it appears in the signature of
`memmem::FinderBuilder::build_forward_with_ranker`, which is public API. A
ranker only ever influenced *which* bytes a prefilter watched, never which
offsets a search reported, so a custom ranker changes nothing observable here.
*/

/// This trait allows the user to customize the byte frequency table used when
/// building a substring searcher.
///
/// # Background
///
/// A substring searcher may use a heuristic prefilter that watches for the
/// rarest bytes of the needle, on the theory that a rare byte is a cheap
/// predictor of a full match. "Rare" is defined by a background frequency
/// distribution over the bytes of the haystack, which for a general-purpose
/// library can only be a guess.
///
/// # Applicability in this crate
///
/// This crate's substring search is a single scalar algorithm with no
/// prefilter, so an implementation of this trait is accepted and ignored. It is
/// retained so that code written against upstream memchr — including code
/// defining its own ranker — compiles and behaves identically. Results are
/// unaffected either way; only upstream's *speed* ever depended on the ranking.
pub trait HeuristicFrequencyRank {
    /// Return the heuristic frequency rank of the given byte. A lower rank
    /// means the byte is believed to occur less frequently in the haystack.
    ///
    /// Some uses of this heuristic may treat arbitrary absolute rank values as
    /// significant. For example, an implementation detail in this crate may
    /// determine that heuristic prefilters are inappropriate if every byte in
    /// the needle has a "high" rank.
    fn rank(&self, byte: u8) -> u8;
}

/// This permits passing any implementation of `HeuristicFrequencyRank` as a
/// borrowed version of itself.
impl<'a, R> HeuristicFrequencyRank for &'a R
where
    R: HeuristicFrequencyRank,
{
    fn rank(&self, byte: u8) -> u8 {
        (**self).rank(byte)
    }
}
