//! Trust (W4 HASHMAP r3, 2026-09-29): how many items an iterator over ALREADY-LIVE
//! std collections can yield, and whether a std destination can RESERVE that many
//! without a "capacity overflow" panic.
//!
//! Both halves of the allocation lane grant a "bounded std source": the extractor
//! rewrites a keyed `collect` / a collection `extend` over one to the TOTAL
//! sentinel (`into_iter_source_live_count` in trust-mir-extract), and vcgen skips
//! the `[unbounded_allocation]` charge of a `collect`/`from_iter`/`unzip`/
//! `collect_into`/`extend` over one (`collect_source_live_count`). The grant's
//! argument was "the source already holds its elements, so it cannot have more of
//! them than fit". That bounds the COUNT, and it is a bound on the destination's
//! allocation only when the destination spends no more per item than the source
//! does. MEASURED on the redo's r2 (`b9288112d`, probe round r2): a `&[u8]` of 2^28
//! bytes zipped with, or mapped to, a `MaybeUninit<[u8; 1 << 35]>` and collected into
//! a `HashMap<u8, _>` (or a `Vec<(u8, _)>`, or `extend`ed into either) built rc=0
//! and panicked "Hash table capacity overflow" / "capacity overflow": 2^28 items of
//! 2^35 bytes are 2^63 bytes.
//!
//! The grant now needs BOTH facts: the source is bounded ([`LiveSourceCount`]), and
//! the destination can hold that many items ([`contiguous_capacity_fits`],
//! [`hash_table_capacity_fits`]). The count bound rests on one modeled-fact axiom,
//! [`MAX_LIVE_USER_ADDRESS_SPACE_BYTES`].
//!
//! Trust (ALLOC-WIDTH-1, 2026-10-08): every item here is a 64-BIT fact — the axiom
//! is about 64-bit address spaces, and the fit checks use the 64-bit `isize::MAX`.
//! Both callers apply them only on a target whose pointer width is witnessed as 64
//! bits (the extractor's `bounded_source_fits_destination` reads
//! `tcx.data_layout`; vcgen's `bounded_source_fits_sink` and its live-receiver
//! charge read `VcgenContext::with_target_pointer_bits`). On a narrower target a
//! live receiver or source may already fill the object limit, so nothing here is
//! granted there.

/// MODELED-FACT AXIOM (docs/TCB.md, "Modeled-fact axioms"): the byte sizes of all
/// SIMULTANEOUSLY LIVE allocations of one process sum to less than `2^56`.
///
/// Live allocations are disjoint ranges of the process's user virtual address
/// space, and no current 64-bit target gives a process more than `2^56` bytes of it:
/// x86-64 with 5-level paging and RISC-V Sv57 have 56-bit user halves, AArch64 at
/// most 52 bits (48 on Apple silicon, whose user map ends below `2^47`), POWER at
/// 52. This is the same address-space reality `MAX_LIVE_ALLOC_BYTES`
/// (`trust-ir-bridge/src/lower.rs`) rests on ("current hardware is <= 2^57
/// virtual"), taken at the user half and over the whole process instead of one
/// allocation, because a node-based collection (`BTreeMap`, `LinkedList`) spans
/// several allocations. It bounds each LEAF of a source on its own; a `chain` sums
/// its sides' bounds, because both sides may walk one buffer
/// ([`LiveSourceCount::chain`]). A target whose user address space can exceed
/// `2^56` (s390x with five-level region tables) is outside the axiom.
///
/// SCOPE DISCIPLINE, as for `MAX_LIVE_ALLOC_BYTES`: it bounds only the item count of
/// a collection that ALREADY EXISTS (or the live length of an `extend` receiver),
/// never a REQUESTED count — `with_capacity(n)`'s `n` carries no such bound.
pub const MAX_LIVE_USER_ADDRESS_SPACE_BYTES: u128 = 1 << 56;

/// `isize::MAX` on the 64-bit lane: RawVec and hashbrown refuse any allocation
/// larger than this ("capacity overflow" / "Hash table capacity overflow").
const ISIZE_MAX_BYTES: u128 = i64::MAX as u128;

/// `usize::MAX` on the 64-bit lane (a zero-sized element's capacity arithmetic).
const USIZE_MAX: u128 = u64::MAX as u128;

/// The largest alignment rustc accepts (`#[repr(align(2^29))]`): an upper bound on
/// hashbrown's `ctrl_align = max(align_of::<T>(), Group::WIDTH)` for ANY element,
/// including an over-aligned zero-sized one.
const MAX_ALIGN_BYTES: u128 = 1 << 29;

/// hashbrown's `Group::WIDTH` upper bound (16 with SSE2/NEON, 8 generic).
const GROUP_WIDTH_BYTES: u128 = 16;

/// An upper bound on the items an iterator over already-live std collections
/// yields.
///
/// A LEAF is bounded on its own: `MAX_LIVE_USER_ADDRESS_SPACE_BYTES /
/// min_item_bytes`, where `min_item_bytes` is a LOWER bound (at least 1) on the
/// live bytes each of its items occupies — its exact size for a slice/`Vec`/array
/// element, one control byte plus the element for a hash table, at least one byte
/// of node storage for a `BTreeMap`/`LinkedList`, one byte for a `str` view. A
/// leaf no live memory backs is bounded by its item count (the single item of an
/// `Option`/`Result`).
///
/// A `chain` SUMS its sides' bounds rather than sharing one address space between
/// them: the two sides may walk the SAME live buffer (`v.iter().chain(v.iter())`
/// yields `2 * v.len()` items from `v.len()` slots), so only each side's own
/// bound is a fact. (Found in the round-3 review: a one-address-space rule
/// under-counted an aliased chain by up to its number of leaves.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiveSourceCount {
    max_items: u128,
}

impl LiveSourceCount {
    /// A leaf whose every item occupies at least `min_item_bytes` bytes of live
    /// memory (clamped to at least one byte: the caller has already established
    /// that the leaf is memory-bounded at all — the F3 zero-sized-element rule).
    #[must_use]
    pub fn memory_backed(min_item_bytes: u128) -> Self {
        Self { max_items: MAX_LIVE_USER_ADDRESS_SPACE_BYTES / min_item_bytes.max(1) }
    }

    /// A `str` view (`chars`, `bytes`, `split*`, `lines`, `matches`, ...) over an
    /// `L`-byte string yields at most `L + 2` items (`"abc".split("")` yields
    /// five), and `L < 2^56` by the axiom, so at most `2^56 + 1`.
    #[must_use]
    pub fn str_view() -> Self {
        Self { max_items: MAX_LIVE_USER_ADDRESS_SPACE_BYTES + 1 }
    }

    /// A source that yields at most `items` items with no live memory behind them
    /// (`Option`, `Result`).
    #[must_use]
    pub fn at_most(items: u128) -> Self {
        Self { max_items: items }
    }

    /// `a.chain(b)`: the SUM of both sides' bounds — the sides may alias one live
    /// buffer, so they do not share one address-space budget (see the type's doc).
    #[must_use]
    pub fn chain(self, other: Self) -> Self {
        Self { max_items: self.max_items.saturating_add(other.max_items) }
    }

    /// `a.zip(b)`: at most as many items as the shorter side.
    #[must_use]
    pub fn shorter(self, other: Self) -> Self {
        if self.max_items <= other.max_items { self } else { other }
    }

    /// The bound itself.
    #[must_use]
    pub fn max_items(self) -> u128 {
        self.max_items
    }
}

/// Can a CONTIGUOUS std buffer of `elem_bytes`-byte elements (`Vec`, `VecDeque`,
/// `String`, `BinaryHeap`, `Box<[T]>`, and the `Vec` a `BTreeMap`/`BTreeSet`
/// `from_iter` sorts in) reserve `items` elements without "capacity overflow"?
///
/// RawVec refuses `cap * size_of::<T>() > isize::MAX - (align_of::<T>() - 1)`; for a
/// sized non-zero-sized `T` the alignment divides the size, so `(items + 1) *
/// elem_bytes <= isize::MAX` implies it. A zero-sized element allocates nothing and
/// only needs `len + additional` to fit a `usize`.
#[must_use]
pub fn contiguous_capacity_fits(elem_bytes: u128, items: u128) -> bool {
    if elem_bytes == 0 {
        return items <= USIZE_MAX;
    }
    items
        .checked_add(1)
        .and_then(|slots| slots.checked_mul(elem_bytes))
        .is_some_and(|bytes| bytes <= ISIZE_MAX_BYTES)
}

/// Can a std `HashMap`/`HashSet` whose table element (`(K, V)` / `T`) is
/// `elem_bytes` bytes reserve `items` items without "Hash table capacity overflow"?
///
/// hashbrown 0.17.1 (`raw.rs`, `capacity_to_buckets` / `calculate_layout_for`):
/// at most 16 buckets below 15 items, otherwise `next_power_of_two(items * 8 / 7)`
/// (`items * 8` overflowing `usize` is itself the panic), and an allocation of
/// `round_up(elem_bytes * buckets, ctrl_align) + buckets + Group::WIDTH` bytes that
/// must not pass `isize::MAX - (ctrl_align - 1)`. With `ctrl_align <= 2^29` (rustc's
/// maximum alignment) the sufficient condition checked here is
/// `(elem_bytes + 1) * buckets + 2 * 2^29 + Group::WIDTH <= isize::MAX`.
#[must_use]
pub fn hash_table_capacity_fits(elem_bytes: u128, items: u128) -> bool {
    let buckets = if items < 15 {
        16
    } else {
        let Some(times_eight) = items.checked_mul(8).filter(|&v| v <= USIZE_MAX) else {
            return false;
        };
        match (times_eight / 7).checked_next_power_of_two() {
            Some(buckets) if buckets <= USIZE_MAX => buckets,
            _ => return false,
        }
    };
    elem_bytes
        .checked_add(1)
        .and_then(|per_bucket| per_bucket.checked_mul(buckets))
        .and_then(|bytes| bytes.checked_add(2 * MAX_ALIGN_BYTES + GROUP_WIDTH_BYTES))
        .is_some_and(|bytes| bytes <= ISIZE_MAX_BYTES)
}

/// The item count an `extend` receiver of `elem_bytes`-byte elements can ALREADY
/// hold while live — its `len`, which `Vec::reserve` adds to the requested
/// `additional` (and its buckets, which hashbrown's `reserve_rehash` compares
/// against). Bounded by [`MAX_LIVE_USER_ADDRESS_SPACE_BYTES`] like any live
/// collection; a hash table spends a control byte per bucket on top.
#[must_use]
pub fn live_receiver_items(elem_bytes: u128, hash_table: bool) -> u128 {
    let per_item = if hash_table { elem_bytes.saturating_add(1) } else { elem_bytes.max(1) };
    MAX_LIVE_USER_ADDRESS_SPACE_BYTES / per_item + 1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_measured_inflation_does_not_fit() {
        // probe r2: 2^28 bytes of `u8` into a 2^35-byte element (u8 + MaybeUninit).
        let source = LiveSourceCount::memory_backed(1);
        let elem = (1u128 << 35) + 8;
        assert!(!contiguous_capacity_fits(elem, source.max_items()));
        assert!(!hash_table_capacity_fits(elem, source.max_items()));
        // ... and it does not fit even at the source's measured 2^28 items.
        assert!(!hash_table_capacity_fits(elem, 1 << 28));
        assert!(!contiguous_capacity_fits(elem, 1 << 28));
    }

    #[test]
    fn ordinary_collects_still_fit() {
        let bytes_of_text = LiveSourceCount::str_view();
        // `text.split_whitespace().map(|w| (w, 1u32)).collect::<HashMap<&str, u32>>()`
        assert!(hash_table_capacity_fits(24, bytes_of_text.max_items()));
        // `... .map(|w| (w.to_string(), 0usize)).collect::<HashMap<String, usize>>()`
        assert!(hash_table_capacity_fits(32, bytes_of_text.max_items()));
        // `text.split(',').map(str::to_owned).collect::<Vec<String>>()`
        assert!(contiguous_capacity_fits(24, bytes_of_text.max_items()));
        // `v.iter().copied().collect::<HashSet<u64>>()` over a `&[u64]`
        assert!(hash_table_capacity_fits(8, LiveSourceCount::memory_backed(8).max_items()));
        // `names.iter().map(|n| (n.clone(), vec![])).collect::<HashMap<String, Vec<u8>>>()`
        assert!(hash_table_capacity_fits(48, LiveSourceCount::memory_backed(24).max_items()));
        // a `&[u8]` into a `Vec<u64>`
        assert!(contiguous_capacity_fits(8, LiveSourceCount::memory_backed(1).max_items()));
    }

    #[test]
    fn hash_table_boundary_is_hashbrowns() {
        // Below 15 items: at most 16 buckets.
        assert!(hash_table_capacity_fits(1 << 40, 14));
        // 2^56 one-byte items need 2^57 buckets: 64-byte elements are the edge.
        let n = 1u128 << 56;
        assert!(hash_table_capacity_fits(62, n));
        assert!(!hash_table_capacity_fits(64, n));
        // `items * 8` overflowing `usize` is itself the panic.
        assert!(!hash_table_capacity_fits(0, 1 << 61));
    }

    #[test]
    fn contiguous_boundary_is_isize_max() {
        assert!(contiguous_capacity_fits(1, (1 << 62) - 1));
        assert!(!contiguous_capacity_fits(2, 1 << 62));
        assert!(contiguous_capacity_fits(0, USIZE_MAX));
        assert!(!contiguous_capacity_fits(0, USIZE_MAX + 1));
    }

    #[test]
    fn chain_sums_its_sides_and_zip_takes_the_shorter() {
        let a = LiveSourceCount::memory_backed(8);
        let b = LiveSourceCount::str_view();
        assert_eq!(
            a.chain(b).max_items(),
            (MAX_LIVE_USER_ADDRESS_SPACE_BYTES >> 3) + MAX_LIVE_USER_ADDRESS_SPACE_BYTES + 1
        );
        // `v.iter().chain(v.iter())` walks ONE buffer twice: the sides do not share
        // an address-space budget, each is bounded on its own.
        assert_eq!(a.chain(a).max_items(), 2 * (MAX_LIVE_USER_ADDRESS_SPACE_BYTES >> 3));
        let bytes = LiveSourceCount::memory_backed(1);
        assert_eq!(bytes.chain(bytes).max_items(), 2 * MAX_LIVE_USER_ADDRESS_SPACE_BYTES);
        // ... which a destination sized for ONE side's bound need not hold: a
        // `HashMap` of 48-byte elements fits `2^56` items and not `2^57`.
        assert!(hash_table_capacity_fits(48, bytes.max_items()));
        assert!(!hash_table_capacity_fits(48, bytes.chain(bytes).max_items()));
        assert_eq!(a.shorter(b), a);
        assert_eq!(LiveSourceCount::at_most(1).shorter(b).max_items(), 1);
        assert_eq!(LiveSourceCount::at_most(1).chain(LiveSourceCount::at_most(1)).max_items(), 2);
        // A zero byte bound is clamped: a leaf is only built for a memory-bounded item.
        assert_eq!(LiveSourceCount::memory_backed(0), LiveSourceCount::memory_backed(1));
    }

    #[test]
    fn extend_receivers_are_live_too() {
        assert_eq!(live_receiver_items(8, false), (1 << 53) + 1);
        assert_eq!(live_receiver_items(0, false), (1 << 56) + 1);
        assert_eq!(live_receiver_items(7, true), (1 << 53) + 1);
    }
}
