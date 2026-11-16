// trust-vcgen/src/generate/rebind_index.rs: place-name interning and the REBINDER
// index — every member of a written-name set that rebinds a given read name, found
// by the STRUCTURE of the read name instead of a scan of the set.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// THE RELATION. [`super::write_rebinds`]`(w, r)` is the disjunction of six string
// relations (1-5 and 7), and [`super::dest_write_rebinds`] adds a seventh (6):
//
//   1. `w == r`;
//   2. `w` is a projection DESCENDANT of `r` (`r` is a separator-prefix of `w`);
//   3. `w` is a projection ANCESTOR of `r` (`w` is a separator-prefix of `r`);
//   4. symbolic-index ALIAS: both contain `[`, their text before the first `[` is
//      equal, and at least one contains `[_`;
//   5. INDEX SEGMENT: `w` is a fallback `_<digits>` and `r` carries the whole segment
//      `[w]`;
//   6. (destinations only) DERIVED LENGTH: `r` is `x__slice_len` where `w == x` or `w`
//      is a separator-prefix of `x`;
//   7. LITERAL-INDEX ALIAS ([`super::path_defs::literal_index_segments_may_alias`]):
//      `w` and `r` first diverge inside a TOP-LEVEL index segment that opens at the
//      same byte of both, and the two segment spellings may name one element
//      (`v*[0;min=1]` / `v*[0;min=2]`, a from-end `[-1;min=1]` / a from-start `[3]`, a
//      subslice).
//
// Trust (merge 2026-10-14): channel 7 is the soundness line's c40884c0106 (a store
// through one slice pattern left a guard through another alive; nine programs PROVED
// kernel-certified that overflow or index out of bounds). It joined
// `place_names_overlap` after this index was written on the other line, and the merge
// (98b7fad77d2) kept both: the index (and `RebindSet`) answered channels 1-6 only, so
// every consumer that asks it instead of the predicate — the SSA version oracle, the
// block write index, the path-def `KillSet`, the definition extraction's clobber walk,
// the interval lane's havoc test — silently dropped the literal alias (the
// differentials caught it on `a[0;min=2]` and on `x_y[0]_.0` vs `x_y[]`). A missing
// rebinder is a SHORTER version union or a fact left unkilled: the false-PROVE
// direction.
//
// Each disjunct is answered by lookups keyed on pieces of `r` — `r` itself, its
// separator-prefixes, its bracket base, its bracket segments, its derived base, the
// text before each of its top-level index segments — plus ONE sorted-range scan for
// the descendants. Every lookup returns exactly the members satisfying that disjunct
// (proofs inline; channel 7's candidates are filtered by the predicate itself), so the
// union is exactly the members `w` with `write_rebinds(w, r)` (resp.
// `dest_write_rebinds`). No member is tested that the relation does not relate (but
// one corner of channel 7, see `LitBucket::for_each_candidate`) — the cost of a probe
// is the number of RELATED members, not the size of the set. (That number can itself
// be large: a base read against every tracked field below it. An existence probe stops at the first
// (`try_for_each_rebinder`); the version oracle's rebinder UNION cannot, and resolves
// it through a balanced tree of GROUP subjects over the rebinders instead, so a read
// costs O(log) resolutions per def that changed — see `version_ssa`, REBINDER UNIONS.)
//
// Parity with the predicates is pinned by `rebind_index_tests` (a brute-force
// comparison over a generated name grammar).

use std::ops::ControlFlow;

use trust_types::fx::{FxHashMap, FxHashSet};

use super::path_defs::{
    SLICE_LEN_SUFFIX, literal_index_segment_constant, literal_index_segments_may_alias,
};

/// A dense id for an interned place name.
pub(crate) type NameId = u32;

/// Interns place-name strings to dense ids, one table per function analysis.
#[derive(Default, Debug)]
pub(crate) struct NameTable {
    ids: FxHashMap<std::rc::Rc<str>, NameId>,
    names: Vec<std::rc::Rc<str>>,
}

impl NameTable {
    pub(crate) fn intern(&mut self, name: &str) -> NameId {
        if let Some(&id) = self.ids.get(name) {
            return id;
        }
        let rc: std::rc::Rc<str> = std::rc::Rc::from(name);
        let id = self.names.len() as NameId;
        self.names.push(std::rc::Rc::clone(&rc));
        self.ids.insert(rc, id);
        id
    }

    pub(crate) fn name(&self, id: NameId) -> &str {
        &self.names[id as usize]
    }

    /// The id of `name`, if interned.
    pub(crate) fn get(&self, name: &str) -> Option<NameId> {
        self.ids.get(name).copied()
    }

    pub(crate) fn len(&self) -> usize {
        self.names.len()
    }
}

/// Which relation a probe answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RebindMode {
    /// [`super::write_rebinds`]: channels 1-5 and 7.
    Plain,
    /// [`super::dest_write_rebinds`]: channels 1-7.
    Dest,
}

/// A projection separator: `.`, `[`, `*` or `@` (Downcast). The SAME set the
/// predicates this index answers for read ([`super::place_names_overlap`]'s
/// `proj_descendant`, `dest_write_rebinds`' derived-length prefix) — the index is
/// exact only while the two agree, so it is [`crate::is_projection_segment_lead`]
/// itself, never a second spelling. (W4 vecslice, 2026-09-25: `@` joined the
/// predicates so a whole write of an enum local kills a fact over its payload;
/// ported here at the rebase onto the rebinder index, 2026-09-29.)
fn is_sep(b: u8) -> bool {
    crate::is_projection_segment_lead(b)
}

/// `_<digits>` with at least one digit — the fallback spelling of a local.
pub(crate) fn is_fallback_name(s: &str) -> bool {
    s.strip_prefix('_').is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_digit()))
}

/// Channel 7's keys of `name`: every TOP-LEVEL index segment that closes, as the text
/// before its `[` and the segment's spelling (the text up to the first following `]`).
/// A `[` opens a top-level segment iff the bracket depth of the text before it is 0,
/// with `[` adding one and `]` taking one away (saturating) — the walk
/// [`literal_index_segments_may_alias`] makes over the common prefix of its two names.
///
/// Why the keys are complete: when that predicate holds for `(w, r)`, the segment it
/// compares opens at a byte `s` inside the common prefix (`w[..s] == r[..s]`, so the
/// depth there is the same for both, and 0), `w[s] == r[s] == '['`, and both segments
/// close. So `s` yields a key of `w` and a key of `r` with the same text before it.
fn for_each_top_level_segment(
    name: &str,
    mut f: impl FnMut(&str, &str) -> ControlFlow<()>,
) -> ControlFlow<()> {
    let Some(first) = name.find('[') else {
        return ControlFlow::Continue(());
    };
    let mut depth = 0usize;
    for (rel, b) in name[first..].bytes().enumerate() {
        let i = first + rel;
        if b == b'['
            && depth == 0
            && let Some(close) = name[i + 1..].find(']')
        {
            f(&name[..i], &name[i + 1..i + 1 + close])?;
        }
        match b {
            b'[' => depth += 1,
            b']' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    ControlFlow::Continue(())
}

/// Channel 7's bucket: the members whose top-level index segment opens after one given
/// text, grouped by the segment's SPELLING, the spellings indexed by class
/// ([`literal_index_segment_constant`]).
#[derive(Debug)]
struct LitBucket<M> {
    groups: FxHashMap<std::rc::Rc<str>, Vec<M>>,
    /// Spellings that are not a constant (a symbolic `_k`, a subslice, anything else).
    other: Vec<std::rc::Rc<str>>,
    /// Constant spellings counted from the start (index 0) and from the end (index 1).
    by_end: [Vec<std::rc::Rc<str>>; 2],
    /// Constant spellings by `(from_end, offset)`.
    by_const: FxHashMap<(bool, u128), Vec<std::rc::Rc<str>>>,
}

impl<M> Default for LitBucket<M> {
    fn default() -> Self {
        LitBucket {
            groups: FxHashMap::default(),
            other: Vec::new(),
            by_end: [Vec::new(), Vec::new()],
            by_const: FxHashMap::default(),
        }
    }
}

impl<M> LitBucket<M> {
    fn push(&mut self, spelling: &str, member: M) {
        if let Some(group) = self.groups.get_mut(spelling) {
            group.push(member);
            return;
        }
        let key: std::rc::Rc<str> = std::rc::Rc::from(spelling);
        match literal_index_segment_constant(spelling) {
            None => self.other.push(std::rc::Rc::clone(&key)),
            Some((from_end, offset)) => {
                self.by_end[usize::from(from_end)].push(std::rc::Rc::clone(&key));
                self.by_const.entry((from_end, offset)).or_default().push(std::rc::Rc::clone(&key));
            }
        }
        self.groups.insert(key, vec![member]);
    }

    /// Every member whose segment here may be the predicate's for a read whose segment
    /// here is spelled `spelling`: the predicate's last step holds for the two
    /// spellings (two constants counted from the same end name one element iff their
    /// offsets are equal; every other pair may alias), and the spellings DIFFER — or
    /// `spelling` holds a `[`.
    ///
    /// Why a different spelling suffices: two segments that open at one byte and are
    /// spelled differently first differ inside both or where one of them closes, so
    /// the common prefix ends inside the segment, at depth >= 1, and the predicate
    /// compares exactly these two segments. Why an identical spelling without a `[` is
    /// left out: the common prefix then runs through the `]` back to depth 0, so the
    /// predicate compares a LATER segment, which is another key of both names. (A `[`
    /// inside the spelling keeps the depth up, so that group is visited, and the
    /// caller's predicate filter decides it — the one candidate the relation may not
    /// relate.)
    fn for_each_candidate(
        &self,
        spelling: &str,
        mut f: impl FnMut(&M) -> ControlFlow<()>,
    ) -> ControlFlow<()> {
        let same_may_alias = spelling.contains('[');
        let mut scan = |spellings: &[std::rc::Rc<str>]| -> ControlFlow<()> {
            for s in spellings {
                if !same_may_alias && **s == *spelling {
                    continue;
                }
                for member in self.groups.get(s).into_iter().flatten() {
                    f(member)?;
                }
            }
            ControlFlow::Continue(())
        };
        scan(&self.other)?;
        match literal_index_segment_constant(spelling) {
            None => {
                scan(&self.by_end[0])?;
                scan(&self.by_end[1])?;
            }
            Some((from_end, offset)) => {
                scan(&self.by_end[usize::from(!from_end)])?;
                if let Some(same_end) = self.by_const.get(&(from_end, offset)) {
                    scan(same_end)?;
                }
            }
        }
        ControlFlow::Continue(())
    }
}

/// Add `member` to channel 7's buckets under every top-level segment of `name`.
fn lit_insert<K, M: Clone>(lit: &mut FxHashMap<K, LitBucket<M>>, name: &str, member: &M)
where
    K: std::borrow::Borrow<str> + std::hash::Hash + Eq + for<'a> From<&'a str>,
{
    let _ = for_each_top_level_segment(name, |prefix, spelling| {
        match lit.get_mut(prefix) {
            Some(bucket) => bucket.push(spelling, member.clone()),
            None => {
                let mut bucket = LitBucket::default();
                bucket.push(spelling, member.clone());
                lit.insert(K::from(prefix), bucket);
            }
        }
        ControlFlow::Continue(())
    });
}

/// Channel 7: visit every member of `lit` that the predicate relates to `read`.
fn lit_rebinders<K, M>(
    lit: &FxHashMap<K, LitBucket<M>>,
    read: &str,
    text: impl Fn(&M) -> &str,
    probes: &mut u64,
    mut visit: impl FnMut(&M) -> ControlFlow<()>,
) -> ControlFlow<()>
where
    K: std::borrow::Borrow<str> + std::hash::Hash + Eq,
{
    if lit.is_empty() {
        return ControlFlow::Continue(());
    }
    for_each_top_level_segment(read, |prefix, spelling| {
        *probes += 1;
        let Some(bucket) = lit.get(prefix) else { return ControlFlow::Continue(()) };
        bucket.for_each_candidate(spelling, |member| {
            *probes += 1;
            if literal_index_segments_may_alias(text(member), read) {
                visit(member)
            } else {
                ControlFlow::Continue(())
            }
        })
    })
}

const SEPS_SORTED: [u8; 4] = [b'*', b'.', b'@', b'['];
const _: () = {
    assert!(crate::PROJECTION_SEGMENT_LEAD.len() == SEPS_SORTED.len());
    assert!(SEPS_SORTED[0] < SEPS_SORTED[1]);
    assert!(SEPS_SORTED[1] < SEPS_SORTED[2]);
    assert!(SEPS_SORTED[2] < SEPS_SORTED[3]);
    let mut i = 0;
    while i < crate::PROJECTION_SEGMENT_LEAD.len() {
        let c = crate::PROJECTION_SEGMENT_LEAD[i] as u8;
        assert!(
            c == SEPS_SORTED[0]
                || c == SEPS_SORTED[1]
                || c == SEPS_SORTED[2]
                || c == SEPS_SORTED[3]
        );
        i += 1;
    }
    // `RebindSet::insert_with_derived_slice_len` relies on `SLICE_LEN_SUFFIX`
    // containing no projection separator byte (so `{base}__slice_len` adds no
    // separator-prefixes or brackets beyond `base`) and not ending in an ASCII
    // digit (so `{base}__slice_len` is never a fallback `_<digits>`).
    let sfx = SLICE_LEN_SUFFIX.as_bytes();
    assert!(!sfx.is_empty());
    assert!(!sfx[sfx.len() - 1].is_ascii_digit());
    let mut j = 0;
    while j < sfx.len() {
        let b = sfx[j];
        assert!(b != b'*' && b != b'.' && b != b'@' && b != b'[' && b != b']');
        j += 1;
    }
};

/// The rebinder index over a set of written names (member ids of one [`NameTable`]).
#[derive(Default, Debug)]
pub(crate) struct RebindIndex {
    /// name text -> member id (channels 1, 3, 5, 6).
    exact: FxHashMap<std::rc::Rc<str>, NameId>,
    /// Members sorted by name text (channel 2: descendant range scans).
    sorted: Vec<(std::rc::Rc<str>, NameId)>,
    /// Maximum byte length among indexed names (fast bound for channel 2).
    max_name_len: usize,
    /// Whether any indexed member is a `_<digits>` fallback (fast gate for channel 5).
    has_fallbacks: bool,
    /// bracket base -> members containing `[` with that base (channel 4, symbolic read).
    any_bracket: FxHashMap<std::rc::Rc<str>, Vec<NameId>>,
    /// bracket base -> members containing `[_` with that base (channel 4, literal read).
    sym_bracket: FxHashMap<std::rc::Rc<str>, Vec<NameId>>,
    /// text before a top-level index segment -> the members with a segment there
    /// (channel 7).
    lit: FxHashMap<std::rc::Rc<str>, LitBucket<(std::rc::Rc<str>, NameId)>>,
}

impl RebindIndex {
    /// Index the members `ids` (duplicates ignored).
    pub(crate) fn build(table: &NameTable, ids: impl IntoIterator<Item = NameId>) -> RebindIndex {
        let mut idx = RebindIndex::default();
        for id in ids {
            let text = std::rc::Rc::clone(&table.names[id as usize]);
            if idx.exact.insert(std::rc::Rc::clone(&text), id).is_some() {
                continue;
            }
            idx.max_name_len = idx.max_name_len.max(text.len());
            if !idx.has_fallbacks && is_fallback_name(&text) {
                idx.has_fallbacks = true;
            }
            if let Some(b_pos) = text.find('[') {
                let base: std::rc::Rc<str> = std::rc::Rc::from(&text[..b_pos]);
                idx.any_bracket.entry(std::rc::Rc::clone(&base)).or_default().push(id);
                if text[b_pos..].contains("[_") {
                    idx.sym_bracket.entry(base).or_default().push(id);
                }
                lit_insert(&mut idx.lit, &text, &(std::rc::Rc::clone(&text), id));
            }
            idx.sorted.push((text, id));
        }
        idx.sorted.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        crate::fn_memo::count_rebind_probes(idx.sorted.len() as u64);
        idx
    }

    pub(crate) fn contains(&self, name: &str) -> Option<NameId> {
        self.exact.get(name).copied()
    }

    /// Visit every member `w` with `write_rebinds(w, read)` (Plain) or
    /// `dest_write_rebinds(w, read)` (Dest). A member may be visited more than once
    /// (it can satisfy several disjuncts); callers union.
    pub(crate) fn for_each_rebinder(
        &self,
        read: &str,
        mode: RebindMode,
        mut visit: impl FnMut(NameId),
    ) {
        let _ = self.try_for_each_rebinder(read, mode, |id| {
            visit(id);
            ControlFlow::Continue(())
        });
    }

    /// [`Self::for_each_rebinder`] with an early exit: the walk stops at the first
    /// `visit` that answers `Break`, so an existence probe costs the lookups up to its
    /// first hit instead of the whole rebinder set (a read with a long descendant range
    /// or a large alias bucket).
    pub(crate) fn try_for_each_rebinder(
        &self,
        read: &str,
        mode: RebindMode,
        mut visit: impl FnMut(NameId) -> ControlFlow<()>,
    ) -> ControlFlow<()> {
        if self.exact.is_empty() {
            return ControlFlow::Continue(());
        }
        let mut probes = 0u64;
        let flow = self.walk(read, mode, &mut visit, &mut probes);
        crate::fn_memo::count_rebind_probes(probes);
        flow
    }

    fn walk(
        &self,
        read: &str,
        mode: RebindMode,
        visit: &mut dyn FnMut(NameId) -> ControlFlow<()>,
        probes: &mut u64,
    ) -> ControlFlow<()> {
        let hit = |name: &str,
                   visit: &mut dyn FnMut(NameId) -> ControlFlow<()>,
                   probes: &mut u64|
         -> ControlFlow<()> {
            *probes += 1;
            match self.exact.get(name) {
                Some(&id) => visit(id),
                None => ControlFlow::Continue(()),
            }
        };
        // 1. equality.
        hit(read, visit, probes)?;
        // 3. `w` a separator-prefix of `read` (`w` a projection ANCESTOR):
        //    `proj_descendant(read, w)` ⟺ `read.len() > w.len() && read.starts_with(w)
        //    && read[w.len()]` is a separator ⟺ `w == read[..i]` for such an `i`
        //    (`i == 0` included: the empty string is a separator-prefix of a name that
        //    starts with a separator, exactly as `place_names_overlap`'s
        //    `proj_descendant` decides).
        let mut first_bracket: Option<usize> = None;
        for (i, b) in read.bytes().enumerate() {
            if is_sep(b) {
                if b == b'[' && first_bracket.is_none() {
                    first_bracket = Some(i);
                }
                hit(&read[..i], visit, probes)?;
            }
        }
        // 2. `read` a separator-prefix of `w` (`w` a projection DESCENDANT): exactly
        //    the members starting with `read + c` for a separator `c`, a contiguous
        //    range of the sorted members for each `c`.
        let rb = read.as_bytes();
        if rb.len() < self.max_name_len {
            let mut lo = 0usize;
            let mut prefix_anchored = false;
            'sep_loop: for sb in SEPS_SORTED {
                let need_search = if prefix_anchored {
                    match self.sorted.get(lo) {
                        None => break,
                        Some((t, _)) => {
                            let tb = t.as_bytes();
                            if !tb.starts_with(rb) {
                                break;
                            }
                            // `prefix_anchored` guarantees `tb > rb`; combined with
                            // `tb.starts_with(rb)` we have `tb.len() > rb.len()`.
                            let next_b = tb[rb.len()];
                            if next_b > SEPS_SORTED[SEPS_SORTED.len() - 1] {
                                break;
                            }
                            if next_b > sb {
                                continue;
                            }
                            next_b < sb
                        }
                    }
                } else {
                    true
                };
                if need_search {
                    lo += self.sorted[lo..].partition_point(|(t, _)| {
                        let tb = t.as_bytes();
                        let common = tb.len().min(rb.len());
                        match tb[..common].cmp(&rb[..common]) {
                            std::cmp::Ordering::Less => true,
                            std::cmp::Ordering::Greater => false,
                            std::cmp::Ordering::Equal => tb.get(rb.len()).is_none_or(|&b| b < sb),
                        }
                    });
                    prefix_anchored = true;
                }
                while let Some((t, id)) = self.sorted.get(lo) {
                    *probes += 1;
                    let tb = t.as_bytes();
                    if tb.len() <= rb.len() || !tb.starts_with(rb) {
                        break 'sep_loop;
                    }
                    if tb[rb.len()] != sb {
                        break;
                    }
                    visit(*id)?;
                    lo += 1;
                }
            }
        }
        if let Some(b_pos) = first_bracket {
            let base = &read[..b_pos];
            // 4. symbolic-index alias: `read` has a `[`; a member with the same text before
            //    its first `[` is related iff one of the two contains `[_`. If `read` does,
            //    every such member is; otherwise exactly those containing `[_`.
            if !self.any_bracket.is_empty() {
                *probes += 1;
                let bucket = if read[b_pos..].contains("[_") {
                    self.any_bracket.get(base)
                } else {
                    self.sym_bracket.get(base)
                };
                for &id in bucket.into_iter().flatten() {
                    *probes += 1;
                    visit(id)?;
                }
            }
            // 5. index segment: `w` is `_<digits>` and `read` carries the whole segment
            //    `[w]`, i.e. `w` is the text between a `[` and the first following `]` —
            //    the scan `write_covers_index_segment` performs.
            if self.has_fallbacks {
                let mut from = b_pos;
                while let Some(off) = read[from..].find('[') {
                    let start = from + off + 1;
                    if let Some(close) = read[start..].find(']') {
                        let seg = &read[start..start + close];
                        if is_fallback_name(seg) {
                            hit(seg, visit, probes)?;
                        }
                    }
                    from = start;
                }
            }
            // 7. literal-index alias: the members sharing the text before one of `read`'s
            //    top-level index segments, with a segment there that may name the element
            //    `read`'s names (`LitBucket::for_each_candidate`), each decided by the
            //    predicate itself.
            if !self.lit.is_empty() {
                lit_rebinders(&self.lit, read, |m| &*m.0, probes, |m| visit(m.1))?;
            }
        }
        // 6. derived length (destinations only): `read == x__slice_len` and `w == x`
        //    or `w` a separator-prefix of `x`.
        if mode == RebindMode::Dest
            && let Some(base) = read.strip_suffix(SLICE_LEN_SUFFIX)
        {
            hit(base, visit, probes)?;
            for (i, b) in base.bytes().enumerate() {
                if is_sep(b) {
                    hit(&base[..i], visit, probes)?;
                }
            }
        }
        ControlFlow::Continue(())
    }

    /// Whether some member rebinds `read` — stops at the first rebinder.
    pub(crate) fn any_rebinder(&self, read: &str, mode: RebindMode) -> bool {
        self.try_for_each_rebinder(read, mode, |_| ControlFlow::Break(())).is_break()
    }
}

/// An INCREMENTAL set of written names answering "does some member `write_rebinds`
/// this read" — channels 1-5 and 7 of the relation (the module doc), by the same lookups
/// [`RebindIndex`] makes, with the descendant channel answered by the set of every
/// member's separator-prefixes instead of a sorted range (so members can be added
/// between queries). A reverse definition walk that grows its clobber set statement by
/// statement and tests every free variable of every earlier definition against it was
/// quadratic in the block with a scan of the set per test.
#[derive(Default, Debug)]
pub(crate) struct RebindSet {
    /// Inserted members mapped to whether `{member}__slice_len` was also inserted via
    /// [`Self::insert_with_derived_slice_len`] without allocating a second string/entry.
    exact: FxHashMap<Box<str>, bool>,
    /// Every separator-prefix of every member (channel 2: `read` is one of them iff a
    /// member is a projection DESCENDANT of `read`).
    sep_prefixes: FxHashSet<Box<str>>,
    /// Whether any inserted member is `_<digits>` (fast gate for channel 5).
    has_fallbacks: bool,
    /// Whether any member carries `true` in `exact` (fast gate for derived-length hits).
    has_derived_slice_lens: bool,
    /// Bracket bases of the members containing `[` / containing `[_` (channel 4).
    any_bracket: FxHashSet<Box<str>>,
    sym_bracket: FxHashSet<Box<str>>,
    /// text before a top-level index segment -> the members with a segment there
    /// (channel 7).
    lit: FxHashMap<Box<str>, LitBucket<std::rc::Rc<str>>>,
}

impl RebindSet {
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.exact.is_empty()
    }

    pub(crate) fn insert(&mut self, name: &str) {
        self.insert_inner(name, false);
    }

    /// Equivalent to `self.insert(name)` plus (when `!name.ends_with(SLICE_LEN_SUFFIX)`)
    /// `self.insert(&format!("{name}{SLICE_LEN_SUFFIX}"))`, avoiding formatting and
    /// hashing the derived `{name}__slice_len` twin when `name` contains no `[`.
    pub(crate) fn insert_with_derived_slice_len(&mut self, name: &str) {
        if name.ends_with(SLICE_LEN_SUFFIX) {
            self.insert_inner(name, false);
            return;
        }
        if name.contains('[') {
            self.insert_inner(name, false);
            self.insert_inner(&format!("{name}{SLICE_LEN_SUFFIX}"), false);
            return;
        }
        self.has_derived_slice_lens = true;
        if let Some(has_derived) = self.exact.get_mut(name) {
            *has_derived = true;
            return;
        }
        self.insert_inner(name, true);
    }

    fn insert_inner(&mut self, name: &str, with_derived_slice_len: bool) {
        if let Some(has_derived) = self.exact.get_mut(name) {
            *has_derived |= with_derived_slice_len;
            return;
        }
        if !self.has_fallbacks && is_fallback_name(name) {
            self.has_fallbacks = true;
        }
        self.exact.insert(name.into(), with_derived_slice_len);
        let mut first_bracket: Option<usize> = None;
        for (i, b) in name.bytes().enumerate() {
            if is_sep(b) {
                if b == b'[' && first_bracket.is_none() {
                    first_bracket = Some(i);
                }
                if !self.sep_prefixes.contains(&name[..i]) {
                    self.sep_prefixes.insert(name[..i].into());
                }
            }
        }
        if let Some(b_pos) = first_bracket {
            let base = &name[..b_pos];
            if !self.any_bracket.contains(base) {
                self.any_bracket.insert(base.into());
            }
            if name[b_pos..].contains("[_") && !self.sym_bracket.contains(base) {
                self.sym_bracket.insert(base.into());
            }
            lit_insert(&mut self.lit, name, &std::rc::Rc::from(name));
        }
    }

    #[inline]
    fn contains_exact(&self, candidate: &str) -> bool {
        self.exact.contains_key(candidate)
            || (self.has_derived_slice_lens
                && candidate
                    .strip_suffix(SLICE_LEN_SUFFIX)
                    .is_some_and(|base| self.exact.get(base) == Some(&true)))
    }

    /// Whether some member `w` has `write_rebinds(w, read)`.
    pub(crate) fn any_rebinder(&self, read: &str) -> bool {
        crate::fn_memo::count_rebind_probes(1);
        if self.exact.is_empty() {
            return false;
        }
        // 1. equality; 2. a member below `read`.
        if self.contains_exact(read) || self.sep_prefixes.contains(read) {
            return true;
        }
        // 3. a member above `read` (one of its separator-prefixes).
        let mut first_bracket: Option<usize> = None;
        for (i, b) in read.bytes().enumerate() {
            if is_sep(b) {
                if b == b'[' && first_bracket.is_none() {
                    first_bracket = Some(i);
                }
                if self.contains_exact(&read[..i]) {
                    return true;
                }
            }
        }
        if let Some(b_pos) = first_bracket {
            let base = &read[..b_pos];
            // 4. symbolic-index alias.
            let bucket =
                if read[b_pos..].contains("[_") { &self.any_bracket } else { &self.sym_bracket };
            if bucket.contains(base) {
                return true;
            }
            // 5. index segment `[w]` of a fallback member `w`.
            if self.has_fallbacks {
                let mut from = b_pos;
                while let Some(off) = read[from..].find('[') {
                    let start = from + off + 1;
                    if let Some(close) = read[start..].find(']') {
                        let seg = &read[start..start + close];
                        if is_fallback_name(seg) && self.exact.contains_key(seg) {
                            return true;
                        }
                    }
                    from = start;
                }
            }
            // 7. literal-index alias (see `RebindIndex::walk`).
            if !self.lit.is_empty() {
                let mut probes = 0u64;
                let hit =
                    lit_rebinders(&self.lit, read, |m| &**m, &mut probes, |_| ControlFlow::Break(()))
                        .is_break();
                crate::fn_memo::count_rebind_probes(probes);
                return hit;
            }
        }
        false
    }
}
