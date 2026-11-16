// Trust (VEC-LEN-LOOP-1, 2026-10-07; review round 1 the same day): the length of a std
// `Vec` that nothing between its establishing read and an index can change, tied at
// each std index call that reads it.
//
// THE DEFECT. A std `Vec` is abstracted to its length under its base local's own
// name (`guards::coll_len_var`), and the two producers of a length fact put it in
// channels that cannot carry it into a loop:
//
//  * `v = vec![x; n]` (`call_facts::vec_from_elem_len_facts`) is a SEMANTIC GUARD.
//    `build_semantic_guard_map` weakens a block to `true` the second time it is
//    reached with different guards, so the fact never survives a loop header.
//  * `_k = v.len()` (`guards::slice_last_some_nonempty_definitions`) is a PATH
//    DEFINITION. The fixpoint kills it at every call that havocs the name `v`. For a
//    `&mut Vec` parameter that is EVERY call: the name is in the whole-function havoc
//    list (`mutable_pointer_local_names`), and `escape_havoc` keeps it because the
//    pointer is handed to `index_mut`. For an owned `Vec` whose `&mut` is taken
//    (`v[i] = x`) it is every call too (`mutably_borrowed_havoc_names`).
//
// Measured on the stage 1 of `7be75e9a80`: `let v = vec![0u8; n]; for i in 0..n {
// v[i] }` and `fn(v: &mut Vec<u8>) { for i in 0..v.len() { v[i] = 1 } }` both read
// `slice failed`, with a counterexample whose `Vec` length is 0, while `&[u8]` over
// `0..v.len()` proved (its length `v__slice_len` is a separate name no havoc of `v`
// reaches).
//
// WHY NOT RELAX A KILL. The version oracle does NOT re-version the name `v` of a
// `&mut Vec` parameter across a call that receives the pointer: after
// `v.truncate(i)` the index still reads bare `v`, the same symbol the pre-loop
// `_k == v` tie names. The kill is what keeps `for i in 0..n { v.truncate(i); v[i] }`
// refuted today. Narrowing it for `index_mut` would also need the opaque element
// store `*elem = 1` (whose havoc list holds `v` too) narrowed, and each narrowing
// would rest on the same unversioned spelling. A second blind spot sits under the
// same kill: `guards::local_mut_borrows_may_resize_one` (behind `coll_base_len_stable`)
// looks only at `&mut`/raw BORROWS of the base, and real MIR passes a `&mut Vec`
// parameter to `Vec::truncate` as `copy _1`, no reborrow, so that oracle calls the
// parameter's length stable in `truncates`/`pops` and the existing tie IS emitted;
// only the kill refuted them (KNOWN_HAZARDS, VEC-LEN-PARAM-COPY-1, CLOSED 2026-10-07:
// that oracle now counts the pointer's own copy into a non-benign callee as a resize,
// so for a `&mut Vec` parameter that reaches ANY resizer the earlier gate
// `collection_abstract_len_with_base` answers `container-index-unstable-len` before
// this module sees the row; `push_then_rw`/`rw_then_truncate` lost their proof to
// that, see DECISION_QUEUE). This module does not touch the kill or the versioning;
// it adds a fact whose truth does not depend on any of them, and its own scan
// classifies `copy _1` as a resizer receiver.
//
// THE FACT. For a base `B` ([`vec_len_never_changes`]: every mention of `B` in the
// body is one that cannot change the `Vec`'s length, or the whole receiver of a
// non-retaining std `Vec` resizer, `push`/`pop`/`truncate`/.. by real-sysroot `alloc`
// identity, whose block is recorded), at a block `U` whose terminator is std's own
// `Index::index`/`IndexMut::index_mut` on a receiver tracing to `B`, for each
// establishing call in block `D` returning to `T` with no recorded resizer block in
// the STRETCH from `T` to `U` (the blocks on a path `T ->* U` that never enters `D`):
//
//   * `_k == len(B)` for `_k = Vec::len(r)`, `r` tracing to `B`, `_k` single-static-
//     assignment, the call's return target `T` entered only from the call block, and
//     `T` dominating `U`;
//   * `len(B) == n` for `B = vec![x; n]` (owned `B`, its one write), under the same
//     target gates, with `n` a constant or a single-static-assignment local whose
//     defining block dominates the call block (a parameter qualifies).
//
// Each fact is renamed at `U`'s terminal, the point the index row is renamed at, and
// put in `U`'s semantic-guard set, which every lane conjoins AFTER its row rename.
//
// SOUNDNESS. Let `D` be the establishing call's block and `U` the use block.
//  1. `B`'s length does not change between the last return of `D` before `U` and `U`.
//     [`vec_len_never_changes`] admits only: shared borrows of `B` (a `&Vec` cannot
//     resize a `Vec`: no interior mutability, and a write through a pointer derived
//     from `&T` is undefined behaviour, the TCB's "shared-reborrow immutability"
//     premise); `&mut B` temporaries and copies of a `&mut Vec` parameter consumed
//     ONLY as the whole receiver of std's own index / `len` / slice-view calls (std
//     contract: none changes the length, none retains the pointer, the `&mut [T]` view
//     reaches elements only) or of a non-retaining std `Vec` resizer (std contract: it
//     may change the length DURING the call, and retains no pointer after it); `Drop(B)`;
//     and, for an owned `B`, its one whole write. Any other mention, a raw borrow, a
//     projected write, a copy into another local, a move, a user or forged-`alloc`
//     callee, an unrecognised statement, refuses the base for the WHOLE body (such a
//     callee may retain the pointer and a later call resize through it). Mentions are
//     found by scanning each serialized statement and terminator for the place local,
//     so a variant this code does not list is a refusal, not a miss. So the length can
//     change only inside a recorded resizer call. Every block that runs after that
//     return of `D` and before `U` lies on a path `T ->* U` that does not re-enter `D`
//     (the STRETCH; computed over the full-graph successors plus unwind cleanup edges,
//     a superset only refuses more), and a fact is placed only when no recorded resizer
//     block is in it. A call returning to its own block (`T == D`) is refused.
//  2. `_k` / `n` denote at `U` the values they had at the last execution of `D` before
//     `U`. A single static def site `N` that dominates `D`, with `D`'s target
//     dominating `U`, cannot execute between that `D` and `U`: the suffix from such an
//     `N` to `U` would avoid `D`, and the shortest entry-to-`N` path avoids `D` (`N`
//     dominates `D`), so their concatenation would reach `U` without passing `D`.
//     The same argument puts the last write of an owned `B` before that `D`.
//  3. The target is entered only from `D` (`call_facts::sole_predecessor_is`, unwind
//     edges included), so entering it means `D` returned normally: `_k` holds the
//     length then, and `B` is the vector `from_elem` returned.
// By 1-3 the fact is true at every point of `U`. Renamed at `U`'s terminal it names
// the values there; a row reading a name the block rewrote before its own point
// carries a different token and the fact does not bind it. The facts are hypotheses
// only: they can turn FAIL into PROVE for a program that does not change the length,
// and a body that may change it gets none.
//
// NOT COVERED (open, DECISION_QUEUE VEC-LEN-LOOP-1): an unknown callee that receives
// the `Vec` ANYWHERE in the body (even before the length is read) still refuses the
// base (`opaque(v); for i in 0..v.len() { v[i] }` reads `slice failed`); and the
// general loop-head frame loss this module works around (the guard map's join
// weakening drops every fact at a loop header; the path-definition kill havocs a `&mut`
// parameter at every call) is unchanged for every other fact.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

/// The base-local kinds whose length this module can hold invariant.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum BaseKind {
    /// An owned std `Vec` local, written exactly once.
    Owned,
    /// A `&mut Vec` parameter, never written.
    MutParam,
}

#[derive(Default)]
struct LocalMentionSites {
    stmts: Vec<(u32, u32)>,
    terms: Vec<u32>,
}

/// Indexed `"local":N[,}]` mentions across serialized statements and terminators of `func`.
///
/// Built in one pass using a single reusable `Vec<u8>` scratch buffer instead of
/// allocating `S + B` JSON `String`s and rescanning every statement/terminator per
/// base local and per `&mut` temporary.
struct BodyText {
    dense: Vec<LocalMentionSites>,
    sparse: FxHashMap<usize, LocalMentionSites>,
}

impl BodyText {
    /// Scan serialized JSON `bytes` for every canonical `"\"local\":{local}[,}]"` pattern,
    /// matching [`LocalTextMatcher`] byte-for-byte.
    fn for_each_mentioned_local(bytes: &[u8], mut f: impl FnMut(usize)) {
        const PREFIX: &[u8] = b"\"local\":";
        const MIN_MATCH_LEN: usize = PREFIX.len() + 2;
        if bytes.len() < MIN_MATCH_LEN {
            return;
        }
        let max_start = bytes.len() - MIN_MATCH_LEN;
        let mut pos = 0usize;
        while pos <= max_start {
            let search = &bytes[pos..=max_start];
            let Some(rel) = search.iter().position(|&b| b == b'"') else {
                break;
            };
            let start = pos + rel;
            if &bytes[start..start + PREFIX.len()] != PREFIX {
                pos = start + 1;
                continue;
            }
            let digits_start = start + PREFIX.len();
            let mut j = digits_start;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            let digits = &bytes[digits_start..j];
            if !digits.is_empty()
                && (digits.len() == 1 || digits[0] != b'0')
                && j < bytes.len()
                && matches!(bytes[j], b',' | b'}')
                && let Some(local) = digits.iter().try_fold(0usize, |acc, &d| {
                    acc.checked_mul(10)?.checked_add((d - b'0') as usize)
                })
            {
                f(local);
                pos = j + 1;
            } else {
                pos = digits_start;
            }
        }
    }

    #[inline]
    fn sites_mut(&mut self, local: usize) -> &mut LocalMentionSites {
        if local < self.dense.len() {
            &mut self.dense[local]
        } else {
            self.sparse.entry(local).or_default()
        }
    }

    #[inline]
    fn stmt_sites(&self, local: usize) -> &[(u32, u32)] {
        if let Some(s) = self.dense.get(local) {
            &s.stmts
        } else if let Some(s) = self.sparse.get(&local) {
            &s.stmts
        } else {
            &[]
        }
    }

    #[inline]
    fn term_blocks(&self, local: usize) -> &[u32] {
        if let Some(s) = self.dense.get(local) {
            &s.terms
        } else if let Some(s) = self.sparse.get(&local) {
            &s.terms
        } else {
            &[]
        }
    }

    /// `None` when any piece fails to serialize: every caller then refuses.
    fn build(func: &VerifiableFunction) -> Option<BodyText> {
        let mut out = BodyText {
            dense: (0..func.body.locals.len()).map(|_| LocalMentionSites::default()).collect(),
            sparse: FxHashMap::default(),
        };
        let mut buf = Vec::with_capacity(256);
        for (bi, b) in func.body.blocks.iter().enumerate() {
            let bi_u32 = u32::try_from(bi).ok()?;
            for (si, stmt) in b.stmts.iter().enumerate() {
                let si_u32 = u32::try_from(si).ok()?;
                buf.clear();
                serde_json::to_writer(&mut buf, stmt).ok()?;
                let site = (bi_u32, si_u32);
                Self::for_each_mentioned_local(&buf, |local| {
                    let stmts = &mut out.sites_mut(local).stmts;
                    if stmts.last() != Some(&site) {
                        stmts.push(site);
                    }
                });
            }
            buf.clear();
            serde_json::to_writer(&mut buf, &b.terminator).ok()?;
            Self::for_each_mentioned_local(&buf, |local| {
                let terms = &mut out.sites_mut(local).terms;
                if terms.last() != Some(&bi_u32) {
                    terms.push(bi_u32);
                }
            });
        }
        Some(out)
    }
}

/// Stack-allocated `"\"local\":{local},"` / `"\"local\":{local}}"` patterns for a local.
struct LocalTextMatcher {
    comma_buf: [u8; 32],
    brace_buf: [u8; 32],
    len: usize,
}

impl LocalTextMatcher {
    fn new(local: usize) -> Self {
        use std::io::Write;
        let mut comma_buf = [0u8; 32];
        let mut cursor = &mut comma_buf[..];
        let _ = write!(cursor, "\"local\":{local}");
        let prefix_len = 32 - cursor.len();
        comma_buf[prefix_len] = b',';
        let mut brace_buf = comma_buf;
        brace_buf[prefix_len] = b'}';
        Self { comma_buf, brace_buf, len: prefix_len + 1 }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    fn matches(&self, serialized: &str) -> bool {
        self.matches_bytes(serialized.as_bytes())
    }

    #[inline]
    fn matches_bytes(&self, haystack: &[u8]) -> bool {
        let pat_len = self.len;
        let pat_comma = &self.comma_buf[..pat_len];
        let pat_brace = &self.brace_buf[..pat_len];
        let mut rem = haystack;
        while rem.len() >= pat_len {
            let search = &rem[..=rem.len() - pat_len];
            let Some(pos) = search.iter().position(|&b| b == b'"') else {
                return false;
            };
            let cand = &rem[pos..pos + pat_len];
            if cand == pat_comma || cand == pat_brace {
                return true;
            }
            rem = &rem[pos + 1..];
        }
        false
    }

    /// Zero-allocation streaming check: answers `true` iff the serialized JSON of `val`
    /// contains `"\"local\":{local}[,}]"` OR fails to serialize (fail-closed).
    fn value_mentions<T: serde::Serialize + ?Sized>(&self, val: &T) -> bool {
        const MAX_OVERLAP: usize = 31;

        struct Stream<'a> {
            matcher: &'a LocalTextMatcher,
            tail: [u8; MAX_OVERLAP],
            tail_len: usize,
        }

        impl std::io::Write for Stream<'_> {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                if buf.is_empty() {
                    return Ok(0);
                }
                let overlap = self.matcher.len.saturating_sub(1).min(MAX_OVERLAP);
                if self.tail_len > 0 && overlap > 0 {
                    let prefix_len = buf.len().min(overlap);
                    let mut combined = [0u8; MAX_OVERLAP * 2];
                    combined[..self.tail_len].copy_from_slice(&self.tail[..self.tail_len]);
                    combined[self.tail_len..self.tail_len + prefix_len]
                        .copy_from_slice(&buf[..prefix_len]);
                    if self.matcher.matches_bytes(&combined[..self.tail_len + prefix_len]) {
                        return Err(std::io::Error::other("matched local"));
                    }
                }
                if self.matcher.matches_bytes(buf) {
                    return Err(std::io::Error::other("matched local"));
                }
                if overlap > 0 {
                    let total = self.tail_len + buf.len();
                    if buf.len() >= overlap {
                        self.tail[..overlap].copy_from_slice(&buf[buf.len() - overlap..]);
                        self.tail_len = overlap;
                    } else if total <= overlap {
                        self.tail[self.tail_len..total].copy_from_slice(buf);
                        self.tail_len = total;
                    } else {
                        let drop = total - overlap;
                        self.tail.copy_within(drop..self.tail_len, 0);
                        let kept = self.tail_len - drop;
                        self.tail[kept..overlap].copy_from_slice(buf);
                        self.tail_len = overlap;
                    }
                }
                Ok(buf.len())
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }

        let mut stream = Stream { matcher: self, tail: [0u8; MAX_OVERLAP], tail_len: 0 };
        serde_json::to_writer(&mut stream, val).is_err()
    }
}

/// Whether serialized text names a place rooted at `local`. Over-matches (any field
/// spelled `local`) only refuse more.
#[cfg_attr(not(test), allow(dead_code))]
fn text_mentions_local(serialized: &str, local: usize) -> bool {
    LocalTextMatcher::new(local).matches(serialized)
}

fn whole(place: &Place, local: usize) -> bool {
    place.local == local && place.projections.is_empty()
}

fn operand_is_whole(op: &Operand, local: usize) -> bool {
    matches!(op, Operand::Copy(p) | Operand::Move(p) if whole(p, local))
}

/// Whether any of `ops` names a place rooted at `local`, by the same serialized scan
/// as [`BodyText`] (a serialization failure answers `true`).
fn operands_mention_local(ops: &[Operand], local: usize) -> bool {
    if ops.is_empty() {
        return false;
    }
    LocalTextMatcher::new(local).value_mentions(ops)
}

/// The base's kind, or `None` for any other local.
fn base_kind(func: &VerifiableFunction, base: usize) -> Option<BaseKind> {
    let ty = crate::local_ty_ref(func, base)?;
    let place = Place::local(base);
    match ty {
        Ty::Ref { mutable: true, .. }
            if crate::local_defs::is_parameter(func, base)
                && crate::guards::place_is_std_vec(func, &place) =>
        {
            Some(BaseKind::MutParam)
        }
        Ty::Ref { .. } => None,
        _ if !crate::local_defs::is_parameter(func, base)
            && crate::guards::place_is_std_vec(func, &place) =>
        {
            Some(BaseKind::Owned)
        }
        _ => None,
    }
}

/// std's own calls that never change a `Vec`'s length and never retain the receiver:
/// `Index::index`/`IndexMut::index_mut` on a std container (exact impl path), std's
/// inherent `len` (exact path or sysroot key), and std `Vec`'s slice views (exact
/// split, receiver a std `Vec` by MIR type). Fail closed on everything else.
fn call_is_length_benign_on(
    func: &VerifiableFunction,
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
    receiver: &Place,
) -> bool {
    crate::generate::is_std_container_index_call(callee)
        || trust_types::total_call_summaries::total_summary_len_call(callee)
        || crate::generate::callee_key_is_std_inherent_len(callee_key)
        || (matches!(
            crate::generate::method_tail(callee),
            "deref" | "deref_mut" | "as_slice" | "as_mut_slice"
        ) && crate::guards::callee_is_std_vec_slice_view(callee)
            && crate::guards::receiver_is_std_vec(func, receiver))
}

/// std `Vec`'s own inherent `&mut self` methods that may change the length but never
/// retain the receiver (std contract: the pointer is not stored anywhere that outlives
/// the call). The defining crate must be the REAL sysroot `alloc` by `CalleeKey` (a
/// path spelling alone is forgeable by a user crate named `alloc`), and the rendering
/// an inherent `alloc::vec::Vec::<..>::m` (no trait impl). Fail closed on everything
/// else: such a call is then an unknown mention and refuses the base.
const STD_VEC_NON_RETAINING_RESIZERS: &[&str] = &[
    "push",
    "pop",
    "truncate",
    "clear",
    "insert",
    "remove",
    "swap_remove",
    "resize",
    "extend_from_slice",
    "reserve",
    "reserve_exact",
    "shrink_to_fit",
];

fn call_is_std_vec_resizer(
    func: &VerifiableFunction,
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
    receiver: &Place,
) -> bool {
    callee_key.is_some_and(|k| {
        k.krate_is_real_sysroot && !k.krate_name_is_ambiguous && k.krate_name == "alloc"
    }) && !callee.contains(" as ")
        && callee.strip_prefix('<').unwrap_or(callee).starts_with("alloc::vec::Vec::<")
        && STD_VEC_NON_RETAINING_RESIZERS.contains(&crate::generate::method_tail(callee))
        && crate::guards::receiver_is_std_vec(func, receiver)
}

/// How a terminator that mentions `local` uses it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ReceiverUse {
    /// The whole receiver (argument 0) of a length-benign std call.
    Benign,
    /// The whole receiver of a non-retaining std `Vec` resizer
    /// ([`STD_VEC_NON_RETAINING_RESIZERS`]): the length may change at this block.
    Resizes,
}

/// A terminator that mentions `local` ONLY as the whole receiver (argument 0) of a
/// length-benign std call or of a non-retaining std `Vec` resizer: not in any other
/// argument, not as the destination. `None` for every other terminator.
fn term_receiver_use(
    func: &VerifiableFunction,
    term: &Terminator,
    local: usize,
) -> Option<ReceiverUse> {
    let Terminator::Call { func: callee, args, dest, callee_key, .. } = term else {
        return None;
    };
    let Some(recv @ (Operand::Copy(p) | Operand::Move(p))) = args.first() else {
        return None;
    };
    if !operand_is_whole(recv, local)
        || dest.local == local
        || operands_mention_local(&args[1..], local)
    {
        return None;
    }
    if call_is_length_benign_on(func, callee, callee_key.as_ref(), p) {
        Some(ReceiverUse::Benign)
    } else if call_is_std_vec_resizer(func, callee, callee_key.as_ref(), p) {
        Some(ReceiverUse::Resizes)
    } else {
        None
    }
}

/// A `&mut` temporary `t` (defined by `def_at`) every OTHER mention of which is the
/// whole receiver of a length-benign std call or of a non-retaining std `Vec` resizer.
/// `Some(blocks)` lists the blocks whose terminator resizes through `t`; `None` refuses.
fn mut_temp_uses(
    func: &VerifiableFunction,
    text: &BodyText,
    t: usize,
    def_at: (usize, usize),
) -> Option<Vec<usize>> {
    for &(bi, si) in text.stmt_sites(t) {
        if (bi as usize, si as usize) != def_at {
            return None;
        }
    }
    let mut resizes = Vec::new();
    for &bi in text.term_blocks(t) {
        let bi = bi as usize;
        match term_receiver_use(func, &func.body.blocks[bi].terminator, t)? {
            ReceiverUse::Benign => {}
            ReceiverUse::Resizes => resizes.push(bi),
        }
    }
    Some(resizes)
}

/// What [`vec_len_never_changes`] admits a base with.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LenVerdict {
    /// The first block in which an owned base's one write has taken effect (`None` for
    /// a parameter).
    write_block: Option<usize>,
    /// The blocks whose terminator is a non-retaining std `Vec` resizer on the base.
    /// The length is constant over any stretch of execution that runs none of them.
    resize_blocks: Vec<usize>,
}

/// Clause 1 of the module's soundness argument: every mention of `base` in the body is
/// either one that cannot change the `Vec`'s length, or the receiver of a non-retaining
/// std `Vec` resizer, whose block is reported so the caller can keep it out of the
/// stretch between an establishing call and a use (an owned base: after its one whole
/// write). `None` refuses.
fn vec_len_never_changes(
    func: &VerifiableFunction,
    text: &BodyText,
    base: usize,
    kind: BaseKind,
) -> Option<LenVerdict> {
    let borrowed = match kind {
        BaseKind::Owned => Place::local(base),
        BaseKind::MutParam => {
            Place { local: base, projections: vec![trust_types::Projection::Deref] }
        }
    };
    // A raw-pointer laundering site (`&raw`, a cast to a raw pointer, an unknown
    // rvalue) anywhere in the body could reach the `Vec` by a route no mention of
    // `base` shows; refuse the whole function, as the per-argument havoc skip does.
    if super::path_defs::func_has_pointer_laundering(func)
        || trust_types::verify_budget::budget_exhausted()
    {
        return None;
    }
    let base_matcher = LocalTextMatcher::new(base);
    let mut write_blocks: Vec<usize> = Vec::new();
    let mut resize_blocks: Vec<usize> = Vec::new();
    for &(bi, si) in text.stmt_sites(base) {
        if trust_types::verify_budget::budget_exhausted() {
            return None;
        }
        let bi = bi as usize;
        let si = si as usize;
        let stmt = &func.body.blocks[bi].stmts[si];
        let Statement::Assign { place: dest, rvalue, .. } = stmt else { return None };
        match rvalue {
            Rvalue::Ref { mutable, place }
                if *place == borrowed && dest.projections.is_empty() && dest.local != base =>
            {
                if *mutable {
                    resize_blocks.extend(mut_temp_uses(func, text, dest.local, (bi, si))?);
                }
            }
            // The owned base's one whole write; the rvalue must not read it.
            _ if kind == BaseKind::Owned && whole(dest, base) => {
                if base_matcher.value_mentions(rvalue) {
                    return None;
                }
                write_blocks.push(bi);
            }
            _ => return None,
        }
    }
    for &bi in text.term_blocks(base) {
        if trust_types::verify_budget::budget_exhausted() {
            return None;
        }
        let bi = bi as usize;
        let b = &func.body.blocks[bi];
        match &b.terminator {
            Terminator::Drop { place, .. } if kind == BaseKind::Owned && whole(place, base) => {}
            Terminator::Call { args, dest, target, .. }
                if kind == BaseKind::Owned && whole(dest, base) =>
            {
                if operands_mention_local(args, base) {
                    return None;
                }
                // The value exists from the return target on; that target must be
                // entered only from this call (so entering it means the call returned).
                let t =
                    target.filter(|t| super::call_facts::sole_predecessor_is(func, *t, b.id))?;
                write_blocks.push(t.0);
            }
            term if kind == BaseKind::MutParam => match term_receiver_use(func, term, base)? {
                ReceiverUse::Benign => {}
                ReceiverUse::Resizes => resize_blocks.push(bi),
            },
            _ => return None,
        }
    }
    let write_block = match (kind, write_blocks.as_slice()) {
        (BaseKind::Owned, &[w]) => Some(w),
        (BaseKind::MutParam, []) => None,
        _ => return None,
    };
    resize_blocks.sort_unstable();
    resize_blocks.dedup();
    Some(LenVerdict { write_block, resize_blocks })
}

/// Every CFG successor of block `bi`: the full-graph targets the dominator tree is
/// built from, plus the unwind cleanup edge (more edges only grow the stretch below,
/// which only refuses more).
fn successors(func: &VerifiableFunction, bi: usize) -> Vec<usize> {
    let b = &func.body.blocks[bi];
    let n = func.body.blocks.len();
    let mut out: Vec<usize> = Vec::new();
    let mut push = |t: BlockId| {
        if t.0 < n {
            out.push(t.0);
        }
    };
    b.terminator.for_each_in_cfg_successor(&mut push);
    super::for_each_v2_terminator_target(&b.terminator, &mut push);
    if let Terminator::Call { unwind, .. }
    | Terminator::Assert { unwind, .. }
    | Terminator::Drop { unwind, .. } = &b.terminator
        && let Some(t) = unwind.cleanup_target()
    {
        push(t);
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// Precomputed forward/backward CFG adjacency for [`stretch_has_resizer`].
fn build_stretch_cfg(func: &VerifiableFunction) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let n = func.body.blocks.len();
    let mut succs: Vec<Vec<usize>> = Vec::with_capacity(n);
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for bi in 0..n {
        let s = successors(func, bi);
        for &target in &s {
            preds[target].push(bi);
        }
        succs.push(s);
    }
    (succs, preds)
}

/// True iff any block in `resize_blocks` can run between the establishing call in block
/// `d` returning (to `t`) and the next reach of `u` — i.e., lies on some path `t ->* u`
/// that never enters `d` (`t` and `u` included). Only these can execute after the LAST
/// run of `d` before `u`, so a resizer outside them cannot change the length the fact reads.
fn stretch_has_resizer(
    succs: &[Vec<usize>],
    preds: &[Vec<usize>],
    d: usize,
    t: usize,
    u: usize,
    resize_blocks: &[usize],
) -> bool {
    let n = succs.len();
    let walk = |start: usize, adj: &[Vec<usize>]| {
        let mut seen = vec![false; n];
        if start == d {
            return seen;
        }
        seen[start] = true;
        let mut stack = vec![start];
        while let Some(v) = stack.pop() {
            for &w in &adj[v] {
                if w != d && !seen[w] {
                    seen[w] = true;
                    stack.push(w);
                }
            }
        }
        seen
    };
    let fwd = walk(t, succs);
    if !resize_blocks.iter().any(|&r| fwd[r]) {
        return false;
    }
    let bwd = walk(u, preds);
    resize_blocks.iter().any(|&r| fwd[r] && bwd[r])
}

/// The first block in which the one whole write of a single-static-assignment local
/// has taken effect: the writing statement's block, or a writing call's return target
/// when that target is entered only from the call. `None` otherwise.
fn def_effect_block(func: &VerifiableFunction, local: usize) -> Option<usize> {
    if crate::local_defs::is_parameter(func, local) {
        return None;
    }
    let bi = crate::local_defs::unique_defining_block(func, local)?;
    let b = func.body.blocks.get(bi)?;
    match &b.terminator {
        Terminator::Call { dest, target, .. } if whole(dest, local) => {
            let t = (*target)?;
            super::call_facts::sole_predecessor_is(func, t, b.id).then_some(t.0)
        }
        _ => Some(bi),
    }
}

/// `(call block, target, fact)` triples establishing `base`'s length: each fact holds
/// at entry to its target and, by the module argument, at every point the target
/// dominates that no resizer can reach from the target first.
fn establishers(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    base: usize,
    kind: BaseKind,
    write_block: Option<usize>,
) -> Vec<(usize, BlockId, Formula)> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let len_b = crate::guards::coll_len_var(func, base);
    let dom = |a: usize, b: usize| sv.cfg().dom().dominates(a as u32, b as u32);
    let mut out = Vec::new();
    for b in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, target: Some(target), callee_key, .. } =
            &b.terminator
        else {
            continue;
        };
        if !dest.projections.is_empty() {
            continue;
        }
        // Both shapes need the return target entered only from this call (clause 3).
        let entered_only_from_call = || super::call_facts::sole_predecessor_is(func, *target, b.id);
        // `_k = Vec::len(r)`, `r` tracing to `base`.
        let is_len = trust_types::total_call_summaries::total_summary_len_call(callee)
            || crate::generate::callee_key_is_std_inherent_len(callee_key.as_ref());
        if is_len
            && args.len() == 1
            && dest.local != base
            && !crate::local_defs::is_parameter(func, dest.local)
            && let Some(Operand::Copy(r) | Operand::Move(r)) = args.first()
            && r.projections.is_empty()
            && crate::guards::base_collection_local_unique(func, r.local) == Some(base)
            && crate::local_defs::is_single_static_assignment(func, dest.local)
            // An owned base's one write precedes every read of it in valid MIR; checked,
            // not assumed: clause 2 needs the block where it has taken effect to
            // dominate this call's (reflexive: a same-block statement write, or a call
            // write whose target is this block, precedes this terminator).
            && write_block.is_none_or(|w| dom(w, b.id.0))
            && entered_only_from_call()
        {
            out.push((
                b.id.0,
                *target,
                Formula::Eq(
                    Box::new(Formula::var_owned(
                        crate::place_to_var_name(func, &Place::local(dest.local)),
                        Sort::Int,
                    )),
                    Box::new(len_b.clone()),
                ),
            ));
            continue;
        }
        // `base = vec![x; n]`, the owned base's one write.
        if kind == BaseKind::Owned
            && dest.local == base
            && args.len() == 2
            && let Some(key) = callee_key
            && key.krate_is_real_sysroot
            && key.sysroot_item == Some(trust_types::SysrootItem::VecFromElem)
        {
            let count = &args[1];
            if !matches!(
                crate::operand_ty_cow(func, count).as_deref(),
                Some(Ty::Int { signed: false, .. })
            ) {
                continue;
            }
            let stable = match count {
                Operand::Constant(_) => true,
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    p.local != base
                        && crate::local_defs::is_single_static_assignment(func, p.local)
                        && (crate::local_defs::is_parameter(func, p.local)
                            || def_effect_block(func, p.local).is_some_and(|nb| dom(nb, b.id.0)))
                }
                _ => false,
            };
            if stable
                && entered_only_from_call()
                && !super::call_facts::body_mentions_opaque_scalar(func)
            {
                out.push((
                    b.id.0,
                    *target,
                    Formula::Eq(
                        Box::new(len_b.clone()),
                        Box::new(crate::operand_to_formula(func, count)),
                    ),
                ));
            }
        }
    }
    out
}

/// The per-block facts of this module (see the header): `(use block, fact renamed at
/// its terminal)`.
pub(super) fn vec_len_invariant_use_facts(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
) -> Vec<(BlockId, Formula)> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    // The use blocks: std index calls on a receiver tracing to a candidate base.
    let mut uses: Vec<(BlockId, usize, BaseKind)> = Vec::new();
    for b in &func.body.blocks {
        let Terminator::Call { func: callee, args, .. } = &b.terminator else { continue };
        let Some(Operand::Copy(r) | Operand::Move(r)) = args.first() else { continue };
        if !r.projections.is_empty() {
            continue;
        }
        if !crate::generate::is_std_container_index_call(callee) {
            continue;
        }
        let Some(base) = crate::guards::base_collection_local_unique(func, r.local) else {
            continue;
        };
        if let Some(kind) = base_kind(func, base) {
            uses.push((b.id, base, kind));
        }
    }
    if uses.is_empty() || super::path_defs::func_has_pointer_laundering(func) {
        return Vec::new();
    }
    let Some(text) = BodyText::build(func) else { return Vec::new() };
    type Est = (Vec<usize>, Vec<(usize, BlockId, Formula)>);
    let mut verdicts: FxHashMap<usize, Est> = FxHashMap::default();
    let mut stretch_cfg: Option<(Vec<Vec<usize>>, Vec<Vec<usize>>)> = None;
    let mut out = Vec::new();
    for (u, base, kind) in uses {
        let (resize_blocks, est) = verdicts.entry(base).or_insert_with(|| {
            match vec_len_never_changes(func, &text, base, kind) {
                Some(v) => (v.resize_blocks, establishers(func, sv, base, kind, v.write_block)),
                None => (Vec::new(), Vec::new()),
            }
        });
        if est.is_empty() {
            continue;
        }
        let terminal = func.body.blocks[u.0].stmts.len();
        for (d, t, fact) in est.iter() {
            // A call that returns to its own block re-runs before any use it dominates
            // could read the fact; refuse it rather than reason about it.
            if *d == t.0 || !sv.cfg().dom().dominates(t.0 as u32, u.0 as u32) {
                continue;
            }
            // Clause 1 for this pair: no resizer runs between the establishing call
            // returning and the use. Skipped (no stretch walk) when there is none.
            if !resize_blocks.is_empty() {
                let (succs, preds) = stretch_cfg.get_or_insert_with(|| build_stretch_cfg(func));
                if stretch_has_resizer(succs, preds, *d, t.0, u.0, resize_blocks) {
                    continue;
                }
            }
            out.push((u, version_rename_at(fact, sv, func, u, terminal)));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_place_mention_is_matched_by_its_whole_local_number() {
        let place = |local: usize| {
            serde_json::to_string(&Operand::Copy(Place::local(local))).expect("serializes")
        };
        assert!(text_mentions_local(&place(1), 1));
        assert!(!text_mentions_local(&place(10), 1), "`_10` is not `_1`");
        assert!(!text_mentions_local(&place(1), 10), "`_1` is not `_10`");
        let deref = serde_json::to_string(&Place {
            local: 3,
            projections: vec![trust_types::Projection::Deref],
        })
        .expect("serializes");
        assert!(text_mentions_local(&deref, 3), "a projected place is a mention: {deref}");
    }

    // The rows below drive this module's gates DIRECTLY on the real-MIR fixtures of
    // `tests/vec_len_loop_head_realmir.rs` (source there and in this module's header).
    // The integration rows cannot reach the owned-base half of the scan: every owned
    // `Vec` whose `&mut` reaches a resizer is preclassified `container-index-unstable-
    // len` (Unknown) by `guards::local_mut_borrows_may_resize` before any fact is read,
    // so only a direct call shows what THIS module answers for it.

    fn load(name: &str) -> VerifiableFunction {
        let path =
            format!("{}/tests/fixtures/vec_len_loop_head/{name}.json", env!("CARGO_MANIFEST_DIR"));
        let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        serde_json::from_str(&json).expect("fixture MIR must deserialize")
    }

    fn facts(func: &VerifiableFunction) -> Vec<(BlockId, Formula)> {
        let sv = crate::generate::stmt_versions_for(func);
        vec_len_invariant_use_facts(func, &sv)
    }

    /// The fixture's `Vec` base: the `vec![..]` call's destination, else the `&mut Vec`
    /// parameter `_1`, with its kind (vacuity guard: the scan under test is reached).
    fn the_base(func: &VerifiableFunction) -> (usize, BaseKind) {
        let base = func
            .body
            .blocks
            .iter()
            .find_map(|b| match &b.terminator {
                Terminator::Call { dest, callee_key: Some(k), .. }
                    if k.sysroot_item == Some(trust_types::SysrootItem::VecFromElem) =>
                {
                    Some(dest.local)
                }
                _ => None,
            })
            .unwrap_or(1);
        let kind = base_kind(func, base)
            .unwrap_or_else(|| panic!("{}: `_{base}` is a candidate base", func.name));
        (base, kind)
    }

    /// The std index uses whose receiver traces to the fixture's base.
    fn index_uses(func: &VerifiableFunction) -> usize {
        let (base, _) = the_base(func);
        func.body
            .blocks
            .iter()
            .filter(|b| match &b.terminator {
                Terminator::Call { func: callee, args, .. }
                    if crate::generate::is_std_container_index_call(callee) =>
                {
                    matches!(args.first(), Some(Operand::Copy(r) | Operand::Move(r))
                        if r.projections.is_empty()
                            && crate::guards::base_collection_local_unique(func, r.local)
                                == Some(base))
                }
                _ => false,
            })
            .count()
    }

    fn verdict(func: &VerifiableFunction) -> Option<LenVerdict> {
        let (base, kind) = the_base(func);
        let text = BodyText::build(func).expect("serializes");
        vec_len_never_changes(func, &text, base, kind)
    }

    #[test]
    fn an_unchanged_or_out_of_stretch_resized_length_mints_a_fact_per_index() {
        // `push_then_rw` resizes BEFORE `v.len()` is read, `rw_then_truncate` after the
        // loop exits: neither resizer can run between the read and the index.
        for name in ["ro", "rw_vec", "rw_vec_local", "first", "push_then_rw", "rw_then_truncate"] {
            let func = load(name);
            let v = verdict(&func).unwrap_or_else(|| panic!("{name}: the scan admits the base"));
            let resizes = !v.resize_blocks.is_empty();
            assert_eq!(
                resizes,
                matches!(name, "push_then_rw" | "rw_then_truncate"),
                "{name}: {v:?}"
            );
            let uses = index_uses(&func);
            assert!(uses >= 1, "{name}: vacuity guard, an index on the base");
            assert_eq!(facts(&func).len(), uses, "{name}: one fact at each index");
        }
    }

    #[test]
    fn an_owned_vec_with_an_unknown_mention_is_refused_by_the_scan_itself() {
        // `opaque_own(&mut v)` (a user callee) and `v = Vec::new()` (a second write).
        // The verdict is the load-bearing assertion: an index whose receiver no longer
        // traces to a unique base never reaches the scan at all.
        for name in ["own_escapes", "own_reassigns"] {
            let func = load(name);
            assert_eq!(the_base(&func).1, BaseKind::Owned, "{name}");
            assert_eq!(verdict(&func), None, "{name}");
            assert!(facts(&func).is_empty(), "{name}");
        }
    }

    #[test]
    fn a_resizer_between_the_establisher_and_the_index_mints_nothing() {
        // Owned (`v.truncate(i)` / `v.push(1)` in the loop) and `&mut Vec` parameter
        // (`truncate`/`pop` before the index, `pop` after it on the back edge): the scan
        // admits the base with the resizer's block, and the stretch refuses the fact.
        for (name, kind) in [
            ("own_truncates", BaseKind::Owned),
            ("own_pushes", BaseKind::Owned),
            ("truncates", BaseKind::MutParam),
            ("pops", BaseKind::MutParam),
            ("pop_after_index", BaseKind::MutParam),
        ] {
            let func = load(name);
            assert_eq!(the_base(&func).1, kind, "{name}");
            let v = verdict(&func).unwrap_or_else(|| panic!("{name}: std resizers only"));
            assert!(!v.resize_blocks.is_empty(), "{name}: vacuity guard, a resizer: {v:?}");
            assert!(index_uses(&func) >= 1, "{name}: vacuity guard, the index reaches the scan");
            assert!(facts(&func).is_empty(), "{name}: {:?}", facts(&func));
        }
    }

    #[test]
    fn a_param_with_an_unknown_mention_is_refused_by_the_scan_itself() {
        // `opaque(v)` (in the loop / before it) and `*v = Vec::new()`.
        for name in ["escapes", "opaque_then_rw", "reassigns"] {
            let func = load(name);
            assert_eq!(the_base(&func).1, BaseKind::MutParam, "{name}");
            assert_eq!(verdict(&func), None, "{name}");
            assert!(facts(&func).is_empty(), "{name}");
        }
    }

    /// Rewrites `func`'s `alloc::vec::Vec::<u8>::push` call: its callee text, and its
    /// `CalleeKey` through `key`.
    fn rewrite_push(
        func: &mut VerifiableFunction,
        callee: &str,
        key: impl Fn(&mut trust_types::CalleeKey),
    ) {
        let mut touched = 0;
        for b in &mut func.body.blocks {
            if let Terminator::Call { func: c, callee_key: Some(k), .. } = &mut b.terminator
                && c == "alloc::vec::Vec::<u8>::push"
            {
                *c = callee.to_string();
                key(k);
                touched += 1;
            }
        }
        assert_eq!(touched, 1, "vacuity guard: one std `push`");
    }

    #[test]
    fn a_resizer_must_be_std_alloc_by_crate_identity() {
        // A user free function taking the `&mut Vec`, and a forged `alloc::…::push`
        // spelling from a crate that is not the real sysroot: both are unknown mentions.
        let mut user = load("push_then_rw");
        rewrite_push(&mut user, "veclen4::my_push", |k| {
            k.krate_is_real_sysroot = false;
            k.krate_name = "veclen4".to_string();
        });
        assert_eq!(verdict(&user), None);
        assert!(facts(&user).is_empty());
        let mut forged = load("push_then_rw");
        rewrite_push(&mut forged, "alloc::vec::Vec::<u8>::push", |k| {
            k.krate_is_real_sysroot = false;
        });
        assert_eq!(verdict(&forged), None);
        assert!(facts(&forged).is_empty());
    }

    #[test]
    fn the_establisher_target_must_be_entered_only_from_its_call() {
        // `rw_vec`: bb0 `_4 = Vec::len(&*_1) -> bb1`; the loop's latch bb8 `goto bb3`.
        // Re-aim the latch at bb1: bb1 still dominates the index (bb6), but is now
        // entered without the call returning, so `_4 == len(v)` is not established.
        let mut func = load("rw_vec");
        assert_eq!(facts(&func).len(), 1, "control: the unmutated function mints the fact");
        let latch = &mut func.body.blocks[8].terminator;
        assert!(matches!(latch, Terminator::Goto(BlockId(3))), "fixture shape: {latch:?}");
        *latch = Terminator::Goto(BlockId(1));
        let sv = crate::generate::stmt_versions_for(&func);
        assert!(sv.cfg().dom().dominates(1, 6), "only the sole-predecessor gate is in play");
        assert!(facts(&func).is_empty(), "{:?}", facts(&func));
    }

    #[test]
    fn the_establisher_target_must_dominate_the_use() {
        // `ro`: bb0 `if n > 1000` -> bb1 (`goto bb11`, return) / bb2 (`v = vec![0; n]
        // -> bb3`); the loop head is bb5 and the index bb8. Re-aim bb1 at the loop head:
        // bb3 stays entered only from bb2, but bb8 is now reachable around it.
        let mut func = load("ro");
        assert_eq!(facts(&func).len(), 1, "control: the unmutated function mints the fact");
        let early = &mut func.body.blocks[1].terminator;
        assert!(matches!(early, Terminator::Goto(BlockId(11))), "fixture shape: {early:?}");
        *early = Terminator::Goto(BlockId(5));
        assert!(super::super::call_facts::sole_predecessor_is(&func, BlockId(3), BlockId(2)));
        assert!(verdict(&func).is_some(), "only the dominance gate is in play");
        assert!(facts(&func).is_empty(), "{:?}", facts(&func));
    }

    #[test]
    fn indexed_local_mentions_and_streaming_matcher_agree_with_text_mentions_local() {
        let samples = [
            r#"{"local":0}"#,
            r#"{"local":0,"projections":[]}"#,
            r#"{"local":12,"projections":[{"Index":3}]}"#,
            r#"{"a":{"local":01},"b":{"local":7}}"#,
            r#""local":"local":9,"#,
            r#"{"local":99999999999999999999999999999999}"#,
            r#"{"msg":"héllo — \"local\":42,"}"#,
        ];
        for s in samples {
            let mut indexed = Vec::new();
            BodyText::for_each_mentioned_local(s.as_bytes(), |l| indexed.push(l));
            for candidate in [0usize, 1, 3, 7, 9, 10, 12, 42] {
                assert_eq!(
                    indexed.contains(&candidate),
                    text_mentions_local(s, candidate),
                    "mismatch on sample={s:?} candidate={candidate}"
                );
            }
        }
        let ops = vec![
            Operand::Constant(ConstValue::Str { bytes: "é—x".as_bytes().to_vec() }),
            Operand::Copy(Place {
                local: 17,
                projections: vec![trust_types::Projection::Index(4)],
            }),
        ];
        let json = serde_json::to_string(&ops).expect("serializes");
        for candidate in [0usize, 1, 4, 7, 17, 170] {
            assert_eq!(
                operands_mention_local(&ops, candidate),
                text_mentions_local(&json, candidate),
                "streaming operands_mention_local mismatch for {candidate}"
            );
        }
    }
}
