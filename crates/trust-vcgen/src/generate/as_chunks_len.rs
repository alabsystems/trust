// Trust (2026-10-15, TRUST-KI-1015-1, AS-CHUNKS-RESULT-LEN): the lengths of the two
// slices core's `[T]::as_chunks::<N>` family returns, as a post-return definition of
// the call.
//
// THE DEFECT (a correct program reported refuted). aterm-digest `Sha256::update`
// (sha256.rs:121-127 at aterm 848d791bd) runs
//
//     let (blocks, rest) = data.as_chunks::<BLOCK_LEN>();   // BLOCK_LEN = 64
//     for block in blocks { compress(&mut self.state, block); }
//     self.buf[..rest.len()].copy_from_slice(rest);         // self.buf: [u8; 64]
//
// and its `[slice]` row at 127:16 (`rest.len() <= 64`) was FAILED by the in-process
// `ay` lane on the channel seal `b58a105dde` and on main, with the model
// `_5.1__slice_len = 65` (the remainder) beside a receiver of length 0. The call
// `_5 = core::slice::<impl [u8]>::as_chunks::<64>(copy data)` is havocked by the VC
// lane: nothing related the two halves' length names to the receiver's length or to
// `N`, so each was bounded by its type range alone and SAT chose a remainder no
// execution produces. The same held for `as_rchunks`, `as_chunks_mut`,
// `as_rchunks_mut`, for a remainder used in a subtraction (`63 - rest.len()`,
// `data.len() - rest.len()`) and for an index into the chunk slice under a guard on
// the receiver (`if data.len() >= 8 { blocks[1] }`): every correct variant was FAILED
// on the channel and on main `9fa33ffd06` (tests/as_chunks_len_realmir.rs).
//
// THE FACT. core (library/core/src/slice/mod.rs) defines, for `N != 0`,
//
//     as_chunks::<N>(s)  = (&s[..len / N * N] as &[[T; N]], &s[len / N * N..])
//     as_rchunks::<N>(s) = (&s[..len - len / N * N], &s[len - len / N * N..] as &[[T; N]])
//
// (`as_chunks_mut` / `as_rchunks_mut` likewise, through `split_at_mut[_unchecked]`),
// where `len = s.len()` and the cast is `as_chunks_unchecked`, a slice of `len / N`
// arrays. It panics only on `N == 0` (the `ConstChunkSize` row charges that). So on
// the normal return, with `C` the chunk slice's length and `R` the remainder's,
//
//     R == len - N * C     0 <= R     R < N
//
// which is exactly Euclidean division (`C == len / N`, `R == len % N`) for `len >= 0`
// and `N > 0`: integer `C` and `R` are then unique. It is stated LINEARLY (`N` is a
// literal), not with `Div`/`Rem`: every `Div`/`Rem` lowers through the signed `mod`
// encoding, which ay's strict certification does not accept
// (`call_facts::div_ceil_call_dest_fact` measured the same for `div_ceil`).
//
// WHERE IT GOES. A POST-RETURN DEFINITION in the path-definition fixpoint
// (`path_defs::v2_path_def_fixpoint`, the `Terminator::Call` arm, beside
// `probe_call_definitions`): added to the call block's NORMAL outflow after the
// terminator kill, so it reaches only the return target (never the cleanup edge), is
// intersected away at any join one of whose entries lacks it, and is killed by every
// later write of one of its names. Facts in that channel are stated over BARE names and
// renamed WITH the body at each use point, so the names must denote, on the return
// edge, exactly the values the call produced and received — which the terminator-kill
// gate below establishes. It reaches the per-statement rows and their hardened twins
// alike (`hardened.rs` reads the same map as its reaching definitions), and it survives
// a loop over the chunks (the digest's `for block in blocks`), whose body writes none
// of its names.
//
// SOUNDNESS — every gate is a hard requirement; a miss emits NOTHING (the rows keep
// their old, weaker hypotheses):
//  * THE BODY THAT RUNS IS CORE'S. The callee is core's inherent `[T]::as_chunks`,
//    `as_chunks_mut`, `as_rchunks` or `as_rchunks_mut` by its `core::slice::<impl [`
//    root on an authenticated sysroot crate (`collection_range::is_core_slice_inherent`,
//    the recognizer the `ConstChunkSize` row keys on; only the crate defining `[T]` can
//    write an inherent impl on it), not a trait method (`<[T] as Ext>::as_chunks`
//    renders with ` as `), with no unauthenticated crate stamp and a `callee_key` from
//    the real sysroot.
//  * `N` IS ONE KNOWN NONZERO INTEGER, AND THE TYPES AGREE WITH IT. `N` is the
//    instantiation's single const generic, a nonzero integer literal
//    (`collection_range::const_generic_literal`; a generic `N` or `0` gets nothing),
//    and the destination's MIR type must be exactly the pair the method returns at
//    that `N`: a 2-tuple of a reference to `[[E; N]]` (the array length equal to the
//    literal) and a reference to `[E]`, in the method's order, with the receiver a
//    reference to `[E]` of the same `E` and the method's mutability. A callee string
//    and a destination type that disagree get no fact.
//  * THE CALL WRITES THE LEFT SIDE AND NOTHING ON THE RIGHT. The destination is a whole
//    local whose halves' lengths are the `{dest}.0__slice_len` / `{dest}.1__slice_len`
//    NAMES (two distinct names), and the version oracle's terminator kill
//    (`StmtVersionCtx::terminator_kill`) must kill both — the call is recognized as
//    their writer, so no stale fact about them survives the call — and must NOT kill
//    the receiver's length: on the return edge that name holds the length the call
//    read.
//
// Which gate a test of `tests/as_chunks_len_realmir.rs` pins (red when the gate alone is
// removed) and which is defence in depth (nothing red without it, measured) is listed in
// that file's header. The ` as ` check alone, the stamp check and the distinct-names
// check are defence in depth. The whole-local check and the halves-kill check are pinned
// only together.
//
// No identity-less-constant gate (`call_facts::body_mentions_opaque_scalar`) is needed:
// the facts mention no operand constant, only `N` (read from the instantiation and
// checked against the destination's type) and three length names.
//
// A row the facts make UNSAT is proved on the solver's own authority, as any row with
// path definitions is; a row they do not make UNSAT keeps a model that now satisfies
// core's contract for the call, so a FAILED that remains (`buf[..rest.len()]` into a
// `[u8; 32]` after `as_chunks::<64>`) is an execution.
//
// NOT HERE: `chunks_exact(n).remainder()` / `rchunks_exact` / `chunks_exact_mut
// .into_remainder()` (the remainder is a field of an iterator struct built by one call
// and read by another, with a runtime chunk size), `array_windows`, and a generic `N`.
// Each keeps its havocked length, and a row over it can still be FAILED on a model no
// execution produces (docs/KNOWN_HAZARDS.md, TRUST-KI-1015-1). Nor does it relate a half
// to a SECOND read of a receiver behind a `&mut` (`d.len() - rest.len()` for
// `d: &mut &[u8]`, or a slice field of a `&mut S`). The fact names the length of the
// receiver temp the call read. The later read goes through a fresh deref temp, and
// nothing ties that temp's length to the first one.

use super::*;

/// The post-return length definitions of every core `as_chunks`-family call in `func`,
/// keyed by the CALL block (see the module header). The path-definition fixpoint adds a
/// block's entry to that block's normal outflow, after its terminator kill.
pub(super) fn as_chunks_result_len_definitions(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut out: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return out;
    }
    for block in &func.body.blocks {
        if !matches!(block.terminator, Terminator::Call { target: Some(_), .. }) {
            continue;
        }
        if let Some(facts) = as_chunks_result_len_facts(func, block) {
            out.insert(block.id, facts);
        }
    }
    out
}

/// Which half of the destination pair is the remainder.
#[derive(Clone, Copy)]
enum ChunkOrder {
    /// `as_chunks{,_mut}`: `(&[[T; N]], &[T])`.
    ChunksFirst,
    /// `as_rchunks{,_mut}`: `(&[T], &[[T; N]])`.
    RemainderFirst,
}

/// The core `as_chunks`-family method `callee` names, with its order and mutability,
/// or `None` for every other spelling (see the module header's first gate).
fn core_as_chunks_method(callee: &str) -> Option<(ChunkOrder, bool)> {
    let shape = match method_tail(callee) {
        "as_chunks" => (ChunkOrder::ChunksFirst, false),
        "as_chunks_mut" => (ChunkOrder::ChunksFirst, true),
        "as_rchunks" => (ChunkOrder::RemainderFirst, false),
        "as_rchunks_mut" => (ChunkOrder::RemainderFirst, true),
        _ => return None,
    };
    let core_inherent = super::collection_range::is_core_slice_inherent(callee)
        && !callee.contains(" as ")
        && !trust_types::path_has_unauthenticated_crate_stamp(callee);
    core_inherent.then_some(shape)
}

/// `R == len - N * C`, `0 <= R`, `R < N` for a core `as_chunks`-family call terminating
/// `block` (`C`/`R` the chunk slice's and the remainder's length names), or `None` when
/// a gate misses.
pub(super) fn as_chunks_result_len_facts(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<Vec<Formula>> {
    let Terminator::Call { func: callee, args, dest, callee_key, .. } = &block.terminator else {
        return None;
    };
    if !dest.projections.is_empty()
        || args.len() != 1
        || !callee_key.as_ref().is_some_and(|key| key.krate_is_real_sysroot)
    {
        return None;
    }
    let Some(Ty::Tuple(dest_elems)) = crate::local_ty_ref(func, dest.local) else {
        return None;
    };
    if dest_elems.len() != 2 {
        return None;
    }
    let (order, mutable) = core_as_chunks_method(callee)?;
    let n = super::collection_range::const_generic_literal(callee).filter(|&n| n != 0)?;
    let n_len = u64::try_from(n).ok()?;
    let n = i128::try_from(n).ok()?;

    // The receiver: a reference to `[E]` of the method's mutability.
    let receiver = &args[0];
    let recv_ty = crate::operand_ty_cow(func, receiver)?;
    let elem = match recv_ty.as_ref() {
        Ty::Ref { mutable: m, inner } if *m == mutable => match inner.as_ref() {
            Ty::Slice { elem } => elem.as_ref(),
            _ => return None,
        },
        _ => return None,
    };
    // The destination: the pair the method returns at this `N`, in its order.
    let (chunk_field, rem_field) = match order {
        ChunkOrder::ChunksFirst => (0, 1),
        ChunkOrder::RemainderFirst => (1, 0),
    };
    let chunk_elem_ok = matches!(
        &dest_elems[chunk_field],
        Ty::Ref { mutable: m, inner }
            if *m == mutable
                && matches!(
                    inner.as_ref(),
                    Ty::Slice { elem: arr }
                        if matches!(arr.as_ref(), Ty::Array { elem: e, len } if *len == n_len && e.as_ref() == elem)
                )
    );
    let rem_elem_ok = matches!(
        &dest_elems[rem_field],
        Ty::Ref { mutable: m, inner }
            if *m == mutable
                && matches!(inner.as_ref(), Ty::Slice { elem: e } if e.as_ref() == elem)
    );
    if !chunk_elem_ok || !rem_elem_ok {
        return None;
    }
    let field = |k: usize| Place {
        local: dest.local,
        projections: vec![trust_types::Projection::Field(k)],
    };
    let (chunk_place, rem_place) = (field(chunk_field), field(rem_field));
    let chunks_len = super::range_index_len::slice_len_name(func, chunk_place)?;
    let rem_len = super::range_index_len::slice_len_name(func, rem_place)?;
    if chunks_len == rem_len {
        return None;
    }
    let len = crate::slice_len_formula(func, receiver)?;

    // The call writes both halves' length names and not the receiver's length.
    let sv = super::stmt_versions_for(func);
    let kill = sv.terminator_kill(func, block);
    let chunks = Formula::Var(chunks_len, Sort::Int);
    let rem = Formula::Var(rem_len, Sort::Int);
    if kill.survives_havoc_plain(&chunks)
        || kill.survives_havoc_plain(&rem)
        || !kill.survives_havoc_plain(&len)
    {
        return None;
    }
    let n = Formula::Int(n);
    Some(vec![
        Formula::Eq(
            Box::new(rem.clone()),
            Box::new(Formula::Sub(
                Box::new(len),
                Box::new(Formula::Mul(Box::new(n.clone()), Box::new(chunks))),
            )),
        ),
        Formula::Le(Box::new(Formula::Int(0)), Box::new(rem.clone())),
        Formula::Lt(Box::new(rem), Box::new(n)),
    ])
}
