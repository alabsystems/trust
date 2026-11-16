// Trust (2026-10-15, TRUST-KI-1015-1, RANGE-INDEX-RESULT-LEN): the length of the slice a
// std range index (and `[T]::split_at`) returns, as a post-return definition of the call.
//
// THE DEFECT (a correct program reported refuted). `if input.len() < 6 { return None }
// let rest = &input[2..]; rest.len() - 4` had both its `[overflow:sub]` row and the row's
// hardened `mir_assert::Overflow(Sub)` twin FAILED on the channel seal `b58a105dde`, by
// the in-process `ay` lane (`solver: ay-in-process`; the trust-mc typed-CHC evidence on
// the same rows was demoted to unknown and is not what refuted them), with the
// counterexample `input__slice_len = 6, rest__slice_len#s4_t = 0`. The index lowers to
// the call `rest = <[u8] as Index<RangeFrom<usize>>>::index(copy input, move _13)`,
// which the VC lane havocs: the length metadata of its destination, `rest__slice_len`,
// was a fresh version constrained by nothing but `0 <= len <= isize::MAX`, so SAT chose
// a length no execution of the program produces. The same held for every range shape
// (`&s[a..b]`, `&s[..b]`, `&s[k..]` with a symbolic `k`, `&mut s[2..]`, an array or
// `str` receiver, a sub-slice of a sub-slice, `s = &s[2..]` in place and in a loop) and
// for `split_at`: each SAFE variant was FAILED on the channel and on main `edbb3f3009`
// (`tests/subslice_len_realmir.rs`).
//
// THE FACT. On the normal return of a std range index of a built-in slice, array or
// `str`, the result's length is exactly
//
//   s[a..]   len - a      (`RangeFrom`)
//   s[a..b]  b - a        (`Range`)
//   s[..b]   b            (`RangeTo`)
//
// where `len`, `a` and `b` are the values the call received. The call returns only when
// the range is in bounds (`a <= len`, resp. `a <= b <= len`, `b <= len`: the panic the
// `RangeIndex` row charges at the same call), and std's `SliceIndex` impls then return
// the sub-slice `[a, b)` (for `str`, additionally only when both ends are char
// boundaries; the byte length is the same). Integer subtraction: no wrap is assumed,
// none is possible on the return edge. `(head, tail) = s.split_at(mid)` on a `[T]` is
// `(&s[..mid], &s[mid..])` when it returns (it panics on `mid > len`, the row
// `SliceMethodPanic::SplitAt` charges): `head.len() == mid`, `tail.len() == len - mid`.
//
// WHERE IT GOES. A POST-RETURN DEFINITION in the path-definition fixpoint
// (`path_defs::v2_path_def_fixpoint`, the `Terminator::Call` arm, beside
// `probe_call_definitions`): added to the call block's NORMAL outflow after the
// terminator kill, so it reaches only the return target (never the cleanup edge), is
// intersected away at any join one of whose entries lacks it, and is killed by every
// later write of one of its names. Facts in that channel are stated over BARE names and
// renamed WITH the body at each use point, so the names must denote, on the return
// edge, exactly the values the call received — which is what the terminator-kill gate
// below establishes. It reaches the per-statement rows and their hardened twins alike
// (`hardened.rs` reads the same map as its reaching definitions), and it lives inside a
// loop body, where the semantic-guard map collapses at the header's revisit.
//
// SOUNDNESS — every gate is a hard requirement; a miss emits NOTHING (the rows keep
// their old, weaker hypotheses):
//  * THE IMPL THAT RUNS IS STD'S. The callee is the `Index`/`IndexMut` (or `SliceIndex`)
//    trait method of `core`/`std` instantiated at a std panicking range type
//    (`panic_calls::callee_panicking_range_index`, the recognizer the `RangeIndex` row
//    keys on), with no unauthenticated crate stamp anywhere in the spelling and a
//    `callee_key` from the real sysroot. The INDEXED type in that instantiation is a
//    built-in slice `[T]`, array `[T; N]` or `str`, and so is the receiver's own MIR
//    type (behind a reference). No other crate can implement `Index<core::ops::Range*>`
//    for those types (the orphan rule: foreign trait, foreign self type, foreign
//    argument), so the body is core's. `split_at`: core's inherent `[T]::split_at{,_mut}`
//    by its `core::slice::<impl [T]>` root (only the crate defining `[T]` can write an
//    inherent impl on it) and its real-sysroot key, a `&[T]`/`&mut [T]` receiver and an
//    unsigned `mid` by their MIR types; `str::split_at` is not admitted.
//  * THE RANGE IS READ EXACTLY AS THE ROW READS IT. The range argument is the one the
//    row takes (`panic_calls::range_index_range_operand`), it traces to a `Range` /
//    `RangeTo` / `RangeFrom` aggregate (`iterator_yield::trace_local_to_range_family`),
//    and each bound resolves through `panic_calls::range_bound_at_call_formula`, the
//    resolution the row's own violation uses (a constant, a single-valued name, a name
//    unchanged between the aggregate and the call, or the root versioned at the read).
//    The receiver length is `panic_calls::range_index_receiver_len`, the row's. Each
//    names the value the call received, read at the call.
//  * THE CALL WRITES THE LEFT SIDE AND NOTHING ON THE RIGHT. The destination is a whole
//    local whose length is the `{dest}__slice_len` NAME (for `split_at`, the two
//    `{dest}.0__slice_len` / `{dest}.1__slice_len` names of a `(&[T], &[T])` tuple), and
//    the version oracle's terminator kill (`StmtVersionCtx::terminator_kill`) must kill
//    that name — the call is recognized as its writer, so no stale fact about it
//    survives the call — and must kill NO name of the right side: the receiver length
//    and the bounds hold on the return edge the values the call read. This is what
//    refuses `s = index(copy s, ..)` (a destination that is its own receiver would make
//    the bare fact `x == x - 2`).
//  * NO IDENTITY-LESS CONSTANT. A body that mentions a `ConstValue::OpaqueScalar` gets no
//    fact (the `call_facts::vec_from_elem_len_facts` gate): a bound spelled by such a
//    constant need not denote one value.
//
// WHICH GATES A PROGRAM REACHES ALONE (2026-10-15, the review's SHOULD-FIX; DECISION_QUEUE
// RANGE-INDEX-RESULT-LEN-1). Four of them are defence in depth, each pinned by `gate_tests`
// below on a real-MIR fixture, edited where no compiler output reaches it:
//  * the left-side kill: no body reaches it. A whole-local destination's length name is
//    `{dest}__slice_len`, which the call's kill names (`path_defs::dest_term_extras`), or an
//    `as_bytes` receiver's (`guards::as_bytes_length_receiver`), which needs the
//    destination's one whole write to be that `as_bytes` call, not this one; a `split_at`
//    half's `{dest}.k__slice_len` lies under the destination's name;
//  * the receiver's MIR type and `split_at`'s unsigned `mid`: no well-typed call reaches
//    them (`Index::index` takes `&Self`, `SliceIndex::index` a `&T` of its indexed type,
//    `split_at` a `usize`); they refuse an extraction whose callee spelling and operand
//    types disagree;
//  * the `OpaqueScalar` gate: every body that mentions one reaches it, and a correct row
//    there keeps its old hypotheses (the cost; docs/KNOWN_HAZARDS.md); no wrong program
//    was found that it alone keeps refuted. A keyed constant is one value per function
//    instance, and a positional one is the value of a statement that dominates the call,
//    which no point the fact reaches can re-run without running the call again.
//
// A row the fact makes UNSAT is proved on the solver's own authority, as any row with
// path definitions is; a row it does not make UNSAT keeps a model that now satisfies
// the std contract, so a FAILED that remains (`&input[2..]`, `rest.len() - 5` under
// `len >= 6`) is an execution.
//
// NOT HERE: `RangeInclusive`/`RangeToInclusive`/`(Bound, Bound)` and the `core::range`
// types (the tracer reads none of them, and the inclusive end carries an `exhausted`
// flag), `RangeFull`, owned `Vec`/`String` receivers (no slice length at the call), and
// the `chunks` family (its items are an iterator's yields; `chunks_exact` and the
// non-emptiness of a `chunks` item are proved by the adapter-yield lanes). Each keeps
// its havocked length, and a row over it can still be FAILED on a model no execution
// produces (docs/KNOWN_HAZARDS.md, TRUST-KI-1015-1).

use super::*;

/// The post-return result-length definitions of every std range-index and `split_at`
/// call in `func`, keyed by the CALL block (see the module header). The path-definition
/// fixpoint adds a block's entry to that block's normal outflow, after its terminator
/// kill.
pub(super) fn range_index_result_len_definitions(
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
        if let Some(fact) = range_index_result_len_fact(func, block) {
            out.insert(block.id, vec![fact]);
        } else if let Some(facts) = split_at_result_len_facts(func, block)
            && !facts.is_empty()
        {
            out.insert(block.id, facts);
        }
    }
    // The identity gate, asked once and only when some call produced a fact.
    if !out.is_empty() && super::call_facts::body_mentions_opaque_scalar(func) {
        return FxHashMap::default();
    }
    out
}

pub(super) fn block_range_index_result_len_definitions(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Vec<Formula> {
    if !matches!(block.terminator, Terminator::Call { target: Some(_), .. }) {
        return Vec::new();
    }
    let facts = range_index_result_len_fact(func, block)
        .map(|fact| vec![fact])
        .or_else(|| split_at_result_len_facts(func, block))
        .unwrap_or_default();
    if !facts.is_empty() && super::call_facts::body_mentions_opaque_scalar(func) {
        return Vec::new();
    }
    facts
}

/// `{dest}__slice_len == <length of the range at the call>` for a std range index
/// terminating `block`, or `None` when a gate misses.
fn range_index_result_len_fact(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<Formula> {
    let Terminator::Call { func: callee, args, dest, callee_key, .. } = &block.terminator else {
        return None;
    };
    if !dest.projections.is_empty()
        || args.len() != 2
        || !callee_key.as_ref().is_some_and(|key| key.krate_is_real_sysroot)
    {
        return None;
    }
    // The impl that runs is core's.
    let indexed = std_builtin_range_index(callee)?;
    if trust_types::path_has_unauthenticated_crate_stamp(callee) {
        return None;
    }
    // The range argument the `RangeIndex` row takes, in the position the instantiation
    // names; the receiver is the other argument, a reference to a built-in slice, array
    // or `str` by its own MIR type.
    let range_operand = super::panic_calls::range_index_range_operand(func, callee, args)?;
    if !std::ptr::eq(range_operand, &args[indexed.range_arg]) {
        return None;
    }
    let receiver = &args[1 - indexed.range_arg];
    if !receiver_is_builtin_indexed(func, receiver) {
        return None;
    }
    let (Operand::Copy(range_place) | Operand::Move(range_place)) = range_operand else {
        return None;
    };
    if !range_place.projections.is_empty()
        || crate::local_defs::is_parameter(func, range_place.local)
    {
        return None;
    }
    let traced = trace_local_to_range_family(func, range_place.local, 8)?;
    let bound = |op: &Operand| {
        super::panic_calls::range_bound_at_call_formula(func, range_operand, op, block)
    };
    let len_at_call = match traced {
        RangeFamilyOperands::From(start) => {
            let len = super::panic_calls::range_index_receiver_len(func, args)?;
            Formula::Sub(Box::new(len), Box::new(bound(start)?))
        }
        RangeFamilyOperands::Exclusive(start, end) => {
            Formula::Sub(Box::new(bound(end)?), Box::new(bound(start)?))
        }
        RangeFamilyOperands::To(end) => bound(end)?,
    };
    let dest_len = slice_len_name(func, dest.clone())?;
    written_by_call_alone(func, block, [(dest_len, len_at_call)]).and_then(|mut v| v.pop())
}

/// `{dest}.0__slice_len == mid` and `{dest}.1__slice_len == len - mid` for core's
/// `[T]::split_at{,_mut}(s, mid)` terminating `block`, or `None` when a gate misses.
fn split_at_result_len_facts(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<Vec<Formula>> {
    let Terminator::Call { func: callee, args, dest, callee_key, .. } = &block.terminator else {
        return None;
    };
    if !dest.projections.is_empty()
        || args.len() != 2
        || !callee_key.as_ref().is_some_and(|key| key.krate_is_real_sysroot)
    {
        return None;
    }
    let Some(Ty::Tuple(dest_elems)) = crate::local_ty_ref(func, dest.local) else {
        return None;
    };
    if dest_elems.len() < 2
        || !matches!(&dest_elems[0], Ty::Ref { inner, .. } if matches!(inner.as_ref(), Ty::Slice { .. }))
        || !matches!(&dest_elems[1], Ty::Ref { inner, .. } if matches!(inner.as_ref(), Ty::Slice { .. }))
    {
        return None;
    }
    if !matches!(method_tail(callee), "split_at" | "split_at_mut")
        || callee.contains(" as ")
        || !(callee.starts_with("core::slice::<impl [")
            || callee.starts_with("std::slice::<impl ["))
        || trust_types::path_has_unauthenticated_crate_stamp(callee)
    {
        return None;
    }
    let (receiver, mid) = (&args[0], &args[1]);
    let receiver_is_slice = matches!(
        crate::operand_ty_cow(func, receiver).as_deref(),
        Some(Ty::Ref { inner, .. }) if matches!(inner.as_ref(), Ty::Slice { .. })
    );
    let mid_is_unsigned = matches!(
        crate::operand_ty_cow(func, mid).as_deref(),
        Some(Ty::Int { signed: false, .. } | Ty::PtrSizedInt { signed: false })
    );
    if !receiver_is_slice || !mid_is_unsigned {
        return None;
    }
    // Each half of the `(&[T], &[T])` destination is a slice reference with a length NAME.
    let half = |field: usize| -> Option<String> {
        let place =
            Place { local: dest.local, projections: vec![trust_types::Projection::Field(field)] };
        slice_len_name(func, place)
    };
    let (head_len, tail_len) = (half(0)?, half(1)?);
    if head_len == tail_len {
        return None;
    }
    let len = crate::slice_len_formula(func, receiver)?;
    let mid = crate::operand_to_formula(func, mid);
    written_by_call_alone(
        func,
        block,
        [(head_len, mid.clone()), (tail_len, Formula::Sub(Box::new(len), Box::new(mid)))],
    )
}

/// The length NAME (`{place}__slice_len`) of a slice-reference place, or `None` when its
/// length is not such a name. Also `as_chunks_len`'s reader of the two halves' names.
pub(super) fn slice_len_name(func: &VerifiableFunction, place: Place) -> Option<String> {
    match crate::slice_len_formula(func, &Operand::Copy(place)) {
        Some(Formula::Var(name, Sort::Int))
            if name.ends_with(SLICE_LEN_SUFFIX) && !name.contains('#') =>
        {
            Some(name)
        }
        _ => None,
    }
}

/// The definitions `lhs == rhs`, when the call terminating `block` writes every `lhs`
/// name and NO name of any `rhs` (the version oracle's terminator kill; see the module
/// header). `None` when either fails for any pair.
fn written_by_call_alone(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    defs: impl IntoIterator<Item = (String, Formula)>,
) -> Option<Vec<Formula>> {
    let sv = super::stmt_versions_for(func);
    let kill = sv.terminator_kill(func, block);
    defs.into_iter()
        .map(|(lhs, rhs)| {
            let lhs = Formula::Var(lhs, Sort::Int);
            let written = !kill.survives_havoc_plain(&lhs);
            let rhs_untouched = kill.survives_havoc_plain(&rhs);
            (written && rhs_untouched).then(|| Formula::Eq(Box::new(lhs), Box::new(rhs)))
        })
        .collect()
}

/// The argument position of the range in a std range-index callee whose INDEXED type —
/// the `Index`/`IndexMut` Self type, or the `SliceIndex` trait argument — is a built-in
/// slice `[T]`, array `[T; N]` or `str`. `None` for every other spelling.
struct BuiltinRangeIndex {
    range_arg: usize,
}

fn std_builtin_range_index(callee: &str) -> Option<BuiltinRangeIndex> {
    let shape = super::panic_calls::callee_panicking_range_index(callee)?;
    let q = super::iterator_yield::ParsedQualifier::parse(callee)?;
    let trait_path = q.trait_path?;
    let self_ty = q.self_ty.trim();
    let open = trait_path.find('<')?;
    let generic = trait_path[open + 1..].trim_end().strip_suffix('>')?.trim();
    let indexed = match shape.range_arg {
        1 => self_ty,
        0 => generic,
        _ => return None,
    };
    let builtin = indexed == "str" || (indexed.starts_with('[') && indexed.ends_with(']'));
    builtin.then_some(BuiltinRangeIndex { range_arg: shape.range_arg })
}

/// The receiver's MIR type is a reference to a built-in slice, array (a const-generic
/// one included) or `str`.
fn receiver_is_builtin_indexed(func: &VerifiableFunction, receiver: &Operand) -> bool {
    match crate::operand_ty_cow(func, receiver).as_deref() {
        Some(Ty::Ref { inner, .. }) => matches!(
            inner.as_ref(),
            Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. } | Ty::Str
        ),
        _ => false,
    }
}

/// The gates no program-level test reaches alone (see the module header): each test asks
/// this module's own functions about a real-MIR fixture of `tests/subslice_len_realmir.rs`
/// (`tests/fixtures/subslice_len/`, the channel's raw `trustc` dump), with a control that
/// the same call passes when the gate's input is left as the compiler produced it. Each
/// goes red when its gate is switched off.
#[cfg(test)]
mod gate_tests {
    use super::*;

    fn load(name: &str) -> VerifiableFunction {
        let path =
            format!("{}/tests/fixtures/subslice_len/{name}.json", env!("CARGO_MANIFEST_DIR"));
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
        serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
    }

    /// The one block of `func` whose terminator calls a callee spelled with `needle`.
    fn call_block<'a>(func: &'a VerifiableFunction, needle: &str) -> &'a trust_types::BasicBlock {
        let mut hits = func.body.blocks.iter().filter(|b| {
            matches!(&b.terminator, Terminator::Call { func: callee, .. } if callee.contains(needle))
        });
        let block = hits.next().unwrap_or_else(|| panic!("a call to `{needle}`"));
        assert!(hits.next().is_none(), "exactly one call to `{needle}`");
        block
    }

    const RANGE_FROM_INDEX: &str = "Index<core::ops::range::RangeFrom";

    /// The left-side gate of `written_by_call_alone`: a definition is minted only for a
    /// name the call itself writes. No body reaches it (the module header), so it is asked
    /// directly: a15's index call writes its destination's length and READS its receiver's,
    /// and a definition of the receiver's length is refused.
    #[test]
    fn a_definition_whose_left_side_the_call_does_not_write_is_refused() {
        let func = load("a15_subslice_ok");
        let block = call_block(&func, RANGE_FROM_INDEX);
        let Terminator::Call { args, dest, .. } = &block.terminator else { unreachable!() };
        let dest_len = slice_len_name(&func, dest.clone()).expect("the destination's length name");
        assert!(
            written_by_call_alone(&func, block, [(dest_len, Formula::Int(0))]).is_some(),
            "control: the call writes its destination's length"
        );
        let Some(Formula::Var(receiver_len, Sort::Int)) = crate::slice_len_formula(&func, &args[0])
        else {
            panic!("a15's receiver has a length name");
        };
        assert!(
            written_by_call_alone(&func, block, [(receiver_len, Formula::Int(0))]).is_none(),
            "the call does not write its receiver's length: no definition of it"
        );
    }

    /// The `OpaqueScalar` gate, reached by a real program: `g1_opaque_start_ok<T: Cut>`
    /// (`&input[T::K..]`, an associated constant keyed by its item) passes every other gate,
    /// so its call alone yields the fact, and the body-wide gate withholds it.
    #[test]
    fn a_body_that_mentions_an_opaque_scalar_gets_no_definition() {
        let func = load("g1_opaque_start_ok");
        let block = call_block(&func, RANGE_FROM_INDEX);
        assert!(
            range_index_result_len_fact(&func, block).is_some(),
            "control: every gate but the body-wide one passes"
        );
        assert!(super::super::call_facts::body_mentions_opaque_scalar(&func));
        assert!(
            range_index_result_len_definitions(&func).is_empty(),
            "a body that mentions an OpaqueScalar gets no definition"
        );
    }

    /// The receiver's MIR-type gate: a15 with its receiver retyped `*const [u8]` while the
    /// callee still reads `<[u8] as Index<RangeFrom<usize>>>::index`. No well-typed call
    /// has that shape (`Index::index` takes `&Self`); the gate refuses a spelling and an
    /// operand type that disagree.
    #[test]
    fn a_receiver_whose_mir_type_is_not_a_builtin_reference_gets_no_fact() {
        let control = load("a15_subslice_ok");
        assert!(
            range_index_result_len_fact(&control, call_block(&control, RANGE_FROM_INDEX)).is_some(),
            "control: the unedited call yields the fact"
        );
        let mut edited = load("a15_subslice_ok");
        let receiver = {
            let Terminator::Call { args, .. } = &call_block(&edited, RANGE_FROM_INDEX).terminator
            else {
                unreachable!()
            };
            let (Operand::Copy(place) | Operand::Move(place)) = &args[0] else {
                panic!("a15's receiver is a place");
            };
            place.local
        };
        let decl = edited
            .body
            .locals
            .iter_mut()
            .find(|l| l.index == receiver)
            .expect("the receiver's declaration");
        let Ty::Ref { inner, .. } = &decl.ty else { panic!("a15's receiver is a reference") };
        decl.ty = Ty::RawPtr { mutable: false, pointee: inner.clone() };
        assert!(
            range_index_result_len_fact(&edited, call_block(&edited, RANGE_FROM_INDEX)).is_none(),
            "a receiver that is not a reference to a built-in slice, array or str: no fact"
        );
    }

    /// `split_at`'s unsigned-`mid` gate: b5's `split_at(2)` with its `mid` constant made a
    /// signed `ConstValue::Int`. No well-typed call has that shape (`mid: usize`).
    #[test]
    fn a_split_at_whose_mid_is_not_unsigned_gets_no_fact() {
        let control = load("b5_split_at_ok");
        assert!(
            split_at_result_len_facts(&control, call_block(&control, "::split_at")).is_some(),
            "control: the unedited call yields both halves"
        );
        let mut edited = load("b5_split_at_ok");
        let mut retyped = 0;
        for block in &mut edited.body.blocks {
            if let Terminator::Call { func: callee, args, .. } = &mut block.terminator
                && callee.ends_with("::split_at")
            {
                assert!(matches!(args[1], Operand::Constant(ConstValue::Uint(2, 64))));
                args[1] = Operand::Constant(ConstValue::Int(2));
                retyped += 1;
            }
        }
        assert_eq!(retyped, 1, "b5 has one split_at call");
        assert!(
            split_at_result_len_facts(&edited, call_block(&edited, "::split_at")).is_none(),
            "a mid that is not unsigned by its MIR type: no fact"
        );
    }
}
