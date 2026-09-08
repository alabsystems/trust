// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # The crate-free grant: a bounded-allocation obligation deleted with no impersonation
//!
//! `collect_source_is_bounded_std_collection` GRANTS — a `true` makes
//! `generate_unbounded_allocation_vcs` `continue` past the whole collect, so the
//! obligation is not weakened, it DISAPPEARS. Until 2026-08-16 its adaptor step
//! tested the callee's LAST PATH SEGMENT and nothing else: no crate named, no
//! root anchored, no stamp consulted. So an ORDINARY crate — no impersonation, no
//! `--crate-name` trick — bought the grant by naming a function `map`:
//!
//! ```ignore
//! pub struct Endless { pub i: u64 }
//! impl Iterator for Endless {
//!     type Item = u8;
//!     fn next(&mut self) -> Option<u8> { self.i = self.i.wrapping_add(1); Some(0) }
//! }
//! pub struct Adapt;
//! impl Adapt { pub fn map(s: core::slice::Iter<'_, u8>, _f: u8) -> Endless { Endless { i: 0 } } }
//! // consumer:
//! pub fn boom(v: &Vec<u8>) -> Vec<u8> { mycrate::Adapt::map(v.iter(), 0).collect() }
//! ```
//!
//! `Endless::next` never returns `None`, so `boom` allocates without bound in
//! every execution. The evidence the engine threw away is in the sink's own
//! spelling: `<mycrate::Endless as core::iter::…::Iterator>::collect::<Vec<u8>>`
//! — the iterator being collected is a USER ADT.
//!
//! Two authenticators come out of that, and they are NOT the same claim:
//!
//!   * the CALLEE-side one closes the measured exploit and its siblings (every
//!     crate-free segment test in this lane), and
//!   * the VALUE-side one enforces the closure property the callee side assumes —
//!     see `the_walks_closure_property_is_enforced_not_assumed`, which states
//!     plainly that it is an invariant made checkable rather than a second
//!     demonstrated hole.
//!
//! ## What is measured here and what is assembled
//!
//! Every callee spelling and every ADT type name below is VERBATIM from a real
//! `-Ztrust-dump=mir` bundle checked into this tree; each one carries the file it
//! was taken from in a comment. The two *bundles* in [`exploit_bundle`] are
//! assembled from those strings rather than dumped, because no trust compiler was
//! available in this session (`stage2/bin` was empty and being rebuilt).
//!
//! The SHAPE those bundles assert about is measured, not assumed. The exploit
//! source above (checked in as
//! `tests/ui/trust/unauthenticated_iter_adaptor_collect_refused.rs`) compiles to
//! this MIR under a stock rustc — the pre-optimization stage the extractor reads,
//! confirmed by `stdctl_fine_real_std.json` carrying the same `Deref::deref` then
//! `core::slice::<impl [u8]>::iter` pair:
//!
//! ```text
//! let mut _2: mycrate::Endless;
//! let mut _3: std::slice::Iter<'_, u8>;
//!   _4 = <Vec<u8> as Deref>::deref(copy _1)
//!   _3 = core::slice::<impl [u8]>::iter(copy _4)
//!   _2 = Adapt::map(move _3, const 0_u8)
//!   _0 = <Endless as Iterator>::collect::<Vec<u8>>(move _2)
//! ```
//!
//! and the control's MIR differs from it in exactly one line and one identifier
//! (`Adapt::nudge`). Note `_2: mycrate::Endless`: the value-side discriminator is
//! present in the real MIR, it was simply never consulted.
//!
//! The REAL-DUMP tests below (`the_real_production_*`) replay unmodified
//! production bundles through the same production entry point, so the shapes the
//! assembled pair asserts about are not the only evidence.
//!
//! Every test drives `generate_unbounded_allocation_vcs` — the production entry
//! point — never a re-implementation of the walk.

use trust_types::{BasicBlock, LocalDecl, UnwindEdge, VerifiableBody};

use super::*;

// ======================================================================
// Verbatim spellings, with provenance
// ======================================================================

/// `fixtures/trusted-root-spoof-endless-iter-2026-08-16/stdctl_fine_real_std.json`,
/// block 1: the genuine slice-iterator producer.
const REAL_SLICE_ITER: &str = "core::slice::<impl [u8]>::iter";

/// The same file, local 3: the type that producer returns.
const REAL_SLICE_ITER_TY: &str = "core::slice::iter::Iter<'_, u8>";

/// `…/user_boom_ordinary_crate_name.json`, block 1: a `collect` sink whose `Self`
/// is a USER ADT. Only the crate/module prefix of the `Self` type differs from the
/// bundle the compiler produced for the exploit source.
const USER_ADT_COLLECT_SINK: &str = "<mycrate::vec::Endless as \
     core::iter::traits::iterator::Iterator>::collect::<alloc::vec::Vec<u8>>\
     ::<__trust_elem_bytes@8>";

/// The same file, local 2: the user iterator ADT's rendered type name.
const USER_ADT_ITER_TY: &str = "mycrate::vec::Endless";

/// The same file, block 0: how the extractor renders a call to a USER crate's
/// inherent method. `mycrate::vec::Adapt::map` below is this shape with the type
/// and method renamed; compare `term::Context::iter` and
/// `lib::arrayvec::ArrayVec::<T, CAP>::drain::<…>` in the wider dump corpus.
const USER_INHERENT_CALL_SHAPE: &str = "mycrate::vec::Vec::<u8>::iter";

/// `trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0/term__Context__new.json`,
/// block 1: the GENERIC spelling of a std `Iterator` adaptor. Both this and the
/// QUALIFIED spelling occur in the corpus, which is why the authenticator accepts
/// both.
const REAL_STD_MAP_GENERIC: &str = "std::iter::Iterator::map";

/// `…/stdctl_fine_real_std.json`, block 2: the QUALIFIED spelling.
const REAL_STD_COPIED_QUALIFIED: &str = "<core::slice::iter::Iter<'_, u8> as \
     core::iter::traits::iterator::Iterator>::copied::<'_, u8>";

fn adt(name: &str) -> Ty {
    Ty::adt(name, vec![])
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: Option<BlockId>) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target,
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        is_foreign: false,
    }
}

/// `<adaptor>(v.iter(), 0).collect()`, where `v.iter()` is the genuine
/// `core::slice::<impl [u8]>::iter` and the value the adaptor returns is the user
/// ADT `mycrate::vec::Endless`.
///
/// `adaptor` is the ONLY thing that varies between the exploit and its control,
/// and it varies in one identifier.
fn exploit_bundle(adaptor: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "boom".to_string(),
        def_path: "user::boom".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: adt("alloc::vec::Vec<u8>"), name: None },
                // The RECEIVER of `core::slice::<impl [u8]>::iter`, and it is
                // `&[u8]` because that is what the compiler renders — MEASURED at
                // four of the six genuine grant sites in the bundle corpus. It was
                // a `Ty::u32()` placeholder until 2026-08-17; no compiler emits
                // that, and `producer_receiver_value_is_authenticated_sysroot`
                // correctly refuses it, so the placeholder made this bundle
                // untestable for the receiver conjunct.
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                    },
                    name: Some("v".into()),
                },
                LocalDecl { index: 2, ty: adt(USER_ADT_ITER_TY), name: Some("it".into()) },
                LocalDecl { index: 3, ty: adt(REAL_SLICE_ITER_TY), name: Some("src".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(
                        REAL_SLICE_ITER,
                        vec![Operand::Move(Place::local(1))],
                        3,
                        Some(BlockId(1)),
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: call(
                        adaptor,
                        vec![Operand::Move(Place::local(3)), Operand::Constant(ConstValue::Int(0))],
                        2,
                        Some(BlockId(2)),
                    ),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: call(
                        USER_ADT_COLLECT_SINK,
                        vec![Operand::Move(Place::local(2))],
                        0,
                        None,
                    ),
                },
            ],
            arg_count: 1,
            return_ty: adt("alloc::vec::Vec<u8>"),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Obligations the unbounded-allocation lane emits, in either form it uses: a
/// solvable `UnboundedAllocation` bound, or the visible `UnsupportedMir` row
/// (preclassified Unknown, never PROVEd) it raises when the element count is not
/// recoverable. A `collect` over an opaque source takes the second road — the row
/// the shipped compiler reported for the measured control run.
fn unbounded_alloc_rows(func: &VerifiableFunction) -> usize {
    generate_unbounded_allocation_vcs(func)
        .iter()
        .filter(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } => kind.contains("UnboundedAllocation"),
            other => format!("{other:?}").contains("UnboundedAllocation"),
        })
        .count()
}

fn fixture(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).unwrap_or_else(|e| panic!("parse dump bundle: {e}"))
}

// ======================================================================
// The exploit, and the one-identifier control
// ======================================================================

/// FALSIFY-ONCE for the adaptor step, at the production entry point.
///
/// The planted violation is asserted first, so the test cannot pass vacuously:
/// the user callee's last path segment really is `map`, which is really a member
/// of the length-preserving name set the old predicate tested — that predicate is
/// what stepped the walk through to argument 0 and found a genuine std producer
/// there.
///
/// The CONTROL differs from the exploit in one identifier (`nudge` for `map`) and
/// reports the obligation in both states, which is what makes the exploit's
/// silence a defect rather than a modeling gap.
#[test]
fn a_user_fn_whose_last_segment_is_map_no_longer_deletes_the_obligation() {
    let exploit_adaptor = "mycrate::vec::Adapt::map";
    assert_eq!(
        callee_tail(exploit_adaptor),
        "map",
        "planted violation is gone: the exploit callee's tail is no longer `map`, so the \
         old tail-only predicate would not have matched it and this test proves nothing"
    );
    assert!(
        !is_authenticated_std_len_preserving_adaptor(exploit_adaptor, "map"),
        "the user inherent fn must not authenticate as a std adaptor"
    );
    // ... while the two spellings the extractor really produces for std's `map`
    // and `copied` still do, so the refusal is an anchor and not a blanket.
    assert!(is_authenticated_std_len_preserving_adaptor(REAL_STD_MAP_GENERIC, "map"));
    assert!(is_authenticated_std_len_preserving_adaptor(REAL_STD_COPIED_QUALIFIED, "copied"));

    let control = exploit_bundle("mycrate::vec::Adapt::nudge");
    assert_eq!(
        unbounded_alloc_rows(&control),
        1,
        "planted violation is gone: the byte-identical control (one identifier apart) no \
         longer reports the unbounded allocation, so the exploit proves nothing"
    );

    let exploit = exploit_bundle(exploit_adaptor);
    assert_eq!(
        unbounded_alloc_rows(&exploit),
        1,
        "renaming a user function to `map` must not delete the unbounded-allocation \
         obligation: `Endless::next` never returns None, so this collect is unbounded in \
         every execution"
    );
}

/// A user adaptor returning a GENUINE std iterator type which happens to be
/// unbounded.
///
/// ```ignore
/// impl Adapt {
///     pub fn map(s: core::slice::Iter<'_, u8>, _f: u8) -> core::iter::Cycle<core::slice::Iter<'_, u8>> {
///         s.cycle()
///     }
/// }
/// pub fn boom(v: &Vec<u8>) -> Vec<u8> { mycrate::Adapt::map(v.iter(), 0).collect() }
/// ```
///
/// 2026-08-17 (round 4) CORRECTION, and the reason this test now asserts the
/// opposite of what it used to for its own control. It shipped as *"only the
/// callee test can refuse it"* with a control asserting that the SAME bundle with
/// a genuine `core::iter::Iterator::map` in the adaptor slot takes the
/// bounded-source skip — i.e. the test itself recorded a measured grant over a
/// `Cycle` value, which never returns `None`. That grant was a false proof of
/// exactly the class `bounded_source_value_tests` exists for: `Cycle` is real
/// `core`, correctly unstamped, and endless. Both bundles are gated now, by two
/// independent conditions, and the test says which condition sees which.
#[test]
fn a_user_adaptor_returning_an_unbounded_std_iterator_type_stays_gated() {
    const CYCLE_TY: &str = "core::iter::adapters::cycle::Cycle<core::slice::iter::Iter<'_, u8>>";
    const BOUNDED_TY: &str =
        "core::iter::adapters::cloned::Cloned<core::slice::iter::Iter<'_, u8>>";
    let bundle = |adaptor: &str, value_ty: &str| {
        let mut f = exploit_bundle(adaptor);
        for decl in &mut f.body.locals {
            if decl.index == 2 {
                decl.ty = adt(value_ty);
            }
        }
        for block in &mut f.body.blocks {
            if let Terminator::Call { func: callee, .. } = &mut block.terminator
                && callee_tail(callee) == "collect"
            {
                *callee = format!(
                    "<{value_ty} as core::iter::traits::iterator::Iterator>\
                     ::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@1>"
                );
            }
        }
        f
    };

    // Non-vacuity for the CALLEE half: the same shape with a BOUNDED std value
    // type and a genuine std adaptor really does take the skip, so the two
    // refusals below are about the callee and the boundedness — not about the
    // shape being unrecognized.
    assert_eq!(
        unbounded_alloc_rows(&bundle(REAL_STD_MAP_GENERIC, BOUNDED_TY)),
        0,
        "planted violation is gone: an authenticated chain over a bounded std value no \
         longer takes the skip, so nothing below is isolating anything"
    );

    // The CALLEE half, on its own: bounded value, user adaptor.
    assert_eq!(
        unbounded_alloc_rows(&bundle("mycrate::vec::Adapt::map", BOUNDED_TY)),
        1,
        "a user inherent fn whose last path segment is `map` must not step the walk"
    );

    // The BOUNDEDNESS half, on its own: every callee genuine, value is `Cycle`.
    // This is the case the pre-round-4 tree granted.
    assert!(
        ty_is_authenticated_std_iterator(&adt(CYCLE_TY)),
        "planted violation is gone: `Cycle` no longer passes the PROVENANCE authenticator, \
         so gating it below would say nothing about boundedness"
    );
    assert_eq!(
        unbounded_alloc_rows(&bundle(REAL_STD_MAP_GENERIC, CYCLE_TY)),
        1,
        "a genuine, correctly-unstamped `core` iterator that never returns `None` must keep \
         the obligation whatever produced it"
    );

    // …and both halves failing at once, which is the program in the doc comment.
    let planted = bundle("mycrate::vec::Adapt::map", CYCLE_TY);
    assert_eq!(
        unbounded_alloc_rows(&planted),
        1,
        "a user adaptor returning a genuine-but-unbounded std iterator type must keep the \
         obligation"
    );
}

/// FALSIFY-ONCE for the adaptor hop in the COUNT reconstruction (as opposed to the
/// bounded-source walk): `(0..3)` fed through a user `map` used to hand the count
/// `3` to a `collect` whose real source is endless. A constant count below the
/// ceiling is skipped outright, so the row vanished with no diagnostic.
#[test]
fn a_user_adaptor_over_a_real_range_no_longer_supplies_the_count() {
    let bundle = |adaptor: &str| VerifiableFunction {
        name: "boom".to_string(),
        def_path: "user::boom".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: adt("alloc::vec::Vec<u8>"), name: None },
                LocalDecl { index: 1, ty: adt("core::ops::range::Range<u64>"), name: None },
                LocalDecl { index: 2, ty: adt(USER_ADT_ITER_TY), name: Some("it".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "core::ops::range::Range<u64>".to_string(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![
                                Operand::Constant(ConstValue::Int(0)),
                                Operand::Constant(ConstValue::Int(3)),
                            ],
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: call(
                        adaptor,
                        vec![Operand::Move(Place::local(1)), Operand::Constant(ConstValue::Int(0))],
                        2,
                        Some(BlockId(1)),
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: call(
                        USER_ADT_COLLECT_SINK,
                        vec![Operand::Move(Place::local(2))],
                        0,
                        None,
                    ),
                },
            ],
            arg_count: 0,
            return_ty: adt("alloc::vec::Vec<u8>"),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let sound = bundle(REAL_STD_MAP_GENERIC);
    assert_eq!(
        unbounded_alloc_rows(&sound),
        0,
        "planted violation is gone: `(0..3).map(f).collect()` no longer recovers the \
         constant count 3 through the adaptor, so the forgery below proves nothing"
    );
    let planted = bundle("mycrate::vec::Adapt::map");
    assert_eq!(
        unbounded_alloc_rows(&planted),
        1,
        "a user fn named `map` must not carry the Range's count across to the collect"
    );
}

/// The VALUE-side half, and an HONEST statement of what it is for.
///
/// It is not a patch for a demonstrated exploit. It enforces the CLOSURE PROPERTY
/// the callee-side authenticators silently rely on: *every accepted step returns a
/// value whose `next` is std's own code.* That property holds of today's arm set —
/// I looked for a source program that defeats the callee side alone and did not
/// find one: every std-rooted spelling with a producer tail
/// (`iter`/`into_iter`/`drain`/`keys`/…) that also satisfies one of the module
/// disjuncts returns a std iterator, and the one std-rooted spelling that CAN
/// return a caller-chosen iterator, the generic
/// `core::iter::traits::collect::IntoIterator::into_iter`, is kept out only by
/// those disjuncts not mentioning `core::iter::` (asserted below, so the day
/// somebody widens them this test is the tripwire).
///
/// That is a property of a hand-maintained substring list, holding by luck, and
/// re-derived by every reader. Here it is a checked invariant of the walk instead:
/// the identity of the value is read from the MIR local's own `Ty`, at every step.
/// The planted violation is the bundle that violates the closure property with
/// every callee spelling genuine.
#[test]
fn the_walks_closure_property_is_enforced_not_assumed() {
    let generic_into_iter = "core::iter::traits::collect::IntoIterator::into_iter";
    assert!(
        trust_types::path_root_is_authenticated_sysroot_crate(generic_into_iter),
        "the generic IntoIterator spelling root-authenticates — so the ONLY thing \
         keeping it out of the producer set is the module-disjunct list"
    );
    assert_eq!(callee_tail(generic_into_iter), "into_iter", "…and its tail is in the tail set");
    assert!(
        !is_std_collection_iter_producer(generic_into_iter, callee_tail(generic_into_iter)),
        "TRIPWIRE: the producer disjuncts now admit `core::iter::…::IntoIterator::into_iter`, \
         whose return type is the CALLER's `IntoIter`. The walk's closure property no longer \
         holds on the callee side alone; the value-side check below is now load-bearing for a \
         REACHABLE program and this test must be rewritten to exhibit it."
    );

    // Every callee in this bundle is a genuine, authenticated std spelling: the
    // leaf producer, the length-preserving adaptor and the sink. The only planted
    // fact is that the value the adaptor yields is a USER ADT.
    let mut planted = exploit_bundle(REAL_STD_MAP_GENERIC);
    assert!(
        is_authenticated_std_len_preserving_adaptor(REAL_STD_MAP_GENERIC, "map"),
        "the adaptor must authenticate, or this test is measuring the callee side"
    );
    assert_eq!(
        unbounded_alloc_rows(&planted),
        1,
        "a chain of authenticated std callees whose intermediate VALUE is a user ADT must \
         keep the obligation: only the value's own type says whose `next` runs"
    );

    // Same bundle, same callees, with the value type std's `map` would really have
    // produced: the grant is available again — an anchor, not a blanket refusal.
    for decl in &mut planted.body.locals {
        if decl.index == 2 {
            decl.ty =
                adt("core::iter::adapters::map::Map<core::slice::iter::Iter<'_, u8>, [closure]>");
        }
    }
    assert_eq!(
        unbounded_alloc_rows(&planted),
        0,
        "an authenticated chain over authenticated std iterator values must still be waved \
         through"
    );
}

// ======================================================================
// The real production chains — the over-decline check
// ======================================================================

/// `term::Context::new` = `s.iter().map(f).collect()`, an UNMODIFIED production
/// dump (`trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0/`). It takes the
/// bounded-source skip on pristine `main` and must keep taking it: the leaf is
/// `core::slice::<impl [T]>::iter`, the adaptor is `std::iter::Iterator::map`, and
/// the iterator locals are typed `std::slice::Iter` / `std::iter::Map`. Both
/// authenticators are satisfied by the compiler's own bytes — nothing here was
/// adjusted to make them pass.
#[test]
fn the_real_production_slice_iter_map_collect_keeps_its_bounded_source_skip() {
    let func = fixture(include_str!(
        "../../../trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0/term__Context__new.json"
    ));
    // Non-vacuity: this bundle really is the shape under test.
    let callees: Vec<&str> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.as_str()),
            _ => None,
        })
        .collect();
    assert!(callees.contains(&"core::slice::<impl [T]>::iter"), "{callees:?}");
    assert!(callees.contains(&REAL_STD_MAP_GENERIC), "{callees:?}");
    assert!(callees.iter().any(|c| callee_tail(c) == "collect"), "{callees:?}");

    assert_eq!(
        unbounded_alloc_rows(&func),
        0,
        "a genuine `slice::iter().map(f).collect()` must stay free of the obligation"
    );
}

/// `term::auto_generate_context` = `(0..n).map(f).collect()`, an UNMODIFIED
/// production dump. This one does NOT take the bounded-source skip (a `Range` is
/// generative); it reaches `iter_collect_count`, whose `Range`-aggregate arm and
/// length-preserving hop are both now anchored. The recovered count must survive,
/// because losing it would replace a solvable bound with an Unknown.
#[test]
fn the_real_production_range_map_collect_keeps_its_recovered_count() {
    let func = fixture(include_str!(
        "../../../trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0/term__auto_generate_context.json"
    ));
    let counted = generate_unbounded_allocation_vcs(&func)
        .iter()
        .filter(|vc| !matches!(&vc.kind, VcKind::UnsupportedMir { .. }))
        .count();
    let unknown = generate_unbounded_allocation_vcs(&func)
        .iter()
        .filter(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, .. } => kind.contains("UnboundedAllocation"),
            _ => false,
        })
        .count();
    assert_eq!(
        (counted, unknown),
        (1, 0),
        "`(0..n).map(f).collect()` must keep its SOLVABLE count obligation, not degrade \
         to a count-not-derivable Unknown"
    );
}

/// `term::generate_binder_names` = `(0..).map(f).filter(g).take(n).collect()`, an
/// UNMODIFIED production dump. The count comes from the `take` arm, whose
/// `tail == "take"` test named no crate; it is now authenticated and the count
/// must still be recovered.
#[test]
fn the_real_production_take_capped_chain_keeps_its_recovered_count() {
    let func = fixture(include_str!(
        "../../../trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0/term__generate_binder_names.json"
    ));
    let rows = generate_unbounded_allocation_vcs(&func);
    assert_eq!(
        rows.iter().filter(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. })).count(),
        0,
        "the `take(n)` count must still be recoverable, not degrade to an Unknown"
    );
    assert_eq!(rows.len(), 1, "one solvable count obligation, as on pristine main");
}

// ======================================================================
// The remaining crate-free grants in the same lane
// ======================================================================

/// FALSIFY-ONCE for the `Range`-aggregate identity in `iter_collect_count`.
///
/// The old test was `name.contains("Range")`, which names no crate: a user
/// `struct MyRange { a: u64, b: u64 }` with an endless `Iterator` impl bought the
/// count `3`, and a constant count below the ceiling is SKIPPED outright — so the
/// obligation vanished with no diagnostic at all. `aggregate_is_exclusive_range`
/// is this crate's existing anchored range-family identity.
#[test]
fn a_user_adt_named_like_a_range_no_longer_buys_a_count() {
    let bundle = |adt_name: &str| VerifiableFunction {
        name: "boom".to_string(),
        def_path: "user::boom".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: adt("alloc::vec::Vec<u8>"), name: None },
                LocalDecl { index: 1, ty: adt(adt_name), name: Some("r".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: adt_name.to_string(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        vec![
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(3)),
                        ],
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: call(
                    USER_ADT_COLLECT_SINK,
                    vec![Operand::Move(Place::local(1))],
                    0,
                    None,
                ),
            }],
            arg_count: 0,
            return_ty: adt("alloc::vec::Vec<u8>"),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    // Non-vacuity: the genuine exclusive Range still yields the derivable count 3,
    // which (being a small constant) is legitimately skipped — zero rows.
    let genuine = bundle("core::ops::range::Range<u64>");
    assert!(
        aggregate_is_exclusive_range("core::ops::range::Range<u64>"),
        "planted violation is gone: the anchored identity no longer accepts the real Range"
    );
    assert_eq!(
        unbounded_alloc_rows(&genuine),
        0,
        "a real `(0..3).collect()` is bounded by a derivable constant count"
    );

    let planted = bundle("mycrate::MyRange<u64>");
    assert!(
        "mycrate::MyRange<u64>".contains("Range"),
        "planted violation is gone: the old unanchored test no longer matches"
    );
    assert_eq!(
        unbounded_alloc_rows(&planted),
        1,
        "a user ADT merely NAMED like a Range must not supply the collected count"
    );
}

/// FALSIFY-ONCE for the `repeat_n` free-function arm, whose `tail == "repeat_n"`
/// test named no crate either. `core::iter::repeat_n(x, n)` yields exactly `n`;
/// `mycrate::iter::repeat_n(x, n)` may yield anything.
#[test]
fn a_user_free_fn_named_repeat_n_no_longer_supplies_the_count() {
    assert!(
        is_authenticated_std_iter_free_fn("core::iter::repeat_n::<u32>", "repeat_n"),
        "the measured std spelling must still authenticate"
    );
    for forged in [
        "mycrate::iter::repeat_n::<u32>",
        "mycrate::repeat_n",
        "core::iterations::repeat_n",
        "__trust_crate@deadbeefdeadbeef::core::iter::repeat_n",
    ] {
        assert_eq!(callee_tail(forged), "repeat_n", "planted violation is gone for {forged}");
        assert!(
            !is_authenticated_std_iter_free_fn(forged, "repeat_n"),
            "an unauthenticated `repeat_n` must not supply the count: {forged}"
        );
    }

    // …and at the OBLIGATION, which is what the guard actually protects. A
    // constant count below the ceiling is SKIPPED outright, so a forged count of
    // `3` deletes the row with no diagnostic at all.
    let genuine = single_producer_collect_bundle("core::iter::repeat_n::<u8>", 1);
    assert_eq!(
        unbounded_alloc_rows(&genuine),
        0,
        "planted violation is gone: the genuine `repeat_n(x, 3)` no longer yields a \
         derivable constant count, so the forgery below proves nothing"
    );
    let forged = single_producer_collect_bundle("mycrate::iter::repeat_n::<u8>", 1);
    assert_eq!(
        unbounded_alloc_rows(&forged),
        1,
        "a user `repeat_n` must not supply the collected count"
    );
}

/// FALSIFY-ONCE for the `take` arm of the count reconstruction — the other
/// crate-free `tail ==` test. `Iterator::take(it, n)` yields at most `n` whatever
/// `it` is, which is why the arm is sound; `mycrate::Adapt::take(endless, 3)` is a
/// user function that may yield anything.
#[test]
fn a_user_fn_named_take_no_longer_supplies_the_count() {
    let genuine = single_producer_collect_bundle("std::iter::Iterator::take", 1);
    assert_eq!(
        unbounded_alloc_rows(&genuine),
        0,
        "planted violation is gone: the measured std `take` spelling no longer yields a \
         derivable constant count, so the forgery below proves nothing"
    );
    let forged = single_producer_collect_bundle("mycrate::vec::Adapt::take", 1);
    assert_eq!(callee_tail("mycrate::vec::Adapt::take"), "take");
    assert_eq!(
        unbounded_alloc_rows(&forged),
        1,
        "a user fn whose last path segment is `take` must not cap the collected count"
    );
}

/// FALSIFY-ONCE for [`is_str_view_iter_producer`]'s root anchor. Its
/// `contains("::str::")` disjunct named no crate at all, so a user MODULE called
/// `str` bought the bounded-source grant — no impersonation needed, the same class
/// as the adaptor forgery.
#[test]
fn a_user_module_named_str_no_longer_buys_the_bounded_source_grant() {
    let genuine = "core::str::<impl str>::chars";
    assert!(
        is_str_view_iter_producer(genuine, callee_tail(genuine)),
        "planted violation is gone: the measured std spelling no longer matches, so the \
         forgery below proves nothing"
    );
    for forged in ["mycrate::str::Endless::chars", "mycrate::my_str::str::Weird::bytes"] {
        assert!(
            forged.contains("::str::"),
            "planted violation is gone: {forged} no longer satisfies the old disjunct"
        );
        assert!(
            !is_str_view_iter_producer(forged, callee_tail(forged)),
            "a user module named `str` must not authenticate: {forged}"
        );
    }

    // At the obligation: `mycrate::str::Endless::chars(x).collect()`.
    let planted = str_producer_collect_bundle("mycrate::str::Endless::chars");
    assert_eq!(
        unbounded_alloc_rows(&planted),
        1,
        "a `chars()` on a user module named `str` must keep the obligation"
    );
    let sound = str_producer_collect_bundle(genuine);
    assert_eq!(
        unbounded_alloc_rows(&sound),
        0,
        "the genuine `core::str::<impl str>::chars` must still be waved through"
    );
}

/// `producer(…, const 3).collect()`, with the producer's result typed as the user
/// iterator ADT and the constant `3` placed at argument index `count_arg_idx` (the
/// count arms under test read argument 1 — the receiver occupies argument 0).
fn single_producer_collect_bundle(producer: &str, count_arg_idx: usize) -> VerifiableFunction {
    let mut args = vec![Operand::Move(Place::local(1)); count_arg_idx];
    args.push(Operand::Constant(ConstValue::Int(3)));
    VerifiableFunction {
        name: "boom".to_string(),
        def_path: "user::boom".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: adt("alloc::vec::Vec<u8>"), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: adt(USER_ADT_ITER_TY), name: Some("it".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(producer, args, 2, Some(BlockId(1))),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: call(
                        USER_ADT_COLLECT_SINK,
                        vec![Operand::Move(Place::local(2))],
                        0,
                        None,
                    ),
                },
            ],
            arg_count: 1,
            return_ty: adt("alloc::vec::Vec<u8>"),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `producer(s).collect()` where the produced iterator is typed as std's `Chars`
/// — so the VALUE-side authenticator is satisfied and only the producer path is
/// under test.
fn str_producer_collect_bundle(producer: &str) -> VerifiableFunction {
    let mut func = single_producer_collect_bundle(producer, 0);
    for decl in &mut func.body.locals {
        if decl.index == 2 {
            decl.ty = adt("core::str::iter::Chars<'_>");
        }
        // The str-view producer's RECEIVER, and it is a real `&str` place rather
        // than the shared builder's `const 3` filler: `chars()` is called ON
        // something, `producer_receiver_value_is_authenticated_sysroot` reads that
        // something's own type, and a constant operand has none. (The filler is
        // right for the COUNT-lane bundles this builder also serves, which is why
        // the fix is here and not in `single_producer_collect_bundle`.)
        if decl.index == 1 {
            decl.ty = Ty::Ref { mutable: false, inner: Box::new(Ty::Str) };
        }
    }
    for block in &mut func.body.blocks {
        if let Terminator::Call { func: callee, args, .. } = &mut block.terminator
            && callee == producer
        {
            *args = vec![Operand::Move(Place::local(1))];
        }
    }
    func
}

// ======================================================================
// The authenticators themselves, on measured spellings
// ======================================================================

/// The value-side authenticator: `Ty::Ref` is transparent (`Iterator::by_ref`
/// hands out `&mut I`), a std-rooted ADT authenticates, and everything else fails
/// closed.
///
/// 2026-08-17 (round 4) CORRECTION. This doc used to say *"the extractor does NOT
/// stamp `Ty::Adt` names, so a `--crate-name alloc` impersonator's own struct
/// renders `alloc::vec::Endless` and DOES pass this check"*. That stopped being
/// true in the same patch that wrote it: `trust_mir_extract::lib::
/// sysroot_authenticated_def_path_str` applies the identity rule to `Ty::Adt` /
/// `AggregateKind::Adt` NAMES as well as to callee paths, so an impersonator's
/// own struct renders STAMPED and this check refuses it. The bundle below carries
/// the unstamped spelling because it is verbatim PRE-fix compiler output.
///
/// What this authenticator still cannot do — and the reason it is one of four
/// conditions and not two — is say anything about how many elements the value
/// yields: see [`alloc_vcs::ty_is_unbounded_sysroot_iterator`] and
/// `bounded_source_value_tests`.
#[test]
fn the_value_side_authenticator_peels_refs_and_fails_closed_otherwise() {
    assert!(ty_is_authenticated_std_iterator(&adt(REAL_SLICE_ITER_TY)));
    assert!(ty_is_authenticated_std_iterator(&Ty::Ref {
        mutable: true,
        inner: Box::new(adt(REAL_SLICE_ITER_TY)),
    }));
    assert!(!ty_is_authenticated_std_iterator(&adt(USER_ADT_ITER_TY)));
    assert!(!ty_is_authenticated_std_iterator(&Ty::u32()));
    assert!(!ty_is_authenticated_std_iterator(&adt(
        "__trust_crate@1973d11b2baa21fa::alloc::vec::Endless"
    )));
    // The residual, asserted so it cannot be forgotten: an unstamped
    // impersonating TYPE name authenticates on the value side alone.
    assert!(ty_is_authenticated_std_iterator(&adt("alloc::vec::Endless")));
    assert!(
        !is_std_collection_iter_producer(
            "__trust_crate@1973d11b2baa21fa::alloc::vec::Vec::<u8>::iter",
            "iter"
        ),
        "...and the callee side is what refuses it"
    );
}

/// `Option::map` / `Option::filter` satisfied the old tail-only adaptor test —
/// measured spellings, from the real dump corpus. They are refused now, at no
/// cost: `Option` is not an `Iterator`, so no `Option::map` result can reach a
/// `collect` sink.
#[test]
fn option_combinators_are_not_iterator_adaptors() {
    for callee in [
        "core::option::Option::<i32>::map::<i32, {closure@main.rs:12:11: 12:14}>",
        "std::option::Option::<T>::map",
        "std::option::Option::<T>::filter",
        "std::option::Option::<&T>::cloned",
    ] {
        let tail = callee_tail(callee);
        assert!(
            matches!(tail, "map" | "filter" | "cloned"),
            "planted violation is gone: {callee} no longer has an adaptor tail"
        );
        assert!(
            !is_authenticated_std_len_nonincreasing_adaptor(callee, tail),
            "an `Option` combinator must not step the iterator chain: {callee}"
        );
    }
}

/// The user-inherent shape the exploit uses is a real extractor rendering, and the
/// exploit's own strings are the ones the dumps carry.
#[test]
fn the_assembled_bundle_uses_measured_spellings() {
    assert_eq!(callee_tail(USER_INHERENT_CALL_SHAPE), "iter");
    assert_eq!(callee_tail(USER_ADT_COLLECT_SINK), "collect");
    assert!(is_collect_sink(USER_ADT_COLLECT_SINK));
    assert!(is_std_collection_iter_producer(REAL_SLICE_ITER, callee_tail(REAL_SLICE_ITER)));
    // The sink's `Self` is a user ADT; the corpus spelling and the local type the
    // assembled bundle carries name the same type.
    assert!(USER_ADT_COLLECT_SINK.contains(USER_ADT_ITER_TY));
}

// ======================================================================
// 2026-08-17 — the receiver of a QUALIFIED producer spelling
// ======================================================================
//
// The first form of this fix anchored the RAW callee string:
//
//     if !path_root_is_authenticated_sysroot_crate(callee) { return false; }
//
// `path_root_is_authenticated_sysroot_crate` is a ROOT test and its own doc says
// so — *a caller holding a qualified spelling must split it*. A qualified
// spelling starts with `<`, so that form refused EVERY `<Self as Trait>::method`
// callee out of hand. `.into_iter()` is always that spelling, which made
// `v.into_iter().collect()` — the most ordinary bounded collect in the language —
// lose its grant and report an `UnsupportedMir{count-not-derivable}` Unknown.
// MEASURED on `main`: `is_std_collection_iter_producer` is `true` for eleven such
// spellings that the raw anchor refused, including
// `<alloc::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter`
// and the corpus-verbatim `<core::iter::adapters::zip::Zip<…> as
// core::iter::traits::collect::IntoIterator>::into_iter` from
// `trust-clean/fixtures/census-2026-07-06/byteorder/`.
//
// The repair is to NORMALIZE before anchoring — `producer_receiver_path` splits
// the qualifier with the crate's existing qualified-spelling parser and reads the
// SELF type's root — while the whole-string stamp scan keeps running on the
// untouched callee. That is exactly what the callee-side authenticator
// (`vc_callee_is_std_iter_trait_method`) has always done for the TRAIT half; the
// producer side is now consistent with it.
//
// Reading the RECEIVER rather than the whole string also closes a false proof
// that `main` has and that the raw anchor closed only by accident — see
// `a_std_rooted_adaptor_receiver_with_a_slice_iter_type_argument_is_not_a_collection`.

/// `v.into_iter().collect()`, the shape that motivated this section. `producer`
/// is the only thing that varies.
fn into_iter_collect_bundle(producer: &str, iter_ty: &str) -> VerifiableFunction {
    let sink = format!(
        "<{iter_ty} as core::iter::traits::iterator::Iterator>\
         ::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@1>"
    );
    VerifiableFunction {
        name: "consume".to_string(),
        def_path: "user::consume".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: adt("alloc::vec::Vec<u8>"), name: None },
                LocalDecl { index: 1, ty: adt("alloc::vec::Vec<u8>"), name: Some("v".into()) },
                LocalDecl { index: 2, ty: adt(iter_ty), name: Some("it".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(
                        producer,
                        vec![Operand::Move(Place::local(1))],
                        2,
                        Some(BlockId(1)),
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: call(&sink, vec![Operand::Move(Place::local(2))], 0, None),
                },
            ],
            arg_count: 1,
            return_ty: adt("alloc::vec::Vec<u8>"),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The genuine `.into_iter()` spelling for a `Vec`, byte-for-byte as rustc's
/// def-path renderer produces it.
const VEC_INTO_ITER_QUALIFIED: &str =
    "<alloc::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter";
const VEC_INTO_ITER_TY: &str = "alloc::vec::into_iter::IntoIter<u8>";

/// FALSIFY-ONCE for the receiver split, at the production entry point, with BOTH
/// states observed.
///
/// The PLANTED VIOLATION is the round-1 form of the anchor: anchoring the raw
/// qualified callee. It is asserted to be `false` here — that is the defect —
/// while the production predicate is `true` and the bundle reports zero rows. If
/// the split were ever removed, the first assertion would still hold and the last
/// two would fail loudly.
#[test]
fn a_qualified_into_iter_on_a_std_collection_keeps_the_bounded_source_grant() {
    // The defect, stated as an assertion: the raw string does not anchor.
    assert!(
        !trust_types::path_root_is_authenticated_sysroot_crate(VEC_INTO_ITER_QUALIFIED),
        "planted violation is gone: the raw qualified callee now anchors on its own, so \
         this test no longer demonstrates why the split is needed"
    );
    // The split reads the receiver, and the receiver is `alloc`-rooted.
    assert_eq!(producer_receiver_path(VEC_INTO_ITER_QUALIFIED), "alloc::vec::Vec");
    assert!(is_std_collection_iter_producer(VEC_INTO_ITER_QUALIFIED, "into_iter"));

    let bundle = into_iter_collect_bundle(VEC_INTO_ITER_QUALIFIED, VEC_INTO_ITER_TY);
    assert_eq!(
        unbounded_alloc_rows(&bundle),
        0,
        "`v.into_iter().collect()` collects at most `v.len()` elements — the bounded-source \
         grant must survive the qualified spelling"
    );

    // NON-VACUITY, the other observed state: the same bundle with a USER receiver
    // reports the obligation, so the zero above is a decision and not silence.
    let user = into_iter_collect_bundle(
        "<mycrate::vec::Endless as core::iter::traits::collect::IntoIterator>::into_iter",
        USER_ADT_ITER_TY,
    );
    assert_eq!(
        unbounded_alloc_rows(&user),
        1,
        "a user type's `into_iter` must not buy the bounded-source grant"
    );
}

/// Every qualified producer spelling that `main` granted and the round-1 anchor
/// refused, restored — and the forgeries in the same syntactic class, still
/// refused. One table, so a future edit cannot loosen one row without the other
/// rows noticing.
#[test]
fn the_qualified_producer_spellings_main_granted_are_granted_and_the_forgeries_are_not() {
    // (callee, expected). The `true` rows are MEASURED `main` behaviour restored;
    // the `false` rows are the classes this campaign is about.
    let cases: &[(&str, bool)] = &[
        (VEC_INTO_ITER_QUALIFIED, true),
        ("<&alloc::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter", true),
        (
            "<&mut alloc::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter",
            true,
        ),
        ("<&'a alloc::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter", true),
        (
            "<std::collections::hash::map::HashMap<K, V> as \
             core::iter::traits::collect::IntoIterator>::into_iter",
            true,
        ),
        (
            "<alloc::collections::btree::map::BTreeMap<K, V> as \
             core::iter::traits::collect::IntoIterator>::into_iter",
            true,
        ),
        (
            "<alloc::collections::vec_deque::VecDeque<u8> as \
             core::iter::traits::collect::IntoIterator>::into_iter",
            true,
        ),
        // the argument fingerprint is not a crate stamp — it rides on genuine callees
        (
            "<alloc::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>\
             ::into_iter::<__trust_args@cb41af7cc8f0962be19cf147890eca17>",
            true,
        ),
        // …and the forgeries, in the same syntactic class:
        ("<mycrate::vec::Endless as core::iter::traits::collect::IntoIterator>::into_iter", false),
        // a stamped receiver: the split does not stop the whole-string stamp scan
        (
            "<__trust_crate@0000000000000022::alloc::vec::Vec<u8> as \
             core::iter::traits::collect::IntoIterator>::into_iter",
            false,
        ),
        // A stamp the RECEIVER ANCHOR ALONE cannot see, which is why the
        // whole-string scan is a separate conjunct and not redundant: the
        // normalization that makes the receiver anchorable — generic stripping —
        // also deletes a stamp that lives inside a generic ARGUMENT, and the
        // qualifier split hides one that lives in the TRAIT half. Both of these
        // authenticate perfectly on the normalized receiver `alloc::vec::Vec`.
        (
            "<alloc::vec::Vec<__trust_crate@0000000000000022::alloc::Evil> as \
             core::iter::traits::collect::IntoIterator>::into_iter",
            false,
        ),
        (
            "<alloc::vec::Vec<u8> as \
             __trust_crate@0000000000000022::core::iter::traits::collect::IntoIterator>::into_iter",
            false,
        ),
        // an authenticated RECEIVER under a USER trait still fails, because the
        // value-side identity is what such a call's result would have to satisfy —
        // but the receiver anchor alone must not be read as authenticating the
        // method, so this row pins that the trait half is not ignored elsewhere.
        ("<&[i32] as core::iter::traits::collect::IntoIterator>::into_iter", false),
        ("<&L as core::iter::traits::collect::IntoIterator>::into_iter", false),
    ];
    for (callee, expected) in cases {
        assert_eq!(
            is_std_collection_iter_producer(callee, callee_tail(callee)),
            *expected,
            "producer authentication disagreed for {callee}"
        );
    }
}

/// DELIBERATE NARROWING, stated as a test so it cannot be mistaken for an
/// accident: reading the RECEIVER instead of the whole callee closes a false
/// proof that `main` has.
///
/// ```ignore
/// let it = my_endless.chain(v.iter());   // core::iter::adapters::chain::Chain<Endless, Iter<'_, u8>>
/// let out: Vec<u8> = it.into_iter().collect();
/// ```
///
/// `main`'s disjuncts scan the WHOLE callee, so `core::slice::` appearing in a
/// TYPE ARGUMENT of `Chain` grants the bounded-source `continue` — for a chain
/// that never ends. The receiver's own path (`core::iter::adapters::chain::Chain`)
/// is not a collection, so the repaired predicate refuses it.
///
/// The same reading also refuses `<core::iter::adapters::zip::Zip<…> as
/// IntoIterator>::into_iter`, which IS a bounded iterator; that spelling occurs 9
/// times in the checked-in dump corpus and in every one of them the function has
/// no `collect`/`from_iter` sink at all (it is a `for`-loop desugaring), so the
/// narrowing costs zero rows across all 2 557 bundles. Recovering `zip` soundly
/// needs a `zip` arm in the walk (`min` of two lengths), which is a NEW grant and
/// not part of this fix.
#[test]
fn a_std_rooted_adaptor_receiver_with_a_slice_iter_type_argument_is_not_a_collection() {
    const CHAIN_OVER_ENDLESS: &str = "<core::iter::adapters::chain::Chain<mycrate::Endless, \
         core::slice::iter::Iter<'_, u8>> as core::iter::traits::collect::IntoIterator>::into_iter";
    assert!(
        CHAIN_OVER_ENDLESS.contains("core::slice::"),
        "planted violation is gone: the whole-callee substring that granted this on main \
         is no longer present, so this test proves nothing"
    );
    assert_eq!(
        producer_receiver_path(CHAIN_OVER_ENDLESS),
        "core::iter::adapters::chain::Chain",
        "the receiver is the Chain itself, not its type arguments"
    );
    assert!(!is_std_collection_iter_producer(CHAIN_OVER_ENDLESS, "into_iter"));

    let bundle = into_iter_collect_bundle(
        CHAIN_OVER_ENDLESS,
        "core::iter::adapters::chain::Chain<mycrate::Endless, core::slice::iter::Iter<'_, u8>>",
    );
    assert_eq!(
        unbounded_alloc_rows(&bundle),
        1,
        "a Chain whose first half never returns None is unbounded, however std-rooted its \
         own type is"
    );
}

/// The reference peel is the pointee's identity, in both directions.
#[test]
fn a_reference_receiver_is_read_through_to_its_pointee() {
    assert_eq!(vc_peel_reference_prefixes("&'a mut alloc::vec::Vec<u8>"), "alloc::vec::Vec<u8>");
    assert_eq!(vc_peel_reference_prefixes("&&alloc::vec::Vec<u8>"), "alloc::vec::Vec<u8>");
    assert_eq!(
        vc_peel_reference_prefixes("*const core::slice::iter::Iter<'_, u8>"),
        "core::slice::iter::Iter<'_, u8>"
    );
    // and it peels to a USER type just as faithfully
    assert!(!is_std_collection_iter_producer(
        "<&mut mycrate::vec::Endless as core::iter::traits::collect::IntoIterator>::into_iter",
        "into_iter"
    ));
}

/// The str-view producer takes the same split, and keeps the same refusals.
#[test]
fn the_str_view_producer_reads_its_receiver_too() {
    // the genuine inherent spelling, measured in the corpus
    assert!(is_str_view_iter_producer("core::str::<impl str>::chars", "chars"));
    assert!(is_str_view_iter_producer("core::str::<impl str>::bytes", "bytes"));
    // a qualified spelling on a std String receiver
    assert!(is_str_view_iter_producer(
        "<alloc::string::String as core::ops::deref::Deref>::chars",
        "chars"
    ));
    // …and the crate-free forgery this campaign closed, in both spellings
    assert!(
        "mycrate::str::Endless::chars".contains("::str::"),
        "planted violation is gone: the crate-free disjunct no longer matches"
    );
    assert!(!is_str_view_iter_producer("mycrate::str::Endless::chars", "chars"));
    assert!(!is_str_view_iter_producer(
        "<mycrate::str::Endless as core::iter::traits::collect::IntoIterator>::chars",
        "chars"
    ));
}

// ======================================================================
// 2026-08-17 — `RangeInclusive`, counted rather than declined
// ======================================================================
//
// The `Range` aggregate arm used to be `name.contains("Range")`, which swallowed
// `RangeInclusive` into the EXCLUSIVE arithmetic `end - start` and under-counted
// it by one. Round 1 fixed that by restricting the arm to the exclusive family —
// correct about the defect, but it turned the whole `RangeInclusive` class into a
// visible Unknown when the sound count is right there: `end - start + 1`.

/// `(start..=end).collect()` / `(start..end).collect()` as the extractor renders
/// it when the aggregate is visible. The `RangeInclusive` field list is measured:
/// stock rustc renders `(0..=5)` as `RangeInclusive::<i32> { start, end, exhausted }`.
fn range_collect_bundle(adt_name: &str, ops: Vec<Operand>) -> VerifiableFunction {
    VerifiableFunction {
        name: "count".to_string(),
        def_path: "user::count".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: adt("alloc::vec::Vec<u8>"), name: None },
                LocalDecl { index: 1, ty: adt(adt_name), name: Some("r".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: adt_name.to_string(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        ops,
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: call(
                    &format!(
                        "<{adt_name} as core::iter::traits::iterator::Iterator>\
                         ::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@1>"
                    ),
                    vec![Operand::Move(Place::local(1))],
                    0,
                    None,
                ),
            }],
            arg_count: 0,
            return_ty: adt("alloc::vec::Vec<u8>"),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn int(n: i128) -> Operand {
    Operand::Constant(ConstValue::Int(n))
}

const RANGE_INCLUSIVE_ADT: &str = "core::ops::range::RangeInclusive<i32>";

/// FALSIFY-ONCE for the inclusive arithmetic, with BOTH observed states: the
/// exclusive formula on the SAME aggregate is one short, and one short is exactly
/// a false proof at the ceiling.
///
/// `(0..=CEILING-1)` yields `CEILING` elements — the allocation the ceiling
/// exists to catch. `main` computed `end - start == CEILING - 1`, which is
/// strictly below the ceiling, so the constant-count skip DELETED the obligation.
#[test]
fn an_inclusive_range_is_counted_end_minus_start_plus_one() {
    let ceiling = UNBOUNDED_ALLOC_ELEM_CEILING;

    // (a) The planted violation, asserted directly on the arithmetic: the
    //     exclusive formula on this aggregate is one short of the truth.
    let inclusive_count = |lo: i128, hi: i128| -> Option<Formula> {
        let f = range_collect_bundle(RANGE_INCLUSIVE_ADT, vec![int(lo), int(hi), int(0)]);
        iter_collect_count(&f, &Operand::Move(Place::local(1)))
    };
    assert_eq!(
        inclusive_count(0, 5),
        Some(Formula::Int(6)),
        "`(0..=5)` yields six elements; `end - start` would say five"
    );

    // (b) The two observed states at the ceiling boundary, through the production
    //     entry point. Exclusive arithmetic on this same aggregate yields
    //     `ceiling - 1`, a constant strictly below the ceiling, which the skip
    //     waves through — zero rows, a false proof. The real count is the ceiling.
    let exclusive_reading = ceiling - 1;
    assert!(
        exclusive_reading < ceiling,
        "planted violation is gone: the under-count no longer clears the ceiling skip, so \
         this boundary case proves nothing"
    );
    assert_eq!(inclusive_count(0, ceiling - 1), Some(Formula::Int(ceiling)));
    let at_ceiling =
        range_collect_bundle(RANGE_INCLUSIVE_ADT, vec![int(0), int(ceiling - 1), int(0)]);
    assert_eq!(
        unbounded_alloc_rows(&at_ceiling),
        1,
        "`(0..=(1<<28)-1).collect()` allocates exactly the ceiling and must report"
    );

    // (c) NON-VACUITY: one element below, the same shape is legitimately silent —
    //     so the row above is the count deciding, not the arm refusing.
    let below = range_collect_bundle(RANGE_INCLUSIVE_ADT, vec![int(0), int(ceiling - 2), int(0)]);
    assert_eq!(unbounded_alloc_rows(&below), 0);

    // (d) The recovery the round-1 form lost: a small inclusive range is proved,
    //     not reported as `count-not-derivable`.
    let small = range_collect_bundle(RANGE_INCLUSIVE_ADT, vec![int(0), int(5), int(0)]);
    assert_eq!(
        unbounded_alloc_rows(&small),
        0,
        "`(0..=5).collect()` is six constant elements — declining the whole inclusive \
         family turns this into a visible Unknown for no soundness gain"
    );

    // (e) The exclusive family is unchanged: `(0..CEILING)` still reports.
    assert_eq!(
        unbounded_alloc_rows(&range_collect_bundle(
            "core::ops::range::Range<i32>",
            vec![int(0), int(ceiling)]
        )),
        1
    );
    assert_eq!(
        unbounded_alloc_rows(&range_collect_bundle(
            "core::ops::range::Range<i32>",
            vec![int(0), int(ceiling - 1)]
        )),
        0
    );
}

/// The `+ 1` on the SYMBOLIC path, where no constant fold happens. A symbolic
/// count never reaches the constant ceiling skip, so this correction is not
/// row-visible — the formula the solver is handed IS the observable, and it is
/// what an `assume n == (1<<28) - 1` caller would be checked against.
///
/// BOTH states: the exclusive family on the same shape produces the bare
/// subtraction (asserted first — that is what the arm would emit without the
/// correction), the inclusive family adds one to it.
#[test]
fn a_symbolic_inclusive_range_adds_one_to_the_span() {
    // `(0..=n).collect()` with `n` an argument, so `end` is a symbol.
    //
    // The PARAMETER is `_1` and the range is the BODY TEMP `_2`. MIR numbers the
    // parameters `1..=arg_count`, so the earlier spelling — `range_collect_bundle`
    // (range at `_1`) with `arg_count = 1` bolted on — made the RANGE the argument
    // and `n` a non-parameter local: the opposite of what the test says, and a shape
    // `alloc_vcs::local_def` now declines outright (a parameter's aggregate `Assign`
    // is its SECOND value, and the count it derives becomes the obligation's count).
    let symbolic = |adt_name: &str, ops: Vec<Operand>| VerifiableFunction {
        name: "count".to_string(),
        def_path: "user::count".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: adt("alloc::vec::Vec<u8>"), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: adt(adt_name), name: Some("r".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt {
                            name: adt_name.to_string(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
                        ops,
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: call(
                    &format!(
                        "<{adt_name} as core::iter::traits::iterator::Iterator>\
                         ::collect::<alloc::vec::Vec<u8>>::<__trust_elem_bytes@1>"
                    ),
                    vec![Operand::Move(Place::local(2))],
                    0,
                    None,
                ),
            }],
            arg_count: 1,
            return_ty: adt("alloc::vec::Vec<u8>"),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let end = Operand::Copy(Place::local(1));

    let exclusive = symbolic("core::ops::range::Range<i32>", vec![int(0), end.clone()]);
    let excl_count = iter_collect_count(&exclusive, &Operand::Move(Place::local(2)));
    assert!(
        matches!(excl_count, Some(Formula::Sub(..))),
        "planted violation is gone: the exclusive arm no longer emits the bare span, so the \
         inclusive correction below is not distinguishable from it"
    );

    let inclusive = symbolic(RANGE_INCLUSIVE_ADT, vec![int(0), end, int(0)]);
    let incl_count = iter_collect_count(&inclusive, &Operand::Move(Place::local(2)));
    match incl_count {
        Some(Formula::Add(span, one)) => {
            assert!(matches!(*span, Formula::Sub(..)), "the inclusive count is span + 1");
            assert_eq!(*one, Formula::Int(1));
        }
        other => panic!("`(0..=n)` must count `n - 0 + 1`, got {other:?}"),
    }
}

/// The inclusive arm is anchored to the std range family, exactly like the
/// exclusive one — a user ADT named `RangeInclusive` buys no count.
#[test]
fn a_user_adt_named_range_inclusive_buys_no_count() {
    assert!(
        "mycrate::MyRangeInclusive<i32>".contains("Range"),
        "planted violation is gone: the old unanchored test no longer matches"
    );
    assert_eq!(range_family_adt_name("mycrate::MyRangeInclusive<i32>"), None);
    let planted =
        range_collect_bundle("mycrate::MyRangeInclusive<i32>", vec![int(0), int(3), int(0)]);
    assert_eq!(unbounded_alloc_rows(&planted), 1);
}

/// The inclusive arm requires the MEASURED three-field aggregate. A different
/// arity is a std layout change, and the fail-closed answer is a visible Unknown
/// rather than reading some other field as `end`.
#[test]
fn an_inclusive_range_aggregate_with_an_unexpected_arity_fails_closed() {
    let two_field = range_collect_bundle(RANGE_INCLUSIVE_ADT, vec![int(0), int(5)]);
    assert_eq!(
        iter_collect_count(&two_field, &Operand::Move(Place::local(1))),
        None,
        "a two-operand RangeInclusive aggregate is not the shape rustc renders"
    );
    assert_eq!(unbounded_alloc_rows(&two_field), 1);
    // …and the genuine three-operand shape is the control.
    let three_field = range_collect_bundle(RANGE_INCLUSIVE_ADT, vec![int(0), int(5), int(0)]);
    assert_eq!(unbounded_alloc_rows(&three_field), 0);
}

/// The constant fold is CHECKED in both families. The previous `e - s` was a raw
/// i128 subtraction: a `Range` straddling the i128 extremes wrapped to a small
/// positive count that the ceiling skip then waved through.
#[test]
fn a_range_whose_span_overflows_i128_yields_no_count_instead_of_a_wrapped_one() {
    assert_eq!(i128::MAX.wrapping_sub(i128::MIN), -1, "planted violation: the raw span wraps");
    let wrapped =
        range_collect_bundle("core::ops::range::Range<i32>", vec![int(i128::MIN), int(i128::MAX)]);
    assert_eq!(iter_collect_count(&wrapped, &Operand::Move(Place::local(1))), None);
    assert_eq!(unbounded_alloc_rows(&wrapped), 1);
    // the inclusive `+ 1` is checked for the same reason
    let saturating =
        range_collect_bundle(RANGE_INCLUSIVE_ADT, vec![int(0), int(i128::MAX), int(0)]);
    assert_eq!(iter_collect_count(&saturating, &Operand::Move(Place::local(1))), None);
    assert_eq!(unbounded_alloc_rows(&saturating), 1);
}

/// `RangeFrom` (`a..`) has no `end` and is unbounded; it must reach a `take(n)`
/// before any count exists. The family-anchored match refuses it up front rather
/// than matching on `contains("Range")` and falling out of the operand indexing.
#[test]
fn a_range_from_aggregate_supplies_no_count() {
    let from = range_collect_bundle("core::ops::range::RangeFrom<i32>", vec![int(0)]);
    assert!(
        "core::ops::range::RangeFrom<i32>".contains("Range"),
        "planted violation is gone: the old unanchored test no longer matches"
    );
    assert_eq!(iter_collect_count(&from, &Operand::Move(Place::local(1))), None);
    assert_eq!(unbounded_alloc_rows(&from), 1);
}

// ======================================================================
// REAL production bundles for the round-2 repair
// ======================================================================

fn round2_fixture(name: &str) -> VerifiableFunction {
    let json = match name {
        "vec_into_iter" => {
            include_str!("../../fixtures/qualified-into-iter-collect-2026-08-17/vec_into_iter.json")
        }
        "inclusive_small" => include_str!(
            "../../fixtures/qualified-into-iter-collect-2026-08-17/inclusive_small.json"
        ),
        "inclusive_at_ceiling" => include_str!(
            "../../fixtures/qualified-into-iter-collect-2026-08-17/inclusive_at_ceiling.json"
        ),
        "exclusive_at_ceiling" => include_str!(
            "../../fixtures/qualified-into-iter-collect-2026-08-17/exclusive_at_ceiling.json"
        ),
        other => panic!("unknown round-2 fixture: {other}"),
    };
    fixture(json)
}

fn callees(func: &VerifiableFunction) -> Vec<&str> {
    func.body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::Call { func, .. } => Some(func.as_str()),
            _ => None,
        })
        .collect()
}

/// THE over-decline, on the compiler's own bytes. `v.into_iter().collect()`
/// dumped from the shipped `trustc` at this patch's base commit.
///
/// BOTH states are pinned here without editing the fixture: the raw-anchor form
/// of the producer test (asserted first) refuses this callee, which is the
/// defect; the receiver-split form accepts it and the bundle reports zero rows.
#[test]
fn the_real_production_vec_into_iter_collect_keeps_its_grant() {
    let func = round2_fixture("vec_into_iter");
    let producer = callees(&func)
        .into_iter()
        .find(|c| callee_tail(c) == "into_iter")
        .expect("the dump carries an `into_iter` producer");
    assert_eq!(
        producer, "<alloc::vec::Vec<u8> as core::iter::traits::collect::IntoIterator>::into_iter",
        "the extractor's spelling for `.into_iter()` changed; this fixture no longer \
         demonstrates the qualified-spelling class"
    );
    assert!(
        !trust_types::path_root_is_authenticated_sysroot_crate(producer),
        "planted violation is gone: the raw qualified callee now anchors on its own"
    );
    assert!(is_std_collection_iter_producer(producer, "into_iter"));
    assert_eq!(
        unbounded_alloc_rows(&func),
        0,
        "the compiler's own `v.into_iter().collect()` bundle must keep the bounded-source grant"
    );
}

/// The reachability fact behind the `RangeInclusive` arithmetic, recorded on real
/// bytes so nobody re-derives it from the source syntax: `a..=b` reaches this
/// lane as a `RangeInclusive::new` CALL, while `a..b` reaches it as an AGGREGATE.
/// The aggregate arm's `end - start + 1` is therefore the correct arithmetic for
/// a shape this stage does not currently produce from `..=` — it is what rustc
/// renders once `new` is inlined — and the inclusive family's row count is
/// unchanged by this patch.
#[test]
fn the_real_inclusive_range_reaches_this_lane_as_a_constructor_call_not_an_aggregate() {
    for name in ["inclusive_small", "inclusive_at_ceiling"] {
        let func = round2_fixture(name);
        assert!(
            callees(&func).iter().any(|c| *c == "core::ops::range::RangeInclusive::<i32>::new"),
            "{name}: `..=` no longer renders as a RangeInclusive::new call"
        );
        assert!(
            !func.body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, .. }, _),
                    ..
                } if range_family_adt_name(name) == Some("RangeInclusive")
            )),
            "{name}: a RangeInclusive aggregate appeared; the reachability note is stale"
        );
        assert_eq!(
            unbounded_alloc_rows(&func),
            1,
            "{name}: no count is derivable from a `RangeInclusive::new` call, in any tree"
        );
    }
    // The exclusive sibling IS an aggregate, and is the arm's live shape.
    let excl = round2_fixture("exclusive_at_ceiling");
    assert!(
        excl.body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(
            s,
            Statement::Assign {
                rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, .. }, ops),
                ..
            } if range_family_adt_name(name) == Some("Range") && ops.len() == 2
        )),
        "`a..b` no longer renders as a two-operand Range aggregate"
    );
    assert_eq!(unbounded_alloc_rows(&excl), 1);
}
