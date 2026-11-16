//! Trust (2026-10-08): the two panics the deleted 256 MiB byte budget had been
//! guarding, pinned at the allocation lane's verdicts (solved in process by `ay`).
//!
//! * **ALLOC-RECEIVER-1.** `reserve` / `reserve_exact` / `extend_reserve`, a
//!   counted `Extend::extend` and a counted `collect_into` ADD their count to what
//!   a live receiver already holds; RawVec asks for `(len + additional) * stride`.
//!   With the budget gone, these rows charged `stride * additional` alone, and the
//!   review of ALLOC-BYTE-1 measured `v.reserve(n)` on a
//!   `Vec<MaybeUninit<[u8; 1 << 35]>>` holding ONE element, under `n < 2^28`,
//!   PROVED on stage 1 and panicking "capacity overflow" at run time
//!   (`reserve_exact` and `extend(repeat_with(..).take(n))` likewise). The fresh
//!   `with_capacity(n)` twin is genuinely safe and stays proved.
//! * **ALLOC-WIDTH-1.** The byte line was the 64-bit `isize::MAX` on every target.
//!   On a 32-bit target `Vec::<[u8; 65536]>::with_capacity(n)` over a `u16`-ranged
//!   `n` panics from `n = 32768`; only the budget refused it. The line is now the
//!   target's own, from the compiler's session fact
//!   (`VcgenContext::with_target_pointer_bits`), and judged at 32 bits when no
//!   width is supplied.
//!
//! Every verdict below is asserted on the SAME function at two or three target
//! widths, so a fixture that stopped reaching the lane could not pass.

use trust_types::{
    BasicBlock, BinOp, BlockId, CalleeKey, ConstValue, LocalDecl, Operand, Place, Rvalue,
    SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition, VerificationResult, render_trailing_elem_bytes_token,
    render_trailing_table_elem_bytes_token,
};

/// `MaybeUninit<[u8; 1 << 35]>`, the review's element: 32 GiB, never touched.
const BIG: u64 = 1 << 35;

/// Where the count goes.
enum Sink {
    /// A direct-size call: `callee(v, n)` when `receiver`, else `callee(n)`.
    Direct { callee: String, receiver: bool },
    /// `it = take(src, n); <Vec<T> as Extend<T>>::extend(v, it)`.
    Extend { callee: String },
    /// `it = take(src, n); it.collect_into(v)`.
    CollectInto { callee: String },
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: BlockId) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(callee),
        is_foreign: false,
    }
}

/// `fn f(v: &mut _, n: uW) { if n < bound { <sink> } }` — locals: 1 `v`, 2 `n`
/// (`count_bits`-wide unsigned, the `usize` of a `count_bits` target), 3 the guard,
/// 4 the call result, 5 the iterator, 6 the iterator's source.
///
/// An `extend` receiver and a `collect_into` destination are typed `&mut Vec<[u8;
/// BIG]>` (a `BIG`-byte element, as the callee's token says), because both arms first
/// ask the RECEIVER's type whether memory bounds its length
/// (`live_receiver_length_is_bounded`; local main `27264a61eb1` for `extend`,
/// ALLOC-RECEIVER-ZST-1 for `collect_into`: a full `Vec<()>` overflows on one more
/// element) and keep a visible Unknown for a receiver they cannot read. Merge
/// 2026-10-14: the `&mut u32` stand-in reached that Unknown instead of the counted row
/// pinned here — for `collect_into` since ALLOC-RECEIVER-ZST-1 (no `u32` is a
/// `collect_into` destination: it implements no `Extend`). A direct-size sink keeps
/// the stand-in: its fixture key (`fixture_key`) is not a sysroot item's, and a
/// non-sysroot `reserve` is not asked about its receiver (see [`sysroot_keyed`]).
fn guarded(sink: &Sink, count_bits: u32, bound: u128) -> VerifiableFunction {
    let receiver = match sink {
        Sink::Extend { .. } | Sink::CollectInto { .. } => {
            vec_of(Ty::Array { elem: Box::new(Ty::u8()), len: BIG })
        }
        Sink::Direct { .. } => Ty::u32(),
    };
    guarded_into(sink, count_bits, bound, receiver)
}

/// [`guarded`] with the receiver (local 1, behind `&mut`) typed `receiver`.
fn guarded_into(sink: &Sink, count_bits: u32, bound: u128, receiver: Ty) -> VerifiableFunction {
    let n = || Operand::Copy(Place::local(2));
    let take = "<core::iter::RepeatWith<F> as core::iter::traits::iterator::Iterator>::take";
    let mut blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Lt,
                    n(),
                    Operand::Constant(ConstValue::Uint(bound, count_bits)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::SwitchInt {
                exhaustive_enum_unreachable: false,
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(1))],
                otherwise: BlockId(2),
                span: SourceSpan::default(),
            },
        },
        BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
    ];
    match sink {
        Sink::Direct { callee, receiver } => {
            let args =
                if *receiver { vec![Operand::Move(Place::local(1)), n()] } else { vec![n()] };
            blocks.push(BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call(callee, args, 4, BlockId(1)),
            });
        }
        Sink::Extend { callee } | Sink::CollectInto { callee } => {
            blocks.push(BasicBlock {
                id: BlockId(2),
                stmts: vec![],
                terminator: call(take, vec![Operand::Move(Place::local(6)), n()], 5, BlockId(3)),
            });
            let args = if matches!(sink, Sink::Extend { .. }) {
                vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(5))]
            } else {
                vec![Operand::Move(Place::local(5)), Operand::Move(Place::local(1))]
            };
            blocks.push(BasicBlock {
                id: BlockId(3),
                stmts: vec![],
                terminator: call(callee, args, 4, BlockId(1)),
            });
        }
    }
    VerifiableFunction {
        name: "grow".to_string(),
        def_path: "test::grow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(receiver) },
                    name: Some("v".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: count_bits, signed: false },
                    name: Some("n".into()),
                },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("c".into()) },
                LocalDecl { index: 4, ty: Ty::Unit, name: None },
                LocalDecl { index: 5, ty: Ty::u32(), name: Some("it".into()) },
                LocalDecl { index: 6, ty: Ty::u32(), name: Some("src".into()) },
            ],
            blocks,
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn vec_method(method: &str, elem: &str, stride: u64) -> String {
    format!("alloc::vec::Vec::<{elem}>::{method}{}", render_trailing_elem_bytes_token(stride))
}

fn big_elem() -> String {
    format!("core::mem::MaybeUninit<[u8; {BIG}]>")
}

fn reserve(method: &str, elem: &str, stride: u64) -> Sink {
    Sink::Direct { callee: vec_method(method, elem, stride), receiver: true }
}

fn with_capacity(elem: &str, stride: u64) -> Sink {
    Sink::Direct { callee: vec_method("with_capacity", elem, stride), receiver: false }
}

/// The allocation rows of `func` with the target's pointer width `bits` installed
/// as the compiler installs it (`None`: a caller that supplies no target).
fn rows(func: &VerifiableFunction, bits: Option<u32>) -> Vec<VerificationCondition> {
    let generate = || {
        super::generate_unbounded_allocation_vcs(func)
            .into_iter()
            .filter(|vc| {
                matches!(
                    vc.kind,
                    VcKind::UnboundedAllocation { .. } | VcKind::UnsupportedMir { .. }
                )
            })
            .collect::<Vec<_>>()
    };
    match bits {
        Some(_) => crate::with_target_pointer_bits(bits, generate),
        None => generate(),
    }
}

fn solve(vc: &VerificationCondition) -> VerificationResult {
    let vc = vc.clone();
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let router = crate::test_router::deterministic_test_router();
            router.verify_all(std::slice::from_ref(&vc)).into_iter().next().expect("one verdict").1
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread")
}

/// The single counted allocation row's verdict at pointer width `bits`.
fn verdict(func: &VerifiableFunction, bits: Option<u32>) -> VerificationResult {
    let rows = rows(func, bits);
    let [row] = rows.as_slice() else {
        panic!("expected exactly one allocation row at {bits:?}, got {rows:#?}");
    };
    assert!(
        matches!(row.kind, VcKind::UnboundedAllocation { .. }),
        "expected a counted row at {bits:?}, got {row:#?}"
    );
    solve(row)
}

fn proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

fn failed(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Failed { .. })
}

/// `Vec<elem>` as the extractor renders it.
fn vec_of(elem: Ty) -> Ty {
    Ty::Seq { elem: Box::new(elem), drop_auth: None }
}

/// `VecDeque<T>` as the extractor renders it: its `RawVec` erases `T`, so no field
/// names the element (the `-Ztrust-dump=mir` of `reserve_deque_u64` on stage 1).
fn vec_deque() -> Ty {
    Ty::adt("alloc::collections::vec_deque::VecDeque", vec![("len".into(), Ty::usize())])
}

/// `String` as the extractor renders it.
fn string() -> Ty {
    Ty::adt("alloc::string::String", vec![("vec".into(), vec_of(Ty::u8()))])
}

/// `func`'s sink call (its last block) keyed as the compiler keys a SYSROOT item —
/// what every std sink carries in real MIR. `fixture_key` keys a spelling it does
/// not list as a crate of its own, which is what a local or dependency body gets.
fn sysroot_keyed(mut func: VerifiableFunction) -> VerifiableFunction {
    let last = func.body.blocks.len() - 1;
    let Terminator::Call { callee_key, .. } = &mut func.body.blocks[last].terminator else {
        panic!("the last block of a `guarded` fixture is its sink call")
    };
    *callee_key = Some(CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: true,
        krate_name_is_ambiguous: false,
        stable_crate_id: 0x5ee,
        krate_name: "alloc".into(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    });
    func
}

/// The lane's only row for `func` at width `bits` is the visible receiver Unknown of
/// the sink displayed `display` (ALLOC-RECEIVER-ZST-1) — no counted row a guard could
/// discharge, and no silent skip.
fn assert_receiver_unknown(func: &VerifiableFunction, bits: Option<u32>, display: &str) {
    let rows = rows(func, bits);
    let [row] = rows.as_slice() else {
        panic!("expected exactly the receiver Unknown at {bits:?}, got {rows:#?}")
    };
    let VcKind::UnsupportedMir { kind, .. } = &row.kind else {
        panic!("expected the receiver Unknown at {bits:?}, got {row:#?}")
    };
    assert_eq!(
        kind,
        &format!("UnboundedAllocation::{display}::receiver-length-not-bounded"),
        "at {bits:?}"
    );
}

/// The sink's count operand replaced by the constant `value`.
fn with_constant_count(mut func: VerifiableFunction, value: u128) -> VerifiableFunction {
    let last = func.body.blocks.len() - 1;
    let Terminator::Call { args, .. } = &mut func.body.blocks[last].terminator else {
        panic!("the last block of a `guarded` fixture is its sink call")
    };
    args[1] = Operand::Constant(ConstValue::Uint(value, 64));
    func
}

// ---------------------------------------------------------------- ALLOC-RECEIVER-1

#[test]
fn reserve_on_a_live_receiver_of_a_huge_element_is_refused() {
    // The review's probe, `grow(v, n)` with `n < 2^28`: one live 2^35-byte element
    // plus `reserve(2^28 - 1)` is a 2^63-byte request.
    for method in ["reserve", "reserve_exact"] {
        let func = guarded(&reserve(method, &big_elem(), BIG), 64, 1 << 28);
        let r = verdict(&func, Some(64));
        assert!(failed(&r), "`{method}` adds to a live receiver and must be refused: {r:?}");
    }
    // `Extend::extend_reserve(v, n)` forwards to `reserve`.
    let extend_reserve = Sink::Direct {
        callee: format!(
            "<alloc::vec::Vec<{0}> as core::iter::traits::collect::Extend<{0}>>::extend_reserve{1}",
            big_elem(),
            render_trailing_elem_bytes_token(BIG)
        ),
        receiver: true,
    };
    let r = verdict(&guarded(&extend_reserve, 64, 1 << 28), Some(64));
    assert!(failed(&r), "`extend_reserve` adds to a live receiver: {r:?}");
}

#[test]
fn a_counted_extend_and_collect_into_charge_the_receiver() {
    let extend = Sink::Extend {
        callee: format!(
            "<alloc::vec::Vec<{0}> as core::iter::traits::collect::Extend<{0}>>::extend::\
             <core::iter::Take<core::iter::RepeatWith<F>>>{1}",
            big_elem(),
            render_trailing_elem_bytes_token(BIG)
        ),
    };
    let r = verdict(&guarded(&extend, 64, 1 << 28), Some(64));
    assert!(failed(&r), "a counted `extend` into a live Vec must charge its length: {r:?}");
    let collect_into = Sink::CollectInto {
        callee: format!(
            "<core::iter::Take<core::iter::RepeatWith<F>> as \
             core::iter::traits::iterator::Iterator>::collect_into::<alloc::vec::Vec<{}>>{}",
            big_elem(),
            render_trailing_elem_bytes_token(BIG)
        ),
    };
    let r = verdict(&guarded(&collect_into, 64, 1 << 28), Some(64));
    assert!(failed(&r), "a counted `collect_into` extends a live destination: {r:?}");
}

#[test]
fn the_fresh_twin_and_an_ordinary_reserve_stay_proved() {
    // CONTROL: `with_capacity(n)` is a FRESH request — `(2^28 - 1) * 2^35 <
    // isize::MAX` — and is genuinely safe; the receiver charge is only for
    // additional counts.
    let r = verdict(&guarded(&with_capacity(&big_elem(), BIG), 64, 1 << 28), Some(64));
    assert!(proved(&r), "the fresh `with_capacity` twin is safe and must stay proved: {r:?}");
    // An ordinary `reserve` on a 64-bit target: a live `Vec<u64>` holds under 2^53
    // elements (the live-address-space axiom), so `reserve(n < 2^20)` fits.
    let r = verdict(&guarded(&reserve("reserve", "u64", 8), 64, 1 << 20), Some(64));
    assert!(proved(&r), "an ordinary 64-bit `reserve` must not be refused: {r:?}");
}

#[test]
fn the_receiver_threshold_is_exactly_the_live_bound_netted_off() {
    // `scale * (count + held) >= limit` spelled `scale * count >= limit - scale *
    // held`, with `held` the live-address-space bound `2^56 / stride + 1`.
    let receiver = rows(&guarded(&reserve("reserve", &big_elem(), BIG), 64, 1 << 28), Some(64));
    let text = receiver[0].formula.to_smtlib();
    let held = (1i128 << 56) / i128::from(BIG) + 1;
    let threshold = super::ALLOC_CAPACITY_OVERFLOW_BYTES - i128::from(BIG) * held;
    assert!(
        text.contains(&format!("(>= (* {BIG} n) {threshold})")),
        "the receiver's capacity atom must be `{BIG} * n >= {threshold}`: {text}"
    );
    // The fresh twin keeps the bare object limit.
    let fresh = rows(&guarded(&with_capacity(&big_elem(), BIG), 64, 1 << 28), Some(64));
    let text = fresh[0].formula.to_smtlib();
    assert!(
        text.contains(&format!("(>= (* {BIG} n) {})", super::ALLOC_CAPACITY_OVERFLOW_BYTES)),
        "a fresh request keeps the object limit: {text}"
    );
}

#[test]
fn a_hash_table_reserve_charges_its_live_buckets() {
    // `HashMap::<u8, [u8; 2^35]>::reserve(n)`: the table element is 2^35 + 1 bytes.
    // Fresh, hashbrown's term fires from about 1.17e8 items; a live table may
    // already hold 2^21 buckets of it, which moves the line down.
    let stride = BIG + 1;
    let table = |method: &str| Sink::Direct {
        callee: format!(
            "std::collections::hash::map::HashMap::<u8, [u8; {BIG}]>::{method}{}",
            render_trailing_table_elem_bytes_token(Some(stride))
        ),
        receiver: method != "with_capacity",
    };
    let stride = i128::from(stride);
    let limit = super::ALLOC_CAPACITY_OVERFLOW_BYTES;
    let (scale, fresh) = super::hash_table_capacity_overflow_term(stride, limit);
    let fresh_first = (fresh + scale - 1) / scale; // smallest firing fresh count
    let bound = u128::try_from(fresh_first).unwrap(); // `n < bound`: fresh never fires
    let r = verdict(&guarded(&table("with_capacity"), 64, bound), Some(64));
    assert!(proved(&r), "a fresh table under its own line is safe: {r:?}");
    let r = verdict(&guarded(&table("reserve"), 64, bound), Some(64));
    assert!(failed(&r), "the same count reserved on a live table must charge its buckets: {r:?}");
}

// ------------------------------------------------------------------- ALLOC-WIDTH-1

#[test]
fn a_32_bit_target_is_judged_at_its_own_object_limit() {
    // The review's probe: `Vec::<[u8; 65536]>::with_capacity(n)` with `n` below
    // 2^16 — at most 2^32 bytes. Fine on a 64-bit target; on a 32-bit one it panics
    // "capacity overflow" from `n = 32768`.
    let sink = with_capacity("[u8; 65536]", 65536);
    let func64 = guarded(&sink, 64, 1 << 16);
    assert!(proved(&verdict(&func64, Some(64))), "within a 64-bit target's object limit");
    let func32 = guarded(&sink, 32, 1 << 16);
    let r = verdict(&func32, Some(32));
    assert!(failed(&r), "a 32-bit target's object limit is 2^31 - 1 bytes: {r:?}");
    // `Vec::<u128>::with_capacity(n)`, `n < 2^28`: 2^32 bytes at most.
    let sink = with_capacity("u128", 16);
    assert!(proved(&verdict(&guarded(&sink, 64, 1 << 28), Some(64))));
    let r = verdict(&guarded(&sink, 32, 1 << 28), Some(32));
    assert!(failed(&r), "16-byte elements reach 2^31 bytes from n = 2^27 on 32 bits: {r:?}");
    let text = rows(&guarded(&sink, 32, 1 << 28), Some(32))[0].formula.to_smtlib();
    assert!(text.contains("(>= (* 16 n) 2147483647)"), "the 32-bit line: {text}");
}

#[test]
fn no_supplied_width_is_judged_at_the_narrowest_modeled_width() {
    // A caller that installs no target (every non-compiler caller) gets the 32-bit
    // verdicts: a lower line only adds failures.
    let sink = with_capacity("[u8; 65536]", 65536);
    let r = verdict(&guarded(&sink, 64, 1 << 16), None);
    assert!(failed(&r), "with no target width, judge at 32 bits: {r:?}");
}

#[test]
fn a_live_receiver_is_never_shown_to_fit_below_64_bits() {
    // Without the 64-bit live-address-space axiom a receiver may already be full —
    // a 2 GiB `Vec<u16>` is a real 32-bit value — so `reserve` always fails closed,
    // even of a one-byte element (where no other stride gets a byte term).
    for (elem, stride) in [("u8", 1u64), ("u64", 8)] {
        let func = guarded(&reserve("reserve", elem, stride), 32, 100);
        let r = verdict(&func, Some(32));
        assert!(failed(&r), "`Vec<{elem}>::reserve` on a 32-bit target: {r:?}");
        let r = verdict(&func, None);
        assert!(failed(&r), "`Vec<{elem}>::reserve` with no target width: {r:?}");
        let r = verdict(&guarded(&reserve("reserve", elem, stride), 64, 100), Some(64));
        assert!(proved(&r), "`Vec<{elem}>::reserve(n < 100)` on a 64-bit target: {r:?}");
    }
    // The one-byte FRESH request is unchanged on every modeled width: the element
    // ceiling (2^28) is below both object limits, so no byte term is added and the
    // guarded row is proved.
    for bits in [32, 64] {
        let func = guarded(&with_capacity("u8", 1), bits, 100);
        let text = rows(&func, Some(bits))[0].formula.to_smtlib();
        assert!(!text.contains("(* "), "no byte term for a fresh one-byte request: {text}");
        let r = verdict(&func, Some(bits));
        assert!(proved(&r), "a guarded one-byte `with_capacity` on {bits} bits: {r:?}");
    }
}

#[test]
fn a_constant_count_is_judged_with_the_receiver_and_the_target() {
    // `v.reserve(10)` on a 32-bit target is a ground failure (the receiver may be
    // full); on a 64-bit target it is skipped outright.
    let func = |bits: u32| {
        let mut f = guarded(&reserve("reserve", "u64", 8), bits, 1 << 20);
        let Terminator::Call { args, .. } = &mut f.body.blocks[2].terminator else {
            unreachable!()
        };
        args[1] = Operand::Constant(ConstValue::Uint(10, bits));
        f
    };
    assert!(rows(&func(64), Some(64)).is_empty(), "`reserve(10)` on 64 bits is skipped");
    let r = verdict(&func(32), Some(32));
    assert!(failed(&r), "`reserve(10)` on 32 bits may overflow a full receiver: {r:?}");
}

#[test]
fn a_16_bit_target_is_a_visible_unknown() {
    // The element ceiling (2^28) is far above a 16-bit object limit: nothing this
    // lane emits there could be trusted, so every row is an Unknown.
    let rows = rows(&guarded(&with_capacity("u64", 8), 16, 100), Some(16));
    let [row] = rows.as_slice() else { panic!("one row, got {rows:#?}") };
    let VcKind::UnsupportedMir { kind, .. } = &row.kind else {
        panic!("a 16-bit target must be a visible Unknown, got {row:#?}")
    };
    assert!(kind.ends_with("::pointer-width-not-modeled"), "{kind}");
}

#[test]
fn the_compiler_entry_carries_the_width_through_its_own_frame() {
    // `generate_vcs_with_context` with the width on the compiler's context — the
    // production path — and the session read through the fresh owner frame that
    // `generate_vcs` pushes above an outer one.
    let func = guarded(&with_capacity("[u8; 65536]", 65536), 64, 1 << 16);
    let at = |bits: u32| {
        let context = crate::VcgenContext::for_function(func.def_path.clone())
            .with_target_pointer_bits(Some(bits));
        crate::generate_vcs_with_context(&func, &context)
            .into_iter()
            .filter(|vc| matches!(vc.kind, VcKind::UnboundedAllocation { .. }))
            .collect::<Vec<_>>()
    };
    let [row64] = at(64).try_into().expect("one row on 64 bits");
    let [row32] = at(32).try_into().expect("one row on 32 bits");
    assert!(proved(&solve(&row64)), "64-bit verdict through the compiler entry");
    assert!(failed(&solve(&row32)), "32-bit verdict through the compiler entry");
    // An owner MISMATCH keeps the session width (it is not a fact about a function).
    let foreign =
        crate::VcgenContext::for_function("test::someone_else").with_target_pointer_bits(Some(64));
    let rows = crate::generate_vcs_with_context(&func, &foreign)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::UnboundedAllocation { .. }))
        .collect::<Vec<_>>();
    assert!(proved(&solve(&rows[0])), "the width crosses an owner mismatch: {rows:#?}");
}

#[test]
fn a_single_value_is_judged_at_the_target_object_limit_inclusive() {
    // A value of exactly `isize::MAX` bytes has a valid `Layout` (`<=`, not `<`);
    // one byte more is past the largest object.
    let box_of = |len: u64| {
        let mut f = guarded(&with_capacity("u8", 1), 64, 1);
        f.body.locals[6].ty = Ty::Array { elem: Box::new(Ty::u8()), len };
        f.body.blocks[2].terminator = call(
            &format!("alloc::boxed::Box::<[u8; {len}]>::new"),
            vec![Operand::Move(Place::local(6))],
            4,
            BlockId(1),
        );
        f
    };
    let at_limit = box_of(u64::MAX >> 1);
    assert!(rows(&at_limit, Some(64)).is_empty(), "isize::MAX bytes is allocatable");
    let past = box_of(1 << 63);
    assert_eq!(rows(&past, Some(64)).len(), 1, "isize::MAX + 1 bytes is not");
    // A 1 TiB value: within a 64-bit target's line, past a 32-bit one's.
    let tib = box_of(1 << 40);
    assert!(rows(&tib, Some(64)).is_empty());
    assert_eq!(rows(&tib, Some(32)).len(), 1);
}

// ------------------------------------------------- the interval lane's atom contract

/// Does trust-router's interval backend (the abstract-interpretation lane the
/// deployed router consults) claim the row PROVED?
fn interval_proves(vc: &VerificationCondition) -> bool {
    use trust_router::VerificationBackend;
    trust_router::interval_backend::IntervalBackend.can_handle(vc)
}

#[test]
fn every_failing_row_stays_unproved_by_the_interval_lane() {
    // trust-router's interval lane reads the failure `Or` as a branch split and
    // dismisses a branch with no RECOGNIZED atom (`Ge`/`Gt` against a constant of at
    // least 2^28) as "allocates nothing". A capacity atom whose threshold is below
    // 2^28 — a live receiver on a narrower target (negative), a 32-bit table of a
    // huge element — would be dismissed, and the guarded count's ceiling atom alone
    // would PROVE a row that always fails. Every row below must fail in the solver
    // AND stay unproved by the interval lane.
    let huge_table = Sink::Direct {
        callee: format!(
            "std::collections::hash::map::HashMap::<u8, [u8; 1073741824]>::with_capacity{}",
            render_trailing_table_elem_bytes_token(Some((1 << 30) + 1))
        ),
        receiver: false,
    };
    // A 64-bit table of a `2^59`-byte element (rustc admits types below `2^61`):
    // hashbrown's line `7 * isize::MAX - 126 * stride - ...` is NEGATIVE there, so
    // this shape was exposed on main before ALLOC-WIDTH-1 too (`n < 100` asks for
    // 128 buckets, `2^66` bytes).
    let huge_table_64 = Sink::Direct {
        callee: format!(
            "std::collections::hash::map::HashMap::<u8, [u8; 576460752303423488]>::with_capacity{}",
            render_trailing_table_elem_bytes_token(Some((1 << 59) + 1))
        ),
        receiver: false,
    };
    let cases = [
        (guarded(&huge_table_64, 64, 100), Some(64)),
        (guarded(&reserve("reserve", "u64", 8), 32, 100), Some(32)),
        (guarded(&reserve("reserve", "u8", 1), 32, 100), Some(32)),
        (guarded(&reserve("reserve", "u64", 8), 64, 100), None),
        (guarded(&huge_table, 32, 2), Some(32)),
        (guarded(&reserve("reserve", &big_elem(), BIG), 64, 1 << 28), Some(64)),
    ];
    for (func, bits) in cases {
        let rows = rows(&func, bits);
        let [row] = rows.as_slice() else { panic!("one row at {bits:?}, got {rows:#?}") };
        let r = solve(row);
        assert!(failed(&r), "the solver must refuse the row at {bits:?}: {r:?}");
        assert!(
            !interval_proves(row),
            "the interval lane must not prove a row that always fails ({bits:?}): {}",
            row.formula.to_smtlib()
        );
    }
}

#[test]
fn the_capacity_atom_is_exact_and_its_constant_is_never_below_the_ceiling() {
    // `capacity_atom` re-spells a low threshold `scale * count + shift >= 2^28`.
    // It must hold at exactly the counts `scale * count >= threshold` holds at, and
    // its constant must be one the interval lane recognizes as a failure atom.
    use trust_types::{Formula, Sort};
    fn eval(f: &Formula, n: i128) -> i128 {
        match f {
            Formula::Int(v) => *v,
            Formula::Var(..) => n,
            Formula::Mul(a, b) => eval(a, n) * eval(b, n),
            Formula::Add(a, b) => eval(a, n) + eval(b, n),
            other => panic!("unexpected term {other:?}"),
        }
    }
    let ceiling = 1i128 << 28;
    let n = Formula::Var("n".into(), Sort::Int);
    for scale in [1i128, 8, 16 * ((1 << 30) + 2), 1 << 35] {
        for threshold in
            [-(1i128 << 62), -1, 0, 1, 4096, ceiling - 1, ceiling, i128::from(i64::MAX)]
        {
            let atom = super::capacity_atom(scale, threshold, &n);
            let Formula::Ge(lhs, rhs) = &atom else { panic!("a `Ge` atom: {atom:?}") };
            let Formula::Int(constant) = rhs.as_ref() else { panic!("a constant: {atom:?}") };
            assert!(*constant >= ceiling, "constant {constant} below the ceiling: {atom:?}");
            for count in [0i128, 1, 2, 100, 1 << 20, ceiling - 1, ceiling, 1 << 40] {
                assert_eq!(
                    eval(lhs, count) >= *constant,
                    scale * count >= threshold,
                    "scale {scale} threshold {threshold} count {count}: {atom:?}"
                );
            }
        }
    }
}

// ------------------------------------------------------------ ALLOC-RECEIVER-ZST-1
//
// Trust (2026-10-14): every sink that ADDS to a live receiver asks one question first —
// does memory bound the length that receiver already holds
// (`alloc_vcs::live_receiver_length_is_bounded`)? Only `extend` asked it (27264a61eb1).
// A `Vec<()>` / `VecDeque<()>` may already hold `usize::MAX` units, and one more element
// panics "capacity overflow"; at stride zero the counted row carried no byte term, so
// it was the element ceiling alone. MEASURED on the stage 1 of `5184affbb97`: `if n <
// 100 { (0..n).map(|_| ()).collect_into(v) }` and `if n < 100 { v.reserve(n) }` on
// `&mut Vec<()>` were KERNEL-CERTIFIED rows, and `v.reserve(5)` had no row at all (the
// realmir twins: `tests/zst_receiver_growth_realmir.rs`).

/// `<Take<RepeatWith<F>> as Iterator>::collect_into::<dest>` with an optional token.
fn collect_into_sink(dest: &str, token: Option<u64>) -> Sink {
    Sink::CollectInto {
        callee: format!(
            "<core::iter::Take<core::iter::RepeatWith<F>> as \
             core::iter::traits::iterator::Iterator>::collect_into::<{dest}>{}",
            token.map(render_trailing_elem_bytes_token).unwrap_or_default()
        ),
    }
}

/// `<coll<elem> as Extend<elem>>::extend::<Take<RepeatWith<F>>>` with the element token.
fn extend_sink(coll: &str, elem: &str, token: u64) -> Sink {
    Sink::Extend {
        callee: format!(
            "<{coll}<{elem}> as core::iter::traits::collect::Extend<{elem}>>::extend::\
             <core::iter::Take<core::iter::RepeatWith<F>>>{}",
            render_trailing_elem_bytes_token(token)
        ),
    }
}

const DEQUE: &str = "alloc::collections::vec_deque::VecDeque";

#[test]
fn collect_into_a_zero_sized_destination_keeps_a_visible_unknown() {
    // The measured shape: a guarded count into `&mut Vec<()>`, at every width, with the
    // extractor's `@0` token and without any token (the element type alone decides).
    for token in [Some(0), None] {
        let func = sysroot_keyed(guarded_into(
            &collect_into_sink("alloc::vec::Vec<()>", token),
            64,
            100,
            vec_of(Ty::Unit),
        ));
        for bits in [Some(64), Some(32), None] {
            assert_receiver_unknown(&func, bits, "Iterator::collect_into");
        }
    }
    // A `@0` token is the extractor's layout of the destination's element: it vetoes
    // a sequence the operand renders as sized.
    let func = guarded_into(
        &collect_into_sink("alloc::vec::Vec<()>", Some(0)),
        64,
        100,
        vec_of(Ty::u64()),
    );
    assert_receiver_unknown(&func, Some(64), "Iterator::collect_into");
    // `VecDeque<()>`: its type erases the element, and the token says zero bytes.
    let func = sysroot_keyed(guarded_into(
        &collect_into_sink(&format!("{DEQUE}<()>"), Some(0)),
        64,
        100,
        vec_deque(),
    ));
    assert_receiver_unknown(&func, Some(64), "Iterator::collect_into");
    // A user destination runs a user `Extend`: no length memory is shown to bound.
    let bag = Ty::adt("mycrate::Bag", vec![("n".into(), Ty::usize())]);
    let func = guarded_into(&collect_into_sink("mycrate::Bag", None), 64, 100, bag);
    assert_receiver_unknown(&func, Some(64), "Iterator::collect_into");
}

#[test]
fn collect_into_a_sized_destination_still_counts() {
    // CONTROL: `Vec<u64>` under `n < 2^20` fits whatever a live `Vec<u64>` holds on a
    // 64-bit target, and on a 32-bit one the receiver may already be full.
    let into_vec = collect_into_sink("alloc::vec::Vec<u64>", Some(8));
    let func = sysroot_keyed(guarded_into(&into_vec, 64, 1 << 20, vec_of(Ty::u64())));
    let r = verdict(&func, Some(64));
    assert!(proved(&r), "a counted `collect_into` into a live `Vec<u64>`: {r:?}");
    let func = sysroot_keyed(guarded_into(&into_vec, 32, 1 << 20, vec_of(Ty::u64())));
    let r = verdict(&func, Some(32));
    assert!(failed(&r), "a 32-bit receiver may already be full: {r:?}");
    // A `VecDeque<u64>` destination is sized by the token of a SYSROOT callee only.
    let into_deque = collect_into_sink(&format!("{DEQUE}<u64>"), Some(8));
    let func = sysroot_keyed(guarded_into(&into_deque, 64, 1 << 20, vec_deque()));
    let r = verdict(&func, Some(64));
    assert!(proved(&r), "a counted `collect_into` into a live `VecDeque<u64>`: {r:?}");
    let func = guarded_into(&into_deque, 64, 1 << 20, vec_deque());
    assert_receiver_unknown(&func, Some(64), "Iterator::collect_into");
    // ... and with no token at all, nothing sizes it.
    let func = sysroot_keyed(guarded_into(
        &collect_into_sink(&format!("{DEQUE}<u64>"), None),
        64,
        1 << 20,
        vec_deque(),
    ));
    assert_receiver_unknown(&func, Some(64), "Iterator::collect_into");
}

#[test]
fn extend_into_a_zero_sized_receiver_keeps_a_visible_unknown() {
    // The x01 probe, `v.extend(..)` into `Vec<()>` and `VecDeque<()>` (closed for `Vec`
    // by 27264a61eb1), through the shared question and a counted source.
    let func = sysroot_keyed(guarded_into(
        &extend_sink("alloc::vec::Vec", "()", 0),
        64,
        100,
        vec_of(Ty::Unit),
    ));
    for bits in [Some(64), Some(32), None] {
        assert_receiver_unknown(&func, bits, "Extend::extend");
    }
    let func = sysroot_keyed(guarded_into(&extend_sink(DEQUE, "()", 0), 64, 100, vec_deque()));
    assert_receiver_unknown(&func, Some(64), "Extend::extend");
    // CONTROL: the sized twins count, and a guarded count is proved on 64 bits.
    let func = sysroot_keyed(guarded_into(
        &extend_sink("alloc::vec::Vec", "u64", 8),
        64,
        1 << 20,
        vec_of(Ty::u64()),
    ));
    let r = verdict(&func, Some(64));
    assert!(proved(&r), "`extend` into a live `Vec<u64>`: {r:?}");
    let func = sysroot_keyed(guarded_into(&extend_sink(DEQUE, "u64", 8), 64, 1 << 20, vec_deque()));
    let r = verdict(&func, Some(64));
    assert!(proved(&r), "`extend` into a live `VecDeque<u64>`: {r:?}");
}

#[test]
fn reserve_on_a_zero_sized_sysroot_receiver_keeps_a_visible_unknown() {
    // Review round 59 kept this row, but as the element ceiling alone: a guard
    // discharged it and a constant count skipped it.
    for method in ["reserve", "reserve_exact"] {
        let func =
            sysroot_keyed(guarded_into(&reserve(method, "()", 0), 64, 100, vec_of(Ty::Unit)));
        for bits in [Some(64), Some(32), None] {
            assert_receiver_unknown(&func, bits, "Vec::reserve");
        }
        assert_receiver_unknown(&with_constant_count(func, 5), Some(64), "Vec::reserve");
    }
    let deque = Sink::Direct {
        callee: format!("{DEQUE}::<()>::reserve{}", render_trailing_elem_bytes_token(0)),
        receiver: true,
    };
    let func = sysroot_keyed(guarded_into(&deque, 64, 100, vec_deque()));
    assert_receiver_unknown(&func, Some(64), "Vec::reserve");
    let extend_reserve = Sink::Direct {
        callee: format!(
            "<alloc::vec::Vec<()> as core::iter::traits::collect::Extend<()>>::extend_reserve{}",
            render_trailing_elem_bytes_token(0)
        ),
        receiver: true,
    };
    let func = sysroot_keyed(guarded_into(&extend_reserve, 64, 100, vec_of(Ty::Unit)));
    assert_receiver_unknown(&func, Some(64), "Vec::reserve");
}

#[test]
fn reserve_on_a_sized_sysroot_receiver_still_counts() {
    // CONTROL: `Vec<u64>` and `VecDeque<u64>` (sized by its sysroot token) count, and
    // the guarded row is proved on 64 bits and refused on 32.
    let func =
        sysroot_keyed(guarded_into(&reserve("reserve", "u64", 8), 64, 1 << 20, vec_of(Ty::u64())));
    assert!(proved(&verdict(&func, Some(64))), "`Vec<u64>::reserve(n < 2^20)` on 64 bits");
    let func =
        sysroot_keyed(guarded_into(&reserve("reserve", "u64", 8), 32, 1 << 20, vec_of(Ty::u64())));
    assert!(failed(&verdict(&func, Some(32))), "`Vec<u64>::reserve` on 32 bits");
    let deque = Sink::Direct {
        callee: format!("{DEQUE}::<u64>::reserve{}", render_trailing_elem_bytes_token(8)),
        receiver: true,
    };
    let func = sysroot_keyed(guarded_into(&deque, 64, 1 << 20, vec_deque()));
    assert!(proved(&verdict(&func, Some(64))), "`VecDeque<u64>::reserve(n < 2^20)` on 64 bits");
    // A non-sysroot `reserve` is not asked about its receiver. Without a layout
    // it must keep a visible gap, rather than prove byte capacity from a count.
    let local = Sink::Direct { callee: "mycrate::Pool::reserve".into(), receiver: true };
    let func = guarded_into(&local, 64, 100, Ty::u32());
    let unknown = rows(&func, Some(64));
    let [row] = unknown.as_slice() else { panic!("one explicit layout gap: {unknown:#?}") };
    assert!(matches!(&row.kind, VcKind::UnsupportedMir { kind, .. }
        if kind.ends_with("::element-size-not-derivable")));
    assert!(matches!(solve(row), VerificationResult::Unknown { .. }));
}

#[test]
fn a_live_receiver_of_unrecoverable_stride_is_never_shown_to_fit_below_64_bits() {
    // `String::reserve` carries no element token (no generic argument), so the row had
    // no capacity term, and below 64 bits — where a `String` may already hold
    // `isize::MAX` bytes — `if n < 100 { s.reserve(n) }` was the element ceiling
    // alone, and proved.
    let sink = Sink::Direct { callee: "alloc::string::String::reserve".into(), receiver: true };
    let func64 = sysroot_keyed(guarded_into(&sink, 64, 100, string()));
    assert!(proved(&verdict(&func64, Some(64))), "the 64-bit axiom bounds a live `String`");
    let func32 = sysroot_keyed(guarded_into(&sink, 32, 100, string()));
    for bits in [Some(32), None] {
        let rows = rows(&func32, bits);
        let [row] = rows.as_slice() else { panic!("one row at {bits:?}, got {rows:#?}") };
        let r = solve(row);
        assert!(failed(&r), "a possibly-full `String` at {bits:?}: {r:?}");
        assert!(
            !interval_proves(row),
            "the interval lane must not prove it either ({bits:?}): {}",
            row.formula.to_smtlib()
        );
    }
    // A constant count is not skipped there either.
    let rows = rows(&with_constant_count(func32, 10), Some(32));
    assert_eq!(rows.len(), 1, "`s.reserve(10)` on 32 bits: {rows:#?}");
    // CONTROL: the FRESH twin carries no receiver and is unchanged on every width.
    let fresh =
        Sink::Direct { callee: "alloc::string::String::with_capacity".into(), receiver: false };
    for bits in [32, 64] {
        let func = guarded(&fresh, bits, 100);
        assert!(
            proved(&verdict(&func, Some(bits))),
            "`String::with_capacity(n < 100)` on {bits} bits"
        );
    }
}

#[test]
fn a_guarded_generic_count_cannot_prove_unknown_byte_capacity() {
    let sink = Sink::Direct {
        callee: "alloc::vec::Vec::<T>::with_capacity".into(),
        receiver: false,
    };
    for bits in [32, 64] {
        let func = guarded(&sink, bits, 1 << 28);
        let unknown = rows(&func, Some(bits));
        let observed = unknown.first().map(solve);
        eprintln!("ALLOC_STRIDE_BASELINE guarded bits={bits} rows={} kind={:?} formula={:?} verdict={observed:?}", unknown.len(), unknown.first().map(|r| &r.kind), unknown.first().map(|r| r.formula.to_smtlib()));
        let [row] = unknown.as_slice() else { panic!("one layout gap: {unknown:#?}") };
        assert!(matches!(&row.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == "UnboundedAllocation::Vec::with_capacity::element-size-not-derivable"));
        assert!(matches!(observed, Some(VerificationResult::Unknown { .. })));
    }
    // These two concrete instantiations have the SAME count precondition. The
    // small element fits; the large one has a reachable capacity overflow. A
    // generic count-only proof would incorrectly bless both instantiations.
    let small = guarded(&with_capacity("u8", 1), 64, 1 << 28);
    assert!(proved(&verdict(&small, Some(64))));
    let large = guarded(&with_capacity("[u8; 1099511627776]", 1 << 40), 64, 1 << 28);
    assert!(failed(&verdict(&large, Some(64))));
}

#[test]
fn a_nonzero_constant_count_does_not_hide_an_unknown_layout() {
    let sink = Sink::Direct {
        callee: "alloc::vec::Vec::<T>::with_capacity".into(),
        receiver: false,
    };
    for count in [2_u128, 1 << 23] {
        let mut func = guarded(&sink, 64, 1 << 28);
        let Terminator::Call { args, .. } = &mut func.body.blocks[2].terminator else {
            unreachable!()
        };
        args[0] = Operand::Constant(ConstValue::Uint(count, 64));
        let unknown = rows(&func, Some(64));
        let observed = unknown.first().map(solve);
        eprintln!("ALLOC_STRIDE_BASELINE constant count={count} rows={} kind={:?} formula={:?} verdict={observed:?}", unknown.len(), unknown.first().map(|r| &r.kind), unknown.first().map(|r| r.formula.to_smtlib()));
        let [row] = unknown.as_slice() else { panic!("constant must retain layout gap: {unknown:#?}") };
        assert!(matches!(&row.kind, VcKind::UnsupportedMir { kind, .. }
            if kind.ends_with("::element-size-not-derivable")));
        assert!(matches!(observed, Some(VerificationResult::Unknown { .. })));
    }
}

#[test]
fn a_literal_zero_request_does_not_require_an_element_layout() {
    let sink = Sink::Direct {
        callee: "alloc::vec::Vec::<T>::with_capacity".into(),
        receiver: false,
    };
    for bits in [32, 64] {
        let mut func = guarded(&sink, bits, 1 << 28);
        let Terminator::Call { args, .. } = &mut func.body.blocks[2].terminator else {
            unreachable!()
        };
        args[0] = Operand::Constant(ConstValue::Uint(0, bits));
        let actual = rows(&func, Some(bits));
        eprintln!("ALLOC_STRIDE_BASELINE zero bits={bits} rows={}", actual.len());
        assert!(actual.is_empty(), "zero allocates no element bytes");
    }
}

#[test]
fn tuple_padding_requires_an_authoritative_allocation_layout() {
    // Native aarch64 layout oracle: compute metadata only, never allocate the
    // huge array. Padding, not field sum, determines this concrete stride.
    #[cfg(target_arch = "aarch64")]
    assert_eq!(std::mem::size_of::<([u8; 68719476727], u64)>(), 1_usize << 36);
    // The field sum is 2^36-1; padding makes the actual tuple 2^36 bytes on
    // aarch64. Multiplying by 2^27 crosses isize::MAX despite the count bound.
    let tuple = "([u8; 68719476727], u64)";
    let nested = format!("[{tuple}; 2]");
    for (element, stride, count) in [(tuple, 1_u64 << 36, 1_u128 << 27),
        (nested.as_str(), 1_u64 << 37, 1_u128 << 26)]
    {
        for known in [false, true] {
            let sink = Sink::Direct {
                callee: format!("alloc::vec::Vec::<{element}>::with_capacity{}",
                    if known { render_trailing_elem_bytes_token(stride) } else { String::new() }),
                receiver: false,
            };
            let mut func = guarded(&sink, 64, 1 << 28);
            let Terminator::Call { args, .. } = &mut func.body.blocks[2].terminator else {
                unreachable!()
            };
            args[0] = Operand::Constant(ConstValue::Uint(count, 64));
            let actual = rows(&func, Some(64));
            let [row] = actual.as_slice() else { panic!("padding cannot hide this request: {actual:#?}") };
            if known {
                assert!(matches!(row.kind, VcKind::UnboundedAllocation { .. }));
                assert!(failed(&solve(row)), "the exact stride has a capacity overflow");
            } else {
                assert!(matches!(&row.kind, VcKind::UnsupportedMir { kind, .. }
                    if kind.ends_with("::element-size-not-derivable")));
                assert!(matches!(solve(row), VerificationResult::Unknown { .. }));
            }
        }
    }
}

#[test]
fn a_tuple_operand_does_not_use_an_unpadded_field_sum() {
    let tuple = Ty::Tuple(vec![
        Ty::Array { elem: Box::new(Ty::u8()), len: 68719476727 }, Ty::u64(),
    ]);
    for known in [false, true] {
        let sink = Sink::Direct {
            callee: format!("alloc::vec::from_elem{}",
                if known { render_trailing_elem_bytes_token(1_u64 << 36) } else { String::new() }),
            receiver: true,
        };
        let mut func = guarded(&sink, 64, 1 << 28);
        func.body.locals[1].ty = tuple.clone();
        let Terminator::Call { args, .. } = &mut func.body.blocks[2].terminator else {
            unreachable!()
        };
        args[1] = Operand::Constant(ConstValue::Uint(1 << 27, 64));
        let actual = rows(&func, Some(64));
        let [row] = actual.as_slice() else { panic!("one exact layout result: {actual:#?}") };
        if known {
            assert!(matches!(row.kind, VcKind::UnboundedAllocation { .. }));
            assert!(failed(&solve(row)));
        } else {
            assert!(matches!(&row.kind, VcKind::UnsupportedMir { kind, .. }
                if kind.ends_with("::element-size-not-derivable")));
            assert!(matches!(solve(row), VerificationResult::Unknown { .. }));
        }
    }
}

#[test]
fn an_array_length_expression_is_not_its_leading_decimal_digits() {
    for element in ["[u8; 1 << 40]", "[u8; 0x10000000000]", "[u8; 1 + 1099511627775]"] {
        let sink = Sink::Direct {
            callee: format!("alloc::vec::Vec::<{element}>::with_capacity"),
            receiver: false,
        };
        let func = guarded(&sink, 64, 1 << 28);
        let actual = rows(&func, Some(64));
        let [row] = actual.as_slice() else { panic!("the whole length needs evidence: {actual:#?}") };
        assert!(matches!(&row.kind, VcKind::UnsupportedMir { kind, .. }
            if kind.ends_with("::element-size-not-derivable")));
        assert!(matches!(solve(row), VerificationResult::Unknown { .. }));
    }
    // Fully evaluated decimal layouts retain the concrete capacity counterexample.
    for element in ["[u8; 1099511627776]", "[u8; 1_099_511_627_776usize]"] {
        let sink = Sink::Direct {
            callee: format!("alloc::vec::Vec::<{element}>::with_capacity"),
            receiver: false,
        };
        assert!(failed(&verdict(&guarded(&sink, 64, 1 << 28), Some(64))));
    }
}
