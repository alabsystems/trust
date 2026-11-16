// Trust (W32-PRIMINT-PIN-1, 2026-10-06): `numeric_panic`'s rows at a POINTER-SIZED
// (`usize`/`isize`) owner.
//
// THE LIE. `PRIMITIVE_INTS` gave `usize`/`isize` the width 64 ("the pinned 64-bit
// target"), while `ranged()` ranged each operand at its DECLARED carrier, which the
// extractor mints at the target's real pointer width (`Ty::Int { width: 32 }` on
// i686 and wasm32). So every 32-bit violation formula asked for a 64-bit threshold
// the operand cannot reach. It was UNSAT, and the row was published `proved`
// (Certified, KernelRechecked) for calls that panic. Measured on the stage 1 of
// `46e9afaf95` (main + waves 18 and 19), raw `trustc --target i686-unknown-linux-gnu`
// and `wasm32-unknown-unknown` with a cross-built `core`. The default policy exited
// rc=0 with these rows proved:
//   * `strict_neg`, `strict_abs`, `next_multiple_of`, `next_power_of_two`;
//   * `strict_shl` under `s < 40`;
//   * `Neg::neg`, `div_euclid(x, -1)`;
//   * wave 19's signed `next_multiple_of`, `funnel_shl`, `strict_cast_signed`,
//     `ShlAssign::shl_assign`, `Shl::shl`, `strict_div`, `strict_add_unsigned`;
//   * `(a..=b).count()` over `usize`.
// `(a..=b).count()` over `u32` got no row at all. Each call panics on the 32-bit
// target: i686 CTFE witnesses, E0080.
//
// These tests build each call at 16-, 32- and 64-bit carriers. Each row must be
// SAT at its own width's panicking witness, and not at the narrower width's (so
// the width is read from the operand, not pinned). The end-to-end lie is pinned
// through the in-process solver. A carrier that does not fix the width must be
// refused, never assumed 64: the faithful `PtrSizedInt`, or a signed literal.

use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, Formula, LocalDecl, Operand, Place, Rvalue,
    Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody,
    VerifiableFunction, VerificationResult,
};

use super::generate_vcs;
use super::numeric_panic::{is_numeric_value_panic_callee, numeric_value_panic_row};
use super::unwrap_panic::{SignedAbsRow, signed_abs_panic_body};

// ---- builders --------------------------------------------------------------------

/// A parameter (or return) type, spelled independently of the carrier width.
#[derive(Clone, Copy, Debug)]
enum P {
    Usize,
    Isize,
    U32,
    MutUsize,
    Str,
    Unit,
}

/// How a pointer-sized type is carried: the legacy `Ty::Int` at a real pointer
/// width, or the faithful `Ty::PtrSizedInt` (whose `int_width` is a pinned 64).
#[derive(Clone, Copy, Debug)]
enum Carrier {
    Bits(u32),
    Faithful,
}

fn ty(p: P, c: Carrier) -> Ty {
    let ptr = |signed| match c {
        Carrier::Bits(width) => Ty::Int { width, signed },
        Carrier::Faithful => Ty::PtrSizedInt { signed },
    };
    match p {
        P::Usize => ptr(false),
        P::Isize => ptr(true),
        P::U32 => Ty::Int { width: 32, signed: false },
        P::MutUsize => Ty::Ref { mutable: true, inner: Box::new(ptr(false)) },
        P::Str => Ty::Ref { mutable: false, inner: Box::new(Ty::Str) },
        P::Unit => Ty::Unit,
    }
}

fn call_terminator(callee: &str, args: Vec<Operand>) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args,
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
        is_foreign: false,
    }
}

/// `fn f(a: params[0], b: params[1], ..) -> ret { callee(args..) }`. The
/// parameters are locals `_1..`, and `_0` is the call's destination.
fn call_fn(callee: &str, params: &[Ty], ret: Ty, args: Vec<Operand>) -> VerifiableFunction {
    const NAMES: [&str; 3] = ["a", "b", "c"];
    let mut locals = vec![LocalDecl { index: 0, ty: ret.clone(), name: None }];
    for (i, t) in params.iter().enumerate() {
        locals.push(LocalDecl { index: i + 1, ty: t.clone(), name: Some(NAMES[i].into()) });
    }
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "w32::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call_terminator(callee, args),
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: params.len(),
            return_ty: ret,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn param(i: usize) -> Operand {
    Operand::Copy(Place::local(i))
}

/// The row `numeric_panic` mints for the function's (last) call.
fn row(f: &VerifiableFunction) -> Option<(Formula, VcKind)> {
    let (callee, args, dest) = f
        .body
        .blocks
        .iter()
        .rev()
        .find_map(|b| match &b.terminator {
            Terminator::Call { func, args, dest, .. } => Some((func, args, dest)),
            _ => None,
        })
        .expect("the fixture makes a call");
    numeric_value_panic_row(f, callee, args, dest)
}

fn unresolved(row: &Option<(Formula, VcKind)>) -> bool {
    matches!(row, Some((_, VcKind::UnsupportedMir { kind, .. })) if kind == "pointer-width-unresolved")
}

// ---- a tiny evaluator for the linear shapes these rows build ---------------------

fn eval_int(f: &Formula, env: &[(String, i128)]) -> i128 {
    let var = |name: &str| {
        env.iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| *v)
            .unwrap_or_else(|| panic!("unbound `{name}` in {}", f.to_smtlib()))
    };
    match f {
        Formula::Int(v) => *v,
        // Only `u128::MAX` (a 128-bit range bound) saturates, which is exact for every
        // comparison against the test values here.
        Formula::UInt(v) => i128::try_from(*v).unwrap_or(i128::MAX),
        Formula::Var(name, _) => var(name),
        Formula::SymVar(sym, _) => var(sym.as_str()),
        Formula::Add(a, b) => eval_int(a, env) + eval_int(b, env),
        Formula::Sub(a, b) => eval_int(a, env) - eval_int(b, env),
        Formula::Neg(a) => -eval_int(a, env),
        other => panic!("not an integer term these rows build: {}", other.to_smtlib()),
    }
}

fn eval_bool(f: &Formula, env: &[(String, i128)]) -> bool {
    let cmp = |a: &Formula, b: &Formula| (eval_int(a, env), eval_int(b, env));
    match f {
        Formula::Bool(v) => *v,
        Formula::Not(a) => !eval_bool(a, env),
        Formula::And(cs) => cs.iter().all(|c| eval_bool(c, env)),
        Formula::Or(cs) => cs.iter().any(|c| eval_bool(c, env)),
        Formula::Eq(a, b) => {
            let (x, y) = cmp(a, b);
            x == y
        }
        Formula::Lt(a, b) => {
            let (x, y) = cmp(a, b);
            x < y
        }
        Formula::Le(a, b) => {
            let (x, y) = cmp(a, b);
            x <= y
        }
        Formula::Gt(a, b) => {
            let (x, y) = cmp(a, b);
            x > y
        }
        Formula::Ge(a, b) => {
            let (x, y) = cmp(a, b);
            x >= y
        }
        other => panic!("not a boolean these rows build: {}", other.to_smtlib()),
    }
}

/// `values[i]` bound to parameter `_{i+1}`'s formula name.
fn env(f: &VerifiableFunction, values: &[i128]) -> Vec<(String, i128)> {
    values
        .iter()
        .enumerate()
        .map(|(i, v)| (crate::place_to_var_name(f, &Place::local(i + 1)), *v))
        .collect()
}

// ---- the width-reading cases -----------------------------------------------------

fn umax(w: u32) -> i128 {
    (1i128 << w) - 1
}
fn smin(w: u32) -> i128 {
    -(1i128 << (w - 1))
}
fn smax(w: u32) -> i128 {
    (1i128 << (w - 1)) - 1
}

/// A call whose row reads its pointer-sized owner's width.
struct Case {
    callee: &'static str,
    params: &'static [P],
    ret: P,
    /// A literal operand appended after the parameters.
    literal: Option<ConstValue>,
    /// Parameter values at which the call PANICS on a `w`-bit target. Each is
    /// in range on every wider target, and does NOT panic there.
    panics: fn(u32) -> Vec<i128>,
}

impl Case {
    fn build(&self, c: Carrier) -> VerifiableFunction {
        let params: Vec<Ty> = self.params.iter().map(|p| ty(*p, c)).collect();
        let mut args: Vec<Operand> = (1..=params.len()).map(param).collect();
        if let Some(lit) = &self.literal {
            args.push(Operand::Constant(lit.clone()));
        }
        call_fn(self.callee, &params, ty(self.ret, c), args)
    }
}

const WIDTH_READING: &[Case] = &[
    // The scout's probe shapes (`w32lib.rs`, `q.rs`).
    Case {
        callee: "core::num::<impl usize>::next_power_of_two",
        params: &[P::Usize],
        ret: P::Usize,
        literal: None,
        panics: |w| vec![umax(w)],
    },
    Case {
        callee: "core::num::<impl usize>::next_multiple_of",
        params: &[P::Usize, P::Usize],
        ret: P::Usize,
        literal: None,
        panics: |w| vec![umax(w), 2],
    },
    Case {
        callee: "core::num::<impl isize>::strict_neg",
        params: &[P::Isize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smin(w)],
    },
    Case {
        callee: "core::num::<impl isize>::strict_abs",
        params: &[P::Isize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smin(w)],
    },
    Case {
        callee: "<isize as core::ops::arith::Neg>::neg",
        params: &[P::Isize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smin(w)],
    },
    // `strict_shl`'s `BITS` is the RECEIVER's width, not the `u32` amount's.
    Case {
        callee: "core::num::<impl usize>::strict_shl",
        params: &[P::Usize, P::U32],
        ret: P::Usize,
        literal: None,
        panics: |w| vec![1, i128::from(w) + 3],
    },
    Case {
        callee: "core::num::<impl isize>::strict_shr",
        params: &[P::Isize, P::U32],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![1, i128::from(w) + 3],
    },
    // `x.div_euclid(-1)`, the scout's `deu`.
    Case {
        callee: "core::num::<impl isize>::div_euclid",
        params: &[P::Isize],
        ret: P::Isize,
        literal: Some(ConstValue::Int(-1)),
        panics: |w| vec![smin(w)],
    },
    Case {
        callee: "core::num::<impl isize>::rem_euclid",
        params: &[P::Isize, P::Isize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smin(w), -1],
    },
    // Wave 19 (NUM-NIGHTLY-UNCHARGED-1)'s arms take the same receiver-width rule.
    Case {
        callee: "core::num::<impl isize>::next_multiple_of",
        params: &[P::Isize, P::Isize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smax(w), 2],
    },
    Case {
        callee: "core::num::<impl usize>::funnel_shl",
        params: &[P::Usize, P::Usize, P::U32],
        ret: P::Usize,
        literal: None,
        panics: |w| vec![1, 0, i128::from(w) + 3],
    },
    Case {
        callee: "core::num::<impl usize>::funnel_shr",
        params: &[P::Usize, P::Usize, P::U32],
        ret: P::Usize,
        literal: None,
        panics: |w| vec![1, 0, i128::from(w) + 3],
    },
    Case {
        callee: "core::num::<impl usize>::strict_cast_signed",
        params: &[P::Usize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smax(w) + 1],
    },
    Case {
        callee: "core::num::<impl isize>::strict_div",
        params: &[P::Isize, P::Isize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smin(w), -1],
    },
    Case {
        callee: "core::num::<impl isize>::strict_rem_euclid",
        params: &[P::Isize, P::Isize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smin(w), -1],
    },
    Case {
        callee: "core::num::<impl isize>::strict_add_unsigned",
        params: &[P::Isize, P::Usize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smax(w), 1],
    },
    Case {
        callee: "core::num::<impl isize>::strict_sub_unsigned",
        params: &[P::Isize, P::Usize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![smin(w), 1],
    },
    Case {
        callee: "core::num::<impl usize>::strict_add_signed",
        params: &[P::Usize, P::Isize],
        ret: P::Usize,
        literal: None,
        panics: |w| vec![umax(w), 1],
    },
    // The by-value operator calls.
    Case {
        callee: "<usize as core::ops::bit::Shl<u32>>::shl",
        params: &[P::Usize, P::U32],
        ret: P::Usize,
        literal: None,
        panics: |w| vec![1, i128::from(w) + 3],
    },
    Case {
        callee: "<isize as core::ops::bit::Shr>::shr",
        params: &[P::Isize, P::Isize],
        ret: P::Isize,
        literal: None,
        panics: |w| vec![1, i128::from(w) + 3],
    },
    // A compound-assign call's `Self` is `*self`, its `&mut` receiver's pointee.
    Case {
        callee: "<usize as core::ops::bit::ShlAssign<u32>>::shl_assign",
        params: &[P::MutUsize, P::U32],
        ret: P::Unit,
        literal: None,
        panics: |w| vec![0, i128::from(w) + 3],
    },
];

/// Every width-reading row is built at its RECEIVER's declared width. At 16 and
/// 32 bits it is SAT at that target's panicking witness. Before the fix it was
/// built at 64 and was false there. At 32 and 64 bits it is not SAT at the
/// narrower target's witness, which is a value that does not panic there. So the
/// 64-bit row is the host's unchanged one.
#[test]
fn pointer_sized_rows_are_built_at_the_receivers_declared_width() {
    for case in WIDTH_READING {
        for w in [16, 32, 64] {
            let f = case.build(Carrier::Bits(w));
            let built = row(&f);
            let Some((formula, kind)) = built else {
                panic!("{} at {w} bits must mint a row", case.callee);
            };
            assert!(
                !matches!(kind, VcKind::UnsupportedMir { .. }),
                "{} at {w} bits: a declared `Int {{ width: {w} }}` receiver resolves the width, \
                 got {kind:?}",
                case.callee
            );
            let at = (case.panics)(w);
            assert!(
                eval_bool(&formula, &env(&f, &at)),
                "{} panics on a {w}-bit target at {at:?}: its row must be SAT there\n{}",
                case.callee,
                formula.to_smtlib()
            );
            if w > 16 {
                let narrower = (case.panics)(w / 2);
                assert!(
                    !eval_bool(&formula, &env(&f, &narrower)),
                    "{} does not panic on a {w}-bit target at {narrower:?}: the {w}-bit row \
                     must not be SAT there\n{}",
                    case.callee,
                    formula.to_smtlib()
                );
            }
        }
    }
}

/// A carrier that does not fix the target's pointer width is REFUSED for every
/// width-reading row. It is never built at an assumed 64 bits. The faithful
/// `PtrSizedInt` carries no width (its `int_width` is a pinned 64).
#[test]
fn a_faithful_ptr_sized_receiver_is_refused_not_assumed_64() {
    for case in WIDTH_READING {
        let f = case.build(Carrier::Faithful);
        let built = row(&f);
        assert!(
            unresolved(&built),
            "{} on a `PtrSizedInt` receiver must be the fail-closed `pointer-width-unresolved` \
             row, got {:?}",
            case.callee,
            built.map(|(_, k)| k)
        );
    }
}

/// A signed literal (`ConstValue::Int`) carries no width: `operand_ty` types it
/// i64 on every target. So it does not resolve a pointer-sized receiver. An
/// UNSIGNED literal carries the extractor's target width (`ConstValue::Uint(_, w)`)
/// and does. `usize::MAX.next_power_of_two()` on a 32-bit target used to mint NO
/// row: the literal `2^32 - 1` is below the 64-bit `2^63`, so the arm decided it
/// cannot panic.
#[test]
fn literal_receivers_resolve_only_through_a_declared_width() {
    let sn = call_fn(
        "core::num::<impl isize>::strict_neg",
        &[],
        Ty::Int { width: 32, signed: true },
        vec![Operand::Constant(ConstValue::Int(smin(32)))],
    );
    assert!(unresolved(&row(&sn)), "a signed literal receiver must be refused");

    let npot = |v: i128, w: u32| {
        call_fn(
            "core::num::<impl usize>::next_power_of_two",
            &[],
            Ty::Int { width: w, signed: false },
            vec![Operand::Constant(ConstValue::Uint(v as u128, w))],
        )
    };
    let Some((formula, _)) = row(&npot(umax(32), 32)) else {
        panic!("`usize::MAX.next_power_of_two()` on a 32-bit target must mint a row");
    };
    assert!(eval_bool(&formula, &[]), "its violation is decided TRUE: {}", formula.to_smtlib());
    // At or below `2^(BITS-1)` it cannot panic, and the arm returns no row, as before.
    assert!(row(&npot(1 << 31, 32)).is_none());
    assert!(row(&npot(1 << 63, 64)).is_none());
}

/// The family's WIDTH-FREE rows keep their row on any carrier. Their violation
/// never reads `BITS`, `MIN` or `MAX`. And a method outside the family mints
/// nothing, even when its receiver's width is unresolved.
#[test]
fn width_free_rows_and_non_family_methods_need_no_resolved_width() {
    for (callee, params, ret) in [
        ("core::num::<impl usize>::ilog2", &[P::Usize][..], P::U32),
        ("core::num::<impl isize>::ilog10", &[P::Isize][..], P::U32),
        ("core::num::<impl isize>::isqrt", &[P::Isize][..], P::Isize),
        ("core::num::<impl usize>::from_str_radix", &[P::Str, P::U32][..], P::Unit),
        ("core::num::<impl usize>::strict_neg", &[P::Usize][..], P::Usize),
        ("core::num::<impl usize>::strict_div", &[P::Usize, P::Usize][..], P::Usize),
    ] {
        for c in [Carrier::Faithful, Carrier::Bits(32)] {
            let f = call_fn(
                callee,
                &params.iter().map(|p| ty(*p, c)).collect::<Vec<_>>(),
                ty(ret, c),
                (1..=params.len()).map(param).collect(),
            );
            let built = row(&f);
            assert!(
                matches!(built, Some((_, VcKind::Assertion { .. }))),
                "{callee} ({c:?}) keeps its precise row, got {:?}",
                built.map(|(_, k)| k)
            );
        }
    }
    for callee in [
        "core::num::<impl usize>::count_ones",
        "core::num::<impl isize>::wrapping_neg",
        "<usize as core::ops::arith::Add>::add",
    ] {
        let f = call_fn(
            callee,
            &[ty(P::Usize, Carrier::Faithful), ty(P::Usize, Carrier::Faithful)],
            ty(P::Usize, Carrier::Faithful),
            vec![param(1), param(2)],
        );
        assert!(row(&f).is_none(), "{callee} is not a numeric value-panic row");
    }
}

/// `strict_cast::<usize>`'s target is the call's destination. A faithful
/// `PtrSizedInt` destination does not carry the target's width, so it is refused.
/// A legacy `Int { width: 32 }` destination is ranged at 32 bits:
/// `u64::strict_cast::<usize>(2^32)` panics on i686.
#[test]
fn a_strict_cast_to_a_pointer_sized_target_takes_the_destinations_width() {
    let cast = |dest: Ty| {
        call_fn(
            "core::num::<impl u64>::strict_cast::<usize>",
            &[Ty::Int { width: 64, signed: false }],
            dest,
            vec![param(1)],
        )
    };
    assert!(unresolved(&row(&cast(Ty::PtrSizedInt { signed: false }))));
    let f = cast(Ty::Int { width: 32, signed: false });
    let Some((formula, _)) = row(&f) else { panic!("a 32-bit target mints a row") };
    assert!(eval_bool(&formula, &env(&f, &[1 << 32])));
    assert!(!eval_bool(&formula, &env(&f, &[umax(32)])));
}

/// Trust (wave-21 integration, 2026-10-10): the wave-19 review's trait spelling
/// `<Dst as CheckedCastFromInt<Src>>::strict_cast_from` landed on `main` after this
/// lane branched. Its row read both sides through `primitive_int`, which pinned
/// `usize`/`isize` at 64, and its destination through `int_width`, which pins a
/// faithful `PtrSizedInt` at 64. Merged with this lane, a pointer-sized side takes
/// its width from a declared carrier: `Dst` from the destination's `Ty::Int`, `Src`
/// from the argument's (`declared_pointer_width`). A faithful destination or an
/// argument that fixes no width is refused, never ranged at 64.
///
/// FAILS BEFORE: with the pinned 64 (`IntWidth::Pointer` read as 64 and `dest_int`
/// answering a `PtrSizedInt` at 64), every 16- and 32-bit case is answered with the
/// `strict-cast-target-unmodeled` row, which is violated at the in-range values too,
/// and the faithful destination gets a 64-bit row instead of the refusal.
#[test]
fn strict_cast_from_reads_a_pointer_sized_sides_width_from_its_carrier() {
    const TO_USIZE: &str =
        "<usize as core::convert::num::CheckedCastFromInt<u64>>::strict_cast_from";
    const FROM_USIZE: &str =
        "<u16 as core::convert::num::CheckedCastFromInt<usize>>::strict_cast_from";
    let uint = |width| Ty::Int { width, signed: false };
    let assertion_row = |f: &VerifiableFunction| match row(f) {
        Some((formula, VcKind::Assertion { .. })) => formula,
        other => panic!("`{}`: expected the out-of-range assertion row, got {other:?}", f.name),
    };
    // `Dst = usize`, carried at the target's pointer width: out of range exactly
    // above that width's `MAX`. From `u64` to a 64-bit `usize` the cast is total.
    for w in [16, 32] {
        let f = call_fn(TO_USIZE, &[uint(64)], uint(w), vec![param(1)]);
        let formula = assertion_row(&f);
        assert!(eval_bool(&formula, &env(&f, &[umax(w) + 1])), "{w}-bit usize: MAX + 1 panics");
        assert!(!eval_bool(&formula, &env(&f, &[umax(w)])), "{w}-bit usize: MAX fits");
    }
    let f = call_fn(TO_USIZE, &[uint(64)], uint(64), vec![param(1)]);
    assert!(!eval_bool(&assertion_row(&f), &env(&f, &[umax(64)])), "u64 fits a 64-bit usize");
    assert!(unresolved(&row(&call_fn(
        TO_USIZE,
        &[uint(64)],
        Ty::PtrSizedInt { signed: false },
        vec![param(1)],
    ))));
    // `Src = usize`, carried at the target's pointer width: the argument is ranged
    // at that width, and the row fires above `u16::MAX`.
    for w in [32, 64] {
        let f = call_fn(FROM_USIZE, &[uint(w)], uint(16), vec![param(1)]);
        let formula = assertion_row(&f);
        assert!(eval_bool(&formula, &env(&f, &[1 << 16])), "{w}-bit usize source: 65536 panics");
        assert!(!eval_bool(&formula, &env(&f, &[umax(16)])), "{w}-bit usize source: 65535 fits");
    }
    assert!(unresolved(&row(&call_fn(
        FROM_USIZE,
        &[Ty::PtrSizedInt { signed: false }],
        uint(16),
        vec![param(1)],
    ))));
    // A signed literal carries no width (`declared_pointer_width`).
    assert!(unresolved(&row(&call_fn(
        "<i16 as core::convert::num::CheckedCastFromInt<isize>>::strict_cast_from",
        &[],
        Ty::Int { width: 16, signed: true },
        vec![Operand::Constant(ConstValue::Int(70_000))],
    ))));
}

// ---- end to end, through the in-process solver -----------------------------------

fn verdicts(f: &VerifiableFunction, prefix: &str) -> Vec<VerificationResult> {
    let router = crate::test_router::deterministic_test_router();
    generate_vcs(f)
        .iter()
        .filter(
            |vc| matches!(&vc.kind, VcKind::Assertion { message } if message.starts_with(prefix)),
        )
        .map(|vc| {
            router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("verdict").1
        })
        .collect()
}

fn lt(f: &VerifiableFunction, local: usize, v: i128) -> Formula {
    let name = crate::place_to_var_name(f, &Place::local(local));
    Formula::Lt(Box::new(Formula::Var(name, Sort::Int)), Box::new(Formula::Int(v)))
}

fn gt(f: &VerifiableFunction, local: usize, v: i128) -> Formula {
    let name = crate::place_to_var_name(f, &Place::local(local));
    Formula::Gt(Box::new(Formula::Var(name, Sort::Int)), Box::new(Formula::Int(v)))
}

/// A measured probe shape: callee, parameters, return type, the verdict message's
/// prefix, an optional literal last operand, and its guard (`0` none, `1` `s < 40`
/// on the second parameter, `2` a nonzero second parameter).
type Shape = (&'static str, &'static [P], P, &'static str, Option<ConstValue>, usize);

/// The scout's measured shapes, end to end. On a 32-bit carrier each family row is
/// REFUTED. Before the fix it was PROVED, which is the published Certified lie.
/// Preconditions stand in for the probes' guards (`if y == 0 { 0 } else { .. }`,
/// `if s < 40 { .. }`). The 64-bit twin of the guarded shift is PROVED, as it was:
/// `s < 40` is in range there.
#[test]
fn the_measured_32_bit_rows_are_refuted_end_to_end() {
    let shapes: [Shape; 7] = [
        (
            "core::num::<impl usize>::next_power_of_two",
            &[P::Usize],
            P::Usize,
            "next_power_of_two",
            None,
            0,
        ),
        (
            "core::num::<impl usize>::next_multiple_of",
            &[P::Usize, P::Usize],
            P::Usize,
            "next_multiple_of",
            None,
            2,
        ),
        ("core::num::<impl isize>::strict_neg", &[P::Isize], P::Isize, "strict_neg", None, 0),
        ("core::num::<impl isize>::strict_abs", &[P::Isize], P::Isize, "strict_abs", None, 0),
        ("<isize as core::ops::arith::Neg>::neg", &[P::Isize], P::Isize, "Neg::neg", None, 0),
        (
            "core::num::<impl usize>::strict_shl",
            &[P::Usize, P::U32],
            P::Usize,
            "strict_shl",
            None,
            1,
        ),
        (
            "core::num::<impl isize>::div_euclid",
            &[P::Isize],
            P::Isize,
            "div_euclid",
            Some(ConstValue::Int(-1)),
            0,
        ),
    ];
    for (callee, params, ret, prefix, literal, guard) in shapes {
        let build = |w: u32| {
            let c = Carrier::Bits(w);
            let mut args: Vec<Operand> = (1..=params.len()).map(param).collect();
            if let Some(lit) = &literal {
                args.push(Operand::Constant(lit.clone()));
            }
            let mut f = call_fn(
                callee,
                &params.iter().map(|p| ty(*p, c)).collect::<Vec<_>>(),
                ty(ret, c),
                args,
            );
            match guard {
                // `if y == 0 { 0 } else { x.next_multiple_of(y) }`
                2 => f.preconditions = vec![gt(&f, 2, 0)],
                // `if s < 40 { x.strict_shl(s) } else { 0 }`
                1 => f.preconditions = vec![lt(&f, 2, 40)],
                _ => {}
            }
            f
        };
        let v32 = verdicts(&build(32), prefix);
        assert!(!v32.is_empty(), "{callee} at 32 bits must mint its family row");
        assert!(
            v32.iter().all(|r| matches!(r, VerificationResult::Failed { .. })),
            "{callee} panics on a 32-bit target: its row must be REFUTED, got {v32:?}"
        );
    }
    // The host twin of the guarded shift: `s < 40 < 64` cannot panic on 64 bits.
    let mut sshl64 = call_fn(
        "core::num::<impl usize>::strict_shl",
        &[ty(P::Usize, Carrier::Bits(64)), ty(P::U32, Carrier::Bits(64))],
        ty(P::Usize, Carrier::Bits(64)),
        vec![param(1), param(2)],
    );
    sshl64.preconditions = vec![lt(&sshl64, 2, 40)];
    let v64 = verdicts(&sshl64, "strict_shl");
    assert!(!v64.is_empty());
    assert!(
        v64.iter().all(|r| matches!(r, VerificationResult::Proved { .. })),
        "`s < 40` cannot overflow a 64-bit shift: the host row stays PROVED, got {v64:?}"
    );
}

// ---- range counts ----------------------------------------------------------------

fn fixture_json() -> serde_json::Value {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/std_numeric_family/range_incl_count.json"
    );
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&text).expect("fixture MIR must deserialize")
}

/// `fn f(a: T, b: T) -> usize { (a..=b).count() }`. This is real extracted MIR
/// (`range_incl_count.json`, with `T = u64` on the 64-bit host), re-typed: the
/// element is spelled `elem` and typed `elem_ty`, and the `usize` destination is
/// typed `dest_ty`.
fn inclusive_count_fn(elem: &str, elem_ty: &Ty, dest_ty: &Ty) -> VerifiableFunction {
    let mut v = fixture_json();
    let to = |t: &Ty| serde_json::to_value(t).expect("Ty serializes");
    v["body"]["return_ty"] = to(dest_ty);
    let locals = v["body"]["locals"].as_array_mut().expect("locals");
    locals[0]["ty"] = to(dest_ty);
    locals[1]["ty"] = to(elem_ty);
    locals[2]["ty"] = to(elem_ty);
    for field in locals[3]["ty"]["Adt"]["fields"].as_array_mut().expect("range fields") {
        if field[0] == "start" || field[0] == "end" {
            field[1] = to(elem_ty);
        }
    }
    for block in v["body"]["blocks"].as_array_mut().expect("blocks") {
        if let Some(call) = block["terminator"].get_mut("Call") {
            let callee =
                call["func"].as_str().expect("callee").replace("<u64>", &format!("<{elem}>"));
            call["func"] = serde_json::Value::String(callee);
        }
    }
    serde_json::from_value(v).expect("re-typed fixture deserializes")
}

/// `fn f(a: T, b: T) -> usize { (a..b).count() }`: the same body, with the range
/// built by the `Range { start: a, end: b }` aggregate MIR uses for `a..b`.
fn exclusive_count_fn(elem: &str, elem_ty: &Ty, dest_ty: &Ty) -> VerifiableFunction {
    let mut f = inclusive_count_fn(elem, elem_ty, dest_ty);
    f.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "core::ops::range::Range".to_string(),
                variant: 0,
                active_field: None,
                args: None,
            },
            vec![param(1), param(2)],
        ),
        span: SourceSpan::default(),
    }];
    f.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
    if let Terminator::Call { func, .. } = &mut f.body.blocks[1].terminator {
        *func = func.replace("RangeInclusive", "Range");
    }
    if let Ty::Adt { name, fields, .. } = &mut f.body.locals[3].ty {
        *name = "core::ops::range::Range".to_string();
        fields.make_mut().retain(|(field, _)| field != "exhausted");
    }
    f
}

fn int(width: u32, signed: bool) -> Ty {
    Ty::Int { width, signed }
}

/// `count`'s bound is THIS target's `usize::MAX`, read from the call's `usize`
/// destination. Before the fix it was the 64-bit `2^64 - 1`. So on a 32-bit
/// target, `(a..=b).count()` over `usize` was PROVED. Over `u32` (and `(a..b)`
/// over `u64`) it got no row, because the gate read only the 64-bit answer. Each
/// panics "count overflowed usize" there.
#[test]
fn range_counts_are_bounded_by_the_targets_usize() {
    // `RangeInclusive<usize>` on 32 bits: SAT at `(0, usize::MAX)`.
    let f = inclusive_count_fn("usize", &int(32, false), &int(32, false));
    let Some((formula, kind)) = row(&f) else { panic!("usize count must mint a row") };
    assert!(matches!(kind, VcKind::Assertion { .. }), "{kind:?}");
    assert!(eval_bool(&formula, &env(&f, &[0, umax(32)])), "{}", formula.to_smtlib());
    assert!(!eval_bool(&formula, &env(&f, &[1, umax(32)])));

    // `RangeInclusive<u32>` on 32 bits: SAT at `(0, u32::MAX)`.
    let f = inclusive_count_fn("u32", &int(32, false), &int(32, false));
    let Some((formula, _)) = row(&f) else {
        panic!("u32 count on a 32-bit target must mint a row")
    };
    assert!(eval_bool(&formula, &env(&f, &[0, umax(32)])));

    // `Range<u64>` on 32 bits: SAT at `(0, 2^32)`, not at `(0, 2^32 - 1)`.
    let f = exclusive_count_fn("u64", &int(64, false), &int(32, false));
    let Some((formula, _)) = row(&f) else {
        panic!("u64 a..b count on a 32-bit target must mint a row")
    };
    assert!(eval_bool(&formula, &env(&f, &[0, 1 << 32])), "{}", formula.to_smtlib());
    assert!(!eval_bool(&formula, &env(&f, &[0, umax(32)])));

    // The 64-bit host is unchanged. These are total there and mint nothing:
    // `RangeInclusive<u32>` and `Range<u64>`.
    assert!(row(&inclusive_count_fn("u32", &int(32, false), &int(64, false))).is_none());
    assert!(row(&exclusive_count_fn("u64", &int(64, false), &int(64, false))).is_none());
    // `RangeInclusive<u64>` keeps its `2^64 - 1` row.
    let f = inclusive_count_fn("u64", &int(64, false), &int(64, false));
    let Some((formula, _)) = row(&f) else { panic!("u64 count on the host keeps its row") };
    assert!(eval_bool(&formula, &env(&f, &[0, umax(64)])));
    assert!(!eval_bool(&formula, &env(&f, &[1, umax(64)])));

    // A destination that does not fix the width is refused.
    let f = inclusive_count_fn(
        "usize",
        &Ty::PtrSizedInt { signed: false },
        &Ty::PtrSizedInt { signed: false },
    );
    assert!(unresolved(&row(&f)), "{:?}", row(&f).map(|(_, k)| k));
}

/// The 32-bit `RangeInclusive<usize>` count row is REFUTED end to end. Before the
/// fix it was PROVED. The host twin is still refuted at `(0, u64::MAX)`.
#[test]
fn the_32_bit_usize_range_count_is_refuted_end_to_end() {
    for w in [32, 64] {
        let f = inclusive_count_fn("usize", &int(w, false), &int(w, false));
        let v = verdicts(&f, "Iterator::count");
        assert!(
            !v.is_empty(),
            "{w}-bit usize count must mint its row; generate_vcs gave {:?}",
            generate_vcs(&f).iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
        assert!(
            v.iter().all(|r| matches!(r, VerificationResult::Failed { .. })),
            "`(0..=usize::MAX).count()` panics on a {w}-bit target: REFUTED, got {v:?}"
        );
    }
}

/// A NAME carries no target, so the name-only family, which the compiler asks
/// about a sysroot fn ITEM handed over as a type argument, answers for EVERY
/// pointer width a target can have (16, 32, 64). That is the deny-list's
/// fail-closed side. A count that is total at every pointer width stays out.
#[test]
fn the_name_only_range_count_family_answers_for_every_pointer_width() {
    let item = |family: &str, elem: &str| {
        format!(
            "<core::ops::range::{family}<{elem}> as core::iter::traits::iterator::Iterator>::count"
        )
    };
    for (family, elem) in [
        // panic on a 32-bit target
        ("Range", "u64"),
        ("Range", "i64"),
        ("RangeInclusive", "u32"),
        ("RangeInclusive", "i32"),
        // panic on a 16-bit target
        ("Range", "u32"),
        ("RangeInclusive", "u16"),
        ("Range", "char"),
        ("RangeInclusive", "char"),
        // panic on every target (unchanged)
        ("RangeInclusive", "usize"),
        ("RangeInclusive", "isize"),
        ("RangeInclusive", "u64"),
        ("Range", "u128"),
    ] {
        assert!(is_numeric_value_panic_callee(&item(family, elem)), "{family}<{elem}>::count");
    }
    for (family, elem) in [
        ("Range", "u8"),
        ("Range", "u16"),
        ("Range", "i16"),
        ("RangeInclusive", "u8"),
        ("RangeInclusive", "i8"),
        ("Range", "usize"),
        ("Range", "isize"),
    ] {
        assert!(
            !is_numeric_value_panic_callee(&item(family, elem)),
            "{family}<{elem}>::count is total at every pointer width"
        );
    }
}

// ---- `abs` on a signed-literal receiver (ABS-LIT-WIDTH-1) ------------------------
//
// THE LIE. `unwrap_panic::signed_abs_panic_body` took the row's width from
// `crate::operand_ty` of the receiver, which types a width-less signed literal
// (`ConstValue::Int`) as i64. `i32::MIN.abs()`, `let m = i32::MIN; m.abs()` and
// `const M: i32 = i32::MIN; M.abs()` all reach the call as the constant `-2^31`, so
// the row asked whether `-2^31 == i64::MIN`: UNSAT, published `proved` with
// clean-kernel `Certified` evidence, for a call that panics. Measured 2026-10-11 on a
// pre-fix stage 1 (`scratchpad/stage1-w22probe`): `i32::MIN.abs()`, `i16::MIN.abs()`
// and `(-128i8).abs()` were each `negation proved (Int { width: 64 })`, the default
// build exited 0, and the binary panicked "attempt to negate with overflow". On
// i686 and wasm32 `isize::MIN.abs()` was proved the same way.
//
// The width is now the OWNER's (`core::num::<impl iN>`); an `isize` owner reads the
// receiver's declared pointer width, then the `Self`-typed destination's, and is
// refused when neither fixes it.

/// `fn f() -> ret { <callee>(receiver) }`, with the call's destination `_0: ret`.
fn abs_lit_fn(callee: &str, receiver: i128, ret: Ty) -> VerifiableFunction {
    call_fn(callee, &[], ret, vec![Operand::Constant(ConstValue::Int(receiver))])
}

/// The `abs` arm's answer for the function's call.
fn abs_row(f: &VerifiableFunction) -> Option<SignedAbsRow> {
    let Terminator::Call { func: callee, args, dest, .. } = &f.body.blocks[0].terminator else {
        panic!("the fixture's first block makes the call");
    };
    signed_abs_panic_body(f, callee, args, dest)
}

/// The in-process verdicts of the function's `negation` rows, with each row's type.
fn negation_verdicts(f: &VerifiableFunction) -> Vec<(Ty, VerificationResult)> {
    let router = crate::test_router::deterministic_test_router();
    generate_vcs(f)
        .iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::NegationOverflow { ty } => Some((
                ty.clone(),
                router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("verdict").1,
            )),
            _ => None,
        })
        .collect()
}

/// A fixed-width owner is its own width, whatever `operand_ty` says of the literal.
#[test]
fn abs_of_a_signed_literal_is_built_at_the_owner_width() {
    for w in [8, 16, 32, 64] {
        let callee = format!("core::num::<impl i{w}>::abs");
        let f = abs_lit_fn(&callee, smin(w), int(w, true));
        let Some(SignedAbsRow::Modeled(body, ty)) = abs_row(&f) else {
            panic!("`i{w}::MIN.abs()` must be modeled, got {:?}", abs_row(&f));
        };
        assert_eq!(ty, int(w, true), "`i{w}::abs`'s row is built at {w} bits");
        assert!(eval_bool(&body, &[]), "`i{w}::MIN.abs()` panics: its violation must hold");
        let ok = abs_lit_fn(&callee, smin(w) + 1, int(w, true));
        let Some(SignedAbsRow::Modeled(body, _)) = abs_row(&ok) else {
            panic!("`(i{w}::MIN + 1).abs()` must be modeled");
        };
        assert!(!eval_bool(&body, &[]), "`(i{w}::MIN + 1).abs()` cannot panic");
    }
}

/// The scout's probe, end to end through the in-process solver: the literal
/// receiver's row is `NegationOverflow { Int { 32 } }` and REFUTED. Before the fix it
/// was `NegationOverflow { Int { 64 } }` and PROVED.
#[test]
fn abs_of_i32_min_literal_is_refuted_at_32_bits_end_to_end() {
    for (w, lit) in [(32, smin(32)), (16, smin(16)), (8, -128)] {
        let f = abs_lit_fn(&format!("core::num::<impl i{w}>::abs"), lit, int(w, true));
        let v = negation_verdicts(&f);
        assert_eq!(v.len(), 1, "`i{w}::MIN.abs()` mints one negation row, got {v:?}");
        assert_eq!(v[0].0, int(w, true), "the row is built at {w} bits, not 64");
        assert!(
            matches!(v[0].1, VerificationResult::Failed { .. }),
            "`{lit}i{w}.abs()` panics: its negation row must be REFUTED, got {:?}",
            v[0].1
        );
    }
    // `(-5i32).abs()` and `(i32::MIN + 1).abs()` stay proved.
    for lit in [-5, smin(32) + 1] {
        let v = negation_verdicts(&abs_lit_fn("core::num::<impl i32>::abs", lit, int(32, true)));
        assert_eq!(v.len(), 1, "{v:?}");
        assert!(
            matches!(v[0].1, VerificationResult::Proved { .. }),
            "`({lit}i32).abs()` cannot panic: PROVED, got {:?}",
            v[0].1
        );
    }
}

/// An `isize` owner with a signed-literal receiver: the literal declares no width,
/// so the row is built at the `Self`-typed destination's. 32 bits (i686, wasm32)
/// panics at `-2^31`; 64 bits (the host) does not, and panics at `-2^63`.
#[test]
fn abs_of_an_isize_literal_reads_the_destination_width() {
    const ISIZE_ABS: &str = "core::num::<impl isize>::abs";
    let modeled =
        |lit: i128, dest_w: u32| match abs_row(&abs_lit_fn(ISIZE_ABS, lit, int(dest_w, true))) {
            Some(SignedAbsRow::Modeled(body, ty)) => (eval_bool(&body, &[]), ty),
            other => panic!("`isize` literal with an Int({dest_w}) destination: {other:?}"),
        };
    assert_eq!(modeled(smin(32), 32), (true, int(32, true)), "32-bit: panics at -2^31");
    assert_eq!(modeled(smin(32), 64), (false, int(64, true)), "64-bit: -2^31 is fine");
    assert_eq!(modeled(smin(64), 64), (true, int(64, true)), "64-bit: panics at -2^63");
    // A place receiver declares its own width, which wins over the destination's.
    let f = call_fn(ISIZE_ABS, &[ty(P::Isize, Carrier::Bits(32))], int(32, true), vec![param(1)]);
    let Some(SignedAbsRow::Modeled(body, t)) = abs_row(&f) else { panic!("modeled") };
    assert_eq!(t, int(32, true));
    assert!(eval_bool(&body, &env(&f, &[smin(32)])));
    assert!(!eval_bool(&body, &env(&f, &[smin(32) + 1])));
}

/// Nothing fixes the width (a signed literal and a faithful `PtrSizedInt`
/// destination, or a faithful receiver and destination): REFUSED, never built at an
/// assumed width and never silently dropped (`abs` has no other row).
#[test]
fn abs_with_an_unresolved_isize_width_is_refused() {
    const ISIZE_ABS: &str = "core::num::<impl isize>::abs";
    let faithful = ty(P::Isize, Carrier::Faithful);
    let lit = abs_lit_fn(ISIZE_ABS, smin(32), faithful.clone());
    let place = call_fn(ISIZE_ABS, &[faithful.clone()], faithful, vec![param(1)]);
    for f in [&lit, &place] {
        match abs_row(f) {
            Some(SignedAbsRow::Refused(formula, VcKind::UnsupportedMir { kind, .. })) => {
                assert_eq!(kind, "pointer-width-unresolved");
                assert_eq!(formula, Formula::Bool(true), "the fail-closed formula");
            }
            other => panic!("an unresolved `isize` width must be refused, got {other:?}"),
        }
        let rows: Vec<_> = generate_vcs(f)
            .into_iter()
            .filter(|vc| {
                matches!(&vc.kind, VcKind::UnsupportedMir { kind, detail }
                    if kind == "pointer-width-unresolved" && detail.contains("`abs`"))
            })
            .collect();
        assert_eq!(rows.len(), 1, "the refusal reaches the generated rows exactly once");
        assert!(rows[0].obligation.is_none(), "a refusal records no obligation");
        assert!(
            !generate_vcs(f).iter().any(|vc| matches!(vc.kind, VcKind::NegationOverflow { .. })),
            "no negation row is built at an assumed width"
        );
    }
}

/// Only core's SIGNED `abs` is modeled: an unsigned owner, a user method and a
/// float `abs` mint nothing here.
#[test]
fn abs_row_needs_cores_signed_owner() {
    for callee in [
        "core::num::<impl u32>::abs_diff",
        "core::num::<impl u32>::abs",
        "user::Wrapper::abs",
        "core::f64::<impl f64>::abs",
    ] {
        let f = abs_lit_fn(callee, -5, int(32, true));
        assert!(abs_row(&f).is_none(), "`{callee}` is not core's signed `abs`");
    }
}

/// Only the WIDTH moved: a receiver with no signed-integer type still gets no `abs`
/// row here, as before (an `Unsupported` operand mints its own fail-closed row).
#[test]
fn abs_of_a_receiver_with_no_integer_type_mints_no_row() {
    let f = call_fn(
        "core::num::<impl i32>::abs",
        &[],
        int(32, true),
        vec![Operand::unsupported("Const::Opaque", "an operand with no type")],
    );
    assert!(abs_row(&f).is_none(), "an untyped receiver keeps today's answer");
}
