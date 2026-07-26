use trust_types::UnwindEdge;
use trust_types::{Formula, Sort};

use super::substitute_summary_params;

// forall i:Int. (x < i)   — `x` is a callee formal, `i` a spec quantifier var.
fn pre_forall_x_lt_i() -> Formula {
    Formula::forall(
        &[("i", Sort::Int)],
        Formula::Lt(
            Box::new(Formula::var("x", Sort::Int)),
            Box::new(Formula::var("i", Sort::Int)),
        ),
    )
}

#[test]
fn substitution_alpha_renames_to_avoid_capture() {
    // soundness (round-7): caller arg for `x` is itself a variable named
    // `i` — the SAME name as the quantifier binder. Naive substitution would
    // capture it into `(i < i)`; the binder must be alpha-renamed so the
    // caller's `i` stays FREE.
    let out = substitute_summary_params(
        &pre_forall_x_lt_i(),
        &[("x".to_string(), Formula::var("i", Sort::Int))],
    );
    match out {
        Formula::Forall(bindings, body) => {
            assert_eq!(bindings.len(), 1);
            let binder = bindings[0].0.as_str();
            assert_ne!(binder, "i", "capturing binder must be alpha-renamed");
            match body.as_ref() {
                Formula::Lt(lhs, rhs) => {
                    assert_eq!(
                        lhs.var_name(),
                        Some("i"),
                        "caller arg `i` must remain FREE, not captured"
                    );
                    assert_eq!(
                        rhs.var_name(),
                        Some(binder),
                        "bound occurrence must use the renamed binder"
                    );
                }
                other => panic!("expected Lt body, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn substitution_keeps_binder_when_no_capture() {
    // Control: the replacement value shares no name with the binder, so the
    // binder is preserved and substitution proceeds normally.
    let out = substitute_summary_params(
        &pre_forall_x_lt_i(),
        &[("x".to_string(), Formula::var("y", Sort::Int))],
    );
    match out {
        Formula::Forall(bindings, body) => {
            assert_eq!(bindings[0].0.as_str(), "i", "binder unchanged when safe");
            match body.as_ref() {
                Formula::Lt(lhs, rhs) => {
                    assert_eq!(lhs.var_name(), Some("y"));
                    assert_eq!(rhs.var_name(), Some("i"));
                }
                other => panic!("expected Lt body, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn place_names_overlap_prefix_semantics() {
    use super::place_names_overlap as ov;
    // Equal, ancestor, descendant -> overlap (a write to one invalidates the other).
    assert!(ov("x", "x"));
    assert!(ov("x", "x.0"), "whole-value write must invalidate field facts");
    assert!(ov("x.0", "x"), "field write must invalidate the whole-value fact");
    assert!(ov("x", "x[0]"), "index child overlaps");
    assert!(ov("x", "x.0.1"));
    // Siblings and unrelated names -> NO overlap (independent locations).
    assert!(!ov("x.0", "x.1"), "sibling fields are independent");
    assert!(!ov("x", "y"));
    assert!(!ov("x", "xy"), "shared prefix without a projection boundary is not overlap");
    assert!(!ov("x.0", "x.01"));
    // Symbolic array-index aliasing (round-12): a symbolic-index write may hit
    // ANY element of the same array, so it overlaps any other index; distinct
    // LITERAL indices stay independent.
    assert!(ov("a[_k]", "a[_j]"), "symbolic sibling indices may alias");
    assert!(ov("a[_k]", "a[5]"), "a symbolic write may hit a literal slot");
    assert!(ov("a[5]", "a[_j]"), "a literal fact is killed by a symbolic write");
    assert!(!ov("a[5]", "a[7]"), "distinct literal slots are independent");
    assert!(!ov("a[_k]", "b[_j]"), "different arrays do not alias");
    // Nested arrays (round-13): a symbolic index at ANY depth aliases same-base
    // siblings; all-literal nested paths stay precise.
    assert!(ov("a[0][_k]", "a[0][_j]"), "symbolic INNER index may alias");
    assert!(!ov("a[0][1]", "a[0][2]"), "all-literal nested indices stay precise");
}

#[test]
fn write_covers_derived_slice_len_semantics() {
    // Trust (P0 false-refutation, 2026-07-02): the version oracle must
    // attribute a write of the SYNTHETIC `{dest}__slice_len` metadata name to
    // the statement that (re)assigns the WHOLE pointer/reference `dest` — the
    // block-def extraction emits `Eq({dest}__slice_len, referent_len)` there,
    // and `writes_until` counts that lhs as written. Without this the read
    // token was the phantom `s{b}_pre` while the tie def stayed bare, so the
    // guarded `&mut [T]` FakeForPtrMetadata bounds proof false-refuted.
    use super::write_covers_derived_slice_len as w;
    // A whole-local write covers its own derived metadata name.
    assert!(w("_6", "_6__slice_len"), "borrow dest must cover its derived slice-len");
    assert!(w("dst", "dst__slice_len"));
    // An ANCESTOR write rewrites the slice-typed field, hence its metadata.
    assert!(w("agg", "agg.0__slice_len"), "whole-aggregate write covers field metadata");
    // An ELEMENT/pointee store preserves length metadata — must NOT cover
    // (a phantom write here would re-version reads away from the live tie).
    assert!(!w("dst*[_2]", "dst__slice_len"), "element store must not cover the length");
    assert!(!w("dst*", "dst__slice_len"), "pointee store must not cover the length");
    // Unrelated locals / non-derived names.
    assert!(!w("_5", "_6__slice_len"));
    assert!(!w("_6", "_6"), "non-derived names are the plain overlap's job");
    assert!(!w("_60", "_6__slice_len"), "no projection boundary => no cover");
}

#[test]
fn mut_pointer_param_pointee_havoced_at_call() {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
        VerifiableBody, VerifiableFunction,
    };
    // fn f(r: &mut u32) { g(r) } — `r` is a &mut PARAMETER (no syntactic
    // `&mut x` statement), so mutably_borrowed_local_names misses it. The
    // Call g(r) can mutate `*r`, so terminator_def_names must still havoc the
    // pointee `r*` (round-12 fix #3).
    let func = VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                    name: Some("r".into()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "g".into(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let kills = super::terminator_def_names(&func, &func.body.blocks[0]);
    assert!(
        kills.iter().any(|n| n == "r*" || n == "r"),
        "a Call must havoc the &mut parameter pointee; kills = {kills:?}"
    );
}

#[test]
fn ty_contains_mut_pointer_recurses_aggregates() {
    use trust_types::Ty;

    use super::ty_contains_mut_pointer as c;
    let mref = || Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) };
    let rawmut = || Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) };
    assert!(c(&mref()));
    assert!(c(&rawmut()));
    assert!(c(&Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "W".into(),
        fields: vec![("p".into(), mref())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }));
    assert!(c(&Ty::Tuple(vec![Ty::u32(), rawmut()])));
    assert!(c(&Ty::Array { elem: Box::new(mref()), len: 4 }));
    // No mutable pointer anywhere -> false.
    assert!(!c(&Ty::u32()));
    assert!(!c(&Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "P".into(),
        fields: vec![("v".into(), Ty::u32())],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, }));
    // A shared `&` is NOT recursed into (cannot drive a mutation).
    assert!(!c(&Ty::Ref { mutable: false, inner: Box::new(mref()) }));
}

#[test]
fn mut_pointer_nested_in_aggregate_havoced_at_call() {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
        VerifiableBody, VerifiableFunction,
    };
    // fn f(s: Wrapper { p: &mut u32 }) { g(s) } — the &mut is NESTED in a
    // non-reference Adt local: no syntactic `&mut x` statement and the local's
    // top-level type is not a pointer. The Call must still havoc `s` (whose
    // prefix-overlap kills the nested pointee fact `s.0*`). Round-13 fix.
    let wrapper = Ty::Adt { adt_kind: None, layout: None, 
        variants: Vec::new(),
        name: "Wrapper".into(),
        fields: vec![("p".into(), Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) })],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    let func = VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: wrapper, name: Some("s".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "g".into(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let kills = super::terminator_def_names(&func, &func.body.blocks[0]);
    assert!(
        kills.iter().any(|n| n == "s"),
        "a Call must havoc an aggregate local carrying a nested &mut (prefix-kills \
         the nested pointee `s.0*`); kills = {kills:?}"
    );
}

#[test]
fn int_op_type_recovers_width_from_nonconst_operand() {
    use trust_types::{
        ConstValue, LocalDecl, Operand, Place, SourceSpan, Ty, VerifiableBody,
        VerifiableFunction,
    };
    // `100i8 + x` (x: i8): a SIGNED constant loses its width at extraction
    // (operand_ty fabricates i64), so the overflow bound must be recovered from
    // the non-constant operand `x` (round-19). Otherwise `100 + x` is checked
    // at the i64 boundary and a real i8 overflow (x = 127 -> 227) is missed.
    let func = VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::i8(), name: Some("x".into()) },
            ],
            blocks: vec![],
            arg_count: 1,
            return_ty: Ty::i8(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let c = Operand::Constant(ConstValue::Int(100));
    let x = Operand::Copy(Place::local(1));
    // Sanity: the bare signed constant fabricates width 64.
    assert_eq!(crate::operand_ty(&func, &c).and_then(|t| t.int_width()), Some(64));
    // Recovery: const+var and var+const both yield the true i8 (8, signed).
    assert_eq!(super::int_op_type(&func, &c, &x), Some((8, true)));
    assert_eq!(super::int_op_type(&func, &x, &c), Some((8, true)));
}

#[test]
fn shift_overflow_uses_dest_width_for_constant_shifted_value() {
    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
    };
    // `r: i32 = 1i32 << n`: the shifted value `1i32` is a signed constant that
    // loses its width (fabricated i64), so the UB check would be `n >= 64` and
    // miss `32 <= n < 64`. The shift width must be recovered from the dest
    // `r: i32` (round-19), making the check `n >= 32`.
    let func = VerifiableFunction {
        name: "f".into(),
        def_path: "f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("r".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("n".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Shl,
                        Operand::Constant(ConstValue::Int(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let vcs = super::generate_vcs(&func);
    let shift_vc = vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::ShiftOverflow { .. }))
        .expect("expected a ShiftOverflow VC for `1i32 << n`");
    let dbg = format!("{:?}", shift_vc.formula);
    assert!(
        dbg.contains("Int(32)"),
        "shift UB bound must be the dest i32 width (32), not the fabricated i64; got {dbg}"
    );
    assert!(
        !dbg.contains("Int(64)"),
        "shift UB bound must NOT be 64 (the lost-width fabrication); got {dbg}"
    );
}

#[test]
fn foreign_flagged_call_fails_closed_even_without_name_marker() {
    use trust_types::{
        BasicBlock, BlockId, Formula, LocalDecl, Place, SourceSpan, Terminator, Ty, VcKind,
        VerifiableBody, VerifiableFunction,
    };
    // round-19 #3: an `extern { fn compute_hash(); }` import has no
    // libc/extern/ffi token in its path and is not a known builtin, so
    // name-substring detection (`is_extern_call`) misses it. With
    // `is_foreign: true` (set at extraction from tcx.is_foreign_item) it
    // must STILL route into the FFI path and fail closed (round-19 #4), so
    // the caller is not silently Proved over an unchecked foreign boundary.
    let build = |is_foreign: bool| VerifiableFunction {
        name: "caller".into(),
        def_path: "caller".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("r".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "compute_hash".into(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign,
                        is_unsafe_sig: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    // is_foreign=true -> conservative fail-closed FFI obligation present.
    let vcs = super::generate_vcs(&build(true));
    assert!(
        vcs.iter().any(|vc| matches!(&vc.kind, VcKind::FfiBoundaryViolation { .. })
            && vc.formula == Formula::Bool(true)),
        "foreign-flagged call must emit a fail-closed FFI obligation; got {vcs:?}"
    );
    // Control: without the flag, the unrecognized name is NOT detected as
    // FFI by name alone — this is precisely the gap the flag closes.
    let vcs_noflag = super::generate_vcs(&build(false));
    assert!(
        !vcs_noflag.iter().any(|vc| matches!(&vc.kind, VcKind::FfiBoundaryViolation { .. })),
        "control: unflagged unrecognized call is invisible to name detection; got {vcs_noflag:?}"
    );
}
