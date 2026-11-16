use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::terminator_def_names;

/// `fn f(r: &mut u32, a: u32)` with a `&mut x`-style borrow statement and a
/// call terminator whose args we vary.
fn call_func(args: Vec<Operand>, extra_stmt: Option<Statement>) -> VerifiableFunction {
    let mut stmts = vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(4) },
        span: SourceSpan::default(),
    }];
    stmts.extend(extra_stmt);
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "test::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::Int { width: 32, signed: false }),
                    },
                    name: Some("r".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 32, signed: false },
                    name: Some("a".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::Int { width: 32, signed: false }),
                    },
                    name: None,
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Int { width: 32, signed: false },
                    name: Some("x".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts,
                terminator: Terminator::Call {
                    unwind: UnwindEdge::Unreachable,
                    func: "test::callee".to_string(),
                    args,
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: crate::sep_engine::tests::fixture_key("test::callee"),
                    is_foreign: false,
                },
            }],
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

/// Pure-scalar args (a Copy u32 + a constant): the dest — and its OWN derived
/// slice-length metadata name, which the callee's write to `dest` also invalidates —
/// is killed, and so is everything of the whole-function list except the protected,
/// pointer-free `&mut` PARAMETER `r` that never leaves the body (TINV-18 correction,
/// coarse rule, `path_defs::escape_havoc`): the `&mut`-borrowed stack local `x`, its
/// derived length, and the `&mut` temp `_3` are havocked (a callee may reach a stack
/// local's borrow through channels the fine-grained rule missed). Guard facts on `*r`
/// survive, which is what the exact-equality assertion pins: `r` appearing here would
/// be the fast path lost; `x` missing would be CALL-HAVOC-ESCAPE-1 reopened. No
/// index-segment fallback `_0` here: nothing in this body indexes BY the
/// destination, so there is no `..[_0]..` name for it to reach (round A10,
/// `local_is_index_operand` — the fallback is minted only where it can rebind
/// something; see `scalar_args_dest_used_as_an_index_mints_its_fallback`).
#[test]
fn scalar_args_skip_the_global_havoc() {
    let func = call_func(
        vec![Operand::Copy(Place::local(2)), Operand::Constant(ConstValue::Uint(7, 32))],
        None,
    );
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert_eq!(
        names,
        ["x", "x__slice_len", "_3", "ret", "ret__slice_len"].map(String::from).to_vec(),
        "everything but the protected parameter `r`; got {names:?}"
    );
}

/// The same fast path when the destination IS an index operand somewhere in the
/// body (`x = (*r)[ret]`): a place name indexed BY the destination (`r*[_0]`) must
/// re-version after the call exactly as it does after an `Assign`, so the
/// index-segment fallback `_0` joins the kill — and, as before, the protected
/// parameter `r` does not.
#[test]
fn scalar_args_dest_used_as_an_index_mints_its_fallback() {
    let indexed_read = Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: 1,
            projections: vec![trust_types::Projection::Deref, trust_types::Projection::Index(0)],
        })),
        span: SourceSpan::default(),
    };
    let func = call_func(
        vec![Operand::Copy(Place::local(2)), Operand::Constant(ConstValue::Uint(7, 32))],
        Some(indexed_read),
    );
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert_eq!(
        names,
        ["x", "x__slice_len", "_3", "ret", "ret__slice_len", "_0"].map(String::from).to_vec(),
        "the dest, its derived metadata and its index fallback; got {names:?}"
    );
}

/// A `&mut`-typed arg keeps the FULL havoc (the callee-write class).
#[test]
fn mut_ref_arg_keeps_full_havoc() {
    let func = call_func(vec![Operand::Copy(Place::local(1))], None);
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(names.len() > 1, "full havoc expected; got {names:?}");
    assert!(names.iter().any(|n| n == "r"), "the &mut param must be havoced");
    assert!(names.iter().any(|n| n == "x"), "the &mut-borrowed local must be havoced");
}

/// The FULL-havoc path must kill the dest's derived slice-length name too.
///
/// Not reachable from Rust source — rustc always interposes a temp
/// (`_9 = f(); _3 = move _9`), so the dest of a `Call` is a fresh local with no
/// tie, and the statement channel catches the follow-up. It IS reachable from
/// every other TrustIR producer (trust-lift, hand-built bodies like this one),
/// where a `Call { dest }` may name a slice local a previous block tied to an
/// array's length — and then the callee's write to `dest` replaces the fat
/// pointer while the tie survives. Its sibling on the pure-scalar fast path is
/// pinned by `scalar_args_skip_the_global_havoc`'s exact-equality assertion; this
/// is the same property on the branch that actually runs for pointer-carrying
/// calls, and the two sites are independently mutable.
#[test]
fn full_havoc_kills_the_dest_derived_slice_len() {
    let func = call_func(vec![Operand::Copy(Place::local(1))], None);
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(names.iter().any(|n| n == "ret"), "the dest must be havoced; got {names:?}");
    assert!(
        names.iter().any(|n| n == "ret__slice_len"),
        "the dest's derived slice-length metadata must be havoced too — the callee \
         writes a whole new value into `dest`, so a slice-typed dest gets new length \
         metadata; got {names:?}"
    );
}

/// A Move arg fails closed (ownership escapes into the callee).
#[test]
fn move_arg_keeps_full_havoc() {
    let func = call_func(vec![Operand::Move(Place::local(2))], None);
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(names.len() > 1, "full havoc expected; got {names:?}");
}

/// An in-function raw-pointer laundering site (`&raw`/cast-to-raw) fails
/// the skip for the WHOLE function even with pure-scalar args: the local's
/// address could have been smuggled through an integer to an earlier callee.
#[test]
fn pointer_laundering_site_keeps_full_havoc() {
    let func = call_func(
        vec![Operand::Copy(Place::local(2))],
        Some(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::AddressOf(true, Place::local(4)),
            span: SourceSpan::default(),
        }),
    );
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(names.len() > 1, "laundering must fail the skip; got {names:?}");
}

/// A function whose ONLY write to the slice local `s` is a plain
/// `Rvalue::Use` — the shape that mints the def name `s` and never `s__slice_len`.
fn slice_reassign_func(rvalue: Rvalue) -> VerifiableFunction {
    let slice_ref = || Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) }),
    };
    VerifiableFunction {
        name: "g".to_string(),
        def_path: "test::g".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: slice_ref(), name: Some("t".into()) },
                LocalDecl { index: 2, ty: slice_ref(), name: Some("s".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue,
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
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

/// The POINT-IN-BLOCK write oracle must report the derived slice-length name.
///
/// `writes_until` answers "what has been written by `stmts[..i]`?" for the
/// statement-granular version token, and it builds its set from
/// `formula_def_name` over the extracted definitions — which for an
/// `Rvalue::Use` reassignment yields `s` and never `s__slice_len`. A caller that
/// asks at a point AFTER the reassignment would otherwise be told the length
/// metadata is still at its entry version, re-uniting a later read with the tie
/// the reassignment invalidated. Reached from Rust source only when the read and
/// the reassignment share a block; hand-built here so the site is pinned
/// regardless.
#[test]
fn writes_until_reports_the_derived_slice_len() {
    let func = slice_reassign_func(Rvalue::Use(Operand::Copy(Place::local(1))));
    let before = super::writes_until(&func, &func.body.blocks[0], 0);
    assert!(before.is_empty(), "nothing is written before stmt 0; got {before:?}");
    let after = super::writes_until(&func, &func.body.blocks[0], 1);
    assert!(after.contains("s"), "the reassigned local must be reported; got {after:?}");
    assert!(
        after.contains("s__slice_len"),
        "reassigning `s` replaces its length metadata, so the point-in-block write \
         set must name `s__slice_len`; got {after:?}"
    );
}

/// `Drop` glue and an `Opaque` terminator run arbitrary code with the same
/// reseat reach as a `Call`, so both must kill the `&mut`-borrowed roots' derived
/// slice-length names too.
///
/// Written against the terminator registry directly because neither arm is
/// reachable from the Rust shapes the fixture corpus covers: `Drop` needs a
/// `impl Drop` that reseats a `&mut &[T]` field, and `Opaque` is minted for
/// constructs (inline asm, unlowered yields) the extractor does not produce for a
/// slice-carrying body. Sharing one helper across the three arms is a code
/// property, not a verdict property — this is the verdict property, per arm.
#[test]
fn drop_and_opaque_kill_the_derived_slice_len_of_mut_borrowed_roots() {
    let mut func = call_func(vec![Operand::Copy(Place::local(1))], None);
    for (label, terminator) in [
        (
            "Drop",
            Terminator::Drop {
                place: Place::local(3),
                target: BlockId(1),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Unreachable,
            },
        ),
        (
            "Opaque",
            Terminator::Opaque {
                kind: "test".into(),
                targets: vec![BlockId(1)],
                span: SourceSpan::default(),
            },
        ),
    ] {
        func.body.blocks[0].terminator = terminator;
        let names = terminator_def_names(&func, &func.body.blocks[0]);
        assert!(
            names.iter().any(|n| n == "x"),
            "{label}: the &mut-borrowed local must be havoced; got {names:?}"
        );
        assert!(
            names.iter().any(|n| n == "x__slice_len"),
            "{label}: arbitrary code holding `&mut x` may store a whole new fat \
             pointer into it, so its derived length metadata must be havoced too; \
             got {names:?}"
        );
    }
}
