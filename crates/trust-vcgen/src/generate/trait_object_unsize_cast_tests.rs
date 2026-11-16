//! A trait-object POINTER unsize (`&T -> &dyn Trait`) carries NO obligation.
//!
//! Regression pin for commit d806992cd4 ("vtable slice 1 (ORACLE ONLY)"). That
//! commit taught `trust-mir-extract`'s `convert.rs` to spell the coercion
//! `Rvalue::Cast(op, &dyn Trait)` instead of `Use(OpaqueConst)`, so the oracle
//! could keep the fat pointer's real DATA lane. It was labelled ORACLE ONLY, but
//! `convert.rs` feeds THIS lane too, and this lane's cast accept-list had no arm
//! for a `Ty::Dynamic` target — so every `&T -> &dyn Trait` in the program fell
//! through to `unsupported_mir` and poisoned its whole enclosing function. Seven
//! `tests/ui/trust/dyn_*` fixtures went red; they are the end-to-end reachability
//! proof and this module is the unit-level pin.
//!
//! The tests below pin: (1) the coercion mints NO `unsupported_mir` VC, via the
//! production `generate_v2_safety_vcs` entry point rather than the predicate; and
//! (2) the fail-closed twin — a pointer cast that is NOT a trait-object unsize
//! still mints its refusal, so the fix widened nothing beyond the coercion.

use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
    VerifiableBody, VerifiableFunction, VerificationCondition,
};

use super::{generate_v2_safety_vcs, unsupported_mir_vcs};

/// `fn go(src: &S) -> <ret>` whose bb0 is a single `_0 = _1 as <target>` — the
/// exact statement shape `convert.rs` emits for `PointerCoercion::Unsize` since
/// d806992cd4.
fn cast_fn(target: Ty) -> VerifiableFunction {
    let source = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Adt {
            name: "test::S".to_string(),
            fields: vec![].into(),
            variants: vec![].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            layout: None,
            enum_layout: None,
            adt_kind: Some(trust_types::AdtKind::Struct),
            arbitrary_precision: None,
            validity_wrapper: None,
        }),
    };
    VerifiableFunction {
        name: "go".to_string(),
        def_path: "test::go".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: target.clone(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: source, name: Some("src".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), target.clone()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: target,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Both production emitters that refuse a cast. The compiler runs BOTH, which is
/// why one coercion produced a PAIR of obligations in the ui reports — the
/// `bb0 stmt 0` spelling comes from `generate_v2_safety_vcs` (checked_vcs.rs) and
/// the `bb0 stmt0` spelling from `unsupported_mir_vcs` (slice_conversion.rs, via
/// the `unsupported.rs` context). A fix that taught only one would halve the
/// obligations and still leave every fixture red, so both are exercised here.
fn unsupported_cast_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_v2_safety_vcs(func)
        .into_iter()
        .chain(unsupported_mir_vcs(func))
        .filter(|vc| format!("{vc:?}").contains("unsupported cast"))
        .collect()
}

fn dyn_ref(mutable: bool) -> Ty {
    Ty::Ref {
        mutable,
        inner: Box::new(Ty::Dynamic {
            trait_name: "test::T".to_string(),
            principal_key: Some("test::T".to_string()),
        }),
    }
}

#[test]
fn trait_object_pointer_unsize_mints_no_obligation() {
    for (label, target) in [
        ("&dyn T", dyn_ref(false)),
        ("&mut dyn T", dyn_ref(true)),
        (
            "*const dyn T",
            Ty::RawPtr {
                mutable: false,
                pointee: Box::new(Ty::Dynamic {
                    trait_name: "test::T".to_string(),
                    principal_key: Some("test::T".to_string()),
                }),
            },
        ),
        (
            "*mut dyn T",
            Ty::RawPtr {
                mutable: true,
                pointee: Box::new(Ty::Dynamic {
                    trait_name: "test::T".to_string(),
                    principal_key: Some("test::T".to_string()),
                }),
            },
        ),
    ] {
        let vcs = unsupported_cast_vcs(&cast_fn(target));
        assert!(
            vcs.is_empty(),
            "`&S -> {label}` is an infallible vtable attach and must mint no \
             unsupported-cast obligation; got {} ({vcs:?})",
            vcs.len()
        );
    }
}

/// The guard this fix must NOT have widened. The new arm is keyed on a `Dynamic`
/// pointee behind a `Ref`/`RawPtr`, which is the ONLY shape `convert.rs` emits for
/// `PointerCoercion::Unsize` — a BARE `Dynamic` target is not that coercion and
/// must keep failing closed. Planting it proves the arm requires the pointer
/// shape rather than merely spotting `Ty::Dynamic` anywhere in the target.
#[test]
fn bare_dynamic_cast_target_still_fails_closed() {
    let target = Ty::Dynamic {
        trait_name: "test::T".to_string(),
        principal_key: Some("test::T".to_string()),
    };
    let vcs = unsupported_cast_vcs(&cast_fn(target));
    assert!(
        !vcs.is_empty(),
        "a bare (non-pointer) `dyn Trait` cast target is not the unsize coercion \
         and must stay fail-closed"
    );
}
