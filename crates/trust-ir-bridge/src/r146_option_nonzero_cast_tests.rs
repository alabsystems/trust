//! R146-SPELLING-1: the R146 arm of `Rvalue::Cast` (an integer cast into
//! `Option<NonZero<..>>`, which the extractor's total-niche gate admits for
//! `NonZero::new`'s transmute) lowers as one obligation-free havoc of the Option type.
//!
//! The arm used to test the target's NAME against `std::option::Option<std::num::NonZero<`
//! and `core::option::Option<core::num::NonZero<`. The extractor prints an ADT's name
//! without its generic arguments (`core::option::Option`, the payload typed
//! `core::num::nonzero::NonZero`), and under the unauthenticated-crate stamp for a `core`
//! loaded from outside the sysroot (`__trust_crate@<id>::core::option::Option`), so the
//! arm matched no extracted input (measured on stage 1, 2026-11-10: `NonZero::new` and a
//! direct transmute, resident and `--extern core=<copy>`). On the logical lane the miss
//! fell to the struct-destination arm, whose fresh `Undef` is the same fact-free value;
//! on the faithful lane, where the Option maps to a first-class `Enum`, it fell to the
//! default `Cast { Bitcast, u32 -> enum }`, which the validator accepts on the enum's
//! layout evidence but the reference interpreter refuses ("destination enum has no bit
//! width"): an instruction with no execution meaning where R146 meant a havoc.
//!
//! These tests pin the extracted spellings the arm now claims, on both lanes, and the
//! controls it must leave alone.

use trust_ir::inst::Inst;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty as IrTy;
use trust_ir::{InstrNode, Module};
use trust_ir_build::validate_module;
use trust_types::{
    AdtKind, AdtLayoutInfo, BasicBlock, BlockId, EnumLayoutInfo, EnumTagEncodingInfo, LocalDecl,
    Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty, ValidityWrapper, VariantDef,
    VerifiableBody, VerifiableFunction,
};

use crate::lower::lower_to_trust_ir;

/// `fn cast_fn(a: From) -> To { a as To }`, the extractor's spelling of a transmute.
fn cast_fn(from: Ty, to: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "cast_fn".to_string(),
        def_path: "test::cast_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: to.clone(), name: None },
                LocalDecl { index: 1, ty: from, name: Some("a".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), to.clone()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: to,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `NonZero<u32>` as the extractor spells it: a one-field struct named `name`,
/// stamped `NonZero` by its diagnostic item when `stamped`.
fn nonzero_u32(name: &str, stamped: bool) -> Ty {
    let mut ty = Ty::adt(name, vec![("0".to_string(), Ty::u32())]);
    if stamped {
        let Ty::Adt { validity_wrapper, .. } = &mut ty else { unreachable!() };
        *validity_wrapper = Some(ValidityWrapper::NonZero);
    }
    ty
}

/// `Option<payload>` as the extractor spells it on the LOGICAL lane: an enum ADT named
/// `name` (no generic arguments), `None` then `Some(payload)`.
fn option_of(name: &str, payload: Ty) -> Ty {
    Ty::adt_enum(
        name,
        vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), payload)],
            },
        ],
    )
}

/// The same Option on the FAITHFUL lane: first-class, with its niche layout
/// (`None` is the zero niche of the `u32` scalar, `Some` the untagged variant), and
/// the payload struct carrying its own concrete layout, as that lane extracts it.
fn faithful_option_of(name: &str, mut payload: Ty) -> Ty {
    let Ty::Adt { layout, .. } = &mut payload else { panic!("the payload is an ADT") };
    *layout = Some(Box::new(AdtLayoutInfo {
        size: 4,
        align: 4,
        field_offsets: vec![0],
        repr: "transparent".to_string(),
    }));
    let mut ty = option_of(name, payload);
    let Ty::Adt { faithful_enum_repr, enum_layout, adt_kind, .. } = &mut ty else { unreachable!() };
    *faithful_enum_repr = Some(None);
    *adt_kind = Some(AdtKind::Enum);
    *enum_layout = Some(Box::new(EnumLayoutInfo {
        encoding: EnumTagEncodingInfo::Niche {
            untagged_variant: 1,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: trust_types::EnumReprHint::U32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![], vec![0]],
    }));
    ty
}

/// The lowered module, or the bridge's refusal rendered as text.
fn try_lower(func: &VerifiableFunction) -> Result<Module, String> {
    let module = lower_to_trust_ir(func).map_err(|error| format!("bridge: {error:?}"))?;
    let errors = validate_module(&module);
    if errors.is_empty() { Ok(module) } else { Err(format!("validator: {errors:?}")) }
}

fn nodes(module: &Module) -> Vec<&InstrNode> {
    assert_eq!(module.functions.len(), 1, "one fixture function");
    module.functions[0].blocks.iter().flat_map(|block| block.body.iter()).collect()
}

/// What the cast lowered to, as the kinds of its instructions.
fn shape(module: &Module) -> Vec<&'static str> {
    nodes(module)
        .iter()
        .map(|node| match &node.inst {
            Inst::Undef { .. } => "Undef",
            Inst::Cast { .. } => "Cast",
            Inst::Assert { .. } => "Assert",
            Inst::ICmp { .. } => "ICmp",
            Inst::MakeAggregate { .. } => "MakeAggregate",
            Inst::Const { .. } => "Const",
            _ => "other",
        })
        .collect()
}

/// Apart from the `Return`, the cast is one fresh `Undef` of the destination's own type,
/// stamped `FreshSymbolicHavoc`; nothing is cast, compared, asserted or constructed.
fn assert_one_stamped_havoc(label: &str, module: &Module) {
    let nodes = nodes(module);
    let body: Vec<&&InstrNode> =
        nodes.iter().filter(|node| !matches!(node.inst, Inst::Return { .. })).collect();
    let [havoc] = body.as_slice() else {
        panic!("{label}: exactly one instruction before the return, got {:?}", shape(module))
    };
    let Inst::Undef { ty } = &havoc.inst else {
        panic!("{label}: an Undef, got {:?}: {havoc:?}", shape(module))
    };
    assert!(
        matches!(ty, IrTy::Struct(_) | IrTy::Enum(_)),
        "{label}: the havoc is at the Option's own type: {ty:?}"
    );
    assert!(
        havoc.proofs.iter().any(|proof| matches!(proof, ProofAnnotation::FreshSymbolicHavoc)),
        "{label}: the havoc is stamped FreshSymbolicHavoc: {havoc:?}"
    );
}

/// Every spelling of `Option<NonZero<u32>>` R146 claims: the two the extractor writes
/// (measured on stage 1: the resident `core`, and a `core` loaded with `--extern` from
/// outside the sysroot, both names under the unauthenticated-crate stamp), the `std`
/// re-export, and the generic-argument spellings the arm used to list.
fn option_of_nonzero_spellings() -> Vec<(&'static str, &'static str)> {
    vec![
        ("core::option::Option", "core::num::nonzero::NonZero"),
        (
            "__trust_crate@ab5530104a8de1b8::core::option::Option",
            "__trust_crate@ab5530104a8de1b8::core::num::nonzero::NonZero",
        ),
        ("std::option::Option", "std::num::NonZero"),
        ("core::option::Option<core::num::NonZero<u32>>", "core::num::NonZero"),
        ("std::option::Option<std::num::NonZero<u32>>", "std::num::NonZero"),
    ]
}

/// R146-SPELLING-1: every spelling, payload stamped or not, on both lanes, lowers to
/// the one stamped havoc. Before, the two extracted spellings missed the arm: the
/// logical lane still got a havoc (the struct-destination arm), the faithful lane got
/// the uninterpretable `Bitcast` instead, which this test refuses.
#[test]
fn r146_claims_every_option_of_nonzero_spelling_on_both_lanes() {
    for (option, nonzero) in option_of_nonzero_spellings() {
        for stamped in [true, false] {
            for (lane, to) in [
                ("logical", option_of(option, nonzero_u32(nonzero, stamped))),
                ("faithful", faithful_option_of(option, nonzero_u32(nonzero, stamped))),
            ] {
                let label = format!("{lane} {option} (payload stamped: {stamped})");
                let module = try_lower(&cast_fn(Ty::u32(), to))
                    .unwrap_or_else(|error| panic!("{label}: must lower and validate: {error}"));
                assert_one_stamped_havoc(&label, &module);
            }
        }
    }
}

/// The payload is recognized by the extractor's identity stamp alone: a `NonZero` that
/// prints under a name no spelling lists (a `#![no_core]` crate's own diagnostic item)
/// is claimed when stamped, and the same name unstamped is not.
#[test]
fn r146_reads_the_payloads_identity_stamp() {
    for stamped in [true, false] {
        let to = faithful_option_of("core::option::Option", nonzero_u32("mycore::Nz", stamped));
        let module = try_lower(&cast_fn(Ty::u32(), to)).expect("the fixture lowers");
        if stamped {
            assert_one_stamped_havoc("stamped mycore::Nz payload", &module);
        } else {
            assert_eq!(
                shape(&module).first().copied(),
                Some("Cast"),
                "an unstamped, unlisted payload is not NonZero to R146: {:?}",
                shape(&module)
            );
        }
    }
}

/// CONTROLS. R146 claims an Option of NonZero only: an Option of a plain integer, an
/// enum that is not `Option`, and a non-integer source each keep the lowering they had
/// (on the faithful lane, the default cast), so the arm's test is the target's
/// identity and not "any enum".
#[test]
fn r146_leaves_other_casts_into_an_enum_alone() {
    let plain_payload = faithful_option_of("core::option::Option", {
        let mut ty = Ty::adt("test::Wrapper", vec![("0".to_string(), Ty::u32())]);
        let Ty::Adt { validity_wrapper, .. } = &mut ty else { unreachable!() };
        *validity_wrapper = None;
        ty
    });
    let not_option =
        faithful_option_of("mycrate::Option", nonzero_u32("core::num::nonzero::NonZero", true));
    for (label, to) in [
        ("Option of a plain newtype", plain_payload),
        ("an enum named mycrate::Option", not_option),
    ] {
        let module = try_lower(&cast_fn(Ty::u32(), to)).expect("the control lowers");
        assert_eq!(
            shape(&module).first().copied(),
            Some("Cast"),
            "{label}: not claimed by R146: {:?}",
            shape(&module)
        );
    }
}
