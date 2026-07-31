// Round-4 forgery [1]: `place_to_var_name` was not injective across the
// base/segment boundary. `Place { local: <named "q">, projections: [Field(0)] }`
// and a local literally NAMED `q.0` both minted the string `q.0`, and every
// downstream lane that recovers an obligation's subject by name-string equality
// then treats a statement about one as a statement about the other.
//
// These tests pin the invariant that closes it: a base name never contains a
// `PROJECTION_SEGMENT_LEAD` character, and a projection segment always starts
// with one, so the split point of an emitted name is unambiguous.

use trust_types::{
    AssertMessage, BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, SourceSpan,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use crate::{PROJECTION_SEGMENT_LEAD, place_to_var_name};

/// `fn f(q: (bool, u32), <the second parameter's name varies>)`, two asserts,
/// one over `q.0` (the projection) and one over the second parameter (a whole
/// local). Both parameters, so neither has a defining statement to be folded
/// into — the emitted formula is the place's variable itself.
fn two_asserts(second_param_name: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".to_string(),
        def_path: "collide::f".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Tuple(vec![Ty::Bool, Ty::u32()]),
                    name: Some("q".into()),
                },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some(second_param_name.into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(1, 0)),
                        expected: false,
                        msg: AssertMessage::Custom("first".to_string()),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::local(2)),
                        expected: false,
                        msg: AssertMessage::Custom("second".to_string()),
                        target: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The producer-level statement of the defect: two DIFFERENT places must not
/// share a variable name.
#[test]
fn source_name_spelled_like_a_projection_does_not_impersonate_it() {
    let func = two_asserts("q.0");
    let projected = place_to_var_name(&func, &Place::field(1, 0));
    let whole = place_to_var_name(&func, &Place::local(2));
    assert_eq!(projected, "q.0", "the projection keeps its ordinary spelling");
    assert_eq!(whole, "_2", "the ambiguous source name demotes to the unique fallback");
    assert_ne!(
        projected, whole,
        "`_1.0` and the local named `q.0` are different storage and must not share an SMT name"
    );
}

/// Every `Var("<name>"` spelled anywhere in `vcs`' formulas.
fn emitted_variables(
    vcs: &[trust_types::VerificationCondition],
) -> std::collections::BTreeSet<String> {
    let mut names = std::collections::BTreeSet::new();
    for vc in vcs {
        let rendered = format!("{:?}", vc.formula);
        let mut rest = rendered.as_str();
        while let Some(at) = rest.find("Var(\"") {
            rest = &rest[at + 5..];
            let Some(end) = rest.find('"') else { break };
            names.insert(rest[..end].to_string());
            rest = &rest[end..];
        }
    }
    names
}

/// The same defect driven through the real emitter: the obligations for two
/// distinct places must be stated in two distinct variables. Pre-fix the whole
/// function's vocabulary collapses onto the single name `q.0`, which is what let
/// a consumer read the second assert's subject off the first assert's place.
#[test]
fn emitted_obligations_over_distinct_places_use_distinct_variables() {
    let vcs = crate::generate_vcs(&two_asserts("q.0"));
    assert!(!vcs.is_empty(), "the emitter must produce the two assert obligations");
    let vars = emitted_variables(&vcs);
    assert!(
        vars.contains("q.0") && vars.contains("_2"),
        "`_1.0` and the local named `q.0` must be spelled differently; emitted vocabulary was {vars:?}"
    );

    // Control: rename the second parameter and the same two places keep the same
    // two spellings, so the assertion above is about the collision, not about
    // this function's shape.
    let control = emitted_variables(&crate::generate_vcs(&two_asserts("flag")));
    assert!(control.contains("q.0") && control.contains("flag"), "control vocabulary {control:?}");
}

/// The fix must be a no-op for every ordinary MIR: an unambiguous source name
/// keeps its spelling, including a non-ASCII identifier, and the projection
/// spelling is unchanged.
#[test]
fn ordinary_names_are_untouched() {
    let func = two_asserts("flag");
    assert_eq!(place_to_var_name(&func, &Place::field(1, 0)), "q.0");
    assert_eq!(place_to_var_name(&func, &Place::local(1)), "q");
    assert_eq!(place_to_var_name(&func, &Place::local(2)), "flag");

    let unicode = two_asserts("café");
    assert_eq!(place_to_var_name(&unicode, &Place::local(2)), "café");
}

/// Half (i) of the invariant: every projection segment announces itself with a
/// `PROJECTION_SEGMENT_LEAD` character. Checked over every `Projection` variant
/// constructible today — the enum is `#[non_exhaustive]`, so a variant added
/// later is caught by the emitter's `@` prefix rather than by this test.
#[test]
fn every_projection_segment_leads() {
    let func = two_asserts("flag");
    // Golden spellings, so this fails on a segment-format change rather than
    // being satisfied by the emitter's own `@` repair.
    let variants = vec![
        (Projection::Field(0), ".0"),
        (Projection::Index(2), "[_2]"),
        (Projection::Deref, "*"),
        (Projection::Downcast(1), "@1"),
        (Projection::OpaqueCast(Ty::Bool), "@opaque_cast"),
        (Projection::UnwrapUnsafeBinder(Ty::Bool), "@unwrap_unsafe_binder"),
        (Projection::ConstantIndex { offset: 1, min_length: 4, from_end: false }, "[1;min=4]"),
        (Projection::ConstantIndex { offset: 1, min_length: 4, from_end: true }, "[-1;min=4]"),
        (Projection::Subslice { from: 1, to: 3, from_end: false }, "[1..3]"),
        (Projection::Subslice { from: 1, to: 3, from_end: true }, "[1..-3]"),
    ];
    for (p, expected) in variants {
        let name = place_to_var_name(&func, &Place { local: 1, projections: vec![p.clone()] });
        assert_eq!(name, format!("q{expected}"), "segment spelling changed for {p:?}");
        assert!(
            expected.starts_with(PROJECTION_SEGMENT_LEAD),
            "segment {expected:?} for {p:?} does not start with a boundary character, so it could \
             be read back as part of a base name"
        );
    }
}
