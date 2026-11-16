//! REAL-ARTIFACT proof of the bundled-member BoundsCheck charge.
//!
//! `tests/data/slice_index_usize_i32_index.json` is the COMPILER'S OWN extracted
//! verification input for `<usize as core::slice::index::SliceIndex<[i32]>>::index`,
//! captured verbatim from the `trustc` that ships in this tree with
//!
//! ```text
//! TRUST_DUMP_MONO=1 trustc --edition 2021 --crate-type lib -Cpanic=abort \
//!     -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//!     tests/trust-falsification/proved/vec_scalar_index_lenchecked.rs
//! ```
//!
//! That dump lane runs the SAME `trust_mir_extract::extract_function_with_contract_bundle`
//! over the SAME fully-monomorphized body as the native-bundle member lane, so this
//! is not a hand-built approximation of the member — it is the member.
//!
//! # What this file pins
//!
//! 1. The member's `BoundsCheck` Assert is EXACTLY CHARGED, not cleared: the
//!    admission lane derives `self < slice__slice_len`.
//! 2. That charge actually LANDS on a caller. The `__slice_len` spelling is the
//!    one `trust_vcgen`'s call-site producer rebinds from the actual's own slice
//!    length, so the second test runs the real producer over a direct caller and
//!    checks the emitted obligation names the CALLER's length symbol and carries
//!    no unsubstituted member spelling. A charge that left `slice__slice_len`
//!    free would look admitted and constrain nothing.
//!
//! # Measured, and NOT fixed here
//!
//! In `proved/vec_scalar_index_lenchecked.rs` this member is reached through
//! `<Vec<i32> as Index<usize>>::index`, i.e. it is a TRANSITIVE bundled member,
//! and its extraction additionally carries the always-true integer type-range
//! precondition `0 <= self <= u64::MAX` that
//! `trust_mir_extract::integer_param_range_preconditions` attaches to every named
//! integer formal. The compiler's
//! `ensure_bundled_member_asserts_exactly_charged` refuses both shapes on its own
//! terms — "no exact direct root call can carry its derived precondition" and
//! "the derived-requires lane is contract-less only" — independently of this
//! lane. Those are separate gate questions; deriving the charge is the
//! prerequisite for either, and refusing remains the correct answer until they
//! are answered.

use trust_ir_bridge::{BundledMemberAssertAdmission, bundled_member_assert_admission};
use trust_types::{
    BasicBlock, BlockId, Formula, FunctionSpec, LocalDecl, Operand, Place, Sort, SourceSpan,
    Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

const MEMBER: &str = "<usize as core::slice::index::SliceIndex<[i32]>>::index";
const MEMBER_MUT: &str = "<usize as core::slice::index::SliceIndex<[i32]>>::index_mut";

fn load(file: &str) -> VerifiableFunction {
    let path = format!("{}/tests/data/{file}", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("real member MIR fixture `{path}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("real member MIR fixture `{path}` must deserialize: {e}"))
}

fn member() -> VerifiableFunction {
    load("slice_index_usize_i32_index.json")
}

/// The WRITE path (`v[i] = x`) bundles `index_mut`, whose only difference is a
/// `&mut [i32]` formal. `proved/vec_scalar_index_write_guarded.rs` and
/// `mutant/vec_scalar_index_write_oob.rs` are refused naming THIS member, so the
/// read-path fixture alone would not cover them.
fn member_mut() -> VerifiableFunction {
    load("slice_index_usize_i32_index_mut.json")
}

fn derived_charge() -> Formula {
    Formula::Lt(
        Box::new(Formula::var("self", Sort::Int)),
        Box::new(Formula::var("slice__slice_len", Sort::Int)),
    )
}

#[test]
fn the_real_slice_index_member_is_exactly_charged() {
    let member = member();
    assert_eq!(member.def_path, MEMBER, "fixture identity");
    // The fixture must still be the shape this lane claims to recognize: one
    // `BoundsCheck` Assert. If a future std/MIR change moves the check, this
    // assertion is what says so instead of the charge quietly becoming vacuous.
    let asserts = member
        .body
        .blocks
        .iter()
        .filter(|block| matches!(&block.terminator, Terminator::Assert { .. }))
        .count();
    assert_eq!(asserts, 1, "the real member carries exactly one Assert");

    let BundledMemberAssertAdmission::Derived { param_names, requires } =
        bundled_member_assert_admission(&member)
    else {
        panic!(
            "the real `{MEMBER}` body must be admitted with an exact charge; \
             a refusal here means the bundled-member Assert gate has no lane for it \
             and the whole proof-authority bundle is refused"
        );
    };
    assert_eq!(param_names, ["self", "slice"]);
    assert_eq!(requires, [derived_charge()]);
}

/// A caller that calls the member DIRECTLY: `p(s: &[i32], i: usize) -> &i32`
/// lowering to `_0 = <member>(copy i, copy s)`.
fn direct_caller() -> VerifiableFunction {
    let elem_ref = Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) };
    let slice_ref =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::i32()) }) };
    VerifiableFunction {
        name: "probe".into(),
        def_path: "krate::probe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: elem_ref.clone(), name: None },
                LocalDecl { index: 1, ty: slice_ref, name: Some("s".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: MEMBER.into(),
                        // Positional, in the member's own formal order
                        // (`self` = the index, then `slice`).
                        args: vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: UnwindEdge::Continue,
                        callee_identity: None,
                        callee_key: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: elem_ref,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
        tuple_layouts: Default::default(),
    }
}

/// The charge must REACH the caller. This runs the production call-site producer
/// over the summary the compiler's gate rebuilds from this very admission, and
/// asserts the emitted obligation is written in the CALLER's vocabulary.
#[test]
fn the_derived_charge_binds_to_the_callers_own_slice_length() {
    let member = member();
    let BundledMemberAssertAdmission::Derived { param_names, requires } =
        bundled_member_assert_admission(&member)
    else {
        panic!("the real member must be admitted before its charge can bind");
    };
    // Exactly the summary `ensure_bundled_member_asserts_exactly_charged`
    // rebuilds: the derived names and requires, plus the member's own formal
    // types as an independent second extraction (it is `param_types` that drives
    // the `__slice_len` substitution).
    let param_types: Vec<Ty> = (1..=member.body.arg_count)
        .map(|index| {
            member
                .body
                .locals
                .iter()
                .find(|local| local.index == index)
                .expect("formal local present")
                .ty
                .clone()
        })
        .collect();
    let mut summary = trust_vcgen::FunctionSummary::new(MEMBER.to_string())
        .with_param_names(param_names)
        .with_param_types(param_types);
    for require in &requires {
        summary = summary.with_precondition(require.clone());
    }
    let mut summaries = trust_vcgen::SummaryDatabase::new();
    summaries.insert(summary);

    let caller = direct_caller();
    let vcs = trust_vcgen::generate_callsite_precondition_vcs(&caller, &summaries);
    let rows: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::Precondition { callee } if callee == MEMBER))
        .collect();
    assert_eq!(
        rows.len(),
        1,
        "one call site and one derived requires must mint exactly one caller-side \
         precondition row; got {vcs:?}"
    );

    let free: Vec<String> = trust_types::collect_free_var_decls(&rows[0].formula)
        .into_iter()
        .map(|(var, _)| var)
        .collect();
    assert!(
        free.iter().any(|var| var == "s__slice_len"),
        "the member's `slice__slice_len` must be rebound to the CALLER's own \
         length symbol; free vars were {free:?}"
    );
    assert!(
        !free.iter().any(|var| var == "slice__slice_len" || var == "self"),
        "no member spelling may survive substitution into the caller's namespace; \
         free vars were {free:?}"
    );
    // And the obligation must be REFUTABLE for an unconstrained index — this
    // caller has no guard, so the negated precondition is satisfiable. A charge
    // that had collapsed to a tautology would be admitted and prove nothing.
    assert_ne!(
        rows[0].formula,
        Formula::Bool(false),
        "the caller-side obligation must not be vacuously unsatisfiable"
    );
}

/// MEASURED on the real extraction, and the reason the recognizer below exists:
/// `trust_mir_extract` attaches the always-true range invariant
/// `0 <= self <= u64::MAX` to this member's `usize` formal. It is a tautology of
/// the parameter's type, not a declared contract — every actual rustc
/// type-checks into it — but its mere presence made the bundled-member gate's
/// "contract-less only" arm refuse every `usize`-indexed BoundsCheck member,
/// i.e. the whole population this lane exists to charge.
///
/// If a future extraction change adds a REAL precondition to a std member, this
/// test goes red rather than the member being quietly admitted.
#[test]
fn the_real_members_only_precondition_is_the_integer_type_range_tautology() {
    let member = member();
    assert_eq!(
        member.preconditions.len(),
        1,
        "the real extraction carries exactly the one synthesized range fact: {:?}",
        member.preconditions
    );
    assert!(
        member.contracts.is_empty() && member.postconditions.is_empty(),
        "the real member declares no contract of its own"
    );
    assert!(
        trust_ir_bridge::member_precondition_is_integer_param_type_range(
            &member,
            &member.preconditions[0],
        ),
        "the synthesized `0 <= self <= u64::MAX` must be recognized as a type \
         tautology; got {:?}",
        member.preconditions[0]
    );
    // The falsifying direction: a bound that is NOT this formal's type range is
    // a real declared requires and must NOT be recognized.
    let tighter = Formula::And(vec![
        Formula::Ge(Box::new(Formula::var("self", Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(Formula::var("self", Sort::Int)), Box::new(Formula::Int(1024))),
    ]);
    assert!(
        !trust_ir_bridge::member_precondition_is_integer_param_type_range(&member, &tighter),
        "a TIGHTER bound is a real obligation, never a tautology"
    );
    // So is a range over a name that is not one of this body's formals.
    let stranger = Formula::And(vec![
        Formula::Ge(Box::new(Formula::var("elsewhere", Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Le(
            Box::new(Formula::var("elsewhere", Sort::Int)),
            Box::new(Formula::Int(18_446_744_073_709_551_615)),
        ),
    ]);
    assert!(
        !trust_ir_bridge::member_precondition_is_integer_param_type_range(&member, &stranger),
        "a range over a non-formal name is not this body's type tautology"
    );
}

#[test]
fn the_real_slice_index_mut_member_is_exactly_charged() {
    let member = member_mut();
    assert_eq!(member.def_path, MEMBER_MUT, "fixture identity");
    let BundledMemberAssertAdmission::Derived { param_names, requires } =
        bundled_member_assert_admission(&member)
    else {
        panic!("the real `{MEMBER_MUT}` body must be admitted with an exact charge");
    };
    assert_eq!(param_names, ["self", "slice"]);
    // Identical to the read path: a `&mut [T]` carries the same pointer
    // metadata, and mutability is not part of the length question.
    assert_eq!(requires, [derived_charge()]);
    assert!(
        member.contracts.is_empty() && member.postconditions.is_empty(),
        "the real member declares no contract of its own"
    );
    assert_eq!(member.preconditions.len(), 1);
    assert!(trust_ir_bridge::member_precondition_is_integer_param_type_range(
        &member,
        &member.preconditions[0],
    ));
}

/// THE FALSIFYING CASE, and the reason the compiler gate now asks a CALL-SITE
/// question as well as a formula-shape one.
///
/// The derived charge is written in `slice__slice_len`. The bridge's
/// `formal_rooted` predicate accepts that spelling on the ground that it is
/// rooted in a formal — which is true — and an earlier comment there went
/// further and claimed it "can no more survive UNSUBSTITUTED into the caller's
/// namespace than the formal itself". That is FALSE, and this test is the
/// measurement: a plain `<formal>` is substituted unconditionally, while
/// `append_length_replacements` emits a length replacement only when
/// `sigma_actual_slice_len` can render THAT actual's length. The caller below
/// obtains its slice from TWO calls — `t = make(); t = make2(); member(i, t)` — so
/// `t` is not a name of one value (`local_defs::path_is_single_static_assignment`
/// refuses two whole writes), `param_slice_len`'s name licence declines, no
/// replacement is emitted, and the row comes back naming the MEMBER's own
/// `slice__slice_len`.
///
/// Trust: 2026-09-16 (round A9) — the unrenderable shape used to be a SINGLE call
/// destination, refused by `slice_len_root_place` for not being a parameter. Since
/// round A8 that function follows every hop to a root of ANY kind and the caller
/// (`param_slice_len`) licenses the root by NAME instead; a single-write call
/// destination passes the licence, and its length renders under the caller's
/// versioned spelling — see
/// `a_single_write_call_destination_actual_renders_under_its_versioned_name` for
/// why that is the exact substitution and not a leak. The gate's premise is
/// unchanged: an actual the licence refuses leaves the member spelling alive,
/// and that is what it must refuse on.
///
/// A free variable is normally only inert incompleteness. It stops being inert
/// when the caller has a variable of the same name, which is why
/// `derived_member_length_var_survives` must report it and the gate must refuse.
#[test]
fn an_unrenderable_slice_actual_leaves_the_member_length_alive_and_is_caught() {
    let (param_names, summaries) = member_summary();
    let vcs =
        trust_vcgen::generate_callsite_precondition_vcs(&call_dest_slice_caller(2), &summaries);
    let rows: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::Precondition { callee } if callee == MEMBER))
        .collect();
    assert_eq!(rows.len(), 1, "one call site, one requires, one row; got {vcs:?}");

    let free: Vec<String> = trust_types::collect_free_var_decls(&rows[0].formula)
        .into_iter()
        .map(|(var, _)| var)
        .collect();
    assert!(
        free.iter().any(|var| var == "slice__slice_len"),
        "the producer is CONDITIONAL: with an unrenderable actual the member's own \
         length spelling survives into the caller's row. If this ever stops being \
         true the gate's call-site check can be relaxed — but only then. Free vars \
         were {free:?}"
    );
    // ...and that is exactly what the compiler gate refuses on.
    assert_eq!(
        trust_ir_bridge::derived_member_length_var_survives(&param_names, &rows[0].formula),
        Some("slice__slice_len".to_owned()),
        "a surviving member length must be reported by name, so the gate can refuse \
         the member instead of shipping a charge on a free variable"
    );
}

/// Trust: 2026-09-16 (round A9) — THE RELAXATION, AND WHY IT IS SOUND. `t = make();
/// member(i, t)`: the slice actual is a call destination written ONCE on every
/// channel, so `local_defs::path_is_single_static_assignment(t)` licenses the name
/// `t__slice_len` — a name of ONE value — and `sigma_actual_slice_len` renders the
/// member's `slice__slice_len` as it. The call-site producer then versions the
/// substituted row at the call: the free variable is `t__slice_len#s0_t`, the value
/// `make` wrote into `t` at the bb0 terminator and the ONLY value `t` ever holds,
/// which is precisely the length the member's `slice.len()` observes. Nothing in the
/// caller constrains it, so the row is a free-variable obligation: satisfiable,
/// never a proof — the same inertness the member spelling had, now in the caller's
/// own vocabulary where a caller-side guard on `t.len()` (versioned identically) can
/// discharge it. What the gate refuses is a SURVIVING member spelling; none survives
/// here, so the gate admits, and the compiler gate's call-site check keeps exactly
/// the premise the previous test pins: refuse on a name the caller cannot render.
#[test]
fn a_single_write_call_destination_actual_renders_under_its_versioned_name() {
    let (param_names, summaries) = member_summary();
    let vcs =
        trust_vcgen::generate_callsite_precondition_vcs(&call_dest_slice_caller(1), &summaries);
    let rows: Vec<_> = vcs
        .iter()
        .filter(|vc| matches!(&vc.kind, VcKind::Precondition { callee } if callee == MEMBER))
        .collect();
    assert_eq!(rows.len(), 1, "one call site, one requires, one row; got {vcs:?}");
    let free: Vec<String> = trust_types::collect_free_var_decls(&rows[0].formula)
        .into_iter()
        .map(|(var, _)| var)
        .collect();
    assert!(
        free.iter().any(|var| var.starts_with("t__slice_len#")),
        "the actual's length must render under the CALLER's versioned spelling of `t`; \
         free vars were {free:?}"
    );
    assert!(
        !free.iter().any(|var| var == "slice__slice_len" || var == "self"),
        "no member spelling may survive; free vars were {free:?}"
    );
    assert_eq!(
        trust_ir_bridge::derived_member_length_var_survives(&param_names, &rows[0].formula),
        None
    );
    assert_ne!(
        rows[0].formula,
        Formula::Bool(false),
        "a free-variable obligation is never a proof"
    );
}

/// The control: the RENDERABLE caller of
/// `the_derived_charge_binds_to_the_callers_own_slice_length` must report no
/// survivor, so the check above is not simply always-true.
#[test]
fn a_renderable_slice_actual_leaves_no_member_spelling_behind() {
    let member = member();
    let BundledMemberAssertAdmission::Derived { param_names, requires } =
        bundled_member_assert_admission(&member)
    else {
        panic!("admitted");
    };
    let param_types: Vec<Ty> = (1..=member.body.arg_count)
        .map(|index| {
            member
                .body
                .locals
                .iter()
                .find(|local| local.index == index)
                .expect("formal local present")
                .ty
                .clone()
        })
        .collect();
    let mut summary = trust_vcgen::FunctionSummary::new(MEMBER.to_string())
        .with_param_names(param_names.clone())
        .with_param_types(param_types);
    for require in &requires {
        summary = summary.with_precondition(require.clone());
    }
    let mut summaries = trust_vcgen::SummaryDatabase::new();
    summaries.insert(summary);
    let vcs = trust_vcgen::generate_callsite_precondition_vcs(&direct_caller(), &summaries);
    for vc in &vcs {
        if let VcKind::Precondition { callee } = &vc.kind
            && callee == MEMBER
        {
            assert_eq!(
                trust_ir_bridge::derived_member_length_var_survives(&param_names, &vc.formula),
                None,
                "a caller whose actual IS a parameter reborrow renders the length, so \
                 nothing of the member's vocabulary may remain: {:?}",
                vc.formula
            );
        }
    }
}

/// The member's summary exactly as `ensure_bundled_member_asserts_exactly_charged`
/// rebuilds it (the derived names and requires plus the formal types), with the
/// admission's `param_names` beside it for the survivor check.
fn member_summary() -> (Vec<String>, trust_vcgen::SummaryDatabase) {
    let member = member();
    let BundledMemberAssertAdmission::Derived { param_names, requires } =
        bundled_member_assert_admission(&member)
    else {
        panic!("the real member must be admitted before its charge can be probed");
    };
    let param_types: Vec<Ty> = (1..=member.body.arg_count)
        .map(|index| {
            member
                .body
                .locals
                .iter()
                .find(|local| local.index == index)
                .expect("formal local present")
                .ty
                .clone()
        })
        .collect();
    let mut summary = trust_vcgen::FunctionSummary::new(MEMBER.to_string())
        .with_param_names(param_names.clone())
        .with_param_types(param_types);
    for require in &requires {
        summary = summary.with_precondition(require.clone());
    }
    let mut summaries = trust_vcgen::SummaryDatabase::new();
    summaries.insert(summary);
    (param_names, summaries)
}

/// `t = make(); [t = make(); ...] member(i, t)` — the slice actual is a CALL
/// DESTINATION written by `reseats` calls in sequence. With one write `t` is a name
/// of one value and its length renders; with two it is not, and nothing renders.
fn call_dest_slice_caller(reseats: usize) -> VerifiableFunction {
    let elem_ref = Ty::Ref { mutable: false, inner: Box::new(Ty::i32()) };
    let slice_ref =
        Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::i32()) }) };
    let mut blocks: Vec<BasicBlock> = (0..reseats)
        .map(|k| BasicBlock {
            id: BlockId(k),
            stmts: vec![],
            terminator: Terminator::Call {
                func: "krate::make".into(),
                args: vec![],
                dest: Place::local(2),
                target: Some(BlockId(k + 1)),
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                unwind: UnwindEdge::Continue,
                callee_identity: None,
                callee_key: None,
            },
        })
        .collect();
    blocks.push(BasicBlock {
        id: BlockId(reseats),
        stmts: vec![],
        terminator: Terminator::Call {
            func: MEMBER.into(),
            args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
            dest: Place::local(0),
            target: Some(BlockId(reseats + 1)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Continue,
            callee_identity: None,
            callee_key: None,
        },
    });
    blocks.push(BasicBlock {
        id: BlockId(reseats + 1),
        stmts: vec![],
        terminator: Terminator::Return,
    });
    VerifiableFunction {
        name: "probe_call_dest".into(),
        def_path: "krate::probe_call_dest".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: elem_ref.clone(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 2, ty: slice_ref, name: Some("t".into()) },
            ],
            blocks,
            arg_count: 1,
            return_ty: elem_ref,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: FunctionSpec::default(),
        tuple_layouts: Default::default(),
    }
}
