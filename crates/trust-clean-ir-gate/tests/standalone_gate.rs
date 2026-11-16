// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clean_kernel::Name;
use trust_certify::lean_source_batch::{
    AcceptedLeanSourceContext, CheckedLeanSourceBatch, LeanSourceInput,
};
use trust_clean_ir_gate::standalone::{admit_standalone_scalar, admit_standalone_wrapping_binop};
use trust_clean_ir_gate::{admit_clean_origin, admit_wrapping_binop};
use trust_clean_origin::emit::plan_standalone_clean_origin_body;
use trust_clean_origin::{CleanOriginPlan, CleanOriginShape, plan_clean_origin_body};
use trust_ir::node::InstrNode;
use trust_ir::proof::{ProofAnnotation, ProofContext, ProofDigest, ProofFormula};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{
    BinOp, CallingConv, Constant, Function, FunctionSummary, IdentityScheme, Inst, Linkage, Module,
    Producer, SourceProvenance,
};
use trust_types::digest::canonical_json_sha256;

const ADD8: &str = "def add8 (a b : UInt8) : UInt8 := a + b";
const FIRST8: &str = "def first8 (a b : UInt8) : UInt8 := a";
const LITERAL8: &str = "def literal8 (a b : UInt8) : UInt8 := 7";

fn checked(module: &str, path: &str, source: &str) -> CheckedLeanSourceBatch {
    let batch = CheckedLeanSourceBatch::check(
        vec![LeanSourceInput {
            module: module.to_owned(),
            path: path.to_owned(),
            source: source.to_owned(),
        }],
        false,
    );
    assert!(batch.accepted_context().is_some(), "fixture refused: {:?}", batch.errors());
    batch
}

fn emitted(
    context: &AcceptedLeanSourceContext<'_>,
    name: &str,
) -> (Name, CleanOriginPlan, FuncTy, Function) {
    let plan = plan_clean_origin_body(context.environment(), name).expect("source plan");
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).expect("signature");
    let function =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .expect("emitted SSA");
    (Name::from_string(name), plan, signature, function)
}

/// WS5.2: the in-crate (Rust) lane names its subject by the minted Rust item's
/// link-time symbol and keeps the Lean spelling as `display_path` — the
/// collector's `bind_clean_origin_link_symbol`, over a fixture symbol. The
/// standalone lane (no Rust item) keeps the Lean spelling as the name.
fn rust_bound(function: &Function) -> Function {
    let mut bound = function.clone();
    assert!(bound.display_path.is_none());
    let lean =
        std::mem::replace(&mut bound.name, format!("_RNvCs0_7fixture{}", function.name.len()));
    bound.name.push_str(&lean);
    bound.display_path = Some(lean);
    bound
}

fn change_binop(function: &Function, replacement: BinOp) -> Function {
    let mut changed = function.clone();
    for node in &mut changed.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            *op = replacement;
            return changed;
        }
    }
    panic!("fixture has no binop");
}

#[test]
fn all_twelve_carrier_operation_pairs_mint_and_publish_from_accepted_source() {
    let mut source = String::new();
    for width in [8, 16, 32, 64] {
        for (name, op) in [("add", "+"), ("sub", "-"), ("mul", "*")] {
            source.push_str(&format!(
                "def {name}{width} (a b : UInt{width}) : UInt{width} := a {op} b\n"
            ));
        }
    }
    let batch = checked("Arithmetic", "Arithmetic.lean", &source);
    let context = batch.accepted_context().expect("accepted");
    let mut admitted = 0;
    for width in [8, 16, 32, 64] {
        for operation in ["add", "sub", "mul"] {
            let name = format!("{operation}{width}");
            let (name, _plan, signature, function) = emitted(&context, &name);
            let token = admit_standalone_wrapping_binop(&context, &name, &signature, &function)
                .expect("actual SSA must kernel-admit");
            let unified = admit_standalone_scalar(&context, &name, &signature, &function)
                .expect("unified API retains every wrapping operation");
            assert_eq!(unified.subject_digest(), token.subject_digest());
            token.authenticate(&context, &name, &signature, &function).expect("authenticate");
            assert_eq!(token.carrier_tag(), format!("UInt{width}"));
            assert_eq!(token.method_tag(), "definitional-equality");
            let mut published = function.clone();
            published.id = FuncId::new(admitted + 1);
            published.ty = FuncTyId::new(admitted + 2);
            published.producer = Some(Producer::Clean);
            let final_token = token
                .authenticate_published(&context, &name, &signature, &function, &published)
                .expect("exact publication");
            assert_ne!(final_token.subject_digest(), token.subject_digest());
            assert_eq!(final_token.identity(), token.identity());
            assert_eq!(final_token.carrier_tag(), token.carrier_tag());
            assert_eq!(final_token.method_tag(), token.method_tag());
            admitted += 1;
        }
    }
    assert_eq!(admitted, 12);
}

#[test]
fn rust_digest_recipe_remains_byte_for_byte_and_standalone_is_domain_separated() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _plan, signature, function) = emitted(&context, "add8");
    let rust_function = rust_bound(&function);
    let legacy = admit_wrapping_binop(
        context.environment(),
        &_plan,
        7,
        "fixture::add8",
        &signature,
        &rust_function,
    )
    .expect("legacy Rust API remains valid");
    // This is the historical recipe, deliberately independent of the gate's
    // private implementation: exact name, one signature, one unmodified body.
    // WS5.2 changed the INPUT (the subject is now named by its link-time symbol
    // with the Lean spelling as display_path), not the recipe: the two pinned
    // digests below were re-measured over `rust_bound` and the recipe equality
    // above them is unchanged.
    let mut image = Module::new(
        "@trust-internal::clean-wrapping-binop-gate-subject-v1::def-index=7::def-path=fixture::add8",
    );
    image.func_types.push(signature.clone());
    image.functions.push(rust_function.clone());
    assert_eq!(legacy.subject_digest(), image.stable_digest());
    // WHY BOTH MINTED LITERALS MOVED, and why that is a wire consequence, not a payload change.
    // c9de6a13bd (2026-09-20, "pins+consumers: RE-LAND trust-ir v45 and trust-cg") moved
    // first-party/trust-ir 4ac1b25c -> dfdb950a. There `Module::stable_digest` stopped hashing
    // under the `trust_ir.module.v2` domain and hashes under `IdentityScheme::CURRENT` = V3
    // (`trust_ir.module.v3`, wire v44's portable identity, which projects every `Module.files`
    // string to ""). This image has no files, so V3 hashes the same bytes under a new domain
    // tag. The V2 pins are the historical literals, unchanged byte for byte: the name, the
    // signature, and the emitted body did not move. Measured 2026-09-27 by running this test
    // at each commit: 0c10bce0 at c9de6a13bd's parent e5ce196fd2, 41b60ea3 at c9de6a13bd;
    // 8325008ba6 carried the same trust-ir pin first (41b60ea3) and beaa06d218 rolled it back
    // (0c10bce0). A V2 miss means the payload moved; a miss on the CURRENT pin alone means the
    // identity scheme moved again.
    //
    // WS5.2 then moved the PAYLOAD (the name is the link-time symbol, the Lean spelling moved
    // to `display_path`), so all four literals moved with it. WS5.2 first pinned only
    // `stable_digest` (03201d34 / b8cfa5a7, measured at first-party/trust-ir 29744d5f, where
    // `stable_digest` was ALREADY `IdentityScheme::CURRENT`); those are the CURRENT literals
    // below, and they re-measured byte for byte on the c603897b pin, which is the check that
    // moving the pin moved nothing for this image. The V2 literals (96a80357 / e2ee5c9d) were
    // measured on 2026-09-28 at c603897b. A standalone trust-ir probe over a one-function
    // module agrees: its V2 and CURRENT digests are identical at 29744d5f and at c603897b,
    // with and without a `display_path`.
    assert!(image.files.is_empty(), "V3 blanks `files`; this recipe relies on having none");
    assert_eq!(
        image.stable_digest_under(IdentityScheme::V2).to_string(),
        "sha256:96a80357f67e5fbc638e16808c27dd65de5dfacb3f5e36682a722894fc405c9c",
    );
    assert_eq!(
        legacy.subject_digest().to_string(),
        "sha256:03201d34fa83324132c4672aa63fe7160c89467db092b367b3af0af9cc723f07",
    );

    let standalone = admit_standalone_wrapping_binop(&context, &name, &signature, &function)
        .expect("standalone gate");
    assert_ne!(legacy.subject_digest(), standalone.subject_digest());
    let mut published = rust_function.clone();
    published.id = FuncId::new(23);
    published.ty = FuncTyId::new(9);
    published.producer = Some(Producer::Clean);
    let final_legacy = legacy
        .authenticate_published("add8", 7, "fixture::add8", &signature, &rust_function, &published)
        .expect("legacy publication");
    image.functions[0] = published;
    assert_eq!(final_legacy.subject_digest(), image.stable_digest());
    assert_eq!(
        image.stable_digest_under(IdentityScheme::V2).to_string(),
        "sha256:e2ee5c9d2d5b302de5695033e25dc7f71e25746ca735e272bda81d5c3302bef6",
    );
    assert_eq!(
        final_legacy.subject_digest().to_string(),
        "sha256:b8cfa5a7219187b03adccb4bbe50525cf0d96ad13efd39e5cea33e9f75a56e03",
    );
}

#[test]
fn rust_digest_domains_follow_the_reflected_family_at_every_binding_seam() {
    let batch = checked("Fixture", "Fixture.lean", &format!("{ADD8}\n{FIRST8}\n{LITERAL8}"));
    let context = batch.accepted_context().expect("accepted");
    let legacy_domain = "@trust-internal::clean-wrapping-binop-gate-subject-v1";
    let extended_domain = "@trust-internal::clean-carrier-gate-subject-v2";
    for (name, domain, wrong_domain) in [
        ("add8", legacy_domain, extended_domain),
        ("first8", extended_domain, legacy_domain),
        ("literal8", extended_domain, legacy_domain),
    ] {
        let (_, plan, signature, function) = emitted(&context, name);
        let function = rust_bound(&function);
        let token = admit_clean_origin(
            context.environment(),
            &plan,
            7,
            "fixture::body",
            &signature,
            &function,
        )
        .expect("unified carrier gate");
        let independent_image = |domain: &str, function: &Function| {
            let mut image = Module::new(format!("{domain}::def-index=7::def-path=fixture::body"));
            image.func_types.push(signature.clone());
            image.functions.push(function.clone());
            image.stable_digest()
        };
        assert_eq!(token.subject_digest(), independent_image(domain, &function));
        assert_ne!(token.subject_digest(), independent_image(wrong_domain, &function));
        let wrapping = admit_wrapping_binop(
            context.environment(),
            &plan,
            7,
            "fixture::body",
            &signature,
            &function,
        );
        if name == "add8" {
            assert_eq!(
                wrapping.expect("legacy wrapping entrypoint").subject_digest(),
                token.subject_digest()
            );
        } else {
            assert_eq!(
                wrapping.expect_err("new shapes cannot select the legacy entrypoint").stage(),
                "target-shape"
            );
        }
        token.authenticate(name, 7, "fixture::body", &signature, &function).expect("exact binding");
        for (index, path) in [(8, "fixture::body"), (7, "fixture::other")] {
            assert_eq!(
                token
                    .authenticate(name, index, path, &signature, &function)
                    .expect_err("Rust identity changed")
                    .stage(),
                "token-digest"
            );
        }
        let mut published = function.clone();
        published.id = FuncId::new(23);
        published.ty = FuncTyId::new(9);
        published.producer = Some(Producer::Clean);
        let final_token = token
            .authenticate_published(name, 7, "fixture::body", &signature, &function, &published)
            .expect("exact publication");
        assert_eq!(final_token.subject_digest(), independent_image(domain, &published));
        assert_ne!(final_token.subject_digest(), independent_image(wrong_domain, &published));
        for (index, path) in [(8, "fixture::body"), (7, "fixture::other")] {
            assert_eq!(
                token
                    .authenticate_published(name, index, path, &signature, &function, &published)
                    .expect_err("publication cannot change the Rust identity")
                    .stage(),
                "token-digest"
            );
        }
    }
}

#[test]
fn identity_recomputes_exact_kernel_payload_and_accepted_closures() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _plan, signature, function) = emitted(&context, "add8");
    let token =
        admit_standalone_wrapping_binop(&context, &name, &signature, &function).expect("gate");
    let env = context.environment();
    let payload = canonical_json_sha256(&(
        env.get_const(&name).expect("constant"),
        env.get_inductive(&name),
        env.get_constructor(&name),
        env.get_recursor(&name),
        env.quotients().find(|value| value.name == name),
    ))
    .expect("canonical payload");
    assert_eq!(token.identity().declaration(), &name);
    assert_eq!(token.identity().kernel_payload_sha256(), payload);
    assert_eq!(token.identity().source_closure_sha256(), context.source_closure_sha256());
    assert_eq!(token.identity().owned_declarations_sha256(), context.owned_declarations_sha256());
}

#[test]
fn source_bytes_module_and_path_retargeting_cannot_reuse_a_token() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _plan, signature, function) = emitted(&context, "add8");
    let token =
        admit_standalone_wrapping_binop(&context, &name, &signature, &function).expect("gate");
    for (module, path, source) in [
        ("Other", "Fixture.lean", ADD8.to_owned()),
        ("Fixture", "other/Fixture.lean", ADD8.to_owned()),
        ("Fixture", "Fixture.lean", format!("-- exact bytes matter\n{ADD8}")),
    ] {
        let changed = checked(module, path, &source);
        let changed_context = changed.accepted_context().expect("accepted changed source");
        let fresh = admit_standalone_wrapping_binop(&changed_context, &name, &signature, &function)
            .expect("same body still passes its own fresh kernel gate");
        assert_eq!(
            fresh.identity().kernel_payload_sha256(),
            token.identity().kernel_payload_sha256()
        );
        assert_ne!(fresh.subject_digest(), token.subject_digest());
        assert!(token.authenticate(&changed_context, &name, &signature, &function).is_err());
    }
}

#[test]
fn kernel_payload_or_added_module_roster_change_cannot_reuse_a_token() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _plan, signature, function) = emitted(&context, "add8");
    let token =
        admit_standalone_wrapping_binop(&context, &name, &signature, &function).expect("gate");
    for source in [
        "def add8 (a b : UInt8) : UInt8 := a - b".to_owned(),
        format!("{ADD8}\ndef extra (a b : UInt8) : UInt8 := a * b"),
    ] {
        let changed = checked("Fixture", "Fixture.lean", &source);
        let changed_context = changed.accepted_context().expect("accepted changed source");
        assert_ne!(
            context.owned_declarations_sha256(),
            changed_context.owned_declarations_sha256()
        );
        assert!(token.authenticate(&changed_context, &name, &signature, &function).is_err());
    }
}

#[test]
fn declaration_name_and_plan_are_not_interchangeable() {
    let batch = checked(
        "Fixture",
        "Fixture.lean",
        &format!("{ADD8}\ndef other (a b : UInt8) : UInt8 := a + b"),
    );
    let context = batch.accepted_context().expect("accepted");
    let (name, _plan, signature, function) = emitted(&context, "add8");
    let token =
        admit_standalone_wrapping_binop(&context, &name, &signature, &function).expect("gate");
    let other = Name::from_string("other");
    assert!(token.authenticate(&context, &other, &signature, &function).is_err());
    assert_eq!(
        admit_standalone_wrapping_binop(&context, &other, &signature, &function)
            .expect_err("freshly derived plan must bind the exact owned name")
            .stage(),
        "subject-name"
    );
}

#[test]
fn prelude_and_unowned_declarations_cannot_be_admitted() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (_, _plan, signature, function) = emitted(&context, "add8");
    for name in ["UInt8.add", "Nat", "absent"] {
        assert_eq!(
            admit_standalone_wrapping_binop(
                &context,
                &Name::from_string(name),
                &signature,
                &function,
            )
            .expect_err("only owned source declarations")
            .stage(),
            "standalone-source-owner"
        );
    }
}

#[test]
fn rejected_or_tainted_source_has_no_context_that_can_mint_a_gate() {
    for source in [
        "theorem wrong : False := by trivial",
        "axiom arbitrary : UInt8",
        "def good (a b : UInt8) : UInt8 := a + b\ntheorem wrong : False := by trivial",
    ] {
        let batch = CheckedLeanSourceBatch::check(
            vec![LeanSourceInput {
                module: "Rejected".into(),
                path: "Rejected.lean".into(),
                source: source.into(),
            }],
            false,
        );
        assert!(batch.accepted_context().is_none(), "rejected source exposed a kernel context");
    }
}

#[test]
fn mutated_operation_reaches_the_actual_kernel_disagreement() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _plan, signature, function) = emitted(&context, "add8");
    let changed = change_binop(&function, BinOp::Sub);
    assert_eq!(
        admit_standalone_wrapping_binop(&context, &name, &signature, &changed)
            .expect_err("false source/SSA relation must fail at kernel")
            .stage(),
        "kernel-disagreement"
    );
}

#[test]
fn an_emitter_plan_from_another_accepted_context_is_not_gate_authority() {
    let original = checked("Fixture", "Fixture.lean", ADD8);
    let original_context = original.accepted_context().expect("original accepted");
    let (name, _stale_plan, signature, stale_function) = emitted(&original_context, "add8");
    let changed = checked("Fixture", "Fixture.lean", "def add8 (a b : UInt8) : UInt8 := a - b");
    let changed_context = changed.accepted_context().expect("changed accepted");
    assert_eq!(
        admit_standalone_wrapping_binop(&changed_context, &name, &signature, &stale_function)
            .expect_err("gate must freshly derive its source plan and compare actual new source")
            .stage(),
        "kernel-disagreement",
    );
    let (_, _, fresh_signature, fresh_function) = emitted(&changed_context, "add8");
    admit_standalone_wrapping_binop(&changed_context, &name, &fresh_signature, &fresh_function)
        .expect("new source and its own emitter remain admissible");
}

#[test]
fn body_signature_and_noncomputational_metadata_mutations_invalidate_token() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _plan, signature, function) = emitted(&context, "add8");
    let token =
        admit_standalone_wrapping_binop(&context, &name, &signature, &function).expect("gate");
    let mut renamed = function.clone();
    renamed.name.push_str("_changed");
    let mut debug_changed = function.clone();
    debug_changed.value_names = Some(vec![(function.blocks[0].params[0].0, "different".into())]);
    let mut id_changed = function.clone();
    id_changed.id = FuncId::new(3);
    for changed in [change_binop(&function, BinOp::Mul), renamed, debug_changed, id_changed] {
        assert!(token.authenticate(&context, &name, &signature, &changed).is_err());
    }
    let mut changed_signature = signature.clone();
    changed_signature.returns = vec![Ty::U16];
    assert!(token.authenticate(&context, &name, &changed_signature, &function).is_err());
}

#[test]
fn publication_only_permits_id_type_and_clean_producer_relocation() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _plan, signature, function) = emitted(&context, "add8");
    let token =
        admit_standalone_wrapping_binop(&context, &name, &signature, &function).expect("gate");
    let mut published = function.clone();
    published.producer = Some(Producer::Clean);
    let base = token
        .authenticate_published(&context, &name, &signature, &function, &published)
        .expect("Clean publication");
    let mut id_changed = published.clone();
    id_changed.id = FuncId::new(23);
    let mut ty_changed = published.clone();
    ty_changed.ty = FuncTyId::new(9);
    for changed in [id_changed, ty_changed] {
        let final_token = token
            .authenticate_published(&context, &name, &signature, &function, &changed)
            .expect("placement-only change");
        assert_ne!(base.subject_digest(), final_token.subject_digest());
    }
    let mut wrong_producer = published.clone();
    wrong_producer.producer = Some(Producer::TRust);
    assert_eq!(
        token
            .authenticate_published(&context, &name, &signature, &function, &wrong_producer)
            .expect_err("producer must be Clean")
            .stage(),
        "published-producer"
    );
    let mut wrong_metadata = published.clone();
    wrong_metadata.name.push_str("_changed");
    for changed in [wrong_metadata, change_binop(&published, BinOp::Sub)] {
        assert_eq!(
            token
                .authenticate_published(&context, &name, &signature, &function, &changed)
                .expect_err("only explicit placement fields may change")
                .stage(),
            "published-relocation"
        );
    }
}

#[test]
fn fresh_mint_refuses_unproved_metadata_even_before_any_digest_exists() {
    let batch = checked("Fixture", "Fixture.lean", ADD8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _, signature, function) = emitted(&context, "add8");
    let mut mutations = Vec::new();
    let mut changed = function.clone();
    changed.summary = Some(FunctionSummary {
        requires: vec![],
        ensures: vec![ProofFormula::trust_types_json(r#"{"Bool":false}"#, "false", "Bool")],
        params: vec!["a".into(), "b".into()],
        proved: true,
        // v41, pre-v41 meanings: these mutation fixtures carry no `decreases`
        // measure, and `backed_by: None` is NOT RECORDED — the point of each is
        // that the gate must reject the mutated summary on its own content.
        decreases: Vec::new(),
        backed_by: None,
        effects: None,
    });
    mutations.push(("false proved summary", changed));
    let mut changed = function.clone();
    changed.proofs.push(ProofAnnotation::NoOverflow);
    mutations.push(("function proof", changed));
    let mut changed = function.clone();
    changed.blocks[0].body[0].proofs.push(ProofAnnotation::NoOverflow);
    mutations.push(("instruction proof", changed));
    let mut changed = function.clone();
    changed.attrs.readnone = true;
    mutations.push(("optimizer attribute", changed));
    let mut changed = function.clone();
    changed.source_provenance =
        Some(SourceProvenance::new(ProofDigest::zero(), ProofDigest::zero(), vec![]));
    mutations.push(("semantic provenance", changed));
    let mut changed = function.clone();
    changed.blocks[0].body[0].proof_context = Some(ProofContext::default());
    mutations.push(("instruction proof context", changed));
    let mut changed = function.clone();
    changed.blocks[0].body[0].scope = Some(0);
    mutations.push(("instruction scope", changed));
    let mut changed = function.clone();
    changed.blocks[0].body[0].span = Some(trust_ir::value::SourceSpan { file: 0, line: 1, col: 1 });
    mutations.push(("instruction span", changed));
    let mut changed = function.clone();
    changed.value_names = Some(vec![(function.blocks[0].params[0].0, "fake".into())]);
    mutations.push(("debug metadata", changed));
    let mut changed = function.clone();
    changed.calling_conv = CallingConv::C;
    mutations.push(("foreign ABI", changed));
    let mut changed = function.clone();
    changed.linkage = Linkage::Internal;
    mutations.push(("changed linkage", changed));
    for (label, changed) in mutations {
        assert_eq!(
            admit_standalone_wrapping_binop(&context, &name, &signature, &changed)
                .expect_err(label)
                .stage(),
            "standalone-metadata",
            "{label} must not be laundered by a fresh kernel token",
        );
    }
    admit_standalone_wrapping_binop(&context, &name, &signature, &function)
        .expect("neutral emitted body remains admitted");
}

#[test]
fn ordinary_projections_cover_every_uint_width_arity_and_parameter_position() {
    let mut source = String::new();
    let mut cases = Vec::new();
    for width in [8, 16, 32, 64] {
        for arity in 1..=3 {
            let parameters = (0..arity).map(|i| format!("x{i}")).collect::<Vec<_>>().join(" ");
            for projected in 0..arity {
                let name = format!("project{width}arity{arity}index{projected}");
                source.push_str(&format!(
                    "def {name} ({parameters} : UInt{width}) : UInt{width} := x{projected}\n"
                ));
                cases.push((name, width, projected));
            }
        }
    }
    for (projected, width) in [8, 16, 32, 64].into_iter().enumerate() {
        let name = format!("mixed{projected}");
        source.push_str(&format!(
            "def {name} (x0 : UInt8) (x1 : UInt16) (x2 : UInt32) (x3 : UInt64) : UInt{width} := x{projected}\n"
        ));
        cases.push((name, width, projected));
    }
    let batch = checked("Projections", "Projections.lean", &source);
    let context = batch.accepted_context().expect("accepted");
    assert_eq!(cases.len(), 28);
    for (name, width, projected) in cases {
        let (name, plan, signature, function) = emitted(&context, &name);
        assert_eq!(plan.shape(), &CleanOriginShape::Projection { projected });
        let token = admit_standalone_scalar(&context, &name, &signature, &function)
            .expect("actual projection must kernel-admit");
        token.authenticate(&context, &name, &signature, &function).expect("authenticate");
        assert_eq!(token.carrier_tag(), format!("UInt{width}"));
        assert_eq!(token.method_tag(), "definitional-equality");
        let mut published = function.clone();
        published.id = FuncId::new(12);
        published.ty = FuncTyId::new(34);
        published.producer = Some(Producer::Clean);
        let final_token = token
            .authenticate_published(&context, &name, &signature, &function, &published)
            .expect("projection publication");
        assert_ne!(final_token.subject_digest(), token.subject_digest());
        assert_eq!(final_token.identity(), token.identity());
        assert_eq!(final_token.carrier_tag(), token.carrier_tag());
        assert_eq!(final_token.method_tag(), token.method_tag());
        assert_eq!(
            admit_standalone_wrapping_binop(&context, &name, &signature, &function)
                .expect_err("old wrapping-only API stays narrow")
                .stage(),
            "target-shape"
        );
    }
}

#[test]
fn projection_wrong_parameter_reaches_kernel_disagreement_not_planner_comparison() {
    let batch = checked("Fixture", "Fixture.lean", FIRST8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _, signature, mut function) = emitted(&context, "first8");
    function.blocks[0].body[0].inst = Inst::Return { values: vec![function.blocks[0].params[1].0] };
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &function)
            .expect_err("actual second argument is not first argument for every input")
            .stage(),
        "kernel-disagreement"
    );
}

#[test]
fn projection_ssa_identity_is_not_assumed_to_equal_parameter_index() {
    let batch = checked("Fixture", "Fixture.lean", FIRST8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _, signature, mut function) = emitted(&context, "first8");
    function.entry = BlockId::new(19);
    function.blocks[0].id = function.entry;
    function.blocks[0].params[0].0 = ValueId::new(87);
    function.blocks[0].params[1].0 = ValueId::new(42);
    function.blocks[0].body[0].inst = Inst::Return { values: vec![ValueId::new(87)] };
    admit_standalone_scalar(&context, &name, &signature, &function)
        .expect("SSA renaming preserves the projection relation");
    function.blocks[0].body[0].inst = Inst::Return { values: vec![ValueId::new(42)] };
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &function)
            .expect_err("renamed second argument is still semantically wrong")
            .stage(),
        "kernel-disagreement"
    );
}

#[test]
fn projection_rejects_wrong_width_signedness_arity_and_malformed_ssa() {
    let batch = checked("Fixture", "Fixture.lean", FIRST8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _, signature, function) = emitted(&context, "first8");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).expect("gate");
    let mut cases = Vec::new();
    for ty in [Ty::U16, Ty::I8] {
        let mut sig = signature.clone();
        let mut body = function.clone();
        sig.params = vec![ty.clone(), ty.clone()];
        sig.returns = vec![ty.clone()];
        body.blocks[0].params[0].1 = ty.clone();
        body.blocks[0].params[1].1 = ty;
        cases.push(("retagged signature/body", sig, body));
    }
    let mut sig = signature.clone();
    sig.returns = vec![Ty::U16];
    cases.push(("return width", sig, function.clone()));
    let mut sig = signature.clone();
    sig.params.push(Ty::U8);
    let mut body = function.clone();
    body.blocks[0].params.push((ValueId::new(3), Ty::U8));
    cases.push(("source arity", sig, body));
    let mut sig = signature.clone();
    sig.params.pop();
    cases.push(("entry arity", sig, function.clone()));
    let mut sig = signature.clone();
    sig.is_vararg = true;
    cases.push(("vararg", sig, function.clone()));
    let mut body = function.clone();
    body.blocks[0].params[1].1 = Ty::U16;
    cases.push(("entry width", signature.clone(), body));
    let mut body = function.clone();
    body.blocks[0].params[1].0 = body.blocks[0].params[0].0;
    cases.push(("duplicate SSA", signature.clone(), body));
    let mut body = function.clone();
    body.blocks[0].body[0].inst = Inst::Return { values: vec![ValueId::new(99)] };
    cases.push(("undefined SSA", signature.clone(), body));
    let mut body = function.clone();
    body.blocks[0].body[0].results.push(ValueId::new(2));
    cases.push(("Return defines value", signature.clone(), body));
    for values in [vec![], vec![ValueId::new(0), ValueId::new(1)]] {
        let mut body = function.clone();
        body.blocks[0].body[0].inst = Inst::Return { values };
        cases.push(("return arity", signature.clone(), body));
    }
    for position in [0, 1] {
        let mut body = function.clone();
        body.blocks[0].body.insert(
            position,
            InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(0) })
                .with_results(vec![ValueId::new(2)]),
        );
        cases.push(("extra instruction", signature.clone(), body));
    }
    let mut body = function.clone();
    body.blocks[0].body.clear();
    cases.push(("missing Return", signature.clone(), body));
    let mut body = function.clone();
    body.blocks.push(body.blocks[0].clone());
    cases.push(("extra block", signature.clone(), body));
    let mut body = function.clone();
    body.entry = BlockId::new(9);
    cases.push(("missing entry", signature.clone(), body));
    let mut body = function.clone();
    body.id = FuncId::new(9);
    cases.push(("non-placeholder", signature.clone(), body));
    let mut body = function.clone();
    body.name.push_str("_different");
    cases.push(("wrong function name", signature.clone(), body));
    for (label, sig, body) in cases {
        assert!(admit_standalone_scalar(&context, &name, &sig, &body).is_err(), "{label}");
        assert!(token.authenticate(&context, &name, &sig, &body).is_err(), "{label}");
    }
}

#[test]
fn projection_fresh_mint_and_relocation_cannot_launder_proof_metadata() {
    let batch = checked("Fixture", "Fixture.lean", FIRST8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _, signature, function) = emitted(&context, "first8");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).expect("gate");
    let mut cases = Vec::new();
    let mut body = function.clone();
    body.summary = Some(FunctionSummary {
        requires: vec![],
        ensures: vec![ProofFormula::trust_types_json(r#"{"Bool":false}"#, "false", "Bool")],
        params: vec!["a".into(), "b".into()],
        proved: true,
        // v41, pre-v41 meanings: these mutation fixtures carry no `decreases`
        // measure, and `backed_by: None` is NOT RECORDED — the point of each is
        // that the gate must reject the mutated summary on its own content.
        decreases: Vec::new(),
        backed_by: None,
        effects: None,
    });
    cases.push(body);
    let mut body = function.clone();
    body.blocks[0].body[0].proofs.push(ProofAnnotation::NoOverflow);
    cases.push(body);
    let mut body = function.clone();
    body.proofs.push(ProofAnnotation::NoOverflow);
    cases.push(body);
    let mut body = function.clone();
    body.attrs.readnone = true;
    cases.push(body);
    for mut body in cases {
        assert_eq!(
            admit_standalone_scalar(&context, &name, &signature, &body)
                .expect_err("fresh metadata has no independent proof")
                .stage(),
            "standalone-metadata"
        );
        body.producer = Some(Producer::Clean);
        assert_eq!(
            token
                .authenticate_published(&context, &name, &signature, &function, &body)
                .expect_err("publication cannot add metadata")
                .stage(),
            "published-relocation"
        );
    }
}

#[test]
fn projection_tokens_bind_source_context_and_fresh_mint_checks_the_new_source() {
    let batch = checked("Fixture", "Fixture.lean", FIRST8);
    let context = batch.accepted_context().expect("accepted");
    let (name, _, signature, function) = emitted(&context, "first8");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).expect("gate");
    for (module, path, source) in [
        ("Other", "Fixture.lean", FIRST8.to_owned()),
        ("Fixture", "Other.lean", FIRST8.to_owned()),
        ("Fixture", "Fixture.lean", format!("-- retained exact bytes\n{FIRST8}")),
        ("Fixture", "Fixture.lean", "def first8 (a b : UInt8) : UInt8 := b".to_owned()),
    ] {
        let changed = checked(module, path, &source);
        let changed_context = changed.accepted_context().expect("accepted");
        assert!(token.authenticate(&changed_context, &name, &signature, &function).is_err());
        let fresh = admit_standalone_scalar(&changed_context, &name, &signature, &function);
        if source.ends_with(":= b") {
            assert_eq!(
                fresh.expect_err("old SSA must not represent changed source").stage(),
                "kernel-disagreement"
            );
        } else {
            assert_ne!(
                fresh.expect("same semantics freshly checked").subject_digest(),
                token.subject_digest()
            );
        }
    }
}

#[test]
fn inductive_projection_is_excluded_before_any_scalar_carrier_check() {
    let batch = checked(
        "Fixture",
        "Fixture.lean",
        &format!(
            "{FIRST8}\ndef foldIdentity (n : Nat) : Nat := @Nat.rec.{{1}} (fun _ => Nat) Nat.zero (fun _ ih => Nat.succ ih) n"
        ),
    );
    let context = batch.accepted_context().expect("accepted");
    let plan =
        plan_clean_origin_body(context.environment(), "foldIdentity").expect("real induction plan");
    assert_eq!(plan.shape(), &CleanOriginShape::InductiveProjection { projected: 0 });
    let (_, _, signature, mut function) = emitted(&context, "first8");
    function.name = "foldIdentity".into();
    assert_eq!(
        admit_standalone_scalar(
            &context,
            &Name::from_string("foldIdentity"),
            &signature,
            &function
        )
        .expect_err("inductive plan cannot enter ordinary projection gate")
        .stage(),
        "target-shape"
    );
}

#[test]
fn literal_boundaries_cover_all_uint_widths_and_nullary_or_unused_parameters() {
    let mut source = String::new();
    let mut cases = Vec::new();
    for width in [8, 16, 32, 64] {
        for (tag, value) in [("zero", 0_u128), ("max", (1_u128 << width) - 1)] {
            for arity in [0, 3] {
                let name = format!("literal{width}{tag}arity{arity}");
                let params =
                    if arity == 0 { String::new() } else { format!("(a b c : UInt{width})") };
                source.push_str(&format!("def {name} {params} : UInt{width} := {value}\n"));
                cases.push((name, width, value));
            }
        }
    }
    let batch = checked("Literals", "Literals.lean", &source);
    let context = batch.accepted_context().unwrap();
    assert_eq!(context.owned_declarations().len(), 16);
    for (name, width, value) in cases {
        let (name, plan, signature, function) = emitted(&context, &name);
        assert_eq!(plan.shape(), &CleanOriginShape::ConstantUint { value });
        let standalone =
            plan_standalone_clean_origin_body(context.environment(), &name.to_string()).unwrap();
        assert_eq!(
            trust_clean_ir::emit_standalone_clean_origin_function(
                &standalone,
                FuncId::new(0),
                FuncTyId::new(0)
            )
            .unwrap(),
            function,
            "new route preserves exact old literal bytes"
        );
        let token =
            admit_standalone_scalar(&context, &name, &signature, &function).expect("literal gate");
        assert_eq!(token.carrier_tag(), format!("UInt{width}"));
        assert_eq!(token.method_tag(), "definitional-equality");
        token.authenticate(&context, &name, &signature, &function).unwrap();
        let mut published = function.clone();
        published.id = FuncId::new(8);
        published.ty = FuncTyId::new(9);
        published.producer = Some(Producer::Clean);
        let final_token = token
            .authenticate_published(&context, &name, &signature, &function, &published)
            .unwrap();
        assert_ne!(token.subject_digest(), final_token.subject_digest());
        assert_eq!(token.identity(), final_token.identity());
        assert_eq!(
            admit_standalone_wrapping_binop(&context, &name, &signature, &function)
                .unwrap_err()
                .stage(),
            "target-shape"
        );
    }
}

#[test]
fn literal_reads_actual_ssa_value_and_reaches_whole_term_kernel_disagreement() {
    let batch = checked("Fixture", "Fixture.lean", LITERAL8);
    let context = batch.accepted_context().unwrap();
    let (name, _, signature, mut function) = emitted(&context, "literal8");
    function.blocks[0].body[0].inst = Inst::Const { ty: Ty::U8, value: Constant::Int(8) };
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &function).unwrap_err().stage(),
        "kernel-disagreement"
    );
}

#[test]
fn literal_ssa_renaming_is_semantic_but_returning_an_unused_parameter_is_not() {
    let batch = checked("Fixture", "Fixture.lean", LITERAL8);
    let context = batch.accepted_context().unwrap();
    let (name, _, signature, mut function) = emitted(&context, "literal8");
    function.entry = BlockId::new(19);
    function.blocks[0].id = function.entry;
    function.blocks[0].params[0].0 = ValueId::new(42);
    function.blocks[0].params[1].0 = ValueId::new(87);
    function.blocks[0].body[0].results = vec![ValueId::new(99)];
    function.blocks[0].body[1].inst = Inst::Return { values: vec![ValueId::new(99)] };
    admit_standalone_scalar(&context, &name, &signature, &function)
        .expect("actual IDs, not positional guesses");
    function.blocks[0].body[1].inst = Inst::Return { values: vec![ValueId::new(42)] };
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &function).unwrap_err().stage(),
        "return"
    );
}

#[test]
fn literal_rejects_invalid_constants_carriers_telescope_and_ssa() {
    let batch = checked("Fixture", "Fixture.lean", LITERAL8);
    let context = batch.accepted_context().unwrap();
    let (name, _, signature, function) = emitted(&context, "literal8");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    let mut cases = Vec::new();
    for value in [
        Constant::Int(-1),
        Constant::Int(256),
        Constant::U128(7),
        Constant::U128(u128::MAX),
        Constant::Bool(true),
        Constant::Float(7.0),
    ] {
        let mut body = function.clone();
        body.blocks[0].body[0].inst = Inst::Const { ty: Ty::U8, value };
        cases.push(("invalid constant", signature.clone(), body));
    }
    for ty in [Ty::U16, Ty::I8, Ty::Bool] {
        let mut sig = signature.clone();
        let mut body = function.clone();
        sig.params = vec![ty.clone(), ty.clone()];
        sig.returns = vec![ty.clone()];
        body.blocks[0].params.iter_mut().for_each(|(_, t)| *t = ty.clone());
        body.blocks[0].body[0].inst = Inst::Const { ty, value: Constant::Int(7) };
        cases.push(("retagged source carrier", sig, body));
    }
    let mut sig = signature.clone();
    sig.is_vararg = true;
    cases.push(("vararg", sig, function.clone()));
    let mut sig = signature.clone();
    sig.returns.clear();
    cases.push(("missing return type", sig, function.clone()));
    let mut sig = signature.clone();
    sig.returns.push(Ty::U8);
    cases.push(("extra return type", sig, function.clone()));
    let mut sig = signature.clone();
    sig.params.push(Ty::U8);
    let mut body = function.clone();
    body.blocks[0].params.push((ValueId::new(42), Ty::U8));
    cases.push(("source arity", sig, body));
    let mut body = function.clone();
    body.blocks[0].params[0].1 = Ty::U16;
    cases.push(("entry type", signature.clone(), body));
    let mut body = function.clone();
    body.blocks[0].params[1].0 = body.blocks[0].params[0].0;
    cases.push(("duplicate parameter", signature.clone(), body));
    for results in [vec![], vec![ValueId::new(2), ValueId::new(3)], vec![ValueId::new(0)]] {
        let mut body = function.clone();
        body.blocks[0].body[0].results = results;
        cases.push(("Const result identity", signature.clone(), body));
    }
    for values in [
        vec![],
        vec![ValueId::new(2), ValueId::new(0)],
        vec![ValueId::new(0)],
        vec![ValueId::new(99)],
    ] {
        let mut body = function.clone();
        body.blocks[0].body[1].inst = Inst::Return { values };
        cases.push(("Return operands", signature.clone(), body));
    }
    let mut body = function.clone();
    body.blocks[0].body[1].results.push(ValueId::new(3));
    cases.push(("Return defines value", signature.clone(), body));
    let mut body = function.clone();
    body.blocks[0].body[0].inst = Inst::Undef { ty: Ty::U8 };
    cases.push(("undef", signature.clone(), body));
    let mut body = function.clone();
    body.blocks[0].body.swap(0, 1);
    cases.push(("instruction order", signature.clone(), body));
    let mut body = function.clone();
    let extra = body.blocks[0].body[1].clone();
    body.blocks[0].body.push(extra);
    cases.push(("extra instruction", signature.clone(), body));
    let mut body = function.clone();
    body.blocks[0].body.pop();
    cases.push(("missing Return", signature.clone(), body));
    let mut body = function.clone();
    body.blocks.push(body.blocks[0].clone());
    cases.push(("extra block", signature.clone(), body));
    let mut body = function.clone();
    body.entry = BlockId::new(9);
    cases.push(("missing entry", signature.clone(), body));
    let mut body = function.clone();
    body.id = FuncId::new(9);
    cases.push(("non-placeholder", signature.clone(), body));
    for (label, sig, body) in cases {
        assert!(admit_standalone_scalar(&context, &name, &sig, &body).is_err(), "{label}");
        assert!(token.authenticate(&context, &name, &sig, &body).is_err(), "{label}");
    }
}

#[test]
fn literal_fresh_mint_and_relocation_refuse_unproved_metadata() {
    let batch = checked("Fixture", "Fixture.lean", LITERAL8);
    let context = batch.accepted_context().unwrap();
    let (name, _, signature, function) = emitted(&context, "literal8");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    let mut cases = Vec::new();
    let mut body = function.clone();
    body.summary = Some(FunctionSummary {
        requires: vec![],
        ensures: vec![ProofFormula::trust_types_json(r#"{"Bool":false}"#, "false", "Bool")],
        params: vec!["a".into(), "b".into()],
        proved: true,
        // v41, pre-v41 meanings: these mutation fixtures carry no `decreases`
        // measure, and `backed_by: None` is NOT RECORDED — the point of each is
        // that the gate must reject the mutated summary on its own content.
        decreases: Vec::new(),
        backed_by: None,
        effects: None,
    });
    cases.push(body);
    let mut body = function.clone();
    body.blocks[0].body[0].proofs.push(ProofAnnotation::NoOverflow);
    cases.push(body);
    let mut body = function.clone();
    body.proofs.push(ProofAnnotation::NoOverflow);
    cases.push(body);
    let mut body = function.clone();
    body.attrs.readnone = true;
    cases.push(body);
    let mut body = function.clone();
    body.calling_conv = CallingConv::C;
    cases.push(body);
    for mut body in cases {
        assert_eq!(
            admit_standalone_scalar(&context, &name, &signature, &body).unwrap_err().stage(),
            "standalone-metadata"
        );
        body.producer = Some(Producer::Clean);
        assert_eq!(
            token
                .authenticate_published(&context, &name, &signature, &function, &body)
                .unwrap_err()
                .stage(),
            "published-relocation"
        );
    }
}

#[test]
fn literal_source_bytes_payload_and_owned_roster_are_bound() {
    let batch = checked("Fixture", "Fixture.lean", LITERAL8);
    let context = batch.accepted_context().unwrap();
    let (name, _, signature, function) = emitted(&context, "literal8");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    for (module, path, source) in [
        ("Other", "Fixture.lean", LITERAL8.to_owned()),
        ("Fixture", "Other.lean", LITERAL8.to_owned()),
        ("Fixture", "Fixture.lean", format!("-- bytes\n{LITERAL8}")),
        ("Fixture", "Fixture.lean", format!("{LITERAL8}\ndef sibling : UInt8 := 0")),
        ("Fixture", "Fixture.lean", LITERAL8.replace(":= 7", ":= 8")),
    ] {
        let changed = checked(module, path, &source);
        let changed_context = changed.accepted_context().unwrap();
        assert!(token.authenticate(&changed_context, &name, &signature, &function).is_err());
        let remint = admit_standalone_scalar(&changed_context, &name, &signature, &function);
        if source.ends_with(":= 8") {
            assert_ne!(
                context.environment().get_const(&name).unwrap().value,
                changed_context.environment().get_const(&name).unwrap().value
            );
            assert_eq!(remint.unwrap_err().stage(), "kernel-disagreement");
        } else {
            assert_ne!(remint.unwrap().subject_digest(), token.subject_digest());
        }
    }
}

#[test]
fn literal_digest_has_a_distinct_domain_and_cannot_borrow_wrapping_or_projection_identity() {
    let batch = checked("Fixture", "Fixture.lean", LITERAL8);
    let context = batch.accepted_context().unwrap();
    let (name, _, signature, function) = emitted(&context, "literal8");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    let identity = token.identity();
    let identity_sha = canonical_json_sha256(&(
        "trust.clean.standalone-source-identity.v1",
        identity.source_closure_sha256(),
        identity.owned_declarations_sha256(),
        identity.declaration(),
        identity.kernel_payload_sha256(),
    ))
    .unwrap();
    for (domain, same) in
        [("constant-uint", true), ("wrapping-binop", false), ("projection", false)]
    {
        let mut module = Module::new(format!(
            "@trust-internal::clean-standalone-{domain}-gate-subject-v1::lean-identity-sha256={identity_sha}"
        ));
        module.func_types.push(signature.clone());
        module.functions.push(function.clone());
        assert_eq!(module.stable_digest() == token.subject_digest(), same);
    }
}

#[test]
fn literal_unsupported_parameter_and_out_of_range_source_plans_remain_refused() {
    for source in [
        "def literal8 (a : Bool) (b : UInt8) : UInt8 := 7",
        "def literal8 (a b : UInt8) : UInt8 := 256",
        "def literal8 (a b : UInt8) : UInt8 := UInt8.ofNat 256",
        "def literal8 (a b : UInt8) (h : a = b) : UInt8 := 7",
    ] {
        let batch = checked("Fixture", "Fixture.lean", source);
        let context = batch.accepted_context().unwrap();
        let name = Name::from_string("literal8");
        // Supplying plausible scalar SSA cannot erase a source restriction.
        let signature = FuncTy {
            params: vec![Ty::U8, Ty::U8],
            returns: vec![Ty::U8],
            is_vararg: false,
            abi: None,
        };
        let mut function =
            Function::new(FuncId::new(0), "literal8", FuncTyId::new(0), BlockId::new(0));
        function.calling_conv = CallingConv::Rust;
        let mut block = trust_ir::Block::new(BlockId::new(0))
            .with_param(ValueId::new(0), Ty::U8)
            .with_param(ValueId::new(1), Ty::U8);
        block.body = vec![
            InstrNode::new(Inst::Const { ty: Ty::U8, value: Constant::Int(7) })
                .with_results(vec![ValueId::new(2)]),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
        ];
        function.blocks.push(block);
        assert!(
            admit_standalone_scalar(&context, &name, &signature, &function).is_err(),
            "{source}"
        );
    }
}

#[test]
fn mixed_literal_gate_checks_every_return_width_and_complete_parameter_order() {
    let mut source = String::new();
    let mut cases = Vec::new();
    for width in [8, 16, 32, 64] {
        for (tag, parameters, value) in [
            (
                "forward",
                "(a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64)",
                (1_u128 << width) - 1,
            ),
            ("reverse", "(a : UInt64) (b : UInt32) (c : UInt16) (d : UInt8)", 0),
        ] {
            let name = format!("{tag}{width}");
            source.push_str(&format!("def {name} {parameters} : UInt{width} := {value}\n"));
            cases.push((name, width));
        }
    }
    let batch = checked("Mixed", "Mixed.lean", &source);
    let context = batch.accepted_context().unwrap();
    assert_eq!(context.owned_declarations().len(), 8);
    for (name, width) in cases {
        let plan = plan_standalone_clean_origin_body(context.environment(), &name).unwrap();
        assert!(plan.legacy_plan().is_none());
        assert!(plan_clean_origin_body(context.environment(), &name).is_err());
        let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
        let function = trust_clean_ir::emit_standalone_clean_origin_function(
            &plan,
            FuncId::new(0),
            FuncTyId::new(0),
        )
        .unwrap();
        let name = Name::from_string(&name);
        let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
        assert_eq!(token.carrier_tag(), format!("UInt{width}"));
        token.authenticate(&context, &name, &signature, &function).unwrap();
        let mut published = function.clone();
        published.id = FuncId::new(5);
        published.ty = FuncTyId::new(9);
        published.producer = Some(Producer::Clean);
        token.authenticate_published(&context, &name, &signature, &function, &published).unwrap();
        assert!(admit_standalone_wrapping_binop(&context, &name, &signature, &function).is_err());
    }
}

#[test]
fn unused_mixed_parameters_cannot_hide_signature_order_or_ssa_mutations() {
    let batch = checked(
        "Mixed",
        "Mixed.lean",
        "def mixed (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64) : UInt8 := 7",
    );
    let context = batch.accepted_context().unwrap();
    let plan = plan_standalone_clean_origin_body(context.environment(), "mixed").unwrap();
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
    let function = trust_clean_ir::emit_standalone_clean_origin_function(
        &plan,
        FuncId::new(0),
        FuncTyId::new(0),
    )
    .unwrap();
    let name = Name::from_string("mixed");
    let token = admit_standalone_scalar(&context, &name, &signature, &function).unwrap();
    let mut wrong_sig = signature.clone();
    let mut wrong_body = function.clone();
    wrong_sig.params.swap(0, 3);
    wrong_body.blocks[0].params[0].1 = Ty::U64;
    wrong_body.blocks[0].params[3].1 = Ty::U8;
    assert_eq!(
        admit_standalone_scalar(&context, &name, &wrong_sig, &wrong_body).unwrap_err().stage(),
        "source-ir-carrier"
    );
    for ty in [Ty::Bool, Ty::I16] {
        let mut sig = signature.clone();
        let mut body = function.clone();
        sig.params[1] = ty.clone();
        body.blocks[0].params[1].1 = ty;
        assert!(admit_standalone_scalar(&context, &name, &sig, &body).is_err());
    }
    let mut body = function.clone();
    body.blocks[0].params[1].0 = body.blocks[0].params[0].0;
    assert!(admit_standalone_scalar(&context, &name, &signature, &body).is_err());
    let mut body = function.clone();
    body.blocks[0].body[0].inst = Inst::Const { ty: Ty::U8, value: Constant::Int(8) };
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &body).unwrap_err().stage(),
        "kernel-disagreement"
    );
    let changed = checked(
        "Mixed",
        "Mixed.lean",
        "def mixed (a : UInt64) (b : UInt16) (c : UInt32) (d : UInt8) : UInt8 := 7",
    );
    let changed_context = changed.accepted_context().unwrap();
    assert!(token.authenticate(&changed_context, &name, &signature, &function).is_err());
    assert_eq!(
        admit_standalone_scalar(&changed_context, &name, &signature, &function)
            .unwrap_err()
            .stage(),
        "source-ir-carrier"
    );
}

/// The standalone lane admits a transparent local helper call; the join keeps
/// its targeting policy. `call8 := helper8 a b` plans as `WrappingBinOp` (the
/// planner looks through the helper) and its own value is a call, not the op,
/// so the rustc mixed-link join — whose kernel-TV companion cannot read a
/// helper head — leaves it untargeted (`target-shape`). The standalone lane has
/// no companion and no lower tier, and the kernel unfolds the helper, so it
/// admits the row: refusing it there made targo-trust's lean_build fatal on
/// every transparent helper call (37e92f7922c measured only this crate).
#[test]
fn a_transparent_helper_call_is_admitted_standalone_and_untargeted_at_the_join() {
    let batch = checked(
        "Fixture",
        "Fixture.lean",
        "def helper8 (a b : UInt8) : UInt8 := a + b\ndef call8 (a b : UInt8) : UInt8 := helper8 a b",
    );
    let context = batch.accepted_context().expect("accepted");
    let (name, plan, signature, function) = emitted(&context, "call8");
    assert!(matches!(plan.shape(), CleanOriginShape::WrappingBinOp { .. }));
    admit_standalone_scalar(&context, &name, &signature, &function)
        .expect("standalone scalar admits a transparent helper call");
    admit_standalone_wrapping_binop(&context, &name, &signature, &function)
        .expect("standalone wrapping binop admits a transparent helper call");
    for refusal in [
        admit_clean_origin(
            context.environment(),
            &plan,
            7,
            "fixture::call8",
            &signature,
            &function,
        )
        .expect_err("the join never targets a helper-reached row"),
        admit_wrapping_binop(
            context.environment(),
            &plan,
            7,
            "fixture::call8",
            &signature,
            &function,
        )
        .expect_err("the join never targets a helper-reached row"),
    ] {
        assert_eq!(refusal.stage(), "target-shape");
    }
    // Negative control: the standalone admission is the kernel's, not the
    // planner's word — a body that disagrees with the helper still refuses.
    let changed = change_binop(&function, BinOp::Sub);
    assert_eq!(
        admit_standalone_wrapping_binop(&context, &name, &signature, &changed)
            .expect_err("a false helper body must fail at the kernel")
            .stage(),
        "kernel-disagreement"
    );
    assert_eq!(
        admit_standalone_scalar(&context, &name, &signature, &changed)
            .expect_err("a false helper body must fail at the kernel on the scalar path too")
            .stage(),
        "kernel-disagreement"
    );
}

/// An OPAQUE helper is never seen through: the standalone lane admits a
/// helper call only because the kernel unfolds it, so an opaque one refuses.
#[test]
fn an_opaque_helper_call_is_not_admitted_standalone() {
    let batch = checked(
        "Fixture",
        "Fixture.lean",
        "opaque helper8 (a b : UInt8) : UInt8 := a + b\ndef call8 (a b : UInt8) : UInt8 := helper8 a b",
    );
    let context = batch.accepted_context().expect("accepted");
    // The planner may refuse the opaque head outright; if it plans the call,
    // the kernel cannot unfold it and the gate refuses.
    if let Ok(plan) = plan_clean_origin_body(context.environment(), "call8") {
        let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).expect("signature");
        let function =
            trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
                .expect("emitted SSA");
        let name = Name::from_string("call8");
        assert!(admit_standalone_scalar(&context, &name, &signature, &function).is_err());
        assert!(admit_standalone_wrapping_binop(&context, &name, &signature, &function).is_err());
    }
}
