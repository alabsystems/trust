// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Rebinding controls use actual source elaboration, SSA emission and kernel
//! admission. Neither a copied stamp nor equality against a changed source
//! function is sufficient to authenticate a codegen subject.

use trust_certify::clean_island::CleanIslandSession;
use trust_clean_ir_gate::{
    CodegenRelocation, PublishedTrustIrFaithful, admit_clean_origin, authenticate_codegen,
    clean_carrier_gate_stamp,
};
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::ty::FuncTy;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{BinOp, CallingConv, Function, Inst, Linkage, Producer, Ty, Visibility};

fn subject(name: &str, body: &str) -> (PublishedTrustIrFaithful, FuncTy, Function) {
    subject_with_metadata(name, body, |_| {})
}

fn subject_with_metadata(
    name: &str,
    body: &str,
    decorate: impl FnOnce(&mut Function),
) -> (PublishedTrustIrFaithful, FuncTy, Function) {
    let mut session = CleanIslandSession::new();
    let source = format!("def {name} (a b : UInt64) : UInt64 := {body}");
    let outcome = session.check(&source);
    assert!(!outcome.is_rejected(), "fixture must kernel-check: {outcome:?}");
    let environment = session.environment().expect("accepted source");
    let plan = plan_clean_origin_body(environment, name).expect("source plan");
    let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).expect("signature");
    let mut emitted =
        trust_clean_ir::emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .expect("SSA emission");
    emitted.display_path = Some(emitted.name.clone());
    emitted.name = format!("_RNvCs0_7fixture{}{name}", name.len());
    decorate(&mut emitted);
    let path = format!("m::{name}");
    let token = admit_clean_origin(environment, &plan, 4, &path, &signature, &emitted)
        .expect("kernel carrier gate");
    let mut published = emitted.clone();
    published.id = FuncId::new(5);
    published.ty = FuncTyId::new(2);
    published.producer = Some(Producer::Clean);
    published.body_gate = Some(clean_carrier_gate_stamp());
    let entry = token
        .authenticate_published(name, 4, &path, &signature, &emitted, &published)
        .expect("authenticated publication");
    (entry, signature, published)
}

fn placement() -> CodegenRelocation {
    CodegenRelocation {
        function_id: FuncId::new(13),
        linkage: Linkage::Internal,
        visibility: Visibility::Default,
    }
}

fn relocated(published: &Function) -> Function {
    let mut codegen = published.clone();
    codegen.id = placement().function_id;
    codegen.linkage = placement().linkage;
    codegen.visibility = placement().visibility;
    codegen
}

fn subtract(function: &mut Function) {
    for node in &mut function.blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst {
            *op = BinOp::Sub;
            return;
        }
    }
    panic!("fixture has no arithmetic instruction");
}

#[test]
fn every_current_carrier_shape_can_rebind_without_changing_its_computation() {
    for (name, body) in
        [("sum", "a + b"), ("first", "a"), ("seven", "7"), ("composed", "(a + b) * (a - b)")]
    {
        let (entry, signature, published) = subject(name, body);
        authenticate_codegen(
            &entry,
            &signature,
            &published,
            &signature,
            &relocated(&published),
            placement(),
        )
        .expect("exact identity relocation");
    }
}

#[test]
fn body_and_identity_mutations_cannot_inherit_a_published_permission() {
    let (entry, signature, published) = subject("sum", "a + b");
    let mutations: &[(&str, fn(&mut Function))] = &[
        ("body", subtract),
        ("function id", |f| f.id = FuncId::new(99)),
        ("type id", |f| f.ty = FuncTyId::new(99)),
        ("symbol", |f| f.name.push_str("_other")),
        ("linkage", |f| f.linkage = Linkage::External),
        ("visibility", |f| f.visibility = Visibility::Hidden),
        ("producer", |f| f.producer = Some(Producer::TRust)),
        ("stamp", |f| f.body_gate = None),
        ("display path", |f| f.display_path = Some("other".into())),
        ("retention", |f| f.retained = true),
        ("section", |f| f.section = Some("other".into())),
        ("calling convention", |f| {
            f.calling_conv =
                if f.calling_conv == CallingConv::C { CallingConv::Rust } else { CallingConv::C };
        }),
    ];
    for (name, mutate) in mutations {
        let mut codegen = relocated(&published);
        mutate(&mut codegen);
        authenticate_codegen(&entry, &signature, &published, &signature, &codegen, placement())
            .expect_err(name);
    }
}

#[test]
fn equality_to_a_changed_publication_does_not_replace_ledger_authentication() {
    let (entry, signature, mut published) = subject("sum", "a + b");
    subtract(&mut published);
    let refusal = authenticate_codegen(
        &entry,
        &signature,
        &published,
        &signature,
        &relocated(&published),
        placement(),
    )
    .expect_err("both copies changed after the kernel gate");
    assert_eq!(refusal.stage(), "ledger-digest");
}

#[test]
fn signature_legalization_is_not_identity_relocation() {
    let (entry, signature, published) = subject("sum", "a + b");
    let mut changed = signature.clone();
    changed.returns[0] = Ty::U32;
    let refusal = authenticate_codegen(
        &entry,
        &signature,
        &published,
        &changed,
        &relocated(&published),
        placement(),
    )
    .expect_err("a changed carrier cannot reuse the source gate");
    assert_eq!(refusal.stage(), "codegen-signature");
}

#[test]
fn authenticated_metadata_cannot_be_silently_discarded_by_codegen() {
    for provenance in [false, true] {
        let (entry, signature, published) = subject_with_metadata("sum", "a + b", |function| {
            if provenance {
                function.source_provenance = Some(trust_ir::SourceProvenance::new(
                    trust_ir::proof::ProofDigest::zero(),
                    trust_ir::proof::ProofDigest::zero(),
                    Vec::new(),
                ));
            } else {
                function.summary = Some(trust_ir::FunctionSummary::default());
            }
        });
        for discard in [false, true] {
            let mut codegen = relocated(&published);
            if discard {
                codegen.summary = None;
                codegen.source_provenance = None;
            }
            let refusal = authenticate_codegen(
                &entry,
                &signature,
                &published,
                &signature,
                &codegen,
                placement(),
            )
            .expect_err("metadata needs a separate preservation rule before admission");
            assert_eq!(refusal.stage(), "codegen-metadata");
        }
    }
}
