// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Actual public pinned-source owners. Configured genuine library DATA is
//! required; no private environment constructor, imported token or skip path.

use clean_kernel::Name;
use trust_certify::lean_source_batch::{LeanSourceInput, PinnedLeanSourceWorld};
use trust_clean_ir_gate::standalone::admit_standalone_scalar;
use trust_clean_origin::emit::plan_clean_origin_body;
use trust_ir::Producer;
use trust_ir::value::{FuncId, FuncTyId};

fn source() -> Vec<LeanSourceInput> {
    vec![LeanSourceInput {
        module: "ContextCustody".into(),
        path: "/unread-context-label/ContextCustody.lean".into(),
        source: "def identity64 (x : UInt64) : UInt64 := x".into(),
    }]
}

#[test]
fn pinned_standalone_tokens_retain_the_actual_accepted_context() {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(|| {
            let mut first_world = PinnedLeanSourceWorld::new().expect("genuine pinned Init DATA");
            let first = first_world.check(source(), false);
            let first_context = first.accepted_context().expect("first actual source context");
            let name = Name::from_string("identity64");
            let plan = plan_clean_origin_body(first_context.environment(), "identity64")
                .expect("actual projection plan");
            let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
            let function = trust_clean_ir::emit_clean_origin_function(
                &plan,
                FuncId::new(0),
                FuncTyId::new(0),
            )
            .unwrap();
            let token = admit_standalone_scalar(&first_context, &name, &signature, &function)
                .expect("actual same-context kernel mint");
            token
                .authenticate(&first_context, &name, &signature, &function)
                .expect("same-context token authentication");
            let mut relocated = function.clone();
            relocated.id = FuncId::new(7);
            relocated.ty = FuncTyId::new(3);
            relocated.producer = Some(Producer::Clean);
            let published = token
                .authenticate_published(
                    &first_context,
                    &name,
                    &signature,
                    &function,
                    &relocated,
                )
                .expect("actual same-context publication");
            published.authenticate_context(&first_context).expect("same publication context");
            let first_reborrow = first.accepted_context().unwrap();
            token
                .authenticate(&first_reborrow, &name, &signature, &function)
                .expect("reborrow shares the accepted context");
            published.authenticate_context(&first_reborrow).expect("published reborrow");

            // Real second initialization through the public configured-world API.
            // All public identity fields coincide; an existing token must still
            // retain the particular checked source context that minted it.
            let mut second_world = PinnedLeanSourceWorld::new().expect("independent genuine Init");
            let second = second_world.check(source(), false);
            let second_context = second.accepted_context().expect("second actual source context");
            assert_eq!(first_context.sources(), second_context.sources());
            assert_eq!(first_context.aliases(), second_context.aliases());
            assert_eq!(first_context.source_closure_sha256(), second_context.source_closure_sha256());
            assert_eq!(first_context.owned_declarations_sha256(), second_context.owned_declarations_sha256());
            assert_eq!(first_context.environment().get_const(&name), second_context.environment().get_const(&name));
            let direct = token.authenticate(&second_context, &name, &signature, &function);
            let republished = token.authenticate_published(
                &second_context,
                &name,
                &signature,
                &function,
                &relocated,
            );
            let publication = published.authenticate_context(&second_context);
            eprintln!("PINNED_CONTEXT_CUSTODY direct={direct:?}, republish={republished:?}, published={publication:?}");
            assert_eq!(
                direct.expect_err("independent context borrowed token authority").stage(),
                "standalone-source-context"
            );
            assert_eq!(
                republished.expect_err("independent context republished token authority").stage(),
                "standalone-source-context"
            );
            assert_eq!(
                publication.expect_err("independent context borrowed published authority").stage(),
                "standalone-codegen-context"
            );

        })
        .unwrap()
        .join()
        .unwrap();
}
