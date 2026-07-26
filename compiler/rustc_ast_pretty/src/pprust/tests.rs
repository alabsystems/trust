use rustc_ast as ast;
use rustc_span::{DUMMY_SP, Ident, create_default_session_globals_then};
use thin_vec::{ThinVec, thin_vec};

use super::*;

fn fun_to_string(
    decl: &ast::FnDecl,
    header: ast::FnHeader,
    ident: Ident,
    generics: &ast::Generics,
) -> String {
    to_string(|s| {
        let (cb, ib) = s.head("");
        s.print_fn(decl, header, Some(ident), generics);
        s.end(ib);
        s.end(cb);
    })
}

fn variant_to_string(var: &ast::Variant) -> String {
    to_string(|s| s.print_variant(var))
}

fn ty_to_string(ty: &ast::Ty) -> String {
    to_string(|s| {
        s.print_type(ty);
    })
}

fn contract_to_string(contract: &ast::FnContract) -> String {
    to_string(|s| s.print_contract(contract))
}

#[test]
fn test_fun_to_string() {
    create_default_session_globals_then(|| {
        let abba_ident = Ident::from_str("abba");

        let decl = ast::FnDecl { inputs: ThinVec::new(), output: ast::FnRetTy::Default(DUMMY_SP) };
        let generics = ast::Generics::default();
        assert_eq!(
            fun_to_string(&decl, ast::FnHeader::default(), abba_ident, &generics),
            "fn abba()"
        );
    })
}

#[test]
fn test_variant_to_string() {
    create_default_session_globals_then(|| {
        let ident = Ident::from_str("principal_skinner");

        let var = ast::Variant {
            ident,
            vis: ast::Visibility {
                span: DUMMY_SP,
                kind: ast::VisibilityKind::Inherited,
                tokens: None,
            },
            attrs: ast::AttrVec::new(),
            id: ast::DUMMY_NODE_ID,
            data: ast::VariantData::Unit(ast::DUMMY_NODE_ID),
            disr_expr: None,
            span: DUMMY_SP,
            is_placeholder: false,
        };

        let varstr = variant_to_string(&var);
        assert_eq!(varstr, "principal_skinner");
    })
}

#[test]
fn test_field_view() {
    create_default_session_globals_then(|| {
        let ty = ast::Ty {
            id: ast::DUMMY_NODE_ID,
            kind: ast::TyKind::View(
                Box::new(ast::Ty {
                    id: ast::DUMMY_NODE_ID,
                    kind: ast::TyKind::Dummy,
                    span: DUMMY_SP,
                    tokens: None,
                }),
                thin_vec![Ident::from_str("milhouse"), Ident::from_str("apu")],
            ),
            span: DUMMY_SP,
            tokens: None,
        };

        let ty_str = ty_to_string(&ty);
        assert_eq!(ty_str, "(/*DUMMY*/).{ milhouse, apu }");
    });
}

#[test]
fn contract_pretty_print_uses_validated_authored_order() {
    create_default_session_globals_then(|| {
        let mut contract = ast::FnContract::default();
        contract.trust_native_requires.push(ast::TrustNativeClause {
            predicate: DUMMY_SP,
            payload: rustc_span::sym::dummy,
            citation: None,
        });
        contract.requires_clauses.push(Box::new(ast::Expr::dummy()));
        contract.trust_opaque_ensures.push(DUMMY_SP);
        contract.trust_native_decreases.push(ast::TrustNativeClause {
            predicate: DUMMY_SP,
            payload: rustc_span::sym::dummy,
            citation: None,
        });
        contract.clause_order.push(ast::FnContractClauseMarker {
            ordinal: 0,
            kind: ast::FnContractClauseKind::Ensures,
            lane: ast::FnContractClauseLane::Opaque,
            lane_index: 0,
        });
        contract.clause_order.push(ast::FnContractClauseMarker {
            ordinal: 1,
            kind: ast::FnContractClauseKind::Requires,
            lane: ast::FnContractClauseLane::Typed,
            lane_index: 0,
        });
        contract.clause_order.push(ast::FnContractClauseMarker {
            ordinal: 2,
            kind: ast::FnContractClauseKind::Decreases,
            lane: ast::FnContractClauseLane::Native,
            lane_index: 0,
        });
        contract.clause_order.push(ast::FnContractClauseMarker {
            ordinal: 3,
            kind: ast::FnContractClauseKind::Requires,
            lane: ast::FnContractClauseLane::Native,
            lane_index: 0,
        });

        let printed = contract_to_string(&contract);
        let ensures = printed.find("trust_ensures_opaque").expect("opaque ensures marker");
        let typed = printed.find("rustc_requires").expect("typed requires marker");
        let decreases = printed.find("trust_decreases_native").expect("native decreases marker");
        let requires = printed.find("trust_requires_native").expect("native requires marker");
        assert!(printed.contains("/*DUMMY*/"), "typed clause payload was dropped: {printed}");
        assert!(
            ensures < typed && typed < decreases && decreases < requires,
            "pretty output ignored authored marker order: {printed}"
        );
        assert_eq!(
            printed.matches("trust_decreases_native").count(),
            1,
            "native decreases clause was emitted more than once: {printed}"
        );
    });
}

#[test]
fn contract_pretty_print_marks_invalid_order_without_grouped_fallback() {
    create_default_session_globals_then(|| {
        let mut contract = ast::FnContract::default();
        contract.trust_native_requires.push(ast::TrustNativeClause {
            predicate: DUMMY_SP,
            payload: rustc_span::sym::dummy,
            citation: None,
        });

        let printed = contract_to_string(&contract);
        assert!(printed.contains("trust_invalid_contract_order"));
        assert!(!printed.contains("trust_requires_native"));
    });
}
