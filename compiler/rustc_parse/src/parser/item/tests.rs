// Trust: component identity must survive the syntax-only AST summary.
use clean_parser::{SurfaceDecl, SurfaceName, TacticPatterns};
use rustc_span::{create_default_session_globals_then, sym};

use super::{CleanDeclKind, clean_decl_is_private, clean_decl_kind_and_name};

#[test]
fn clean_ast_names_preserve_components_and_canonicalize_quotes() {
    create_default_session_globals_then(|| {
        let decls = clean_parser::parse_file_with_tactics_located(
            "def A.B : Nat := 1\ndef «A.B» : Nat := 2\ndef «plain» : Nat := 3\ndef plain : Nat := 4\ndef «7» : Nat := 5",
            &TacticPatterns::new(),
        ).unwrap();
        let names: Vec<_> =
            decls.iter().map(|decl| clean_decl_kind_and_name(decl).unwrap().1).collect();
        assert_ne!(names[0], names[1]);
        assert_eq!(names[2], names[3]);
        assert_eq!(names[0].as_str(), "A.B");
        assert_eq!(names[1].as_str(), "«A.B»");
        assert_eq!(names[4].as_str(), "«7»");
        for (decl, name) in decls.iter().zip(&names) {
            let SurfaceDecl::Def { name: original, .. } = decl else { panic!("expected def") };
            assert_eq!(clean_parser::parse_name(name.as_str()).unwrap().name(), original.name());
        }
    });
}

#[test]
fn clean_ast_names_refuse_generated_numeric_identity() {
    create_default_session_globals_then(|| {
        let mut decls = clean_parser::parse_file_with_tactics_located(
            "def seed : Nat := 0",
            &TacticPatterns::new(),
        )
        .unwrap();
        let SurfaceDecl::Def { name, .. } = &mut decls[0] else { panic!("expected def") };
        *name = SurfaceName::from_name(name.name().clone().num(7));
        assert!(clean_decl_kind_and_name(&decls[0]).is_err());
    });
}

fn one_clean_decl(source: &str) -> SurfaceDecl {
    let mut decls = clean_parser::parse_file_with_tactics_located(source, &TacticPatterns::new())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert_eq!(decls.len(), 1, "{source}");
    decls.remove(0)
}

#[test]
fn clean_ast_prelude_is_a_syntax_only_anonymous_marker() {
    create_default_session_globals_then(|| {
        let decl = one_clean_decl("prelude");
        assert!(matches!(decl, SurfaceDecl::Prelude { .. }));
        assert_eq!(clean_decl_kind_and_name(&decl), Ok((CleanDeclKind::Prelude, sym::empty)));
        assert_eq!(CleanDeclKind::Prelude.descr(), "prelude");
        assert!(!CleanDeclKind::Prelude.introduces_name());
        assert!(!clean_decl_is_private(&decl));
    });
}

#[test]
fn clean_ast_alias_summary_preserves_single_identity_and_private_multi_commands() {
    create_default_session_globals_then(|| {
        for (source, expected_name, private, count) in [
            ("alias A.B := original", "A.B", false, 1),
            ("alias «A.B» := original", "«A.B»", false, 1),
            ("alias «7» := original", "«7»", false, 1),
            ("private alias «local alias» := «target.name»", "«local alias»", true, 1),
            ("alias ⟨fwd, bwd⟩ := iffThm", "", false, 2),
            ("private alias ⟨«left.part», «right.part»⟩ := iffThm", "", true, 2),
            ("alias ⟨_, «back.part»⟩ := iffThm", "«back.part»", false, 1),
            ("alias ⟨_, _⟩ := iffThm", "", false, 0),
        ] {
            let decl = one_clean_decl(source);
            let SurfaceDecl::Alias { names, .. } = &decl else {
                panic!("expected alias: {source}")
            };
            assert_eq!(names.len(), count, "{source}");
            let (kind, name) = clean_decl_kind_and_name(&decl).unwrap();
            assert_eq!(kind, CleanDeclKind::Alias);
            assert_eq!(name.as_str(), expected_name, "{source}");
            assert_eq!(clean_decl_is_private(&decl), private, "{source}");
            assert_eq!(decl.span().end, source.len(), "complete command extent: {source}");
            if let [(original, _)] = names.as_slice() {
                assert_eq!(
                    clean_parser::parse_name(name.as_str()).unwrap().name(),
                    original.name()
                );
            }
        }
        assert_eq!(CleanDeclKind::Alias.descr(), "alias");
        assert!(CleanDeclKind::Alias.introduces_name());
    });
}

#[test]
fn clean_ast_reduce_is_not_eval() {
    create_default_session_globals_then(|| {
        for source in ["#reduce 1", "#reduce (proofs := true) (types := true) 1"] {
            let decl = one_clean_decl(source);
            assert!(matches!(decl, SurfaceDecl::Reduce { .. }));
            assert_eq!(clean_decl_kind_and_name(&decl), Ok((CleanDeclKind::Reduce, sym::empty)));
            assert!(!clean_decl_is_private(&decl));
        }
        let eval = one_clean_decl("#eval 1");
        assert_eq!(clean_decl_kind_and_name(&eval), Ok((CleanDeclKind::Eval, sym::empty)));
        assert_eq!(CleanDeclKind::Reduce.descr(), "#reduce");
        assert_ne!(CleanDeclKind::Reduce, CleanDeclKind::Eval);
        assert!(!CleanDeclKind::Reduce.introduces_name());
    });
}
