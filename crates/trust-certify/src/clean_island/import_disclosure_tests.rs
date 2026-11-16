// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clean_parser::{SurfaceDecl, parse_file};

use super::{CleanIslandSession, FileContext, standin_imports_in};

#[test]
fn new_leaf_commands_preserve_actual_import_disclosures() {
    for (source, leaf) in [
        ("prelude\nimport Lean\n", "prelude"),
        ("import Lean\nalias copied := original\n", "alias"),
        ("import Lean\n#reduce Nat.succ 0\n", "reduce"),
    ] {
        let declarations = parse_file(source).expect("real Clean parser accepts the fixture");
        assert!(declarations.iter().any(|declaration| match leaf {
            "prelude" => matches!(declaration, SurfaceDecl::Prelude { .. }),
            "alias" => matches!(declaration, SurfaceDecl::Alias { .. }),
            "reduce" => matches!(declaration, SurfaceDecl::Reduce { .. }),
            _ => unreachable!(),
        }));
        let mut context = FileContext::new();
        context.disable_external_import_search();
        let imports = standin_imports_in(&declarations, &context);
        assert_eq!(imports.len(), 1, "{source}");
        assert_eq!(imports[0].module, "Lean");
        assert_eq!(&source[imports[0].start..imports[0].end], "import");
    }
}

#[test]
fn prelude_still_refuses_the_seeded_island_environment() {
    let mut session = CleanIslandSession::new();
    let outcome = session.check("prelude\n");
    assert!(outcome.is_rejected());
    assert!(outcome.errors.iter().any(|error| error.message.contains("fresh module environment")));
    assert!(outcome.registered.is_empty());
    assert!(outcome.standin_imports.is_empty());
}
