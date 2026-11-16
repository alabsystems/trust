//! Diagnostic wrappers retain declaration identity and kernel obligations.

use clean_elab::source_diagnostics::SourceDiagnostic;
use clean_elab::{ElabError, ElabResult};
use clean_kernel::{Expr, Level};

use super::*;

fn definition(valid: bool) -> ElabResult {
    ElabResult::Definition {
        name: Name::from_string("diagnosed_bridge_decl"),
        universe_params: vec![],
        ty: Expr::sort(if valid { Level::succ(Level::zero()) } else { Level::zero() }),
        val: Expr::sort(Level::zero()),
        modifiers: Default::default(),
    }
}

fn diagnosed(result: ElabResult) -> ElabResult {
    ElabResult::Diagnosed {
        result: Box::new(result),
        diagnostics: vec![SourceDiagnostic {
            error: ElabError::CommandFailed { message: "native compilation diagnostic".to_owned() },
            span: None,
        }],
    }
}

#[test]
fn diagnosed_declaration_retains_its_name_and_source_diagnostics() {
    let result = diagnosed(definition(true));
    let message = result.source_error_message().expect("source diagnostic retained");
    assert_eq!(elab_result_name(&result), "diagnosed_bridge_decl");
    assert_eq!(result.source_error_message().as_deref(), Some(message.as_str()));
}

#[test]
fn nested_diagnosed_declarations_recheck_the_actual_type_and_value() {
    let result = diagnosed(diagnosed(definition(true)));
    let env = Environment::default();
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert_eq!(elab_result_name(&result), "diagnosed_bridge_decl");
    typecheck_elab_result(&result, &tc, &env).expect("Sort 0 has type Sort 1");
    assert!(result.source_error_message().is_some());
}

#[test]
fn diagnosed_declarations_cannot_hide_an_invalid_value() {
    let result = diagnosed(diagnosed(definition(false)));
    let env = Environment::default();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let error =
        typecheck_elab_result(&result, &tc, &env).expect_err("Sort 0 cannot have type Sort 0");
    assert!(error.contains("type check error on value"), "{error}");
    assert!(result.source_error_message().is_some());
}

#[test]
fn bridge_source_retains_registration_but_rejects_guard_diagnostics() {
    let mut env = Environment::with_prelude();
    let source = "/-- error: deliberately unmatched message -/\n#guard_msgs in\ndef bridge_diagnosed : Nat := 0\n";
    let error = load_bridge_source(&mut env, source)
        .expect_err("a registered declaration cannot hide a failed source assertion");
    assert!(error.contains("source diagnostics"), "{error}");
    assert!(error.contains("does not match generated message"), "{error}");
    assert!(env.get_const(&Name::from_string("bridge_diagnosed")).is_some());
}
