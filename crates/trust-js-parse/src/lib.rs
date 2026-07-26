// trust-js-parse: the TrustJS ECMAScript parser — M1 D1 (see Cargo.toml).
//
// FROZEN API CONTRACT for the parse-verdict differential lane: the harness
// judges exactly this surface.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

pub mod ast;
pub mod lexer;
mod parser;
mod parser_expr;
mod regex_validate;
mod unicode_id;
mod unicode_props;

use lexer::Fail;

/// The parse verdict for one source in one mode. `Unsupported` is a sound
/// refusal (grammar not yet implemented) — never a guessed verdict; the
/// verdict lane counts it as no-coverage, and the M1 gate ratchets it to
/// zero.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseOutcome {
    /// The source parses as a Script with no early errors.
    Script(Program),
    /// The spec mandates an early SyntaxError for this source in this mode.
    EarlyError { reason: String },
    /// Grammar surface not yet implemented.
    Unsupported { reason: String },
}

/// AST root; opaque to the verdict lane, consumed by the tier-0 interpreter.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Program {
    pub body: Vec<ast::Stmt>,
    /// The script is strict (caller context or directive prologue).
    pub strict: bool,
}

/// Parse `source` as a Script. `strict` = the caller prepended (or the file
/// carries) a strict-mode context; the directive prologue inside `source`
/// also activates strict per spec.
#[must_use]
pub fn parse_script(source: &str, strict: bool) -> ParseOutcome {
    // Totality belt-and-braces: the parser is written panic-free, but a
    // panic must never surface as anything but a sound refusal.
    let src = source.to_string();
    let result = std::panic::catch_unwind(move || {
        let p = parser::Parser::new(&src);
        p.parse_program(strict)
    });
    match result {
        Ok(Ok(program)) => ParseOutcome::Script(program),
        Ok(Err(Fail::Early(reason))) => ParseOutcome::EarlyError { reason },
        Ok(Err(Fail::Unsupported(reason))) => ParseOutcome::Unsupported { reason },
        Err(_) => ParseOutcome::Unsupported {
            reason: "internal parser panic (refused, not judged)".to_string(),
        },
    }
}

/// Parse `source` as a Module (ECMA-262 §16.2). Modules are ALWAYS strict and
/// carry the module goal (top-level `import`/`export` declarations, top-level
/// `await`, `import.meta`). The verdict has the same three arms as
/// [`parse_script`]; `Script(_)` here means "parses as a Module with no early
/// error". Same totality belt-and-braces: a panic is a sound refusal, never a
/// judged verdict.
#[must_use]
pub fn parse_module(source: &str) -> ParseOutcome {
    let src = source.to_string();
    let result = std::panic::catch_unwind(move || {
        let p = parser::Parser::new(&src);
        p.parse_module_program()
    });
    match result {
        Ok(Ok(program)) => ParseOutcome::Script(program),
        Ok(Err(Fail::Early(reason))) => ParseOutcome::EarlyError { reason },
        Ok(Err(Fail::Unsupported(reason))) => ParseOutcome::Unsupported { reason },
        Err(_) => ParseOutcome::Unsupported {
            reason: "internal parser panic (refused, not judged)".to_string(),
        },
    }
}
