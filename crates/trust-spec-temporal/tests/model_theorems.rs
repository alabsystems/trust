// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! B1b's theorem harness (lane `lane/beyond-tla-b1b`, B1B-01a; B1B-D05, D06, D09, D20).
//!
//! B1b's Clean modules (`THEORY`) are served by this test target only during the lane
//! (B1B-D05): B1a's `trust-model-prelude` is never touched. A test of a module elaborates,
//! on a clone of B1a's cached model prelude (`with_model_prelude`, on the kernel-worker
//! pool), the module's transitive dependency closure in `THEORY` order and nothing
//! else, each module through B1a's `elaborate_model_suffix`. It then checks:
//!
//! * **exact set** (B1B-D09): the theorems the module adds are exactly the `proved`
//!   rows of `THEOREMS.tsv` for it, no more and no fewer;
//! * **kernel** (B1B-D05): each through B1a's `check_model_theorem` (kernel re-check,
//!   constructive quality, empty `axiom_deps`, certification audit), a spent
//!   declaration budget being a failure, never a pass;
//! * **census** (B1B-D06 (b)): each theorem's foundational axioms lie in
//!   `{propext, Quot.sound, Quot, Quot.mk, Quot.lift, Quot.ind}`, plus
//!   `Classical.choice` only when its row's `classical` column names the decision that
//!   admits it (and a named waiver must be used);
//! * **no axiom-kind constant** (B1B-D06 (c)): no module of the closure adds an
//!   axiom-kind constant (an `axiom`, or a body-less `opaque`, which Clean lowers to
//!   one), by a kernel walk over every constant each module adds, backed by a token
//!   scan of the sources (on Clean's lexer) for `axiom`, `sorry`, `sorryAx`, `admit`,
//!   the trust markers and a body-less `opaque`;
//! * a module run that checked no theorem fails.
//!
//! A definition module's test (`definitions_<m>`) requires, of every constant it adds,
//! an empty `axiom_deps` and a clean certification audit (B1B-D49), and applies census
//! rule (d): the constant reaches no foundational axiom beyond the union of those its
//! B1a callees reach, and never `Classical.choice`.
//!
//! The token scan and the `autoImplicit` shape check read the source through Clean's
//! own lexer (B1B-D49).
//!
//! * **statement digest** (B1B-D07 (d), B1B-01b): each theorem's elaborated statement
//!   digest ([`statement_digest`]) equals its THEOREMS.tsv `stmt_digest`;
//! * **no implicit premise** (B1B-D30, kernel side, B1B-01b): for a ledger-backed
//!   theorem, no non-explicit binder of the leading Pi telescope of its type has a type
//!   that is (or may be) a proposition ([`implicit_binders`]);
//! * **no unchecked axiom route through a helper** (B1B-01b, the B1B-01f verifier's
//!   item 3): every constant the module adds, theorem or not, has empty `axiom_deps`.
//!
//! Each checked theorem prints `census <name> foundational=[...] classical=<decision|->`,
//! `digest <name> <hex>`, for a ledger-backed one `binders <name> implicit=<k>
//! implicit_premises=<p>`, then `theorem <name> ok`, and the run ends with
//! `module <m>: <n> theorems`.
//!
//! Kernel tests are release-only (B1B-D20): this crate has no opt-level overrides for
//! Clean. The `smoke_*` tests run in debug, on the push lane, and elaborate nothing.
//!
//! Naming: a `THEORY` module's harness name is its last path component, lowercased
//! (`Trust.Thm.Ports` is `ports`); `module_<m>` resolves it among the theorem modules
//! (`Trust.Thm.*`), `definitions_<m>` among the others (B1B-D44).

use std::collections::{BTreeMap, BTreeSet, HashSet};

use clean_kernel::env::{CertificationIssue, Environment};
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, TypeChecker};
use clean_parser::lexer::{Lexer, Token, TokenKind};
use trust_sha2::{Digest, Sha256};
use trust_spec_temporal::model_prelude::{
    ModelPrelude, ModelPreludeError, check_model_theorem, elaborate_model_suffix,
    prelude_added_constants, with_model_prelude,
};

/// `(module, direct dependencies, source)`.
type TheoryModule = (&'static str, &'static [&'static str], &'static str);

/// B1b's lane modules (B1B-D05), definition modules first, then the theorem modules in
/// row order; a module enters in the row that creates it, and `THEORY_DIGEST` is
/// re-blessed in that row (`print_theory_digest`, TASK-STATE 4.5).
const THEORY: &[TheoryModule] = &[("Trust.Thm.Ports", &[], trust_model_prelude::PORTS)];

/// SHA-256 over `(name NUL source NUL)*` in `THEORY` order (B1B-D05, B1A-D35's framing).
const THEORY_DIGEST: &str = "0045228e0561364437a4d3d2882a2d8215e4f6ce0d64fd6e201cafc01a4584b5";

/// The exact declarations each definition module adds, by harness name (B1B-D09).
const DEFINITIONS: &[(&str, &[&str])] = &[];

const THEOREMS_TSV: &str = include_str!("model_theorems/THEOREMS.tsv");
/// The per-constant digests of the statement closures of the proved rows (B1B-D59).
const CLOSURE_TSV: &str = include_str!("model_theorems/CLOSURE.tsv");
const CLOSURE_HEADER: [&str; 2] = ["constant", "digest"];
const THEOREM_MODULE_PREFIX: &str = "Trust.Thm.";
const THEOREMS_HEADER: [&str; 7] =
    ["ledger_id", "lean_name", "module", "row", "stmt_digest", "classical", "status"];

/// B1B-D06 (b): the foundational axioms a theorem may reach without a waiver.
const ALLOWED_FOUNDATIONAL: [&str; 6] =
    ["propext", "Quot.sound", "Quot", "Quot.mk", "Quot.lift", "Quot.ind"];
const CLASSICAL_CHOICE: &str = "Classical.choice";

/// Identifiers the token scan refuses wherever they occur outside comments and strings
/// (B1B-D06 (c)); a body-less `opaque` is scanned for separately.
const FORBIDDEN_TOKENS: [&str; 6] =
    ["axiom", "sorry", "sorryAx", "admit", "trustedArith", "trustedAy"];

// ---------------------------------------------------------------------------------
// THEOREMS.tsv
// ---------------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
struct TheoremRow {
    ledger_id: String,
    lean_name: String,
    module: String,
    row: String,
    stmt_digest: String,
    classical: String,
    proved: bool,
}

fn is_row_id(text: &str) -> bool {
    let Some(rest) = text.strip_prefix("B1B-") else { return false };
    let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
    let tail = &rest[digits..];
    (digits == 2
        && (tail.is_empty() || (tail.len() == 1 && tail.as_bytes()[0].is_ascii_lowercase())))
        || rest == "M1"
}

fn is_decision(text: &str) -> bool {
    text.strip_prefix("B1B-D")
        .is_some_and(|d| d.len() == 2 && d.bytes().all(|b| b.is_ascii_digit()))
}

/// Parse a THEOREMS.tsv (TASKS.md Appendix B): the exact header, seven tab-separated
/// cells per row, a `TH-` ledger id or `-`, a qualified unique `lean_name`, a harness
/// module name, a B1b row id, a 64-hex digest or `-`, a `B1B-Dnn` waiver or `-`, and
/// `pending` or `proved`.
fn parse_theorems(text: &str) -> Result<Vec<TheoremRow>, String> {
    let mut lines = text.lines();
    let header: Vec<&str> = lines.next().ok_or("empty table")?.split('\t').collect();
    if header != THEOREMS_HEADER {
        return Err(format!("header {header:?} is not {THEOREMS_HEADER:?}"));
    }
    let mut rows = Vec::new();
    let mut names = BTreeSet::new();
    for (number, line) in lines.enumerate() {
        let at = number + 2;
        let cells: Vec<&str> = line.split('\t').collect();
        let [ledger_id, lean_name, module, row, stmt_digest, classical, status] = cells[..] else {
            return Err(format!("line {at}: {} cells, want 7", cells.len()));
        };
        if !(ledger_id == "-" || ledger_id.starts_with("TH-") && ledger_id.len() > 3) {
            return Err(format!("line {at}: ledger id {ledger_id:?}"));
        }
        if !lean_name.contains('.') || lean_name.contains(char::is_whitespace) {
            return Err(format!("line {at}: lean_name {lean_name:?} is not a qualified name"));
        }
        if !names.insert(lean_name.to_owned()) {
            return Err(format!("line {at}: lean_name {lean_name} listed twice"));
        }
        if module.is_empty()
            || !module.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit())
        {
            return Err(format!("line {at}: module {module:?} is not a harness name"));
        }
        if !is_row_id(row) {
            return Err(format!("line {at}: row {row:?}"));
        }
        if !(stmt_digest == "-"
            || stmt_digest.len() == 64
                && stmt_digest.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase()))
        {
            return Err(format!("line {at}: stmt_digest {stmt_digest:?}"));
        }
        if !(classical == "-" || is_decision(classical)) {
            return Err(format!("line {at}: classical {classical:?} is neither - nor B1B-Dnn"));
        }
        let proved = match status {
            "proved" => true,
            "pending" => false,
            other => return Err(format!("line {at}: status {other:?}")),
        };
        rows.push(TheoremRow {
            ledger_id: ledger_id.to_owned(),
            lean_name: lean_name.to_owned(),
            module: module.to_owned(),
            row: row.to_owned(),
            stmt_digest: stmt_digest.to_owned(),
            classical: classical.to_owned(),
            proved,
        });
    }
    Ok(rows)
}

fn theorems() -> Vec<TheoremRow> {
    parse_theorems(THEOREMS_TSV).unwrap_or_else(|error| panic!("THEOREMS.tsv: {error}"))
}

fn is_digest(text: &str) -> bool {
    text.len() == 64 && text.bytes().all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

/// Parse a CLOSURE.tsv (B1B-D59): the exact header `constant<TAB>digest`, then one row
/// per closure constant, its name and a 64-hex digest, names unique and ascending.
fn parse_closure(text: &str) -> Result<BTreeMap<String, String>, String> {
    let mut lines = text.lines();
    let header: Vec<&str> = lines.next().ok_or("empty table")?.split('\t').collect();
    if header != CLOSURE_HEADER {
        return Err(format!("header {header:?} is not {CLOSURE_HEADER:?}"));
    }
    let mut table = BTreeMap::new();
    let mut last: Option<String> = None;
    for (number, line) in lines.enumerate() {
        let at = number + 2;
        let cells: Vec<&str> = line.split('\t').collect();
        let [constant, digest] = cells[..] else {
            return Err(format!("line {at}: want 2 cells"));
        };
        if constant.is_empty() || constant.contains(char::is_whitespace) || !is_digest(digest) {
            return Err(format!("line {at}: {line:?}"));
        }
        if last.as_deref().is_some_and(|l| l >= constant) {
            return Err(format!("line {at}: {constant} is not after {}", last.unwrap_or_default()));
        }
        last = Some(constant.to_owned());
        table.insert(constant.to_owned(), digest.to_owned());
    }
    Ok(table)
}

fn closure_table() -> BTreeMap<String, String> {
    parse_closure(CLOSURE_TSV).unwrap_or_else(|error| panic!("CLOSURE.tsv: {error}"))
}

// ---------------------------------------------------------------------------------
// THEORY: digest, names, dependency closure
// ---------------------------------------------------------------------------------

fn theory_digest(theory: &[TheoryModule]) -> String {
    let mut hasher = Sha256::new();
    for (name, _, source) in theory {
        hasher.update(name.as_bytes());
        hasher.update([0u8]);
        hasher.update(source.as_bytes());
        hasher.update([0u8]);
    }
    hasher.finalize().as_ref().iter().map(|byte| format!("{byte:02x}")).collect()
}

fn harness_name(module: &str) -> String {
    module.rsplit('.').next().unwrap_or(module).to_ascii_lowercase()
}

/// The `THEORY` index of the theorem module (`theorems`) or definition module
/// (`!theorems`) whose harness name is `harness`.
fn find_module(
    theory: &[TheoryModule],
    theorem_prefix: &str,
    theorems: bool,
    harness: &str,
) -> Result<usize, String> {
    let found: Vec<usize> = (0..theory.len())
        .filter(|&i| theory[i].0.starts_with(theorem_prefix) == theorems)
        .filter(|&i| harness_name(theory[i].0) == harness)
        .collect();
    match found[..] {
        [index] => Ok(index),
        [] => Err(format!(
            "no {} module named {harness}",
            if theorems { "theorem" } else { "definition" }
        )),
        _ => Err(format!("{} modules are named {harness}", found.len())),
    }
}

/// The transitive dependency closure of `theory[index]`, in `THEORY` order, ending with
/// the module itself. A dependency must be an earlier `THEORY` module.
fn closure(theory: &[TheoryModule], index: usize) -> Result<Vec<usize>, String> {
    let mut needed = BTreeSet::from([index]);
    let mut work = vec![index];
    while let Some(i) = work.pop() {
        for dep in theory[i].1 {
            let Some(d) = theory.iter().position(|(name, _, _)| name == dep) else {
                return Err(format!(
                    "{} depends on {dep}, which is not a THEORY module",
                    theory[i].0
                ));
            };
            if d >= i {
                return Err(format!(
                    "{} depends on {dep}, which is not earlier in THEORY",
                    theory[i].0
                ));
            }
            if needed.insert(d) {
                work.push(d);
            }
        }
    }
    Ok(needed.into_iter().collect())
}

/// Structural checks of a THEORY list: unique names, unique harness names per kind,
/// dependencies earlier, and every module's `autoImplicit` setting fixed (B1B-D07 (b),
/// D44, D49): its first three tokens are `set_option autoImplicit false`, alone on the
/// first code line and not continued by `in` (which would scope the option to one
/// command), and no later token names `autoImplicit` or `relaxedAutoImplicit` (a later
/// `set_option autoImplicit true`, or a `set_option autoImplicit true in` prefix, would
/// undo it). Tokens come from Clean's own lexer, which the elaborator parses with.
fn theory_shape(theory: &[TheoryModule], theorem_prefix: &str) -> Vec<String> {
    let mut problems = Vec::new();
    let mut names = BTreeSet::new();
    let mut harness = BTreeSet::new();
    for (index, (name, _, source)) in theory.iter().enumerate() {
        if !names.insert(*name) {
            problems.push(format!("{name} listed twice"));
        }
        if !harness.insert((name.starts_with(theorem_prefix), harness_name(name))) {
            problems.push(format!("harness name {} used twice", harness_name(name)));
        }
        if let Err(error) = closure(theory, index) {
            problems.push(error);
        }
        problems.extend(auto_implicit_problems(source).into_iter().map(|p| format!("{name} {p}")));
    }
    problems
}

/// Option names whose later setting would re-enable auto-bound implicits.
const AUTO_IMPLICIT_OPTIONS: [&str; 2] = ["autoImplicit", "relaxedAutoImplicit"];

fn is_ident(token: &Token, text: &str) -> bool {
    matches!(&token.kind, TokenKind::Ident(name) if name == text)
}

/// The `autoImplicit` problems of one module's source (see [`theory_shape`]).
fn auto_implicit_problems(source: &str) -> Vec<String> {
    let tokens = Lexer::tokenize(source);
    let mut problems = Vec::new();
    let opens = tokens.len() >= 4
        && tokens[0].kind == TokenKind::SetOption
        && is_ident(&tokens[1], "autoImplicit")
        && is_ident(&tokens[2], "false")
        && tokens[1..3].iter().all(|t| t.line == tokens[0].line)
        && (tokens[3].kind == TokenKind::Eof || tokens[3].line > tokens[0].line);
    if !opens {
        problems.push(
            "does not begin with `set_option autoImplicit false` alone on its line".to_owned(),
        );
    }
    if tokens.get(3).is_some_and(|t| t.kind == TokenKind::In) {
        problems.push("scopes `set_option autoImplicit false` to one command with `in`".to_owned());
    }
    for token in tokens.iter().skip(if opens { 3 } else { 0 }) {
        if let TokenKind::Ident(ident) = &token.kind {
            if ident.split('.').any(|part| AUTO_IMPLICIT_OPTIONS.contains(&part)) {
                problems.push(format!("sets `{ident}` again (line {})", token.line));
            }
        }
    }
    problems
}

// ---------------------------------------------------------------------------------
// Token scan (B1B-D06 (c), D49)
// ---------------------------------------------------------------------------------

/// Every forbidden token of `source` and every body-less `opaque` declaration (an
/// `opaque` whose declaration, up to the next token that starts a line at column 0,
/// has no `:=`), as `<token> (line <n>)`, plus every lexer error (`lex error`).
///
/// The source is read by Clean's own lexer (`clean_parser::lexer::Lexer`, the one the
/// elaborator's parser uses), so comments, string literals and character literals are
/// exactly what Clean takes them to be: a `'"'` cannot open a string here that Clean
/// never opens (B1B-D49). An identifier is refused when any of its `.`-separated
/// components is forbidden (`_root_.sorryAx` included); `sorry`, `axiom` and `opaque`
/// are keyword tokens. A lexer error is reported, never skipped: the token stream after
/// it is not one this scan can vouch for.
///
/// Clean's lexer returns an interpolated string (`s!"…{e}…"`, `m!`, `f!`) as one token
/// holding its raw text; the elaborator parses each `{…}` hole as a term, so every hole
/// is scanned in turn, on the same lexer, and a find is reported at the string's line
/// (B1B-01b, the B1B-01f verifier's item 3).
fn axiom_tokens(source: &str) -> Vec<String> {
    axiom_tokens_at(source, None)
}

/// [`axiom_tokens`], every find reported at `at` when given (an interpolation hole).
fn axiom_tokens_at(source: &str, at: Option<u32>) -> Vec<String> {
    let tokens = Lexer::tokenize(source);
    let mut found = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        let line = at.unwrap_or(token.line);
        match &token.kind {
            TokenKind::Axiom => found.push(format!("axiom (line {line})")),
            TokenKind::Sorry => found.push(format!("sorry (line {line})")),
            TokenKind::Ident(ident) => {
                if let Some(part) = ident.split('.').find(|part| FORBIDDEN_TOKENS.contains(part)) {
                    found.push(format!("{part} (line {line})"));
                }
            }
            TokenKind::InterpolatedString(_, raw) => {
                for hole in interpolation_holes(raw) {
                    found.extend(axiom_tokens_at(&hole, Some(line)));
                }
            }
            TokenKind::Opaque => {
                let has_body = tokens[index + 1..]
                    .iter()
                    .take_while(|t| {
                        t.kind != TokenKind::Eof && !(t.preceded_by_newline && t.col == 0)
                    })
                    .any(|t| t.kind == TokenKind::ColonEq);
                if !has_body {
                    found.push(format!("body-less opaque (line {line})"));
                }
            }
            TokenKind::Error(error) => found.push(format!("lex error {error} (line {line})")),
            _ => {}
        }
    }
    found
}

/// Identifiers that open authored syntax and are not keyword tokens of Clean's lexer.
const NOTATION_IDENTS: [&str; 3] = ["declare_syntax_cat", "elab_rules", "notation3"];

/// Every authored-notation command and syntax quotation of `source` (TASK-STATE 4.8,
/// B1A-D70: no authored notation; B1B-01e, the B1B-01g verifier's item 5 (1)), as
/// `<what> (line <n>)`: the keyword tokens `notation`, `infix`, `infixl`, `infixr`,
/// `prefix`, `postfix`, `macro`, `macro_rules`, `syntax` and `elab`, an identifier
/// with a component in [`NOTATION_IDENTS`], and any syntax quotation or name literal
/// (Clean's `SyntaxQuote` token, `` `(…) `` and `` `name ``), each read on Clean's
/// lexer, holes of interpolated strings included. A lane module that redefines what
/// its statement's text means would make the text check compare spellings, not
/// statements, so such a module is refused, never interpreted.
fn notation_tokens(source: &str) -> Vec<String> {
    notation_tokens_at(source, None)
}

fn notation_tokens_at(source: &str, at: Option<u32>) -> Vec<String> {
    let mut found = Vec::new();
    for token in Lexer::tokenize(source) {
        let line = at.unwrap_or(token.line);
        let what = match &token.kind {
            TokenKind::Notation => Some("notation".to_owned()),
            TokenKind::Infix => Some("infix".to_owned()),
            TokenKind::Infixl => Some("infixl".to_owned()),
            TokenKind::Infixr => Some("infixr".to_owned()),
            TokenKind::Prefix => Some("prefix".to_owned()),
            TokenKind::Postfix => Some("postfix".to_owned()),
            TokenKind::Macro => Some("macro".to_owned()),
            TokenKind::MacroRules => Some("macro_rules".to_owned()),
            TokenKind::Syntax => Some("syntax".to_owned()),
            TokenKind::Elab => Some("elab".to_owned()),
            TokenKind::SyntaxQuote(_) => Some("syntax quotation".to_owned()),
            TokenKind::Ident(ident) => {
                ident.split('.').find(|part| NOTATION_IDENTS.contains(part)).map(str::to_owned)
            }
            TokenKind::InterpolatedString(_, raw) => {
                for hole in interpolation_holes(raw) {
                    found.extend(notation_tokens_at(&hole, Some(line)));
                }
                None
            }
            _ => None,
        };
        if let Some(what) = what {
            found.push(format!("{what} (line {line})"));
        }
    }
    found
}

/// The `{…}` holes of an interpolated string's raw text as Clean's lexer keeps it
/// (escapes verbatim, braces balanced inside a hole), outermost holes only; an
/// unbalanced hole runs to the end, so nothing after an open `{` goes unscanned.
fn interpolation_holes(raw: &str) -> Vec<String> {
    let mut holes = Vec::new();
    let mut depth = 0u32;
    let mut current = String::new();
    let mut chars = raw.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            let next = chars.next();
            if depth > 0 {
                current.push(c);
                current.extend(next);
            }
            continue;
        }
        match c {
            '{' => {
                if depth > 0 {
                    current.push(c);
                }
                depth += 1;
            }
            '}' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    holes.push(std::mem::take(&mut current));
                } else {
                    current.push(c);
                }
            }
            _ if depth > 0 => current.push(c),
            _ => {}
        }
    }
    if depth > 0 {
        holes.push(current);
    }
    holes
}

// ---------------------------------------------------------------------------------
// Declarations on Clean's lexer (B1B-D57; the B1B-01b verifier's items 2 and 3)
// ---------------------------------------------------------------------------------

/// One `theorem` or `lemma` declaration of a module source, as Clean's lexer reads it
/// (Clean parses `lemma` as `theorem`, clean-parser `grammar/decl/mod.rs`).
#[derive(Debug, Clone, PartialEq, Eq)]
struct Declaration {
    /// The declared name, resolved in the namespace in effect (`_root_.` is absolute).
    resolved: String,
    /// The namespace in effect (`namespace X` ... `end X`), `""` at the root.
    namespace: String,
    /// The statement from the keyword to the first `:=` outside brackets, rendered from
    /// the tokens: each token's source text, one space where the source has whitespace
    /// or a comment between two tokens, nothing where they touch. A comment is never
    /// part of a statement, and no comment declares anything.
    statement: String,
    line: u32,
}

fn opens_bracket(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::LParen
            | TokenKind::LBrace
            | TokenKind::LBracket
            | TokenKind::LAngle
            | TokenKind::LDAngle
            | TokenKind::LFrench
            | TokenKind::StrictLBrace
    )
}

fn closes_bracket(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::RParen
            | TokenKind::RBrace
            | TokenKind::RBracket
            | TokenKind::RBracketPrime
            | TokenKind::RAngle
            | TokenKind::RDAngle
            | TokenKind::RFrench
            | TokenKind::StrictRBrace
    )
}

/// The dotted name starting at `tokens[index]`: an identifier, then every `.` and
/// identifier that touch it (Clean's lexer returns `A.B` as `A`, `.`, `B`), with the
/// index after it; `None` when `tokens[index]` is no identifier.
fn dotted_name(tokens: &[Token], index: usize) -> Option<(String, usize)> {
    let TokenKind::Ident(first) = &tokens.get(index)?.kind else { return None };
    let mut name = first.clone();
    let mut next = index + 1;
    while let (Some(dot), Some(part)) = (tokens.get(next), tokens.get(next + 1)) {
        let touching =
            dot.span.start == tokens[next - 1].span.end && part.span.start == dot.span.end;
        match (&dot.kind, &part.kind) {
            (TokenKind::Dot, TokenKind::Ident(text)) if touching => {
                name.push('.');
                name.push_str(text);
                next += 2;
            }
            _ => break,
        }
    }
    Some((name, next))
}

/// A scope of [`declarations`]' reading: a `namespace` block with the components it
/// still holds open, a `section` (with its name, if any) or a `mutual` block.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Scope {
    Namespace(Vec<String>),
    Section(Option<String>),
    Mutual,
}

/// Whether `end_name`'s components are a component-wise suffix of `open`'s.
fn is_suffix(open: &[String], end_name: &[&str]) -> bool {
    !end_name.is_empty()
        && end_name.len() <= open.len()
        && open[open.len() - end_name.len()..].iter().zip(end_name).all(|(a, b)| a == b)
}

/// Every `theorem` and `lemma` declaration of `source`, read on Clean's own lexer
/// (`clean_parser::lexer::Lexer`, the one the elaborator parses with), so comments,
/// nested block comments, doc comments, strings and character literals are exactly
/// what Clean takes them to be (B1B-D57).
///
/// Scopes follow Clean's own rule (clean-parser `grammar/decl/commands.rs`,
/// `namespace_block` and `try_consume_end_name`; B1B-01e, the B1B-01g verifier's item
/// 4): `namespace A.B` opens one block holding the components `A`, `B`; an `end X`
/// whose components are a component-wise suffix of the innermost block's closes that
/// many components (a partial `end B` leaves `A` open) and consumes `X`; a bare `end`,
/// or one whose name is no such suffix, closes the whole block and leaves the name
/// unconsumed, as Clean does. `section [S]` and `mutual` open an unnamed scope for the
/// namespace that `end` closes (a named section's `end S` consumes `S`). A lexer
/// error, a declaration keyword without a name, an `end` that closes nothing, a scope
/// still open at the end of the file (legal in Clean, refused here: fail-closed), or
/// a statement with no `:=` before the next command (a token at column 0 on a new
/// line) is an error, never a skipped declaration.
fn declarations(source: &str) -> Result<Vec<Declaration>, String> {
    let tokens = Lexer::tokenize(source);
    let text = |token: &Token| {
        source
            .get(token.span.start..token.span.end)
            .ok_or_else(|| format!("token span {:?} outside the source", token.span))
    };
    let mut scopes: Vec<Scope> = Vec::new();
    let mut out = Vec::new();
    let mut index = 0;
    while index < tokens.len() {
        let token = &tokens[index];
        let line = token.line;
        match &token.kind {
            TokenKind::Error(error) => return Err(format!("lex error {error} (line {line})")),
            TokenKind::Namespace => {
                let Some((name, next)) = dotted_name(&tokens, index + 1) else {
                    return Err(format!("`namespace` without a name (line {line})"));
                };
                scopes.push(Scope::Namespace(name.split('.').map(str::to_owned).collect()));
                index = next;
                continue;
            }
            TokenKind::Section => {
                let named = dotted_name(&tokens, index + 1).filter(|(name, _)| name != "local");
                scopes.push(Scope::Section(named.as_ref().map(|(name, _)| name.clone())));
                index = named.map_or(index + 1, |(_, next)| next);
                continue;
            }
            TokenKind::Mutual => scopes.push(Scope::Mutual),
            TokenKind::End => {
                let end_name = dotted_name(&tokens, index + 1);
                let parts: Vec<&str> = end_name
                    .as_ref()
                    .map(|(name, _)| name.split('.').collect())
                    .unwrap_or_default();
                let mut next = index + 1;
                match scopes.last_mut() {
                    None => return Err(format!("`end` closes no scope (line {line})")),
                    Some(Scope::Namespace(open)) if is_suffix(open, &parts) => {
                        open.truncate(open.len() - parts.len());
                        if open.is_empty() {
                            scopes.pop();
                        }
                        next = end_name.map_or(next, |(_, after)| after);
                    }
                    Some(Scope::Section(Some(section))) => {
                        let open: Vec<String> = section.split('.').map(str::to_owned).collect();
                        if is_suffix(&open, &parts) {
                            next = end_name.map_or(next, |(_, after)| after);
                        }
                        scopes.pop();
                    }
                    Some(_) => {
                        scopes.pop();
                    }
                }
                index = next;
                continue;
            }
            TokenKind::Theorem | TokenKind::Lemma => {
                let Some((name, _)) = dotted_name(&tokens, index + 1) else {
                    return Err(format!("a declaration keyword without a name (line {line})"));
                };
                let namespace: String = scopes
                    .iter()
                    .filter_map(|scope| match scope {
                        Scope::Namespace(open) => Some(open.join(".")),
                        _ => None,
                    })
                    .collect::<Vec<_>>()
                    .join(".");
                let resolved = match name.strip_prefix("_root_.") {
                    Some(absolute) => absolute.to_owned(),
                    None if name == "_root_" => {
                        return Err(format!("`_root_` without a name (line {line})"));
                    }
                    None if namespace.is_empty() => name.clone(),
                    None => format!("{namespace}.{name}"),
                };
                let mut depth = 0i64;
                let mut end = None;
                for (j, next) in tokens.iter().enumerate().skip(index + 1) {
                    if next.kind == TokenKind::Eof || (next.preceded_by_newline && next.col == 0) {
                        break;
                    }
                    if opens_bracket(&next.kind) {
                        depth += 1;
                    } else if closes_bracket(&next.kind) {
                        depth -= 1;
                    } else if next.kind == TokenKind::ColonEq && depth == 0 {
                        end = Some(j);
                        break;
                    }
                }
                let Some(end) = end else {
                    return Err(format!("{resolved}: no `:=` ends its statement (line {line})"));
                };
                let mut statement = String::new();
                for j in index..end {
                    if j > index && tokens[j].span.start > tokens[j - 1].span.end {
                        statement.push(' ');
                    }
                    statement.push_str(text(&tokens[j])?);
                }
                out.push(Declaration { resolved, namespace, statement, line });
                index = end + 1;
                continue;
            }
            _ => {}
        }
        index += 1;
    }
    if !scopes.is_empty() {
        return Err(format!("scope(s) still open at the end of the file: {scopes:?}"));
    }
    Ok(out)
}

/// The `declaration` cross-check of `module_<m>` (B1B-D57): every source declaration
/// (Clean's lexer reading) resolves to a theorem the module adds (`found`), so the
/// lexer's namespace reading agrees with the elaborator's, and every checked theorem
/// (`found` ∩ `expected`) has exactly one source declaration: the text check reads
/// that one. A reading that failed is itself a problem. Returns the problems.
fn declaration_problems(
    declared: &Result<Vec<Declaration>, String>,
    module: &str,
    found: &BTreeSet<String>,
    expected: &BTreeSet<String>,
) -> Vec<String> {
    let declared = match declared {
        Err(error) => return vec![format!("{module}: {error}")],
        Ok(declared) => declared,
    };
    let mut problems = Vec::new();
    for declaration in declared {
        if !found.contains(&declaration.resolved) {
            problems.push(format!(
                "{} (line {}) is no theorem {module} adds",
                declaration.resolved, declaration.line
            ));
        }
    }
    for name in found.intersection(expected) {
        let count = declared.iter().filter(|d| &d.resolved == name).count();
        if count != 1 {
            problems.push(format!("{name}: {count} source declarations resolve to it"));
        }
    }
    problems
}

/// The file a lane `THEORY` module is read from: `Trust.A.B` is `clean/Trust/A/B.lean`
/// under the crate (B1B-D04).
fn theory_file(clean_root: &std::path::Path, module: &str) -> std::path::PathBuf {
    let mut path = clean_root.to_path_buf();
    for part in module.split('.') {
        path.push(part);
    }
    path.set_extension("lean");
    path
}

/// The `THEORY` sources and the files on disk agree (the B1B-01b verifier's item 3):
/// every module's `include_str!` source equals the bytes of [`theory_file`], and every
/// `.lean` file under the B1b-owned directories `owned` (relative to `clean_root`,
/// e.g. `Trust/Thm`) is a `THEORY` module. A missing directory holds no file.
fn theory_file_problems(
    theory: &[TheoryModule],
    clean_root: &std::path::Path,
    owned: &[&str],
) -> Vec<String> {
    let mut problems = Vec::new();
    let mut listed = BTreeSet::new();
    for (module, _, source) in theory {
        let path = theory_file(clean_root, module);
        listed.insert(path.clone());
        match std::fs::read(&path) {
            Ok(bytes) if bytes == source.as_bytes() => {}
            Ok(_) => {
                problems.push(format!("{module}: THEORY's source differs from {}", path.display()))
            }
            Err(error) => problems.push(format!("{module}: {}: {error}", path.display())),
        }
    }
    for dir in owned {
        let Ok(entries) = std::fs::read_dir(clean_root.join(dir)) else { continue };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().is_some_and(|e| e == "lean") && !listed.contains(&path) {
                problems.push(format!("{} is not a THEORY module", path.display()));
            }
        }
    }
    problems
}

/// The directories under `clean/` whose every file is a lane `THEORY` module.
const OWNED_THEORY_DIRS: [&str; 2] = ["Trust/Thm", "Trust/Cert"];

// ---------------------------------------------------------------------------------
// The runners
// ---------------------------------------------------------------------------------

/// What a module run printed and why it failed. A failure reads `<kind>: <detail>`.
#[derive(Debug, Default, Clone)]
struct Outcome {
    lines: Vec<String>,
    failures: Vec<String>,
    checked: usize,
    /// The per-constant closure digests of every digested statement (B1B-D59), for
    /// `print_statement_digests`; not printed.
    closures: BTreeMap<String, String>,
}

impl Outcome {
    fn fail(&mut self, kind: &str, detail: impl std::fmt::Display) {
        self.failures.push(format!("{kind}: {detail}"));
    }

    fn kinds(&self) -> BTreeSet<String> {
        self.failures
            .iter()
            .map(|failure| failure.split(": ").next().unwrap_or(failure).to_owned())
            .collect()
    }

    fn print(&self) {
        for line in &self.lines {
            println!("{line}");
        }
        for failure in &self.failures {
            println!("FAIL {failure}");
        }
    }
}

fn is_budget(error: &ModelPreludeError) -> bool {
    matches!(error, ModelPreludeError::BudgetExhausted { .. })
}

fn name_set(environment: &Environment) -> HashSet<Name> {
    prelude_added_constants(environment).into_iter().collect()
}

fn sorted(names: impl IntoIterator<Item = Name>) -> Vec<Name> {
    let mut names: Vec<Name> = names.into_iter().collect();
    names.sort_by_cached_key(ToString::to_string);
    names
}

/// An axiom-kind constant: an `axiom`, or an `opaque` with no value (B1B-D06 (c)).
fn is_axiom_kind(environment: &Environment, name: &Name) -> bool {
    environment.get_const(name).is_some_and(|constant| {
        constant.kind == ConstantKind::Axiom
            || (constant.kind == ConstantKind::Opaque && constant.value.is_none())
    })
}

/// The foundational axioms `name` reaches. `None` from the kernel (no such constant)
/// is an error, never an empty census (fails closed).
fn foundational(environment: &Environment, name: &Name) -> Result<BTreeSet<String>, String> {
    environment
        .foundational_axiom_deps(name)
        .map(|axioms| axioms.iter().map(ToString::to_string).collect())
        .ok_or_else(|| format!("the kernel has no constant {name} to take the census of"))
}

/// The non-foundational axioms `name` reaches (domain axioms and trust markers such as
/// `sorryAx`), sorted. `None` from the kernel is an error (fails closed).
fn non_foundational(environment: &Environment, name: &Name) -> Result<Vec<String>, String> {
    let axioms = environment
        .axiom_deps(name)
        .ok_or_else(|| format!("the kernel has no constant {name} to take axiom_deps of"))?;
    let mut axioms: Vec<String> = axioms.iter().map(ToString::to_string).collect();
    axioms.sort();
    Ok(axioms)
}

/// Clean's certification audit of a constant a definition module adds (B1B-D06 (b),
/// D49): the judgment `c : type(c)` with `c` applied to its own universe parameters,
/// so the audit walks `c` itself, its type and value, and everything they reach,
/// re-checking each declaration and refusing trust markers, unsafe or partial
/// constants, unchecked or structural-only declarations and non-foundational axioms.
/// A definition's type is data, not a proposition, so the one issue that is admitted is
/// `GoalNotProposition` in the form the audit gives when the goal's sort was inferred
/// and is not `Prop` (clean-kernel `env/axiom_audit.rs`, `audit_certification`:
/// `goal lives in Sort …, not Prop`); the same variant carrying an inference error
/// (`Err(error)` from `infer_sort`) is returned like every other issue (B1B-01b, the
/// B1B-01f verifier's item 5).
fn definition_audit(environment: &Environment, name: &Name) -> Result<Vec<String>, String> {
    let constant = environment
        .get_const(name)
        .ok_or_else(|| format!("the kernel has no constant {name} to audit"))?;
    let levels: Vec<Level> = constant.level_params.iter().cloned().map(Level::param).collect();
    let audit =
        environment.audit_certification(&constant.type_, &Expr::const_(name.clone(), levels));
    Ok(audit
        .issues
        .iter()
        .filter(|issue| !is_data_goal(issue))
        .map(|issue| format!("{issue:?}"))
        .collect())
}

/// The admitted `GoalNotProposition`: an inferred sort that is not `Prop`.
fn is_data_goal(issue: &CertificationIssue) -> bool {
    matches!(issue, CertificationIssue::GoalNotProposition { error }
        if error.starts_with("goal lives in Sort ") && error.ends_with(", not Prop"))
}

// ---------------------------------------------------------------------------------
// The statement digest (B1B-D07 (d)) and the implicit-premise check (B1B-D30)
// ---------------------------------------------------------------------------------

/// The rendering version, part of every digest: a change to the rendering is a
/// re-bless with this cause (TASK-STATE 4.5).
const STATEMENT_DIGEST_VERSION: &str = "b1b-statement-digest-v2";

/// The elaborated statement digest of theorem `name` (B1B-D07 (d), measured at
/// B1B-01b; DQ B1B-D52).
///
/// Clean at trust's pin exposes no per-expression structural digest: its
/// `Environment::content_digest` (clean-kernel `env/content_digest.rs`) digests whole
/// tables, per constant over type **and value**, and its expression digester is
/// private. So, as B1A-D34 does, the digest is SHA-256 over `Debug` renderings, which
/// are deterministic (`Expr`'s `Debug` is the derived `ExprKind` one; metadata maps are
/// `Vec`s; no address is rendered). It covers the statement's **closure**, not only its
/// own `Expr`: the theorem's universe parameters and type, then every constant the type
/// reaches, sorted by name, through the types of everything and the values of
/// definitions and opaques (never a theorem's proof), with each inductive's type,
/// constructors and flags. A statement that keeps its text while a definition it reads
/// changes (an `abbrev` redefined, a B1a body edited, a Clean bump) therefore changes
/// its digest, and TASK-STATE 4.5 records the cause; a re-proof alone never does.
/// A reached name the kernel does not know is rendered as missing (the kernel check
/// refuses such a theorem anyway).
///
/// Version 2 (B1B-D59, the B1B-01b verifier's items 5 and 7) frames the theorem's name
/// right after the version, so two theorems with the same type no longer share a
/// digest and a swap of two same-typed statements moves both; and it returns, beside
/// the digest, one SHA-256 per closure constant over that constant's own frames, which
/// `module_<m>` compares with `CLOSURE.tsv` to name the constants a moved digest moved
/// with (TASK-STATE 4.5's recorded cause).
fn statement_digest(
    environment: &Environment,
    name: &Name,
) -> Result<(String, BTreeMap<String, String>), String> {
    let theorem = environment
        .get_const(name)
        .ok_or_else(|| format!("the kernel has no constant {name} to digest"))?;
    let mut hasher = Sha256::new();
    let mut parts: BTreeMap<String, String> = BTreeMap::new();
    let mut part = Sha256::new();
    let mut frame = |line: String, part: Option<&mut Sha256>| {
        hasher.update(line.as_bytes());
        hasher.update([0u8]);
        if let Some(part) = part {
            part.update(line.as_bytes());
            part.update([0u8]);
        }
    };
    frame(STATEMENT_DIGEST_VERSION.to_owned(), None);
    frame(format!("name {name}"), None);
    frame(format!("stmt {:?} {:?}", theorem.level_params, theorem.type_), None);
    let mut seen: BTreeMap<String, Name> = BTreeMap::new();
    let mut work: Vec<Name> = theorem.type_.collect_constants().into_iter().collect();
    while let Some(next) = work.pop() {
        if seen.contains_key(&next.to_string()) {
            continue;
        }
        seen.insert(next.to_string(), next.clone());
        if let Some(constant) = environment.get_const(&next) {
            work.extend(constant.type_.collect_constants());
            if constant.kind != ConstantKind::Theorem {
                if let Some(value) = &constant.value {
                    work.extend(value.collect_constants());
                }
            }
        }
        if let Some(inductive) = environment.get_inductive(&next) {
            work.extend(inductive.type_.collect_constants());
            work.extend(inductive.all_names.iter().cloned());
            work.extend(inductive.constructor_names.iter().cloned());
        }
        if let Some(constructor) = environment.get_constructor(&next) {
            work.extend(constructor.type_.collect_constants());
            work.push(constructor.inductive_name.clone());
        }
    }
    for (key, reached) in &seen {
        let mut known = false;
        if let Some(c) = environment.get_const(reached) {
            known = true;
            let value = match (&c.kind, &c.value) {
                (ConstantKind::Theorem, _) => "proof".to_owned(),
                (_, Some(value)) => format!("{value:?}"),
                (_, None) => "-".to_owned(),
            };
            frame(
                format!("const {key} {:?} {:?} {:?} {value}", c.kind, c.level_params, c.type_),
                Some(&mut part),
            );
        }
        if let Some(i) = environment.get_inductive(reached) {
            known = true;
            frame(
                format!(
                    "ind {key} {:?} {:?} {:?} {:?} {} {} {} {} {} {}",
                    i.level_params,
                    i.type_,
                    i.all_names,
                    i.constructor_names,
                    i.num_params,
                    i.num_indices,
                    i.is_recursive,
                    i.is_reflexive,
                    i.is_large_elim,
                    i.is_nested
                ),
                Some(&mut part),
            );
        }
        if let Some(c) = environment.get_constructor(reached) {
            known = true;
            frame(
                format!(
                    "ctor {key} {:?} {:?} {:?} {} {} {}",
                    c.inductive_name,
                    c.level_params,
                    c.type_,
                    c.num_params,
                    c.num_fields,
                    c.constructor_idx
                ),
                Some(&mut part),
            );
        }
        if !known {
            frame(format!("missing {key}"), Some(&mut part));
        }
        parts.insert(key.clone(), hex(&std::mem::replace(&mut part, Sha256::new()).finalize()));
    }
    Ok((hex(&hasher.finalize()), parts))
}

fn hex(bytes: &impl AsRef<[u8]>) -> String {
    bytes.as_ref().iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Whether a universe level may be zero for some instantiation of its parameters, so
/// that a type living in `Sort level` may be a proposition (fails closed: a parameter
/// may be zero).
fn level_may_be_zero(level: &Level) -> bool {
    match level {
        Level::Zero | Level::Param(_) => true,
        Level::Succ(_) => false,
        Level::Max(a, b) => level_may_be_zero(a) && level_may_be_zero(b),
        Level::IMax(_, b) => level_may_be_zero(b),
    }
}

/// The implicit-premise check (B1B-D30, kernel side): walks the leading Pi telescope of
/// theorem `name`'s type with a `TypeChecker` over `environment` (each binder pushed as
/// a local with `push_binder_local`, the body instantiated with it, every local popped
/// at the end), and returns `(implicit, premises)`: the number of binders whose
/// `BinderData.info` is not explicit, and the positions of those whose type's type
/// (`whnf(infer_type(..))`) is a sort that may be `Prop`. Kernel Pi binders carry no
/// names (clean-kernel `expr/types.rs`, `BinderData`), so the check is by binder info,
/// and it reads no source text. An inference failure is an error, never a pass.
///
/// The telescope is the one the kernel sees after `whnf` at every step (B1B-D58, the
/// B1B-01b verifier's item 4): a premise hidden behind a definition (`theorem t :
/// Premised` with `Premised := ∀ {h : P}, Q`) is exposed and refused. A Type-valued
/// wrapper of a proposition (`{h : PLift P}`, a `Subtype`, a `PProd` with a Prop
/// field) lives in a sort that is never `Prop`, so it passes here: B1B-01e's text-side
/// `TYPE_HEADS` grammar is what refuses it (B1B-D58), and `statement_selftest` pins
/// that this side lets `{h : Lift P}` (a structure of PLift's shape) through.
fn implicit_binders(environment: &Environment, name: &Name) -> Result<(usize, Vec<usize>), String> {
    let theorem = environment
        .get_const(name)
        .ok_or_else(|| format!("the kernel has no constant {name} to inspect"))?;
    let checker = TypeChecker::new(environment);
    let mut current = theorem.type_.clone();
    let mut pushed = 0usize;
    let mut implicit = 0usize;
    let mut premises = Vec::new();
    let mut result = Ok(());
    loop {
        let reduced = checker.whnf(&current);
        let ExprKind::Pi(binder, domain, body) = reduced.kind() else { break };
        if binder.info != BinderInfo::Default {
            implicit += 1;
            match checker.infer_type(domain) {
                Ok(sort) => match checker.whnf(&sort).kind() {
                    ExprKind::Sort(level) => {
                        if level_may_be_zero(level) {
                            premises.push(pushed);
                        }
                    }
                    other => {
                        result = Err(format!(
                            "{name}: binder {pushed}'s type is typed by {other:?}, not a sort"
                        ));
                        break;
                    }
                },
                Err(error) => {
                    result = Err(format!("{name}: binder {pushed}'s type: {error:?}"));
                    break;
                }
            }
        }
        let local = checker.push_binder_local(
            Name::from_string(&format!("b1b_binder_{pushed}")),
            domain.as_ref().clone(),
            *binder,
        );
        pushed += 1;
        let next = body.instantiate(&Expr::fvar(local));
        current = next;
    }
    for _ in 0..pushed {
        checker.pop_binder_local();
    }
    result.map(|()| (implicit, premises))
}

/// Elaborate `order` (a dependency closure, the target last) after the prelude. Every
/// module's added constants pass the axiom-kind walk. Returns the names the target
/// added, the names B1a's prelude added, and every name added by a theorem module of
/// the closure (a module named under `theorem_prefix`), or `None` after a refused
/// elaboration.
fn elaborate_closure(
    prelude: &mut ModelPrelude,
    theory: &'static [TheoryModule],
    theorem_prefix: &str,
    order: &[usize],
    out: &mut Outcome,
) -> Option<(Vec<Name>, HashSet<Name>, HashSet<Name>)> {
    let b1a = name_set(prelude.environment());
    let mut known = b1a.clone();
    let mut target_added = Vec::new();
    let mut theorem_added = HashSet::new();
    for &index in order {
        let (module, _, source) = theory[index];
        if let Err(error) = elaborate_model_suffix(prelude, source, module) {
            let kind = if is_budget(&error) { "budget exhausted" } else { "elaboration refused" };
            out.fail(kind, format!("{module}: {error}"));
            return None;
        }
        let now = name_set(prelude.environment());
        let added = sorted(now.difference(&known).cloned());
        for name in &added {
            if is_axiom_kind(prelude.environment(), name) {
                out.fail("axiom-kind constant", format!("{name} added by {module}"));
            }
        }
        if module.starts_with(theorem_prefix) {
            theorem_added.extend(added.iter().cloned());
        }
        target_added = added;
        known = now;
    }
    Some((target_added, b1a, theorem_added))
}

fn scan_closure(theory: &[TheoryModule], order: &[usize], out: &mut Outcome) {
    for &index in order {
        for token in axiom_tokens(theory[index].2) {
            out.fail("axiom token", format!("{token} in {}", theory[index].0));
        }
        for token in notation_tokens(theory[index].2) {
            out.fail("notation token", format!("{token} in {}", theory[index].0));
        }
    }
}

/// Resolve `harness` among `theory`'s theorem or definition modules and its closure;
/// on failure the outcome holds the reason.
fn resolve(
    theory: &[TheoryModule],
    theorem_prefix: &str,
    theorems: bool,
    harness: &str,
    out: &mut Outcome,
) -> Option<Vec<usize>> {
    match find_module(theory, theorem_prefix, theorems, harness).and_then(|i| closure(theory, i)) {
        Ok(order) => Some(order),
        Err(error) => {
            out.fail("module", error);
            None
        }
    }
}

/// The `module_<m>` runner (B1B-D09; TASKS.md C3). `starve_checks` arms a one-tick
/// ambient budget around every theorem check: the budget-starved control. `closure`
/// is the `CLOSURE.tsv` table (B1B-D59): with it, a checked theorem's every closure
/// constant must carry its recorded digest (`closure table`), and a moved statement
/// digest names the closure constants that moved with it; `None` (the selftests'
/// default) skips both.
fn run_theorem_module(
    theory: &'static [TheoryModule],
    theorem_prefix: &str,
    rows: &[TheoremRow],
    harness: &str,
    starve_checks: bool,
    closure: Option<BTreeMap<String, String>>,
) -> Outcome {
    let mut out = Outcome::default();
    let Some(order) = resolve(theory, theorem_prefix, true, harness, &mut out) else { return out };
    scan_closure(theory, &order, &mut out);
    // B1B-D57: the module's `theorem`/`lemma` declarations on Clean's lexer, the same
    // reading `print_declarations` gives check_ledger_text.py, are checked against
    // what the kernel added below.
    let target = order.last().map(|&i| theory[i].2).unwrap_or_default();
    let source_declarations = declarations(target);
    let module_name = harness.to_owned();
    let expected: BTreeSet<String> = rows
        .iter()
        .filter(|r| r.proved && r.module == harness)
        .map(|r| r.lean_name.clone())
        .collect();
    let waivers: BTreeMap<String, String> = rows
        .iter()
        .filter(|r| r.proved && r.module == harness && r.classical != "-")
        .map(|r| (r.lean_name.clone(), r.classical.clone()))
        .collect();
    let wanted: BTreeMap<String, TheoremRow> = rows
        .iter()
        .filter(|r| r.proved && r.module == harness)
        .map(|r| (r.lean_name.clone(), r.clone()))
        .collect();
    let prefix = theorem_prefix.to_owned();
    let kernel = with_model_prelude(move |mut prelude| {
        let mut out = Outcome::default();
        let Some((added, _, theorem_added)) =
            elaborate_closure(&mut prelude, theory, &prefix, &order, &mut out)
        else {
            return out;
        };
        let environment = prelude.environment();
        // Every constant the module adds, theorem or helper, reaches no domain axiom and
        // no trust marker (B1B-01b; the B1B-01f verifier's item 3): an unused helper
        // closed by `sorry` is refused here even when no theorem cites it.
        for name in &added {
            match non_foundational(environment, name) {
                Ok(domain) if domain.is_empty() => {}
                Ok(domain) => out.fail("axiom deps", format!("{name} reaches {domain:?}")),
                Err(error) => out.fail("axiom deps", error),
            }
        }
        let found: BTreeSet<String> = added
            .iter()
            .filter(|name| {
                environment.get_const(name).is_some_and(|c| c.kind == ConstantKind::Theorem)
            })
            .map(ToString::to_string)
            .collect();
        for extra in found.difference(&expected) {
            out.fail(
                "extra theorem",
                format!("{extra} is added but not a proved THEOREMS.tsv row"),
            );
        }
        for missing in expected.difference(&found) {
            out.fail(
                "missing theorem",
                format!("{missing} is a proved row the module does not add"),
            );
        }
        // B1B-D57: every source declaration resolves to a theorem the module adds (so
        // the lexer's namespace reading agrees with the elaborator's), and every checked
        // theorem has exactly one source declaration: the text check reads that one.
        for problem in declaration_problems(&source_declarations, &module_name, &found, &expected) {
            out.fail("declaration", problem);
        }
        for name in found.intersection(&expected) {
            if starve_checks {
                clean_kernel::tc::set_declaration_budget(1);
            }
            let checked = check_model_theorem(environment, name);
            if starve_checks {
                clean_kernel::tc::clear_declaration_budget();
            }
            if let Err(error) = checked {
                let kind =
                    if is_budget(&error) { "budget exhausted" } else { "kernel check refused" };
                out.fail(kind, format!("{name}: {error}"));
                continue;
            }
            let axioms = match foundational(environment, &Name::from_string(name)) {
                Ok(axioms) => axioms,
                Err(error) => {
                    out.fail("census", error);
                    continue;
                }
            };
            let waiver = waivers.get(name).map_or("-", String::as_str);
            out.lines.push(format!(
                "census {name} foundational=[{}] classical={waiver}",
                axioms.iter().cloned().collect::<Vec<_>>().join(", ")
            ));
            let outside: Vec<&String> = axioms
                .iter()
                .filter(|a| !ALLOWED_FOUNDATIONAL.contains(&a.as_str()))
                .filter(|a| !(a.as_str() == CLASSICAL_CHOICE && waiver != "-"))
                .collect();
            if !outside.is_empty() {
                out.fail("census", format!("{name} reaches {outside:?} (classical={waiver})"));
                continue;
            }
            if waiver != "-" && !axioms.contains(CLASSICAL_CHOICE) {
                out.fail(
                    "unused waiver",
                    format!("{name} names {waiver} but does not reach {CLASSICAL_CHOICE}"),
                );
                continue;
            }
            let row = &wanted[name];
            let (digest, parts) = match statement_digest(environment, &Name::from_string(name)) {
                Ok(digest) => digest,
                Err(error) => {
                    out.fail("digest", error);
                    continue;
                }
            };
            out.lines.push(format!("digest {name} {digest}"));
            out.closures.extend(parts.iter().map(|(k, v)| (k.clone(), v.clone())));
            // B1B-D59: the closure constants whose digest is not CLOSURE.tsv's.
            let moved: Vec<&String> = closure.as_ref().map_or_else(Vec::new, |table| {
                parts.iter().filter(|(k, v)| table.get(*k) != Some(*v)).map(|(k, _)| k).collect()
            });
            if row.stmt_digest != digest {
                let cause = if closure.is_some() {
                    format!("; closure constants moved or new against CLOSURE.tsv: {moved:?}")
                } else {
                    String::new()
                };
                out.fail(
                    "digest",
                    format!(
                        "{name}: elaborated {digest}, THEOREMS.tsv records {} (re-bless only with a recorded cause, TASK-STATE 4.5){cause}",
                        row.stmt_digest
                    ),
                );
                continue;
            }
            if !moved.is_empty() {
                out.fail(
                    "closure table",
                    format!(
                        "{name}: closure constants not as CLOSURE.tsv records them: {moved:?} (re-bless with print_statement_digests, TASK-STATE 4.5)"
                    ),
                );
                continue;
            }
            // B1B-01e (the B1B-01g verifier's item 5 (2)): a ledger statement reads
            // only the prelude's and the definition modules' vocabulary. A constant a
            // theorem module of the closure adds (a module-local `Spec`, say, that the
            // statement's text resolves to instead of B1a's) would change what the
            // statement means while its text, the text check and the self-blessed
            // digest stay as they were, so its elaborated closure reaching one is
            // refused. A shadowing constant the closure does not reach cannot change the
            // kernel type, which is what is proved.
            if row.ledger_id != "-" {
                let local: Vec<&String> = parts
                    .keys()
                    .filter(|key| theorem_added.contains(&Name::from_string(key)))
                    .collect();
                if !local.is_empty() {
                    out.fail(
                        "statement reads module constant",
                        format!(
                            "{name}: its statement's closure reaches {local:?}, added by a theorem module"
                        ),
                    );
                    continue;
                }
            }
            if row.ledger_id != "-" {
                match implicit_binders(environment, &Name::from_string(name)) {
                    Ok((implicit, premises)) => {
                        out.lines.push(format!(
                            "binders {name} implicit={implicit} implicit_premises={}",
                            premises.len()
                        ));
                        if !premises.is_empty() {
                            out.fail(
                                "implicit premise",
                                format!(
                                    "{name}: non-explicit binder(s) {premises:?} may be propositions (B1B-D30)"
                                ),
                            );
                            continue;
                        }
                    }
                    Err(error) => {
                        out.fail("implicit premise", error);
                        continue;
                    }
                }
            }
            out.lines.push(format!("theorem {name} ok"));
            out.checked += 1;
        }
        out
    });
    match kernel {
        Ok(kernel) => {
            out.lines.extend(kernel.lines);
            out.failures.extend(kernel.failures);
            out.checked = kernel.checked;
            out.closures = kernel.closures;
        }
        Err(error) => out.fail("model prelude", error),
    }
    if out.checked == 0 {
        out.fail("no theorem checked", format!("module {harness}"));
    }
    out.lines.push(format!("module {harness}: {} theorems", out.checked));
    out
}

/// The union of the foundational axioms of the B1a constants `name` reaches, walking
/// through constants that are not B1a's (B1b's own and Clean's kernel prelude) and
/// stopping at each B1a constant: census rule (d)'s allowance. The walk uses Clean's
/// own `Expr::collect_constants`; a reference it missed could only shrink the
/// allowance, so the rule fails closed.
fn b1a_callee_foundational(
    environment: &Environment,
    name: &Name,
    b1a: &HashSet<Name>,
) -> Result<BTreeSet<String>, String> {
    let mut allowed = BTreeSet::new();
    let mut seen = HashSet::from([name.clone()]);
    let mut work: Vec<Name> = Vec::new();
    let push_refs = |constant: &clean_kernel::ConstantInfo, work: &mut Vec<Name>| {
        let mut refs = constant.type_.collect_constants();
        if let Some(value) = &constant.value {
            value.collect_constants_into(&mut refs);
        }
        work.extend(refs);
    };
    if let Some(constant) = environment.get_const(name) {
        push_refs(constant, &mut work);
    }
    while let Some(next) = work.pop() {
        if !seen.insert(next.clone()) {
            continue;
        }
        if b1a.contains(&next) {
            allowed.extend(foundational(environment, &next)?);
        } else if let Some(constant) = environment.get_const(&next) {
            push_refs(constant, &mut work);
        }
    }
    Ok(allowed)
}

/// The `definitions_<m>` runner (B1B-D09; census rules (b) and (d) of B1B-D06, D49):
/// the module adds exactly `expected`, no axiom-kind constant, and every constant it
/// adds reaches no non-foundational axiom (`axiom_deps` empty: no domain axiom, no
/// trust marker such as `sorryAx`, through any constant, Clean's prelude included),
/// passes Clean's certification audit ([`definition_audit`]), and reaches no
/// foundational axiom beyond its B1a callees' and never `Classical.choice`. Each check
/// reports its own failure kind (`axiom deps`, `certification`, `census (d)`).
fn run_definition_module(
    theory: &'static [TheoryModule],
    theorem_prefix: &str,
    harness: &str,
    expected: &[&str],
) -> Outcome {
    let mut out = Outcome::default();
    let Some(order) = resolve(theory, theorem_prefix, false, harness, &mut out) else { return out };
    scan_closure(theory, &order, &mut out);
    let expected: BTreeSet<String> = expected.iter().map(|name| (*name).to_owned()).collect();
    let prefix = theorem_prefix.to_owned();
    let kernel = with_model_prelude(move |mut prelude| {
        let mut out = Outcome::default();
        let Some((added, b1a, _)) =
            elaborate_closure(&mut prelude, theory, &prefix, &order, &mut out)
        else {
            return out;
        };
        let environment = prelude.environment();
        let found: BTreeSet<String> = added.iter().map(ToString::to_string).collect();
        for extra in found.difference(&expected) {
            out.fail("extra declaration", extra);
        }
        for missing in expected.difference(&found) {
            out.fail("missing declaration", missing);
        }
        for name in &added {
            let mut ok = true;
            match non_foundational(environment, name) {
                Ok(domain) if domain.is_empty() => {}
                Ok(domain) => {
                    out.fail("axiom deps", format!("{name} reaches {domain:?}"));
                    ok = false;
                }
                Err(error) => {
                    out.fail("axiom deps", error);
                    ok = false;
                }
            }
            match definition_audit(environment, name) {
                Ok(issues) if issues.is_empty() => {}
                Ok(issues) => {
                    out.fail("certification", format!("{name}: {issues:?}"));
                    ok = false;
                }
                Err(error) => {
                    out.fail("certification", error);
                    ok = false;
                }
            }
            let (axioms, callees) = match (
                foundational(environment, name),
                b1a_callee_foundational(environment, name, &b1a),
            ) {
                (Ok(axioms), Ok(callees)) => (axioms, callees),
                (Err(error), _) | (_, Err(error)) => {
                    out.fail("census (d)", error);
                    continue;
                }
            };
            out.lines.push(format!(
                "census {name} foundational=[{}] b1a_callees=[{}]",
                axioms.iter().cloned().collect::<Vec<_>>().join(", "),
                callees.iter().cloned().collect::<Vec<_>>().join(", ")
            ));
            if axioms.contains(CLASSICAL_CHOICE) {
                out.fail("census (d)", format!("{name} reaches {CLASSICAL_CHOICE}"));
            } else if !axioms.is_subset(&callees) {
                let beyond: Vec<&String> = axioms.difference(&callees).collect();
                out.fail(
                    "census (d)",
                    format!("{name} reaches {beyond:?} beyond its B1a callees'"),
                );
            } else if ok {
                out.checked += 1;
            }
        }
        out
    });
    match kernel {
        Ok(kernel) => {
            out.lines.extend(kernel.lines);
            out.failures.extend(kernel.failures);
            out.checked = kernel.checked;
        }
        Err(error) => out.fail("model prelude", error),
    }
    if out.checked == 0 {
        out.fail("no definition checked", format!("module {harness}"));
    }
    out.lines.push(format!("definitions {harness}: {} constants", out.checked));
    out
}

/// Run and print `module_<harness>` over the lane's `THEORY` and `THEOREMS.tsv`.
fn module_test(harness: &str) {
    let outcome = run_theorem_module(
        THEORY,
        THEOREM_MODULE_PREFIX,
        &theorems(),
        harness,
        false,
        Some(closure_table()),
    );
    outcome.print();
    assert!(outcome.failures.is_empty(), "module {harness} failed: {:#?}", outcome.failures);
    assert!(outcome.checked > 0);
}

#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn module_ports() {
    module_test("ports");
}

/// The explicit least-invariant telescope, constructed without reading an
/// elaborated declaration. Init and next are fields 0 and 1 of the original M.
fn reach_least_statement_type(reachable_conclusion: bool) -> Expr {
    let pi = |domain, body| Expr::pi(BinderInfo::Default, domain, body);
    let b = Expr::bvar;
    let field = |index, machine| {
        Expr::proj(Name::from_string("Trust.Temporal.StateMachine"), index, machine)
    };
    // Before hinit: R, M, S. After its state and proof binders: hi, s, R, M, S.
    let initial = pi(b(2), pi(Expr::app(field(0, b(2)), b(0)), Expr::app(b(2), b(1))));
    // Before hstep: hinit, R, M, S. At its conclusion:
    // hn, hs, t, s, hinit, R, M, S.
    let closed = pi(
        b(3),
        pi(
            b(4),
            pi(
                Expr::app(b(3), b(1)),
                pi(Expr::apps(field(1, b(5)), [b(2), b(1)]), Expr::app(b(5), b(2))),
            ),
        ),
    );
    // At the final conclusion: h, s, hstep, hinit, R, M, S.
    let conclusion = if reachable_conclusion {
        Expr::apps(Expr::const_str("Trust.Temporal.Reach"), [b(6), b(5), b(1)])
    } else {
        Expr::app(b(4), b(1))
    };
    pi(
        Expr::sort(Level::succ(Level::zero())),
        pi(
            Expr::app(Expr::const_str("Trust.Temporal.StateMachine"), b(0)),
            pi(
                pi(b(1), Expr::sort(Level::zero())),
                pi(
                    initial,
                    pi(
                        closed,
                        pi(
                            b(4),
                            pi(
                                Expr::apps(
                                    Expr::const_str("Trust.Temporal.Reach"),
                                    [b(5), b(4), b(0)],
                                ),
                                conclusion,
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Bind the measured statement pin to an independently constructed CIC goal.
/// The alternate final proposition is well-typed, but the actual proof must fail it.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn reach_least_statement_pin() {
    let row = theorems()
        .into_iter()
        .find(|row| row.lean_name == "Trust.Temporal.reach_least")
        .expect("reach_least manifest row");
    assert_eq!(row.module, "ports");
    assert!(row.proved, "the candidate has a real measured manifest pin");
    with_model_prelude(move |mut prelude| {
        elaborate_model_suffix(&mut prelude, trust_model_prelude::PORTS, "Trust.Thm.Ports")
            .expect("ports source");
        let environment = prelude.environment();
        check_model_theorem(environment, &row.lean_name).expect("strict root check");
        let name = Name::from_string(&row.lean_name);
        let actual = environment.get_const(&name).expect("the checked theorem");
        let specified = reach_least_statement_type(false);
        assert_eq!(actual.type_, specified, "exact independent seven-binder goal");
        assert!(actual.level_params.is_empty());
        let checker = TypeChecker::new(environment);
        let check = |label: &str, term: &Expr, expected: &Expr| {
            let limit = trust_spec_temporal::model_prelude::MODEL_DECL_BUDGET;
            clean_kernel::tc::set_declaration_budget(limit);
            let result = checker.check_type(term, expected);
            let ticks = clean_kernel::tc::declaration_budget_used();
            clean_kernel::tc::clear_declaration_budget();
            println!("type pin {label}: ticks={ticks} limit={limit} accepted={}", result.is_ok());
            result
        };
        let proposition = Expr::sort(Level::zero());
        check("specified goal", &specified, &proposition)
            .expect("independent goal is a proposition");
        let proof = actual.value.as_ref().expect("the checked proof body");
        check("actual proof", proof, &specified).expect("proof checks against independent goal");
        let changed = reach_least_statement_type(true);
        check("changed goal", &changed, &proposition).expect("control goal is also a proposition");
        let refused = check("changed conclusion", proof, &changed)
            .expect_err("the actual least-invariant proof has a different conclusion");
        assert!(matches!(refused, clean_kernel::tc::TypeError::TypeMismatch { .. }), "{refused:?}");
        assert!(non_foundational(environment, &name).expect("axioms").is_empty());
        assert!(foundational(environment, &name).expect("foundations").is_empty());
        let (implicit, premises) = implicit_binders(environment, &name).expect("binders");
        assert_eq!(implicit, 0);
        assert!(premises.is_empty(), "implicit premises: {premises:?}");
        let (digest, closure) = statement_digest(environment, &name).expect("statement");
        assert_eq!(digest, row.stmt_digest);
        assert_eq!(closure, closure_table());
        println!("statement {} ok", row.lean_name);
    })
    .expect("model prelude");
}

/// Exercise the shared principle from an ordinary device model, preserve a raw
/// self-loop, and reject a seed-only proof for a machine that actually escapes.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn reach_least_controls() {
    const CALLER: &str = include_str!("model_theorems/selftest/ReachLeastCaller.lean");
    const FALSE: &str = include_str!("model_theorems/selftest/ReachLeastFalse.lean");
    fn measured_suffix(
        prelude: &mut ModelPrelude,
        source: &str,
        unit: &'static str,
    ) -> Result<(), ModelPreludeError> {
        let start = std::time::Instant::now();
        let limit = trust_spec_temporal::model_prelude::MODEL_DECL_BUDGET;
        clean_kernel::tc::set_declaration_budget(limit);
        let result = elaborate_model_suffix(prelude, source, unit);
        let ticks = clean_kernel::tc::declaration_budget_used();
        clean_kernel::tc::clear_declaration_budget();
        println!(
            "source {unit}: bytes={} ticks={ticks} limit={limit} elapsed_us={} accepted={}",
            source.len(),
            start.elapsed().as_micros(),
            result.is_ok()
        );
        result
    }
    for source in [CALLER, FALSE] {
        assert!(auto_implicit_problems(source).is_empty());
        assert!(axiom_tokens(source).is_empty());
        assert!(notation_tokens(source).is_empty());
    }
    with_model_prelude(|mut prelude| {
        let start = std::time::Instant::now();
        measured_suffix(&mut prelude, THEORY[0].2, THEORY[0].0).expect("ports");
        let before = name_set(prelude.environment());
        measured_suffix(&mut prelude, CALLER, "ReachLeastCaller").expect("caller");
        let added = sorted(name_set(prelude.environment()).difference(&before).cloned());
        for name in &added {
            assert!(
                non_foundational(prelude.environment(), name).expect("axiom closure").is_empty()
            );
            assert!(definition_audit(prelude.environment(), name).expect("audit").is_empty());
        }
        let mut checked = 0;
        for name in added.iter().filter(|name| {
            prelude.environment().get_const(name).is_some_and(|c| c.kind == ConstantKind::Theorem)
        }) {
            check_model_theorem(prelude.environment(), &name.to_string()).expect("caller theorem");
            assert!(foundational(prelude.environment(), name).expect("foundations").is_empty());
            println!("caller theorem {name} ok foundational=[]");
            checked += 1;
        }
        assert_eq!(checked, 3);
        let error = measured_suffix(&mut prelude, FALSE, "ReachLeastFalse")
            .expect_err("the 0 -> 1 machine does not preserve state = 0");
        assert!(matches!(error, ModelPreludeError::Clean(_)), "{error}");
        assert!(error.to_string().contains("TypeMismatch"), "{error}");
        assert!(
            prelude
                .environment()
                .get_const(&Name::from_string("ReachLeastFalse.escaping_safe"))
                .is_none()
        );
        println!("false control refused: {error}");
        println!(
            "reach_least controls: checked={checked} elapsed_ms={}",
            start.elapsed().as_millis()
        );
    })
    .expect("model prelude");
    let starved = run_theorem_module(
        THEORY,
        THEOREM_MODULE_PREFIX,
        &theorems(),
        "ports",
        true,
        Some(closure_table()),
    );
    assert_eq!(starved.checked, 0);
    assert!(starved.kinds().contains("budget exhausted"), "{starved:#?}");
    println!("reach_least one-tick control refused");
}

/// Run and print `definitions_<harness>` over the lane's `THEORY` and `DEFINITIONS`.
#[allow(dead_code)] // the first definition module (B1B-03) adds the first caller
fn definitions_test(harness: &str) {
    let expected = DEFINITIONS
        .iter()
        .find(|(module, _)| *module == harness)
        .map(|(_, names)| *names)
        .unwrap_or_else(|| panic!("DEFINITIONS lists no module {harness}"));
    let outcome = run_definition_module(THEORY, THEOREM_MODULE_PREFIX, harness, expected);
    outcome.print();
    assert!(outcome.failures.is_empty(), "definitions {harness} failed: {:#?}", outcome.failures);
    assert!(outcome.checked > 0);
}

// ---------------------------------------------------------------------------------
// Harness selftest (B1B-01a)
// ---------------------------------------------------------------------------------

const SELFTEST_PREFIX: &str = "Selftest.Thm.";

const SELFTEST_THEORY: &[TheoryModule] = &[
    ("Selftest.Thm.Good", &[], include_str!("model_theorems/selftest/Good.lean")),
    (
        "Selftest.Thm.Chain2",
        &["Selftest.Thm.Good"],
        include_str!("model_theorems/selftest/Chain2.lean"),
    ),
    // Broken comes before Indep and neither depends on the other: Indep passes only
    // because a module's test elaborates its own closure and nothing else.
    ("Selftest.Thm.Broken", &[], include_str!("model_theorems/selftest/Broken.lean")),
    ("Selftest.Thm.Indep", &[], include_str!("model_theorems/selftest/Indep.lean")),
    ("Selftest.Thm.Classical", &[], include_str!("model_theorems/selftest/Classical.lean")),
    ("Selftest.Thm.Axiom", &[], include_str!("model_theorems/selftest/Axiom.lean")),
    ("Selftest.Thm.Opaque", &[], include_str!("model_theorems/selftest/Opaque.lean")),
    ("Selftest.Thm.Sorry", &[], include_str!("model_theorems/selftest/Sorry.lean")),
    ("Selftest.Thm.Extra", &[], include_str!("model_theorems/selftest/Extra.lean")),
    ("Selftest.Thm.Missing", &[], include_str!("model_theorems/selftest/Missing.lean")),
    ("Selftest.Thm.Empty", &[], include_str!("model_theorems/selftest/Empty.lean")),
    ("Selftest.DefsGood", &[], include_str!("model_theorems/selftest/DefsGood.lean")),
    ("Selftest.DefsPropext", &[], include_str!("model_theorems/selftest/DefsPropext.lean")),
    ("Selftest.DefsSorry", &[], include_str!("model_theorems/selftest/DefsSorry.lean")),
    ("Selftest.Thm.HelperSorry", &[], include_str!("model_theorems/selftest/HelperSorry.lean")),
    ("Selftest.DefsInductive", &[], include_str!("model_theorems/selftest/DefsInductive.lean")),
    // B1B-01e (the B1B-01g verifier's items 3, 4 and 5 (2)).
    ("Selftest.Thm.PartialEnd", &[], include_str!("model_theorems/selftest/PartialEnd.lean")),
    ("Selftest.Thm.OpenAtEof", &[], include_str!("model_theorems/selftest/OpenAtEof.lean")),
    ("Selftest.Thm.Shadow", &[], include_str!("model_theorems/selftest/Shadow.lean")),
];

const SELFTEST_THEOREMS_TSV: &str = include_str!("model_theorems/selftest/THEOREMS.tsv");

/// Every constant `DefsInductive.lean` adds (the exact-set list of the `defs-inductive`
/// case): the declared names plus those Clean's kernel generates for an inductive and a
/// structure, as measured at B1B-01b (the case tests that these pass the checks, not
/// which auxiliaries Clean generates).
const DEFS_INDUCTIVE: &[&str] = &[
    "Trust.B1bSelftest.DefsInductive.Light",
    "Trust.B1bSelftest.DefsInductive.Light.casesOn",
    "Trust.B1bSelftest.DefsInductive.Light.green",
    "Trust.B1bSelftest.DefsInductive.Light.noConfusion",
    "Trust.B1bSelftest.DefsInductive.Light.noConfusionType",
    "Trust.B1bSelftest.DefsInductive.Light.rec",
    "Trust.B1bSelftest.DefsInductive.Light.recOn",
    "Trust.B1bSelftest.DefsInductive.Light.red",
    "Trust.B1bSelftest.DefsInductive.Pair",
    "Trust.B1bSelftest.DefsInductive.Pair.casesOn",
    "Trust.B1bSelftest.DefsInductive.Pair.fst",
    "Trust.B1bSelftest.DefsInductive.Pair.mk",
    "Trust.B1bSelftest.DefsInductive.Pair.noConfusion",
    "Trust.B1bSelftest.DefsInductive.Pair.noConfusionType",
    "Trust.B1bSelftest.DefsInductive.Pair.rec",
    "Trust.B1bSelftest.DefsInductive.Pair.recOn",
    "Trust.B1bSelftest.DefsInductive.Pair.snd",
    "Trust.B1bSelftest.DefsInductive.defs_flip",
    "Trust.B1bSelftest.DefsInductive.defs_swap",
];

/// `funext`'s foundational closure, derived from its construction (clean-kernel
/// `env/logic.rs`, `init_funext`: `Quot.lift` over `Quot.mk eqv f`, transported by
/// `Quot.sound`, in the type `Quot eqv`), not read off a run.
const FUNEXT_FOUNDATIONAL: &str = "Quot, Quot.lift, Quot.mk, Quot.sound";

/// How a selftest case must come out.
enum Expect {
    /// No failure; exactly this many checked; these exact census lines.
    Pass(usize, &'static [&'static str]),
    /// Exactly these failure kinds; this many theorems still checked.
    Fail(&'static [&'static str], usize),
}

/// `(case, harness name, waiver (theorem, decision), starve the checks, outcome)`.
type TheoremCase = (&'static str, &'static str, Option<(&'static str, &'static str)>, bool, Expect);

fn selftest_rows(waive: Option<(&str, &str)>) -> Vec<TheoremRow> {
    let mut rows = parse_theorems(SELFTEST_THEOREMS_TSV).expect("the selftest table parses");
    if let Some((name, decision)) = waive {
        let row = rows.iter_mut().find(|r| r.lean_name == name).expect("the waived row exists");
        row.classical = decision.to_owned();
    }
    rows
}

fn judge(case: &str, outcome: &Outcome, expect: &Expect) -> Result<(), String> {
    let kinds = outcome.kinds();
    match expect {
        Expect::Pass(checked, census) => {
            if !outcome.failures.is_empty() {
                return Err(format!("{case}: expected a pass, failed {:?}", outcome.failures));
            }
            if outcome.checked != *checked {
                return Err(format!("{case}: checked {}, want {checked}", outcome.checked));
            }
            let lines: BTreeSet<&str> = outcome
                .lines
                .iter()
                .filter(|l| l.starts_with("census "))
                .map(String::as_str)
                .collect();
            let want: BTreeSet<&str> = census.iter().copied().collect();
            if lines != want {
                return Err(format!("{case}: census lines {lines:#?}, want {want:#?}"));
            }
        }
        Expect::Fail(want, checked) => {
            let want: BTreeSet<String> = want.iter().map(|k| (*k).to_owned()).collect();
            if kinds != want {
                return Err(format!(
                    "{case}: failure kinds {kinds:?}, want {want:?}; {:#?}",
                    outcome.failures
                ));
            }
            if outcome.checked != *checked {
                return Err(format!("{case}: checked {}, want {checked}", outcome.checked));
            }
        }
    }
    Ok(())
}

/// Independent CIC specification of Shadow.lean. This reads no elaborated fixture
/// input: Value is an ordinary Type-valued definition and each theorem is explicit
/// reflexivity over Value (or Nat for unshadowed). The legacy carrier control keeps
/// the Pi domain but unfolds only Eq's carrier, pinning the former representation.
fn shadow_reference_environment(
    base: &Environment,
    folded_carrier: bool,
    value_body: Expr,
) -> Environment {
    use clean_kernel::env::Declaration;
    let mut reference = base.clone();
    let one = Level::succ(Level::zero());
    let nat = Expr::const_str("Nat");
    let value = Expr::const_str("Trust.B1bSelftest.Shadow.Value");
    reference
        .add_decl(Declaration::Definition {
            name: Name::from_string("Trust.B1bSelftest.Shadow.Value"),
            level_params: vec![],
            type_: Expr::sort(one.clone()),
            value: value_body,
            is_reducible: false,
        })
        .expect("the independent ordinary Value definition kernel-checks");
    for (short, domain) in [
        ("shadowed", value.clone()),
        ("helper_reads_local", value.clone()),
        ("unshadowed", nat.clone()),
    ] {
        let carrier = if folded_carrier { domain.clone() } else { nat.clone() };
        let equality = Expr::apps(
            Expr::const_str_levels("Eq", vec![one.clone()]),
            [carrier.clone(), Expr::bvar(0), Expr::bvar(0)],
        );
        let proof = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![one.clone()]),
            [carrier, Expr::bvar(0)],
        );
        reference
            .add_decl(Declaration::Theorem {
                name: Name::from_string(&format!("Trust.B1bSelftest.Shadow.{short}")),
                level_params: vec![],
                type_: Expr::pi(BinderInfo::Default, domain.clone(), equality),
                value: Expr::lam(BinderInfo::Default, domain, proof),
            })
            .expect("the independent explicit reflexivity theorem kernel-checks");
    }
    reference
}

/// Pin the refreshed literals to source-independent checked terms, not the same
/// elaborated input whose digest the harness is validating. These checks are part
/// of the existing selftest; the 24 harness cases and their refusal kinds stay.
fn check_shadow_statement_pins() {
    with_model_prelude(|base| {
        let reference =
            shadow_reference_environment(base.environment(), true, Expr::const_str("Nat"));
        let legacy =
            shadow_reference_environment(base.environment(), false, Expr::const_str("Nat"));
        let changed =
            shadow_reference_environment(base.environment(), true, Expr::const_str("Bool"));
        let mut actual = base.clone();
        elaborate_model_suffix(
            &mut actual,
            include_str!("model_theorems/selftest/Shadow.lean"),
            "independent-shadow-statement-control",
        )
        .expect("the original Shadow source elaborates");
        let value_name = Name::from_string("Trust.B1bSelftest.Shadow.Value");
        let value = actual.environment().get_const(&value_name).expect("actual Value");
        assert_eq!(value.kind, ConstantKind::Definition);
        assert!(matches!(value.reducibility, clean_kernel::env::Reducibility::Regular(_)));
        assert!(!value.is_reducible);
        assert!(value.level_params.is_empty());
        assert_eq!(value.type_, Expr::sort(Level::succ(Level::zero())));
        assert_eq!(value.value, Some(Expr::const_str("Nat")));
        assert!(actual.environment().axiom_deps(&value_name).expect("Value closure").is_empty());
        let rows = selftest_rows(None);
        let pins = [
            (
                "shadowed",
                "1832a3405499d6d73e5fb0b077eae501a5150749b296203ed8ab987ccf09989c",
                "14dcdcd007ea86be8c629932a551542a7d6b1e2afc8e1b8db9d157ee85d11f0c",
            ),
            (
                "helper_reads_local",
                "2b411ca8b460ff3380046c25f967034cc9e3cb847ca4a11e82021657358f19da",
                "d273ebbadf48c851eda45b3ad681ed900e48376efd8fcb704ecb140f23ff227a",
            ),
            (
                "unshadowed",
                "d7f724de2eb62bd4d385d19d6f048b2e840a504e0961a13b98844b4593115dfd",
                "d7f724de2eb62bd4d385d19d6f048b2e840a504e0961a13b98844b4593115dfd",
            ),
        ];
        for (short, expected, old) in pins {
            let name = Name::from_string(&format!("Trust.B1bSelftest.Shadow.{short}"));
            let specified = reference.get_const(&name).expect("independent theorem");
            let elaborated = actual.environment().get_const(&name).expect("actual theorem");
            assert_eq!(elaborated.kind, ConstantKind::Theorem);
            assert_eq!(elaborated.level_params, specified.level_params);
            assert_eq!(
                elaborated.type_, specified.type_,
                "{name}: exact independently specified type"
            );
            for environment in [&reference, &legacy, &changed, actual.environment()] {
                check_model_theorem(environment, &name.to_string())
                    .expect("every authority/control theorem independently kernel-checks");
            }
            let (reference_digest, reference_parts) = statement_digest(&reference, &name).unwrap();
            let (actual_digest, actual_parts) =
                statement_digest(actual.environment(), &name).unwrap();
            assert_eq!(reference_digest, expected, "{name}: independent authority pin");
            assert_eq!(actual_digest, expected, "{name}: actual statement pin");
            assert_eq!(actual_parts, reference_parts, "{name}: exact closure pins");
            assert_eq!(
                statement_digest(&legacy, &name).unwrap().0,
                old,
                "{name}: legacy carrier pin"
            );
            let row =
                rows.iter().find(|row| row.lean_name == name.to_string()).expect("pinned TSV row");
            assert_eq!(row.stmt_digest, expected, "{name}: static table pin");
            let (changed_digest, changed_parts) = statement_digest(&changed, &name).unwrap();
            if short == "unshadowed" {
                assert_eq!(
                    changed_digest, expected,
                    "unreached Value cannot change Nat's statement"
                );
                assert!(!changed_parts.contains_key(&value_name.to_string()));
            } else {
                assert_ne!(
                    expected, old,
                    "folded and unfolded carrier have distinct exact representations"
                );
                assert_ne!(
                    changed_digest, expected,
                    "a changed local definition must change its statement closure"
                );
                assert_ne!(
                    changed_parts[&value_name.to_string()],
                    reference_parts[&value_name.to_string()]
                );
            }
        }
        // Identical theorem types still have distinct v2 name-framed digests.
        let shadowed = Name::from_string("Trust.B1bSelftest.Shadow.shadowed");
        let helper = Name::from_string("Trust.B1bSelftest.Shadow.helper_reads_local");
        assert_eq!(
            reference.get_const(&shadowed).unwrap().type_,
            reference.get_const(&helper).unwrap().type_
        );
        assert_ne!(
            statement_digest(&reference, &shadowed).unwrap().0,
            statement_digest(&reference, &helper).unwrap().0
        );
    })
    .expect("cached model prelude for independent statement authority");
}

/// B1B-01a's harness selftest: every case gives exactly its stated outcome.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn harness_selftest() {
    check_shadow_statement_pins();
    let good_census: &[&str] = &[
        "census Trust.B1bSelftest.Good.refl_nat foundational=[] classical=-",
        "census Trust.B1bSelftest.Good.fun_eq foundational=[Quot, Quot.lift, Quot.mk, Quot.sound] classical=-",
    ];
    assert!(good_census[1].contains(FUNEXT_FOUNDATIONAL));
    let theorem_cases: Vec<TheoremCase> = vec![
        ("good", "good", None, false, Expect::Pass(2, good_census)),
        (
            "chain2",
            "chain2",
            None,
            false,
            Expect::Pass(
                1,
                &[
                    "census Trust.B1bSelftest.Chain2.fun_eq_symm foundational=[Quot, Quot.lift, Quot.mk, Quot.sound] classical=-",
                ],
            ),
        ),
        (
            "indep",
            "indep",
            None,
            false,
            Expect::Pass(
                1,
                &["census Trust.B1bSelftest.Indep.indep_true foundational=[] classical=-"],
            ),
        ),
        (
            "broken",
            "broken",
            None,
            false,
            Expect::Fail(&["elaboration refused", "no theorem checked"], 0),
        ),
        ("classical", "classical", None, false, Expect::Fail(&["census", "no theorem checked"], 0)),
        (
            "classical-waived",
            "classical",
            Some(("Trust.B1bSelftest.Classical.em_nat", "B1B-D41")),
            false,
            Expect::Pass(0, &[]), // census line checked below: it names Classical.choice
        ),
        (
            "good-unused-waiver",
            "good",
            Some(("Trust.B1bSelftest.Good.refl_nat", "B1B-D41")),
            false,
            Expect::Fail(&["unused waiver"], 1),
        ),
        ("axiom", "axiom", None, false, Expect::Fail(&["axiom token", "axiom-kind constant"], 1)),
        ("opaque", "opaque", None, false, Expect::Fail(&["axiom token", "axiom-kind constant"], 1)),
        // B1B-01b: the sweep over every added constant also reports sorry_thm's
        // axiom_deps ({sorryAx}); an `axiom` or body-less `opaque` is never its own
        // axiom dependency (axiom_closure_all starts from the constant's references),
        // so the axiom and opaque cases are unchanged.
        (
            "sorry",
            "sorry",
            None,
            false,
            Expect::Fail(
                &["axiom token", "axiom deps", "kernel check refused", "no theorem checked"],
                0,
            ),
        ),
        // B1B-01b (the B1B-01f verifier's item 3): an unused helper closed by sorry.
        (
            "helper-sorry",
            "helpersorry",
            None,
            false,
            Expect::Fail(&["axiom token", "axiom deps"], 1),
        ),
        ("extra", "extra", None, false, Expect::Fail(&["extra theorem"], 1)),
        ("missing", "missing", None, false, Expect::Fail(&["missing theorem"], 1)),
        ("empty", "empty", None, false, Expect::Fail(&["no theorem checked"], 0)),
        (
            "budget-starved",
            "good",
            None,
            true,
            Expect::Fail(&["budget exhausted", "no theorem checked"], 0),
        ),
        ("unknown-module", "nosuch", None, false, Expect::Fail(&["module"], 0)),
        // B1B-01e (the B1B-01g verifier's item 4): a partial `end` leaves the outer
        // components open, as Clean's parser does, so the lexer reading agrees with the
        // elaborator and no `declaration` failure is reported (PartialEnd.lean).
        (
            "partial-end",
            "partialend",
            None,
            false,
            Expect::Pass(
                2,
                &[
                    "census Trust.B1bSelftest.PartialEnd.inside_partial foundational=[] classical=-",
                    "census Trust.B1bSelftest.after_partial foundational=[] classical=-",
                ],
            ),
        ),
        // The B1B-01g verifier's item 3: the `declaration` cross-check's negative
        // control in a kernel run. Clean accepts a namespace open at EOF; the lexer
        // reading refuses it, so exactly `declaration` fails, the theorem still checked.
        ("open-at-eof", "openateof", None, false, Expect::Fail(&["declaration"], 1)),
        // The B1B-01g verifier's item 5 (2): a ledger statement whose closure reaches a
        // theorem module's own definition (Shadow.lean).
        ("shadow", "shadow", None, false, Expect::Fail(&["statement reads module constant"], 2)),
    ];
    let mut failures = Vec::new();
    let mut cases = 0;
    for (case, harness, waive, starve, expect) in &theorem_cases {
        let outcome = run_theorem_module(
            SELFTEST_THEORY,
            SELFTEST_PREFIX,
            &selftest_rows(*waive),
            harness,
            *starve,
            None,
        );
        println!("--- case {case}");
        outcome.print();
        cases += 1;
        // The helper's refusal is the kernel's, about the helper and its trust marker.
        if *case == "helper-sorry"
            && !outcome.failures.iter().any(|f| {
                f.starts_with("axiom deps: Trust.B1bSelftest.HelperSorry.helper_sorry ")
                    && f.contains("sorryAx")
            })
        {
            failures
                .push(format!("{case}: no axiom deps failure naming helper_sorry; {outcome:#?}"));
        }
        let verdict = if *case == "classical-waived" {
            let census = "census Trust.B1bSelftest.Classical.em_nat foundational=[";
            match outcome.lines.iter().find(|l| l.starts_with(census)) {
                Some(line)
                    if outcome.failures.is_empty()
                        && outcome.checked == 1
                        && line.contains(CLASSICAL_CHOICE)
                        && line.ends_with("classical=B1B-D41") =>
                {
                    Ok(())
                }
                _ => Err(format!(
                    "{case}: want one checked theorem whose census names {CLASSICAL_CHOICE} under the waiver; {outcome:#?}"
                )),
            }
        } else {
            judge(case, &outcome, expect)
        };
        if let Err(error) = verdict {
            failures.push(error);
        }
    }
    let definition_cases: Vec<(&str, &str, &[&str], Expect)> = vec![
        (
            "defs-good",
            "defsgood",
            &[
                "Trust.B1bSelftest.DefsGood.defs_cites_b1a",
                "Trust.B1bSelftest.DefsGood.defs_member",
                "Trust.B1bSelftest.DefsGood.defs_plain",
            ],
            Expect::Fail(&[], 3),
        ),
        (
            "defs-propext",
            "defspropext",
            &["Trust.B1bSelftest.DefsPropext.defs_uses_propext"],
            Expect::Fail(&["census (d)", "no definition checked"], 0),
        ),
        (
            "defs-wrong-list",
            "defsgood",
            &["Trust.B1bSelftest.DefsGood.defs_plain", "Trust.B1bSelftest.DefsGood.defs_absent"],
            Expect::Fail(&["extra declaration", "missing declaration"], 3),
        ),
        // B1B-D49: a definition closed by `sorry` (hidden from a hand-written stripper
        // by a `'"'` char literal) is refused by the token scan and, independently, by
        // `axiom_deps` (sorryAx) and the certification audit (a trust marker); census
        // rule (d) alone would pass it (its foundational closure is empty).
        (
            "defs-sorry",
            "defssorry",
            &[
                "Trust.B1bSelftest.DefsSorry.defs_close",
                "Trust.B1bSelftest.DefsSorry.defs_quote",
                "Trust.B1bSelftest.DefsSorry.defs_sorry",
            ],
            Expect::Fail(&["axiom token", "axiom deps", "certification"], 2),
        ),
        // B1B-01b (the B1B-01f verifier's item 4): kernel-generated constants of an
        // inductive and a structure pass every definitions check.
        (
            "defs-inductive",
            "defsinductive",
            DEFS_INDUCTIVE,
            Expect::Fail(&[], DEFS_INDUCTIVE.len()),
        ),
    ];
    for (case, harness, expected, expect) in &definition_cases {
        let outcome = run_definition_module(SELFTEST_THEORY, SELFTEST_PREFIX, harness, expected);
        println!("--- case {case}");
        outcome.print();
        cases += 1;
        let mut verdict = judge(case, &outcome, expect);
        // The allowance is not vacuous: a definition citing a B1a theorem that reaches
        // the quotient constants (through funext, see DefsGood.lean) passes with exactly
        // those as both its closure and its allowance.
        let cites = "census Trust.B1bSelftest.DefsGood.defs_cites_b1a foundational=[Quot, Quot.lift, Quot.mk, Quot.sound] b1a_callees=[Quot, Quot.lift, Quot.mk, Quot.sound]";
        if *case == "defs-good" && verdict.is_ok() && !outcome.lines.iter().any(|l| l == cites) {
            verdict = Err(format!("{case}: no line {cites:?}"));
        }
        // The two kernel refusals are about defs_sorry and its trust marker, and its
        // census line shows rule (d) alone would have passed it.
        let sorry_census =
            "census Trust.B1bSelftest.DefsSorry.defs_sorry foundational=[] b1a_callees=[]";
        if *case == "defs-sorry"
            && verdict.is_ok()
            && !(outcome.failures.iter().any(|f| {
                f.starts_with("axiom deps: Trust.B1bSelftest.DefsSorry.defs_sorry ")
                    && f.contains("sorryAx")
            }) && outcome.failures.iter().any(|f| {
                f.starts_with("certification: Trust.B1bSelftest.DefsSorry.defs_sorry:")
                    && f.contains("TrustMarker")
            }) && outcome.lines.iter().any(|l| l == sorry_census))
        {
            verdict =
                Err(format!("{case}: kernel refusals or census line not as stated; {outcome:#?}"));
        }
        if let Err(error) = verdict {
            failures.push(error);
        }
    }
    println!("selftest_cases={}/{cases}", cases - failures.len());
    assert!(failures.is_empty(), "{failures:#?}");
}

// ---------------------------------------------------------------------------------
// Statement selftest (B1B-01b)
// ---------------------------------------------------------------------------------

const STATEMENT_THEORY: &[TheoryModule] = &[
    // B1B-01e: the definitions `carrier_refl` reads (a ledger statement may not read a
    // theorem module's own constant).
    (
        "Selftest.StatementCarrierNat",
        &[],
        include_str!("model_theorems/selftest/StatementCarrierNat.lean"),
    ),
    (
        "Selftest.StatementCarrierInt",
        &[],
        include_str!("model_theorems/selftest/StatementCarrierInt.lean"),
    ),
    (
        "Selftest.StatementPremiseDefs",
        &[],
        include_str!("model_theorems/selftest/StatementPremiseDefs.lean"),
    ),
    (
        "Selftest.Thm.StatementDigestA",
        &["Selftest.StatementCarrierNat"],
        include_str!("model_theorems/selftest/StatementDigestA.lean"),
    ),
    (
        "Selftest.Thm.StatementDigestB",
        &["Selftest.StatementCarrierInt"],
        include_str!("model_theorems/selftest/StatementDigestB.lean"),
    ),
    (
        "Selftest.Thm.StatementUnbound",
        &[],
        include_str!("model_theorems/selftest/StatementUnbound.lean"),
    ),
    (
        "Selftest.Thm.StatementUnboundControl",
        &[],
        include_str!("model_theorems/selftest/StatementUnboundControl.lean"),
    ),
    (
        "Selftest.Thm.StatementImplicitPremise",
        &["Selftest.StatementPremiseDefs"],
        include_str!("model_theorems/selftest/StatementImplicitPremise.lean"),
    ),
];

/// A proved, ledger-backed (`TH-selftest`) row of the statement selftest.
fn statement_row(name: &str, module: &str, digest: &str) -> TheoremRow {
    TheoremRow {
        ledger_id: "TH-selftest".to_owned(),
        lean_name: name.to_owned(),
        module: module.to_owned(),
        row: "B1B-01b".to_owned(),
        stmt_digest: digest.to_owned(),
        classical: "-".to_owned(),
        proved: true,
    }
}

/// The digests a run printed, by theorem name.
fn printed_digests(outcome: &Outcome) -> BTreeMap<String, String> {
    outcome
        .lines
        .iter()
        .filter_map(|line| line.strip_prefix("digest "))
        .filter_map(|rest| rest.split_once(' '))
        .map(|(name, hex)| (name.to_owned(), hex.to_owned()))
        .collect()
}

/// The statement text of `theorem <name>` in `source`, from `theorem` to `:=`.
fn statement_text<'a>(source: &'a str, name: &str) -> &'a str {
    let start = source.find(&format!("theorem {name} ")).expect("the theorem is declared");
    let end = start + source[start..].find(":=").expect("the theorem has a body");
    &source[start..end]
}

/// B1B-01b's statement selftest: the digest, unbound-identifier and implicit-premise
/// cases each give their stated outcome (TASKS.md B1B-01b).
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn statement_selftest() {
    let mut failures: Vec<String> = Vec::new();
    let mut cases = 0;
    let mut case = |label: &str, verdict: Result<(), String>| {
        cases += 1;
        match verdict {
            Ok(()) => println!("statement case ok: {label}"),
            Err(error) => {
                println!("statement case FAIL: {label}: {error}");
                failures.push(format!("{label}: {error}"));
            }
        }
    };
    let run_with = |module: &str, rows: &[TheoremRow], table: Option<BTreeMap<String, String>>| {
        let outcome =
            run_theorem_module(STATEMENT_THEORY, SELFTEST_PREFIX, rows, module, false, table);
        println!("--- {module}");
        outcome.print();
        outcome
    };
    let run = |module: &str, rows: &[TheoremRow]| run_with(module, rows, None);
    let refl = "Trust.B1bSelftest.StatementDigest.carrier_refl";

    // 1. Digest: the same statement text over a redefined `abbrev` changes the digest;
    //    the digest is stable across runs; a missing or wrong recorded digest fails.
    let source_of = |module: &str| {
        STATEMENT_THEORY.iter().find(|(m, _, _)| *m == module).map(|(_, _, s)| *s).expect("module")
    };
    let a_source = source_of("Selftest.Thm.StatementDigestA");
    let b_source = source_of("Selftest.Thm.StatementDigestB");
    case(
        "the two statements are the same text",
        if statement_text(a_source, "carrier_refl") == statement_text(b_source, "carrier_refl") {
            Ok(())
        } else {
            Err("the selftest files' statements differ".to_owned())
        },
    );
    let unrecorded = run("statementdigesta", &[statement_row(refl, "statementdigesta", "-")]);
    case(
        "a proved row without a recorded digest fails (digest)",
        if unrecorded.kinds()
            == BTreeSet::from(["digest".to_owned(), "no theorem checked".to_owned()])
        {
            Ok(())
        } else {
            Err(format!("kinds {:?}", unrecorded.kinds()))
        },
    );
    let digest_a = printed_digests(&unrecorded).get(refl).cloned().unwrap_or_default();
    let again = run("statementdigesta", &[statement_row(refl, "statementdigesta", "-")]);
    let digest_a2 = printed_digests(&again).get(refl).cloned().unwrap_or_default();
    case(
        "the digest is a SHA-256 and stable across runs",
        if digest_a.len() == 64 && digest_a == digest_a2 {
            Ok(())
        } else {
            Err(format!("{digest_a:?} then {digest_a2:?}"))
        },
    );
    let b = run("statementdigestb", &[statement_row(refl, "statementdigestb", "-")]);
    let digest_b = printed_digests(&b).get(refl).cloned().unwrap_or_default();
    case(
        "a redefined abbrev under the same text changes the digest",
        if digest_b.len() == 64 && digest_b != digest_a {
            Ok(())
        } else {
            Err(format!("A {digest_a:?}, B {digest_b:?}"))
        },
    );
    let recorded = run("statementdigesta", &[statement_row(refl, "statementdigesta", &digest_a)]);
    case(
        "the recorded digest passes, with its binders line",
        if recorded.failures.is_empty()
            && recorded.checked == 1
            && recorded
                .lines
                .iter()
                .any(|l| l == &format!("binders {refl} implicit=0 implicit_premises=0"))
        {
            Ok(())
        } else {
            Err(format!("{recorded:#?}"))
        },
    );
    let crossed = run("statementdigesta", &[statement_row(refl, "statementdigesta", &digest_b)]);
    case(
        "the other module's digest fails (digest)",
        if crossed.kinds() == BTreeSet::from(["digest".to_owned(), "no theorem checked".to_owned()])
        {
            Ok(())
        } else {
            Err(format!("kinds {:?}", crossed.kinds()))
        },
    );
    // B1B-D59 (the B1B-01b verifier's item 7): with a CLOSURE.tsv table, a moved digest
    // names the closure constant that moved: B's `Carrier` is `Int` where A's is `Nat`.
    // Expected by hand: the only constant both closures hold whose body differs is the
    // abbrev `Carrier` (A: `Nat`, B: `Int`); `Int` and its constructors are new in B.
    let table_a = unrecorded.closures.clone();
    let carrier = "Trust.B1bSelftest.StatementDigest.Carrier";
    let moved = run_with(
        "statementdigestb",
        &[statement_row(refl, "statementdigestb", &digest_a)],
        Some(table_a.clone()),
    );
    let digest_failure = moved.failures.iter().find(|f| f.starts_with("digest: ")).cloned();
    case(
        "a moved digest names the closure constants that moved (Carrier)",
        match &digest_failure {
            Some(f)
                if table_a.contains_key(carrier)
                    && f.contains(&format!("\"{carrier}\""))
                    && f.contains("\"Int\"")
                    && !f.contains("\"Nat\"")
                    && moved.kinds()
                        == BTreeSet::from([
                            "digest".to_owned(),
                            "no theorem checked".to_owned(),
                        ]) =>
            {
                Ok(())
            }
            _ => Err(format!("{moved:#?}")),
        },
    );
    let current = run_with(
        "statementdigesta",
        &[statement_row(refl, "statementdigesta", &digest_a)],
        Some(table_a.clone()),
    );
    case(
        "a current CLOSURE.tsv passes",
        if current.failures.is_empty() && current.checked == 1 {
            Ok(())
        } else {
            Err(format!("{current:#?}"))
        },
    );
    let mut stale = table_a.clone();
    stale.insert(carrier.to_owned(), "0".repeat(64));
    let stale_run = run_with(
        "statementdigesta",
        &[statement_row(refl, "statementdigesta", &digest_a)],
        Some(stale),
    );
    case(
        "a stale CLOSURE.tsv row fails (closure table) with the digest still matching",
        if stale_run.kinds()
            == BTreeSet::from(["closure table".to_owned(), "no theorem checked".to_owned()])
            && stale_run.failures.iter().any(|f| f.contains(&format!("\"{carrier}\"")))
        {
            Ok(())
        } else {
            Err(format!("{stale_run:#?}"))
        },
    );

    // 2. Unbound identifier: refused loudly under autoImplicit false; the same text
    //    with auto-bound implicits on elaborates (it then fails only on its digest).
    let unbound = run(
        "statementunbound",
        &[statement_row("Trust.B1bSelftest.StatementUnbound.unbound_eq", "statementunbound", "-")],
    );
    case(
        "an unbound identifier is refused by the elaborator",
        if unbound.kinds()
            == BTreeSet::from(["elaboration refused".to_owned(), "no theorem checked".to_owned()])
            && unbound.failures.iter().any(|f| f.contains("sp"))
        {
            Ok(())
        } else {
            Err(format!("{:#?}", unbound.failures))
        },
    );
    let control = run(
        "statementunboundcontrol",
        &[statement_row(
            "Trust.B1bSelftest.StatementUnboundControl.unbound_eq",
            "statementunboundcontrol",
            "-",
        )],
    );
    case(
        "the control with auto-bound implicits elaborates and is kernel-checked",
        if control.kinds() == BTreeSet::from(["digest".to_owned(), "no theorem checked".to_owned()])
        {
            Ok(())
        } else {
            Err(format!("{:#?}", control.failures))
        },
    );

    // 3. Implicit premises (B1B-D30, kernel side), ledger-backed entries.
    let premise = "statementimplicitpremise";
    let names = ["bad", "good", "pred", "hidden", "lifted"]
        .map(|n| format!("Trust.B1bSelftest.StatementImplicitPremise.{n}"));
    let first =
        run(premise, &names.iter().map(|n| statement_row(n, premise, "-")).collect::<Vec<_>>());
    let digests = printed_digests(&first);
    let rows: Vec<TheoremRow> = names
        .iter()
        .map(|n| statement_row(n, premise, digests.get(n).map_or("-", String::as_str)))
        .collect();
    let checked = run(premise, &rows);
    let line = |n: &str, k: usize, p: usize| {
        format!(
            "binders Trust.B1bSelftest.StatementImplicitPremise.{n} implicit={k} implicit_premises={p}"
        )
    };
    case(
        "{h : sp.wf = true} is an implicit premise: refused",
        if checked.lines.contains(&line("bad", 2, 1))
            && checked.failures.iter().any(|f| {
                f.starts_with("implicit premise: Trust.B1bSelftest.StatementImplicitPremise.bad:")
            })
            && !checked.lines.iter().any(|l| l.ends_with("StatementImplicitPremise.bad ok"))
        {
            Ok(())
        } else {
            Err(format!("{checked:#?}"))
        },
    );
    case(
        "(h : sp.wf = true) explicit: accepted",
        if checked.lines.contains(&line("good", 1, 0))
            && checked
                .lines
                .iter()
                .any(|l| l == "theorem Trust.B1bSelftest.StatementImplicitPremise.good ok")
        {
            Ok(())
        } else {
            Err(format!("{checked:#?}"))
        },
    );
    case(
        "{P : State → Prop} is a predicate variable, not a premise: accepted",
        if checked.lines.contains(&line("pred", 1, 0))
            && checked
                .lines
                .iter()
                .any(|l| l == "theorem Trust.B1bSelftest.StatementImplicitPremise.pred ok")
        {
            Ok(())
        } else {
            Err(format!("{checked:#?}"))
        },
    );
    // B1B-D58 (the B1B-01b verifier's item 4): the telescope is read after whnf.
    case(
        "a premise behind a definition (Premised := ∀ {h : 1 = 1}, True) is refused",
        if checked.lines.contains(&line("hidden", 1, 1))
            && checked.failures.iter().any(|f| {
                f.starts_with(
                    "implicit premise: Trust.B1bSelftest.StatementImplicitPremise.hidden:",
                )
            })
            && !checked.lines.iter().any(|l| l.ends_with("StatementImplicitPremise.hidden ok"))
        {
            Ok(())
        } else {
            Err(format!("{checked:#?}"))
        },
    );
    case(
        "{h : Lift (1 = 1)}, a Type-valued wrapper, passes the kernel side (the limit B1B-D58 leaves to 01e's grammar)",
        if checked.lines.contains(&line("lifted", 1, 0))
            && checked
                .lines
                .iter()
                .any(|l| l == "theorem Trust.B1bSelftest.StatementImplicitPremise.lifted ok")
        {
            Ok(())
        } else {
            Err(format!("{checked:#?}"))
        },
    );
    case(
        "the run's only failures are bad's and hidden's implicit premises",
        if checked.kinds() == BTreeSet::from(["implicit premise".to_owned()])
            && checked.failures.len() == 2
            && checked.checked == 3
        {
            Ok(())
        } else {
            Err(format!("kinds {:?}, checked {}", checked.kinds(), checked.checked))
        },
    );
    // A helper row (ledger id `-`) gets no binders check: bad passes as a helper.
    let helper_rows: Vec<TheoremRow> =
        rows.iter().map(|r| TheoremRow { ledger_id: "-".to_owned(), ..r.clone() }).collect();
    let helpers = run(premise, &helper_rows);
    case(
        "the binders check applies to ledger-backed entries only",
        if helpers.failures.is_empty()
            && helpers.checked == 5
            && !helpers.lines.iter().any(|l| l.starts_with("binders "))
        {
            Ok(())
        } else {
            Err(format!("{helpers:#?}"))
        },
    );
    println!("statement_selftest_cases={}/{cases}", cases - failures.len());
    assert!(failures.is_empty(), "{failures:#?}");
}

/// B1B-01a's measurement (B1B-D06 (d)): the foundational closure of every constant B1a's
/// prelude adds, and which constants reach each axiom. A B1a constant reaching
/// `Classical.choice` is request R4 (B1B-D13), never a widened census.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn prelude_foundational() {
    let (total, reach) = with_model_prelude(|prelude| {
        let environment = prelude.environment();
        let added = prelude_added_constants(environment);
        let mut reach: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut total = 0;
        for name in added.iter().filter(|name| environment.get_const(name).is_some()) {
            total += 1;
            for axiom in foundational(environment, name).expect("a prelude constant") {
                reach.entry(axiom).or_default().push(name.to_string());
            }
        }
        (total, reach)
    })
    .expect("the model prelude elaborates");
    let set: Vec<&String> = reach.keys().collect();
    println!("prelude_constants={total}");
    println!(
        "prelude_foundational={{{}}}",
        set.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(",")
    );
    for (axiom, names) in &reach {
        println!("prelude_reach {axiom} {} constants: {}", names.len(), names.join(" "));
    }
    assert!(total > 0);
    assert!(
        !reach.contains_key(CLASSICAL_CHOICE),
        "B1a prelude constants reach Classical.choice: request R4 (B1B-D06 (d)): {:?}",
        reach.get(CLASSICAL_CHOICE)
    );
}

// ---------------------------------------------------------------------------------
// Debug smoke subset (B1B-D20) and the re-bless printer
// ---------------------------------------------------------------------------------

#[test]
fn smoke_theory_digest() {
    assert_eq!(
        theory_digest(THEORY),
        THEORY_DIGEST,
        "re-bless with print_theory_digest (TASK-STATE 4.5)"
    );
    assert!(
        theory_shape(THEORY, THEOREM_MODULE_PREFIX).is_empty(),
        "{:#?}",
        theory_shape(THEORY, THEOREM_MODULE_PREFIX)
    );
    // The shape check is not vacuous: the selftest THEORY passes it, and a THEORY with a
    // dependency listed after its module, a duplicate name or no autoImplicit line fails.
    assert!(
        theory_shape(SELFTEST_THEORY, SELFTEST_PREFIX).is_empty(),
        "{:#?}",
        theory_shape(SELFTEST_THEORY, SELFTEST_PREFIX)
    );
    let good = SELFTEST_THEORY[0];
    let late: &[TheoryModule] = &[("A.Thm.X", &["A.Thm.Y"], good.2), ("A.Thm.Y", &[], good.2)];
    assert!(theory_shape(late, "A.Thm.").iter().any(|p| p.contains("not earlier")));
    let twice: &[TheoryModule] = &[("A.Thm.X", &[], good.2), ("A.Thm.X", &[], good.2)];
    assert!(theory_shape(twice, "A.Thm.").iter().any(|p| p.contains("listed twice")));
    let implicit: &[TheoryModule] = &[("A.Thm.X", &[], "theorem t : True := True.intro\n")];
    assert!(theory_shape(implicit, "A.Thm.").iter().any(|p| p.contains("autoImplicit")));
    // B1B-D49: the setting cannot be scoped away or undone later in the module.
    let opening = "-- c\nset_option autoImplicit false\n\ntheorem t : True := True.intro\n";
    assert!(auto_implicit_problems(opening).is_empty(), "{:?}", auto_implicit_problems(opening));
    for (bad, want) in [
        ("set_option autoImplicit false\nin theorem t : True := True.intro\n", "`in`"),
        ("set_option autoImplicit false in\ntheorem t : True := True.intro\n", "`in`"),
        (
            "set_option autoImplicit false\nset_option autoImplicit true\n",
            "sets `autoImplicit` again (line 2)",
        ),
        (
            "set_option autoImplicit false\nset_option autoImplicit true in\ntheorem t : True := True.intro\n",
            "sets `autoImplicit` again (line 2)",
        ),
        (
            "set_option autoImplicit false\nset_option relaxedAutoImplicit true\n",
            "relaxedAutoImplicit",
        ),
        ("set_option autoImplicit false theorem t : True := True.intro\n", "alone on its line"),
        ("set_option autoImplicit true\n", "does not begin"),
    ] {
        let problems = auto_implicit_problems(bad);
        assert!(problems.iter().any(|p| p.contains(want)), "{bad:?}: {problems:?}");
    }
    // The framing: a one-byte source change moves the digest.
    let moved: &[TheoryModule] = &[("A.Thm.X", &[], "x")];
    let moved2: &[TheoryModule] = &[("A.Thm.X", &[], "y")];
    assert_ne!(theory_digest(moved), theory_digest(moved2));
}

#[test]
fn smoke_theorems_table() {
    let rows = theorems();
    for row in rows.iter().filter(|r| r.proved) {
        find_module(THEORY, THEOREM_MODULE_PREFIX, true, &row.module)
            .unwrap_or_else(|error| panic!("{}: {error}", row.lean_name));
        assert_ne!(row.stmt_digest, "-", "{} is proved without a statement digest", row.lean_name);
    }
    let selftest = parse_theorems(SELFTEST_THEOREMS_TSV).expect("the selftest table parses");
    assert_eq!(selftest.len(), 20);
    assert_eq!(selftest.iter().filter(|r| !r.proved).count(), 1);
    // B1B-D59 (the B1B-01b verifier's item 5): the digest frames the theorem's name, so
    // the six selftest theorems stated `: True` in six modules carry six digests (each
    // one confirmed by its kernel run in harness_selftest, where a wrong digest fails).
    let trues: BTreeSet<&str> = selftest
        .iter()
        .filter(|r| {
            [
                "indep_true",
                "axiom_free_true",
                "opaque_free_true",
                "extra_one",
                "missing_one",
                "helper_free_true",
            ]
            .iter()
            .any(|n| r.lean_name.ends_with(&format!(".{n}")))
        })
        .map(|r| r.stmt_digest.as_str())
        .collect();
    assert_eq!(trues.len(), 6, "same-typed theorems share a digest: {trues:?}");
    // The parser refuses each malformed form.
    let header = THEOREMS_HEADER.join("\t");
    let good_row = "TH-x\tTrust.Thm.x\tports\tB1B-02\t-\t-\tpending";
    assert!(parse_theorems(&format!("{header}\n{good_row}")).is_ok());
    for bad in [
        "TH-x\tTrust.Thm.x\tports\tB1B-02\t-\t-\tdone",
        "TH-x\tTrust.Thm.x\tports\tB1B-02\t-\tD41\tpending",
        "TH-x\tTrust.Thm.x\tports\tB1B-2\t-\t-\tpending",
        "TH-x\tx\tports\tB1B-02\t-\t-\tpending",
        "TH-x\tTrust.Thm.x\tPorts\tB1B-02\t-\t-\tpending",
        "TH-x\tTrust.Thm.x\tports\tB1B-02\tabc\t-\tpending",
        "LH-x\tTrust.Thm.x\tports\tB1B-02\t-\t-\tpending",
        "TH-x\tTrust.Thm.x\tports\tB1B-02\t-\t-",
    ] {
        assert!(parse_theorems(&format!("{header}\n{bad}")).is_err(), "accepted {bad:?}");
    }
    assert!(
        parse_theorems(&format!("{header}\n{good_row}\n{good_row}")).is_err(),
        "accepted a duplicate"
    );
    assert!(parse_theorems("ledger_id\tlean_name\n").is_err(), "accepted a wrong header");
    // B1B-D59: CLOSURE.tsv parses, and its parser refuses each malformed form.
    closure_table();
    let digest = "0".repeat(64);
    let head = CLOSURE_HEADER.join("\t");
    assert!(parse_closure(&format!("{head}\nA\t{digest}\nB\t{digest}\n")).is_ok());
    for bad in [
        format!("{head}\nB\t{digest}\nA\t{digest}\n"),
        format!("{head}\nA\t{digest}\nA\t{digest}\n"),
        format!("{head}\nA\t{}\n", "0".repeat(63)),
        format!("{head}\nA\t{}\n", "A".repeat(64)),
        format!("{head}\nA B\t{digest}\n"),
        format!("{head}\nA\t{digest}\tx\n"),
        format!("constant\tsha\nA\t{digest}\n"),
    ] {
        assert!(parse_closure(&bad).is_err(), "accepted {bad:?}");
    }
}

/// B1B-D57 (the B1B-01b verifier's item 2): the declarations the text check reads come
/// from Clean's lexer, so a comment declares nothing and a `lemma` is a declaration.
#[test]
fn smoke_declarations() {
    let decl = |resolved: &str, namespace: &str, statement: &str, line: u32| Declaration {
        resolved: resolved.to_owned(),
        namespace: namespace.to_owned(),
        statement: statement.to_owned(),
        line,
    };
    // The verifier's counterexample: the LEDGER span in a block comment, a weakened
    // `lemma` of the same name after it. Only the lemma is declared, with its own text.
    let forged = "set_option autoImplicit false\nnamespace Trust\nnamespace Cert\n\
        /- theorem witnessPathOk_sound (sp : Spec) (w : List State) : witnessPathOk sp w = true → True := -/\n\
        lemma witnessPathOk_sound : True := True.intro\nend Cert\nend Trust\n";
    assert_eq!(
        declarations(forged),
        Ok(vec![decl(
            "Trust.Cert.witnessPathOk_sound",
            "Trust.Cert",
            "lemma witnessPathOk_sound : True",
            5
        )])
    );
    // Line, doc and nested block comments, and a string, declare nothing; a comment
    // inside a statement is not part of it; whitespace runs become one space.
    let comments = "-- theorem a : True := True.intro\n/-- doc: theorem b : True := -/\n\
        /- outer /- inner theorem c : True := -/ still theorem d : True := -/\n\
        def s : String := \"theorem e : True := True.intro\"\n\
        theorem f /- c -/\n    (n : Nat)   -- trailing\n    : n = n := rfl\n";
    assert_eq!(declarations(comments), Ok(vec![decl("f", "", "theorem f (n : Nat) : n = n", 5)]));
    // Namespaces (dotted), sections, mutual blocks and `_root_`.
    let scopes = "namespace A.B\nsection S\ntheorem g : True := True.intro\nend S\n\
        mutual\ntheorem h : True := True.intro\nend\nend A.B\n\
        theorem _root_.X.i : True := True.intro\nnamespace C\ntheorem _root_.Y.j : True := True.intro\nend C\n";
    assert_eq!(
        declarations(scopes),
        Ok(vec![
            decl("A.B.g", "A.B", "theorem g : True", 3),
            decl("A.B.h", "A.B", "theorem h : True", 6),
            decl("X.i", "", "theorem _root_.X.i : True", 9),
            decl("Y.j", "C", "theorem _root_.Y.j : True", 11),
        ])
    );
    // A `:=` inside brackets is not the end; tokens that touch stay touching.
    let brackets = "theorem k (x : Nat := 0) {y : Nat} : (fun z => z) x = x := rfl\n\
        theorem l (n:Nat) : n=n := rfl\n";
    assert_eq!(
        declarations(brackets),
        Ok(vec![
            decl("k", "", "theorem k (x : Nat := 0) {y : Nat} : (fun z => z) x = x", 1),
            decl("l", "", "theorem l (n:Nat) : n=n", 2),
        ])
    );
    // B1B-01e (the B1B-01g verifier's item 4): Clean's scope rule. A partial `end`
    // closes as many components as it names and leaves the rest open; an `end` naming
    // no suffix of the innermost block closes the whole block and is not consumed; a
    // named section's `end S` is consumed.
    let partial = "namespace A.B.C\ntheorem q : True := True.intro\nend B.C\n\
        theorem r : True := True.intro\nend A\nnamespace D.E\nend X\n\
        theorem s : True := True.intro\nsection S\nnamespace F\ntheorem t : True := True.intro\nend F\nend S\n";
    assert_eq!(
        declarations(partial),
        Ok(vec![
            decl("A.B.C.q", "A.B.C", "theorem q : True", 2),
            decl("A.r", "A", "theorem r : True", 4),
            decl("s", "", "theorem s : True", 8),
            decl("F.t", "F", "theorem t : True", 11),
        ])
    );
    // Errors, never a skipped declaration.
    for (bad, want) in [
        ("namespace A\ntheorem u : True := True.intro\n", "still open at the end of the file"),
        (
            "namespace A.B\nend B\ntheorem v : True := True.intro\n",
            "still open at the end of the file",
        ),
        ("section\ntheorem w : True := True.intro\n", "still open at the end of the file"),
        ("end\ntheorem m : True := True.intro\n", "closes no scope"),
        ("theorem n : True\ntheorem o : True := True.intro\n", "no `:=`"),
        ("theorem p : True := '\n", "lex error"),
        ("theorem := True.intro\n", "without a name"),
    ] {
        let got = declarations(bad);
        assert!(got.as_ref().is_err_and(|e| e.contains(want)), "{bad:?}: {got:?}");
    }
    // Every selftest theorem module reads cleanly, except OpenAtEof, the `declaration`
    // negative control (B1B-01e), whose namespace is open at the end of the file.
    for (module, _, source) in SELFTEST_THEORY.iter().chain(STATEMENT_THEORY) {
        let read = declarations(source);
        if *module == "Selftest.Thm.OpenAtEof" {
            assert!(read.as_ref().is_err_and(|e| e.contains("still open")), "{module}: {read:?}");
        } else {
            assert!(read.is_ok(), "{module}: {read:?}");
        }
    }
}

/// B1B-D57 (the B1B-01b verifier's item 3): what the harness elaborates is what is on
/// disk: every lane `THEORY` source equals its file, and every file under the
/// B1b-owned directories is a `THEORY` module; the check is not vacuous (controls in a
/// scratch directory).
#[test]
fn smoke_theory_files() {
    let clean_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("clean");
    let lane = theory_file_problems(THEORY, &clean_root, &OWNED_THEORY_DIRS);
    assert!(lane.is_empty(), "{lane:#?}");
    let dir = std::env::temp_dir().join(format!("b1b-theory-files-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("Trust/Thm")).expect("scratch dir");
    std::fs::create_dir_all(dir.join("Trust/Cert")).expect("scratch dir");
    let good = SELFTEST_THEORY[0].2;
    std::fs::write(dir.join("Trust/Thm/Good.lean"), good).expect("write");
    let problems = |theory: &[TheoryModule]| theory_file_problems(theory, &dir, &OWNED_THEORY_DIRS);
    assert!(problems(&[("Trust.Thm.Good", &[], good)]).is_empty());
    let differs = problems(&[("Trust.Thm.Good", &[], "set_option autoImplicit false\n")]);
    assert!(differs.iter().any(|p| p.contains("differs")), "{differs:?}");
    let gone = problems(&[("Trust.Thm.Good", &[], good), ("Trust.Thm.Gone", &[], good)]);
    assert!(gone.iter().any(|p| p.starts_with("Trust.Thm.Gone: ")), "{gone:?}");
    std::fs::write(dir.join("Trust/Thm/Stray.lean"), "x").expect("write");
    std::fs::write(dir.join("Trust/Cert/Loose.lean"), "x").expect("write");
    let stray = problems(&[("Trust.Thm.Good", &[], good)]);
    assert!(
        stray.iter().any(|p| p.ends_with("Stray.lean is not a THEORY module"))
            && stray.iter().any(|p| p.ends_with("Loose.lean is not a THEORY module"))
            && stray.len() == 2,
        "{stray:?}"
    );
    std::fs::remove_dir_all(&dir).expect("remove the scratch dir");
}

#[test]
fn smoke_no_axiom_tokens() {
    // Controls: the scan finds what it must and nothing else.
    let source = |module: &str| {
        SELFTEST_THEORY
            .iter()
            .find(|(name, _, _)| *name == module)
            .map(|(_, _, s)| *s)
            .expect("module")
    };
    assert_eq!(axiom_tokens(source("Selftest.Thm.Axiom")), ["axiom (line 15)"]);
    assert_eq!(axiom_tokens(source("Selftest.Thm.Opaque")), ["body-less opaque (line 14)"]);
    assert_eq!(axiom_tokens(source("Selftest.Thm.Sorry")), ["sorry (line 12)"]);
    assert!(axiom_tokens(source("Selftest.Thm.Good")).is_empty());
    assert!(
        axiom_tokens(
            "-- sorry axiom\n/- admit /- nested sorry -/ -/\ndef s : String := \"sorry\"\n"
        )
        .is_empty()
    );
    assert_eq!(axiom_tokens("theorem t : 1 = 2 := by admit\n"), ["admit (line 1)"]);
    assert_eq!(axiom_tokens("def x := sorryAx Nat\n"), ["sorryAx (line 1)"]);
    assert!(axiom_tokens("opaque k : Nat :=\n  0\n").is_empty());
    assert!(axiom_tokens("def sorry_free : Nat := 0\ndef Foo.axiomatic := 1\n").is_empty());
    // B1B-D49: Clean's lexer, so a char literal holding a double quote opens no string
    // (the DefsSorry module), an escaped quote in a string closes nothing, and a
    // qualified spelling of a forbidden name is still found.
    assert_eq!(axiom_tokens(source("Selftest.DefsSorry")), ["sorry (line 22)"]);
    assert_eq!(axiom_tokens("def q := '\"'\ndef s := sorry\ndef t := \"x\"\n"), ["sorry (line 2)"]);
    assert_eq!(axiom_tokens("def q := \"a\\\" sorry\"\ndef s := sorry\n"), ["sorry (line 2)"]);
    assert_eq!(
        axiom_tokens("def x' : Nat := 0\ndef y := _root_.sorryAx Nat\n"),
        ["sorryAx (line 2)"]
    );
    assert_eq!(axiom_tokens("def y := «admit»\n"), ["admit (line 1)"]);
    assert!(axiom_tokens("def q := 'ab'\n").iter().any(|t| t.starts_with("lex error")));
    // B1B-01b (the B1B-01f verifier's item 3): an interpolated string is one token, but
    // its holes are terms: each is scanned, at the string's line; the literal text is not.
    assert_eq!(axiom_tokens("def x := 1\ndef s := s!\"a{sorry}b\"\n"), ["sorry (line 2)"]);
    assert_eq!(axiom_tokens("def s := m!\"{f {sorryAx Nat}}\"\n"), ["sorryAx (line 1)"]);
    assert_eq!(axiom_tokens("def s := f!\"x {1} y {admit}\"\n"), ["admit (line 1)"]);
    assert!(axiom_tokens("def s := s!\"sorry axiom {n}\"\n").is_empty());
    assert!(
        axiom_tokens("def s := s!\"\\{sorry}\"\n").is_empty(),
        "an escaped brace opens no hole"
    );
    assert_eq!(interpolation_holes("a{sorry"), ["sorry"], "an unclosed hole is still scanned");
    assert_eq!(interpolation_holes("a{x}b{y {z}}c"), ["x", "y {z}"]);
    // B1B-01e (the B1B-01g verifier's item 5 (1)): authored notation, macros, syntax
    // and syntax quotations are found on Clean's lexer, in interpolation holes too;
    // comments, strings and ordinary identifiers are not.
    for (source, want) in [
        ("infixl:65 \" +++ \" => Nat.add\n", "infixl (line 1)"),
        ("def x := 1\ninfixr:65 \" ** \" => Nat.mul\n", "infixr (line 2)"),
        ("infix:50 \" ~~ \" => Eq\n", "infix (line 1)"),
        ("notation \"⟪\" x \"⟫\" => x\n", "notation (line 1)"),
        ("prefix:max \"√\" => Nat.sqrt\n", "prefix (line 1)"),
        ("postfix:max \"!\" => Nat.factorial\n", "postfix (line 1)"),
        ("macro \"triv\" : tactic => `(tactic| trivial)\n", "macro (line 1)"),
        ("macro_rules | `(tactic| triv) => `(tactic| rfl)\n", "macro_rules (line 1)"),
        ("syntax \"triv\" : tactic\n", "syntax (line 1)"),
        ("elab \"triv\" : tactic => pure ()\n", "elab (line 1)"),
        ("declare_syntax_cat foo\n", "declare_syntax_cat (line 1)"),
        ("def n := `Nat.add\n", "syntax quotation (line 1)"),
        ("def s := s!\"{`(x)}\"\n", "syntax quotation (line 1)"),
    ] {
        let found = notation_tokens(source);
        assert!(found.iter().any(|f| f == want), "{source:?}: {found:?}");
    }
    assert!(
        notation_tokens("-- notation infixl macro\n/- syntax -/\ndef s : String := \"notation\"\ndef notations := 1\n")
            .is_empty()
    );
    for (module, _, source) in SELFTEST_THEORY.iter().chain(STATEMENT_THEORY) {
        assert!(notation_tokens(source).is_empty(), "{module}: {:?}", notation_tokens(source));
    }
    // The lane's modules: none.
    for (module, _, source) in THEORY {
        assert!(axiom_tokens(source).is_empty(), "{module}: {:?}", axiom_tokens(source));
        assert!(notation_tokens(source).is_empty(), "{module}: {:?}", notation_tokens(source));
    }
}

// ---------------------------------------------------------------------------------
// Counterexamples of TASK-STATE 6b (B1B-D11, B1B-01e)
// ---------------------------------------------------------------------------------

/// TASK-STATE.md, the plan of record holding section 6b (read at run time: 6b grows in
/// the row that takes D11, in the same commit as its counterexample file).
const TASK_STATE_REL: &str = "../../docs/plans/beyond-tla-b1b/TASK-STATE.md";
/// The directory every 6b counterexample file lives in.
const SELFTEST_DIR_REL: &str = "tests/model_theorems/selftest";
/// The fixed control, checked on every run (B1B-00 verifier item 3).
const COUNTEREXAMPLE_CONTROL: &str =
    include_str!("model_theorems/selftest/CounterexampleControl.lean");

/// One row of TASK-STATE section 6b: `(ledger id, DR, counterexample file)`.
type Amendment = (String, String, String);

/// The rows of TASK-STATE section 6b's table (`| LEDGER id | DR | Change |
/// Counterexample file | Test that kernel-checks it | Evidence |`). The section must
/// exist with that header; a row that is not six cells, whose id is no `TH-` id, whose
/// DR is no `DR-B1B-Dnn` or whose file is not a bare `<Name>.lean` is an error.
fn amendment_rows(task_state: &str) -> Result<Vec<Amendment>, String> {
    const HEADER: &str = "| LEDGER id | DR | Change (premise added or statement corrected) | Counterexample file | Test that kernel-checks it | Evidence |";
    let mut inside = false;
    let mut header = false;
    let mut rows = Vec::new();
    for line in task_state.lines() {
        if line.starts_with("## ") || line.starts_with("### ") {
            inside = line.starts_with("### 6b.");
            continue;
        }
        if !inside || !line.starts_with('|') {
            continue;
        }
        if line.trim() == HEADER {
            header = true;
            continue;
        }
        if line.starts_with("|---") {
            continue;
        }
        let cells: Vec<&str> = line.trim().trim_matches('|').split('|').map(str::trim).collect();
        if cells.len() != 6 {
            return Err(format!("6b row with {} cells: {line}", cells.len()));
        }
        let file = cells[3].trim_matches('`');
        let dr_ok = cells[1]
            .strip_prefix("DR-B1B-D")
            .is_some_and(|d| d.len() == 2 && d.bytes().all(|b| b.is_ascii_digit()));
        let stem_ok = file.strip_suffix(".lean").is_some_and(|stem| {
            !stem.is_empty() && stem.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
        });
        if !cells[0].starts_with("TH-") || !dr_ok || !stem_ok {
            return Err(format!("6b row is not `TH-… | DR-B1B-Dnn | … | <Name>.lean | …`: {line}"));
        }
        rows.push((cells[0].to_owned(), cells[1].to_owned(), file.to_owned()));
    }
    if !header {
        return Err("TASK-STATE has no section 6b table header".to_owned());
    }
    Ok(rows)
}

/// Kernel-checks one counterexample source (B1B-D11): after the prelude and the lane's
/// definition modules, the source must elaborate, open with `set_option autoImplicit
/// false`, hold no axiom or notation token, add at least one theorem, and every
/// constant it adds must have empty `axiom_deps`; every theorem must pass
/// `check_model_theorem` and the census of B1B-D06 (b) with no waiver.
fn run_counterexample(module: &'static str, source: &'static str) -> Outcome {
    let mut out = Outcome::default();
    for problem in auto_implicit_problems(source) {
        out.fail("autoImplicit", problem);
    }
    for token in axiom_tokens(source) {
        out.fail("axiom token", token);
    }
    for token in notation_tokens(source) {
        out.fail("notation token", token);
    }
    let definitions: Vec<usize> =
        (0..THEORY.len()).filter(|&i| !THEORY[i].0.starts_with(THEOREM_MODULE_PREFIX)).collect();
    let kernel = with_model_prelude(move |mut prelude| {
        let mut out = Outcome::default();
        if elaborate_closure(&mut prelude, THEORY, THEOREM_MODULE_PREFIX, &definitions, &mut out)
            .is_none()
        {
            return out;
        }
        let before = name_set(prelude.environment());
        if let Err(error) = elaborate_model_suffix(&mut prelude, source, module) {
            out.fail("elaboration refused", format!("{module}: {error}"));
            return out;
        }
        let environment = prelude.environment();
        let added = sorted(name_set(environment).difference(&before).cloned());
        for name in &added {
            match non_foundational(environment, name) {
                Ok(domain) if domain.is_empty() => {}
                Ok(domain) => out.fail("axiom deps", format!("{name} reaches {domain:?}")),
                Err(error) => out.fail("axiom deps", error),
            }
        }
        for name in added
            .iter()
            .filter(|n| environment.get_const(n).is_some_and(|c| c.kind == ConstantKind::Theorem))
        {
            if let Err(error) = check_model_theorem(environment, &name.to_string()) {
                out.fail("kernel check refused", format!("{name}: {error}"));
                continue;
            }
            match foundational(environment, name) {
                Ok(axioms) => {
                    let outside: Vec<&String> = axioms
                        .iter()
                        .filter(|a| !ALLOWED_FOUNDATIONAL.contains(&a.as_str()))
                        .collect();
                    out.lines.push(format!(
                        "census {name} foundational=[{}] classical=-",
                        axioms.iter().cloned().collect::<Vec<_>>().join(", ")
                    ));
                    if outside.is_empty() {
                        out.checked += 1;
                    } else {
                        out.fail("census", format!("{name} reaches {outside:?}"));
                    }
                }
                Err(error) => out.fail("census", error),
            }
        }
        out
    });
    match kernel {
        Ok(kernel) => {
            out.lines.extend(kernel.lines);
            out.failures.extend(kernel.failures);
            out.checked = kernel.checked;
        }
        Err(error) => out.fail("model prelude", error),
    }
    if out.checked == 0 {
        out.fail("no theorem checked", module);
    }
    out
}

/// B1B-D11's kernel check (B1B-01e; run first by `b1b_ledger`, whose log
/// check_restatement.py reads): the fixed control `CounterexampleControl.lean` (a
/// closed refutation of a false-as-stated toy statement) prints `counterexample control
/// ok`; a negative control (the `sorry` selftest module) must be refused; then every
/// TASK-STATE 6b row's file is checked and prints `counterexample <id> <file> ok`.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn counterexamples() {
    let control = run_counterexample("Selftest.Cx.CounterexampleControl", COUNTEREXAMPLE_CONTROL);
    control.print();
    assert!(
        control.failures.is_empty() && control.checked == 1,
        "the control failed: {control:#?}"
    );
    println!("counterexample control ok");
    let sorry = SELFTEST_THEORY
        .iter()
        .find(|(module, _, _)| *module == "Selftest.Thm.Sorry")
        .map(|(_, _, source)| *source)
        .expect("the sorry selftest module");
    let negative = run_counterexample("Selftest.Cx.Sorry", sorry);
    assert!(
        negative.kinds().contains("axiom token") && negative.kinds().contains("no theorem checked"),
        "the negative control was not refused: {negative:#?}"
    );
    println!("counterexample negative control ok");
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let task_state = std::fs::read_to_string(manifest.join(TASK_STATE_REL))
        .unwrap_or_else(|error| panic!("{TASK_STATE_REL}: {error}"));
    let rows = amendment_rows(&task_state).unwrap_or_else(|error| panic!("{error}"));
    let mut failures = Vec::new();
    for (id, dr, file) in &rows {
        let path = manifest.join(SELFTEST_DIR_REL).join(file);
        let source = match std::fs::read_to_string(&path) {
            Ok(source) => source,
            Err(error) => {
                failures.push(format!("{id} ({dr}): {}: {error}", path.display()));
                continue;
            }
        };
        let module: &'static str =
            Box::leak(format!("Selftest.Cx.{}", file.trim_end_matches(".lean")).into_boxed_str());
        let outcome = run_counterexample(module, Box::leak(source.into_boxed_str()));
        outcome.print();
        if outcome.failures.is_empty() {
            println!("counterexample {id} {file} ok");
        } else {
            failures.push(format!("{id} ({dr}) {file}: {:?}", outcome.failures));
        }
    }
    println!("counterexamples: rows={} failures={}", rows.len(), failures.len());
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The 6b parser (B1B-01e): the plan of record's table parses; malformed rows and a
/// missing header are refused.
#[test]
fn smoke_amendment_table() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let task_state = std::fs::read_to_string(manifest.join(TASK_STATE_REL)).expect("TASK-STATE");
    amendment_rows(&task_state).expect("TASK-STATE 6b parses");
    let head = "### 6b. Statement amendments (D11)\n\n| LEDGER id | DR | Change (premise added or statement corrected) | Counterexample file | Test that kernel-checks it | Evidence |\n|---|---|---|---|---|---|\n";
    let good = format!(
        "{head}| TH-x | DR-B1B-D61 | premise added | `CxX.lean` | model_theorems counterexamples | e |\n## 7. next\n| TH-y | not | 6b | at | all | here |\n"
    );
    assert_eq!(
        amendment_rows(&good),
        Ok(vec![("TH-x".to_owned(), "DR-B1B-D61".to_owned(), "CxX.lean".to_owned())])
    );
    for bad in [
        format!("{head}| TH-x | DR-B1B-D61 | c | `../x.lean` | t | e |\n"),
        format!("{head}| TH-x | B1B-D61 | c | `CxX.lean` | t | e |\n"),
        format!("{head}| CK-x | DR-B1B-D61 | c | `CxX.lean` | t | e |\n"),
        format!("{head}| TH-x | DR-B1B-D61 | c | `CxX.lean` | t |\n"),
        "### 6b. Statement amendments (D11)\n\nno table\n".to_owned(),
    ] {
        assert!(amendment_rows(&bad).is_err(), "accepted {bad:?}");
    }
}

/// The CLOSURE.tsv rows no proved statement reaches any more (B1B-01e, the B1B-01g
/// verifier's item 6): `committed` keys absent from `reached`, sorted.
fn closure_stale(
    committed: &BTreeMap<String, String>,
    reached: &BTreeMap<String, String>,
) -> Vec<String> {
    committed.keys().filter(|k| !reached.contains_key(*k)).cloned().collect()
}

/// CLOSURE.tsv is exactly the union of the proved rows' closures (B1B-D59 completed at
/// B1B-01e): every module with a proved row runs against the table (a moved or new
/// constant fails there as `closure table`), and no committed row is stale. A gate
/// test (B1B-50, TASK-STATE 11), release-only.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn closure_table_exact() {
    let rows = theorems();
    let committed = closure_table();
    let modules: BTreeSet<String> =
        rows.iter().filter(|r| r.proved).map(|r| r.module.clone()).collect();
    let mut reached: BTreeMap<String, String> = BTreeMap::new();
    let mut failures = Vec::new();
    for module in &modules {
        let outcome = run_theorem_module(
            THEORY,
            THEOREM_MODULE_PREFIX,
            &rows,
            module,
            false,
            Some(committed.clone()),
        );
        failures.extend(outcome.failures.iter().map(|f| format!("{module}: {f}")));
        reached.extend(outcome.closures);
    }
    let stale = closure_stale(&committed, &reached);
    for constant in &stale {
        println!("closure-stale {constant}");
    }
    println!(
        "closure table: modules={} reached={} committed={} stale={}",
        modules.len(),
        reached.len(),
        committed.len(),
        stale.len()
    );
    assert!(failures.is_empty() && stale.is_empty(), "{failures:#?} stale {stale:?}");
}

/// [`closure_stale`] and the `declaration` cross-check ([`declaration_problems`]) on
/// forged inputs: each branch reports, an agreeing reading does not (B1B-01e, the
/// B1B-01g verifier's items 3 and 6).
#[test]
fn smoke_crosscheck_controls() {
    let digest = "0".repeat(64);
    let table = |keys: &[&str]| -> BTreeMap<String, String> {
        keys.iter().map(|k| ((*k).to_owned(), digest.clone())).collect()
    };
    assert_eq!(closure_stale(&table(&["A", "B"]), &table(&["A"])), ["B"]);
    assert!(closure_stale(&table(&["A"]), &table(&["A", "C"])).is_empty());
    let decl = |resolved: &str| Declaration {
        resolved: resolved.to_owned(),
        namespace: String::new(),
        statement: format!("theorem {resolved} : True"),
        line: 1,
    };
    let set =
        |names: &[&str]| -> BTreeSet<String> { names.iter().map(|n| (*n).to_owned()).collect() };
    let found = set(&["M.a", "M.b"]);
    let expected = set(&["M.a", "M.b"]);
    assert!(
        declaration_problems(&Ok(vec![decl("M.a"), decl("M.b")]), "m", &found, &expected)
            .is_empty()
    );
    let wrong = declaration_problems(&Ok(vec![decl("a"), decl("M.b")]), "m", &found, &expected);
    assert!(
        wrong.iter().any(|p| p.starts_with("a (line 1) is no theorem m adds"))
            && wrong.iter().any(|p| p == "M.a: 0 source declarations resolve to it"),
        "{wrong:?}"
    );
    let twice = declaration_problems(
        &Ok(vec![decl("M.a"), decl("M.a"), decl("M.b")]),
        "m",
        &found,
        &expected,
    );
    assert_eq!(twice, ["M.a: 2 source declarations resolve to it"]);
    let refused = declaration_problems(&Err("lex error".to_owned()), "m", &found, &expected);
    assert_eq!(refused, ["m: lex error"]);
}

/// Re-bless (TASK-STATE 4.5): the elaborated statement digest of every `proved`
/// THEOREMS.tsv row, by module, as `stmt_digest <name> <hex>` (a row whose theorem is
/// refused prints the refusal instead), then CLOSURE.tsv's rows as `closure <constant>
/// <hex>` (B1B-D59): the union of those rows' closure constants, each with its digest,
/// and `closure-moved <constant>` for each one whose digest differs from or is absent
/// in the committed CLOSURE.tsv, which is the cause the re-bless records.
#[test]
#[ignore = "re-bless: b1b_ignored model_theorems print_statement_digests"]
fn print_statement_digests() {
    let rows = theorems();
    let committed = closure_table();
    let modules: BTreeSet<String> =
        rows.iter().filter(|r| r.proved).map(|r| r.module.clone()).collect();
    let mut closures: BTreeMap<String, String> = BTreeMap::new();
    for module in &modules {
        let unrecorded: Vec<TheoremRow> =
            rows.iter().map(|r| TheoremRow { stmt_digest: "-".to_owned(), ..r.clone() }).collect();
        let outcome =
            run_theorem_module(THEORY, THEOREM_MODULE_PREFIX, &unrecorded, module, false, None);
        for (name, hex) in printed_digests(&outcome) {
            println!("stmt_digest {name} {hex}");
        }
        for failure in outcome.failures.iter().filter(|f| !f.starts_with("digest: ")) {
            println!("FAIL {module}: {failure}");
        }
        closures.extend(outcome.closures);
    }
    for (constant, hex) in &closures {
        println!("closure {constant} {hex}");
    }
    for (constant, hex) in &closures {
        if committed.get(constant) != Some(hex) {
            println!("closure-moved {constant}");
        }
    }
    // B1B-01e (the B1B-01g verifier's item 6): committed rows no proved statement
    // reaches any more; the re-bless drops them.
    for constant in closure_stale(&committed, &closures) {
        println!("closure-stale {constant}");
    }
    println!(
        "statement digests: {} proved rows in {} modules; {} closure constants",
        rows.iter().filter(|r| r.proved).count(),
        modules.len(),
        closures.len()
    );
}

/// The text check's input (B1B-D57): every `theorem`/`lemma` declaration of every lane
/// theorem module, read on Clean's lexer from the very `THEORY` source the harness
/// elaborates, as `decl<TAB><module><TAB><resolved name><TAB><namespace><TAB>
/// <statement>`, after a `module<TAB><module><TAB><count>` line per module, ending with
/// `declarations modules=<n> decls=<k>`. `b1b_ledger` runs it and hands the log to
/// check_ledger_text.py (`--decls`).
#[test]
#[ignore = "text check: b1b_ignored model_theorems print_declarations (b1b_ledger)"]
fn print_declarations() {
    let mut modules = 0;
    let mut count = 0;
    for (module, _, source) in
        THEORY.iter().filter(|(m, _, _)| m.starts_with(THEOREM_MODULE_PREFIX))
    {
        let harness = harness_name(module);
        let declared = declarations(source).unwrap_or_else(|error| panic!("{module}: {error}"));
        println!("module\t{harness}\t{}", declared.len());
        for declaration in &declared {
            let fields = [&declaration.resolved, &declaration.namespace, &declaration.statement];
            assert!(
                fields.iter().all(|f| !f.contains(['\t', '\n'])),
                "{module}: a tab or newline in {declaration:?}"
            );
            println!(
                "decl\t{harness}\t{}\t{}\t{}",
                declaration.resolved, declaration.namespace, declaration.statement
            );
            count += 1;
        }
        modules += 1;
    }
    println!("declarations modules={modules} decls={count}");
}

/// Re-bless (TASK-STATE 4.5): prints the current `THEORY_DIGEST`.
#[test]
#[ignore = "re-bless: b1b_ignored model_theorems print_theory_digest"]
fn print_theory_digest() {
    println!("THEORY_DIGEST {}", theory_digest(THEORY));
    println!("THEORY modules={}", THEORY.len());
}
