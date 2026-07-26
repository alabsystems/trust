// trust-ts-strip: the eraser.
//
// A recursive-descent walk over the token stream that KEEPS tokens by default
// and records width-preserving "blank" spans for TypeScript type positions.
// The output JS is the original bytes with each blank span's non-newline bytes
// replaced by spaces (newlines kept), so byte offsets, lines, and columns are
// preserved exactly as Node's native stripper does.
//
// SOUNDNESS CONTRACT. The walk only ever emits `Js` when it has traversed the
// entire program through recognized productions. Any unexpected token, any
// construct outside the pure-erasure subset, and any ambiguity it cannot
// resolve locally is a `Refused` for the whole file — never a guess. Active
// erasure happens only in positions the grammar proves are type-only, so a
// wrong strip (JS whose runtime behaviour differs from the TypeScript) is not
// producible. Refusing is always sound; it is the only failure mode.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::StripOutcome;
use crate::lexer::{self, Pk, Tk, Token};

pub(crate) fn erase(src: &str) -> StripOutcome {
    let toks = match lexer::lex(src) {
        Ok(t) => t,
        Err(e) => return StripOutcome::Refused(format!("lex: {e}")),
    };
    let mut e = Eraser { src, toks, pos: 0, blanks: Vec::new() };
    match e.walk_program() {
        Ok(()) => StripOutcome::Js(apply_blanks(src, &e.blanks)),
        Err(reason) => StripOutcome::Refused(reason),
    }
}

/// Replace each blank span's non-newline bytes with spaces (newlines kept).
/// Byte length is preserved, so all offsets stay valid.
fn apply_blanks(src: &str, blanks: &[(usize, usize)]) -> String {
    let mut bytes = src.as_bytes().to_vec();
    for &(s, en) in blanks {
        let en = en.min(bytes.len());
        for byte in &mut bytes[s..en] {
            if *byte != b'\n' && *byte != b'\r' {
                *byte = b' ';
            }
        }
    }
    // All replacements are ASCII spaces over whole tokens; UTF-8 stays valid.
    String::from_utf8(bytes).unwrap_or_else(|_| src.to_string())
}

type R = Result<(), String>;

struct Eraser<'a> {
    src: &'a str,
    toks: Vec<Token>,
    pos: usize,
    blanks: Vec<(usize, usize)>,
}

/// Gt-family punctuators: tokens whose first byte is `>`.
fn is_gt_family(pk: Pk) -> bool {
    matches!(pk, Pk::Gt | Pk::Shr | Pk::UShr | Pk::Ge | Pk::ShrEq | Pk::UShrEq)
}

impl<'a> Eraser<'a> {
    // ---- token cursor helpers ----

    fn cur(&self) -> Token {
        self.toks[self.pos]
    }
    fn at(&self, k: usize) -> Token {
        let i = (self.pos + k).min(self.toks.len() - 1);
        self.toks[i]
    }
    fn kind(&self) -> Tk {
        self.cur().kind
    }
    fn text(&self, t: Token) -> &'a str {
        &self.src[t.start..t.end]
    }
    fn cur_text(&self) -> &'a str {
        self.text(self.cur())
    }
    fn is_eof(&self) -> bool {
        matches!(self.kind(), Tk::Eof)
    }
    fn is_p(&self, pk: Pk) -> bool {
        self.kind() == Tk::Punct(pk)
    }
    fn at_is_p(&self, k: usize, pk: Pk) -> bool {
        self.at(k).kind == Tk::Punct(pk)
    }
    fn is_kw(&self, w: &str) -> bool {
        matches!(self.kind(), Tk::Ident) && self.cur_text() == w
    }
    fn at_is_kw(&self, k: usize, w: &str) -> bool {
        let t = self.at(k);
        matches!(t.kind, Tk::Ident) && self.text(t) == w
    }
    fn at_is_ident(&self, k: usize) -> bool {
        matches!(self.at(k).kind, Tk::Ident)
    }
    fn bump(&mut self) {
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
    }
    fn blank(&mut self, s: usize, e: usize) {
        if e > s {
            self.blanks.push((s, e));
        }
    }
    fn expect(&mut self, pk: Pk) -> R {
        if self.is_p(pk) {
            self.bump();
            Ok(())
        } else {
            Err(format!(
                "expected {:?} but found {:?} at byte {}",
                pk,
                self.kind(),
                self.cur().start
            ))
        }
    }

    /// Consume one `>` from a gt-family token at the cursor, splitting compound
    /// tokens (`>>` -> `>`, `>=` -> `=`, ...). Returns the byte offset just
    /// past the consumed `>`.
    fn eat_gt(&mut self) -> usize {
        let t = self.cur();
        let text = self.text(t);
        debug_assert!(text.starts_with('>'));
        if text.len() == 1 {
            self.bump();
            t.end
        } else {
            let ns = t.start + 1;
            let (pk, len) = lexer::match_punct(self.src.as_bytes(), ns)
                .expect("gt-family remainder is a punctuator");
            self.toks[self.pos] =
                Token { kind: Tk::Punct(pk), start: ns, end: ns + len, nl_before: false };
            ns
        }
    }

    // ---- program / statements ----

    fn walk_program(&mut self) -> R {
        while !self.is_eof() {
            self.walk_stmt()?;
        }
        Ok(())
    }

    fn walk_block(&mut self) -> R {
        self.expect(Pk::LBrace)?;
        while !self.is_p(Pk::RBrace) && !self.is_eof() {
            self.walk_stmt()?;
        }
        self.expect(Pk::RBrace)
    }

    fn walk_stmt(&mut self) -> R {
        // Punctuator-led statements.
        if self.is_p(Pk::Semi) {
            self.bump();
            return Ok(());
        }
        if self.is_p(Pk::LBrace) {
            return self.walk_block();
        }
        if self.is_p(Pk::At) {
            return Err("decorators are not pure type erasure".to_string());
        }

        if let Tk::Ident = self.kind() {
            let w = self.cur_text();
            match w {
                "import" => return self.walk_import(),
                "export" => return self.walk_export(),
                "interface" if self.at_is_ident(1) => return self.erase_interface(),
                "type" if self.looks_like_type_alias() => return self.erase_type_alias(),
                "enum" => return Err("enums are not pure type erasure".to_string()),
                "namespace" | "module" if self.looks_like_namespace() => {
                    return Err("namespaces/modules are not pure type erasure".to_string());
                }
                "declare" => return self.walk_declare(),
                "abstract" if self.at_is_kw(1, "class") => {
                    // Blank the TS-only `abstract` modifier, keep the class.
                    let t = self.cur();
                    self.blank(t.start, t.end);
                    self.bump();
                    return self.walk_class();
                }
                "class" => return self.walk_class(),
                "function" => return self.walk_function(false),
                "async" if self.at_is_kw(1, "function") => return self.walk_function(true),
                "const" if self.at_is_kw(1, "enum") => {
                    return Err("const enums are not pure type erasure".to_string());
                }
                "const" | "let" | "var" => return self.walk_var_stmt(),
                "if" => return self.walk_if(),
                "for" => return self.walk_for(),
                "while" | "with" => return self.walk_while(),
                "do" => return self.walk_do(),
                "switch" => return self.walk_switch(),
                "try" => return self.walk_try(),
                "return" | "throw" => {
                    self.bump();
                    if !self.is_p(Pk::Semi)
                        && !self.is_p(Pk::RBrace)
                        && !self.is_eof()
                        && !self.cur().nl_before
                    {
                        self.walk_expr_until(&[Pk::Semi])?;
                    }
                    if self.is_p(Pk::Semi) {
                        self.bump();
                    }
                    return Ok(());
                }
                "break" | "continue" => {
                    self.bump();
                    if self.at_is_ident_now() && !self.cur().nl_before {
                        self.bump(); // label
                    }
                    if self.is_p(Pk::Semi) {
                        self.bump();
                    }
                    return Ok(());
                }
                "debugger" => {
                    self.bump();
                    if self.is_p(Pk::Semi) {
                        self.bump();
                    }
                    return Ok(());
                }
                "else" | "case" | "default" | "catch" | "finally" => {
                    // Handled by their owning constructs; a stray one is an error.
                    return Err(format!("unexpected `{w}` at statement position"));
                }
                _ => {
                    // Labeled statement: `ident :` at statement start (the colon
                    // is a label, NOT a type annotation).
                    if self.at_is_p(1, Pk::Colon) {
                        self.bump(); // label ident
                        self.bump(); // colon
                        return self.walk_stmt();
                    }
                    // Fall through to expression statement.
                }
            }
        }

        // Expression statement.
        self.walk_expr_until(&[Pk::Semi])?;
        if self.is_p(Pk::Semi) {
            self.bump();
        }
        Ok(())
    }

    fn at_is_ident_now(&self) -> bool {
        matches!(self.kind(), Tk::Ident)
    }

    fn looks_like_type_alias(&self) -> bool {
        // `type Name<...> = ...` or `type Name = ...`
        self.at_is_ident(1) && (self.at_is_p(2, Pk::Eq) || self.at_is_p(2, Pk::Lt))
    }

    fn looks_like_namespace(&self) -> bool {
        // `namespace Name {` / `namespace A.B {` / `module 'x' {`
        (self.at_is_ident(1) && (self.at_is_p(2, Pk::LBrace) || self.at_is_p(2, Pk::Dot)))
            || (matches!(self.at(1).kind, Tk::Str) && self.at_is_p(2, Pk::LBrace))
    }

    // ---- control flow ----

    fn walk_paren_head(&mut self) -> R {
        self.expect(Pk::LParen)?;
        self.walk_expr_until(&[Pk::RParen])?;
        self.expect(Pk::RParen)
    }

    fn walk_if(&mut self) -> R {
        self.bump(); // if
        self.walk_paren_head()?;
        self.walk_stmt()?;
        if self.is_kw("else") {
            self.bump();
            self.walk_stmt()?;
        }
        Ok(())
    }

    fn walk_while(&mut self) -> R {
        self.bump();
        self.walk_paren_head()?;
        self.walk_stmt()
    }

    fn walk_do(&mut self) -> R {
        self.bump(); // do
        self.walk_stmt()?;
        if !self.is_kw("while") {
            return Err("expected `while` after do-body".to_string());
        }
        self.bump();
        self.walk_paren_head()?;
        if self.is_p(Pk::Semi) {
            self.bump();
        }
        Ok(())
    }

    fn walk_for(&mut self) -> R {
        self.bump(); // for
        // optional `await`
        if self.is_kw("await") {
            self.bump();
        }
        self.expect(Pk::LParen)?;
        // Initializer: optional decl keyword, then binding(s) with optional
        // type annotations, then either C-style `; ; )` or `of`/`in` expr.
        if self.is_kw("let") || self.is_kw("const") || self.is_kw("var") {
            self.bump();
            loop {
                self.walk_binding_target()?;
                self.erase_optional_annotation(&[Pk::Eq, Pk::Semi, Pk::Comma, Pk::RParen], true)?;
                if self.is_kw("of") || self.is_kw("in") {
                    self.bump();
                    self.walk_expr_until(&[Pk::RParen])?;
                    break;
                }
                if self.is_p(Pk::Eq) {
                    self.bump();
                    self.walk_expr_until(&[Pk::Comma, Pk::Semi, Pk::RParen])?;
                }
                if self.is_p(Pk::Comma) {
                    self.bump();
                    continue;
                }
                break;
            }
        } else if !self.is_p(Pk::Semi) {
            // expression initializer, or `expr of/in expr`
            self.walk_expr_until(&[Pk::Semi, Pk::RParen])?;
            if self.is_kw("of") || self.is_kw("in") {
                self.bump();
                self.walk_expr_until(&[Pk::RParen])?;
            }
        }
        // C-style remainder.
        if self.is_p(Pk::Semi) {
            self.bump();
            if !self.is_p(Pk::Semi) {
                self.walk_expr_until(&[Pk::Semi])?;
            }
            self.expect(Pk::Semi)?;
            if !self.is_p(Pk::RParen) {
                self.walk_expr_until(&[Pk::RParen])?;
            }
        }
        self.expect(Pk::RParen)?;
        self.walk_stmt()
    }

    fn walk_switch(&mut self) -> R {
        self.bump(); // switch
        self.walk_paren_head()?;
        self.expect(Pk::LBrace)?;
        while !self.is_p(Pk::RBrace) && !self.is_eof() {
            if self.is_kw("case") {
                self.bump();
                self.walk_expr_until(&[Pk::Colon])?;
                self.expect(Pk::Colon)?; // case label colon — kept
            } else if self.is_kw("default") {
                self.bump();
                self.expect(Pk::Colon)?;
            } else {
                self.walk_stmt()?;
            }
        }
        self.expect(Pk::RBrace)
    }

    fn walk_try(&mut self) -> R {
        self.bump(); // try
        self.walk_block()?;
        if self.is_kw("catch") {
            self.bump();
            if self.is_p(Pk::LParen) {
                self.bump();
                self.walk_binding_target()?;
                // `catch (e: unknown)` — erase the annotation.
                self.erase_optional_annotation(&[Pk::RParen], false)?;
                self.expect(Pk::RParen)?;
            }
            self.walk_block()?;
        }
        if self.is_kw("finally") {
            self.bump();
            self.walk_block()?;
        }
        Ok(())
    }

    // ---- variable statements ----

    fn walk_var_stmt(&mut self) -> R {
        self.bump(); // const/let/var
        loop {
            self.walk_binding_target()?;
            // definite-assignment `!` (TS-only) then annotation.
            self.erase_definite_assignment();
            self.erase_optional_annotation(&[Pk::Eq, Pk::Semi, Pk::Comma], true)?;
            if self.is_p(Pk::Eq) {
                self.bump();
                self.walk_expr_until(&[Pk::Comma, Pk::Semi])?;
            }
            if self.is_p(Pk::Comma) {
                self.bump();
                continue;
            }
            break;
        }
        if self.is_p(Pk::Semi) {
            self.bump();
        }
        Ok(())
    }

    /// A binding target: identifier or `{...}` / `[...]` pattern. Patterns are
    /// kept verbatim except nested defaults (expressions) and renamings.
    fn walk_binding_target(&mut self) -> R {
        match self.kind() {
            Tk::Ident => {
                self.bump();
                Ok(())
            }
            Tk::Punct(Pk::LBrace) => self.walk_binding_object(),
            Tk::Punct(Pk::LBracket) => self.walk_binding_array(),
            _ => Err(format!(
                "unexpected binding target {:?} at byte {}",
                self.kind(),
                self.cur().start
            )),
        }
    }

    fn walk_binding_object(&mut self) -> R {
        self.expect(Pk::LBrace)?;
        while !self.is_p(Pk::RBrace) && !self.is_eof() {
            if self.is_p(Pk::Ellipsis) {
                self.bump();
            }
            // key
            match self.kind() {
                Tk::Ident | Tk::Str | Tk::Num => self.bump(),
                Tk::Punct(Pk::LBracket) => {
                    self.bump();
                    self.walk_expr_until(&[Pk::RBracket])?;
                    self.expect(Pk::RBracket)?;
                }
                _ => return Err("bad object binding key".to_string()),
            }
            if self.is_p(Pk::Colon) {
                self.bump(); // rename — colon kept
                self.walk_binding_target()?;
            }
            if self.is_p(Pk::Eq) {
                self.bump();
                self.walk_expr_until(&[Pk::Comma, Pk::RBrace])?;
            }
            if self.is_p(Pk::Comma) {
                self.bump();
            }
        }
        self.expect(Pk::RBrace)
    }

    fn walk_binding_array(&mut self) -> R {
        self.expect(Pk::LBracket)?;
        while !self.is_p(Pk::RBracket) && !self.is_eof() {
            if self.is_p(Pk::Comma) {
                self.bump(); // elision
                continue;
            }
            if self.is_p(Pk::Ellipsis) {
                self.bump();
            }
            self.walk_binding_target()?;
            if self.is_p(Pk::Eq) {
                self.bump();
                self.walk_expr_until(&[Pk::Comma, Pk::RBracket])?;
            }
            if self.is_p(Pk::Comma) {
                self.bump();
            }
        }
        self.expect(Pk::RBracket)
    }

    /// Blank a TS definite-assignment `!` if present at the cursor.
    fn erase_definite_assignment(&mut self) {
        if self.is_p(Pk::Bang) {
            let t = self.cur();
            self.blank(t.start, t.end);
            self.bump();
        }
    }

    /// If the cursor is at `:` (a type annotation), blank `:` + the type,
    /// stopping at a depth-0 token in `stops` (and, if `asi`, at a newline).
    fn erase_optional_annotation(&mut self, stops: &[Pk], asi: bool) -> R {
        if self.is_p(Pk::Colon) {
            let start = self.cur().start;
            self.bump(); // consume `:`; type follows
            let end = self.skip_type(stops, asi)?;
            self.blank(start, end);
        }
        Ok(())
    }

    // ---- imports / exports ----

    fn walk_import(&mut self) -> R {
        // Dynamic import / import.meta are expressions.
        if self.at_is_p(1, Pk::LParen) || self.at_is_p(1, Pk::Dot) {
            self.walk_expr_until(&[Pk::Semi])?;
            if self.is_p(Pk::Semi) {
                self.bump();
            }
            return Ok(());
        }
        // `import type ...` — type-only, erase the whole statement.
        if self.at_is_kw(1, "type") && self.import_type_is_typeonly() {
            return self.erase_stmt_to_end();
        }
        // `import X = ...` — TS import-equals, refuse.
        if self.at_is_ident(1) && self.at_is_p(2, Pk::Eq) {
            return Err("import-equals (`import X = ...`) is not pure erasure".to_string());
        }
        // Ordinary import: keep verbatim to the statement end, but blank any
        // per-specifier `type` markers inside `{ ... }`.
        self.bump(); // import
        while !self.is_p(Pk::Semi) && !self.is_eof() {
            if self.cur().nl_before && self.is_stmt_boundary_ident() {
                break; // ASI
            }
            if self.is_p(Pk::LBrace) {
                self.blank_named_specifier_types()?;
                continue;
            }
            self.bump();
        }
        if self.is_p(Pk::Semi) {
            self.bump();
        }
        Ok(())
    }

    /// Is `import type ...` type-only (vs. `import type from '...'` importing a
    /// binding literally named `type`)?
    fn import_type_is_typeonly(&self) -> bool {
        // peek(1) == "type"; classify peek(2).
        let t2 = self.at(2);
        match t2.kind {
            Tk::Punct(Pk::LBrace) => true,        // import type { ... }
            Tk::Punct(Pk::Star) => true,          // import type * as ns
            Tk::Ident => self.text(t2) != "from", // import type Foo ...
            _ => false,
        }
    }

    fn is_stmt_boundary_ident(&self) -> bool {
        // A newline before one of these idents means the import/export ended.
        matches!(self.kind(), Tk::Ident)
            && matches!(
                self.cur_text(),
                "import"
                    | "export"
                    | "const"
                    | "let"
                    | "var"
                    | "function"
                    | "class"
                    | "return"
                    | "if"
                    | "for"
                    | "while"
                    | "type"
                    | "interface"
            )
    }

    /// At a `{` beginning a named import/export list: blank each `type`
    /// specifier marker (`{ type A, b }` -> `{      A, b }`).
    fn blank_named_specifier_types(&mut self) -> R {
        self.expect(Pk::LBrace)?;
        while !self.is_p(Pk::RBrace) && !self.is_eof() {
            // A type-only specifier `type Name [as Alias]` (but not `type as X`,
            // which imports a binding literally named `type`). The ENTIRE
            // specifier is erased, plus a following comma, so no dangling name
            // is imported/exported as a value. A now-trailing comma is legal.
            let type_only = self.is_kw("type") && self.at_is_ident(1) && !self.at_is_kw(1, "as");
            let start = self.cur().start;
            while !self.is_p(Pk::Comma) && !self.is_p(Pk::RBrace) && !self.is_eof() {
                self.bump();
            }
            let mut end = self.toks[self.pos.saturating_sub(1)].end;
            if self.is_p(Pk::Comma) {
                end = self.cur().end;
                self.bump();
            }
            if type_only {
                self.blank(start, end);
            }
        }
        self.expect(Pk::RBrace)
    }

    fn walk_export(&mut self) -> R {
        // `export = X` — refuse.
        if self.at_is_p(1, Pk::Eq) {
            return Err("export-equals (`export = ...`) is not pure erasure".to_string());
        }
        // `export type ...` — erase.
        if self.at_is_kw(1, "type")
            && (self.at_is_p(2, Pk::LBrace) || self.at_is_ident(2) || self.at_is_p(2, Pk::Star))
        {
            return self.erase_stmt_to_end();
        }
        // `export interface ...` / `export enum` / `export namespace` / declare.
        if self.at_is_kw(1, "interface") {
            return self.erase_stmt_to_end_with_block();
        }
        if self.at_is_kw(1, "enum") {
            return Err("enums are not pure type erasure".to_string());
        }
        if self.at_is_kw(1, "namespace") || self.at_is_kw(1, "module") {
            return Err("namespaces/modules are not pure type erasure".to_string());
        }
        // `export default <expr|decl>`
        if self.at_is_kw(1, "default") {
            self.bump(); // export
            self.bump(); // default
            if self.is_kw("function") {
                return self.walk_function(false);
            }
            if self.is_kw("async") && self.at_is_kw(1, "function") {
                return self.walk_function(true);
            }
            if self.is_kw("class") {
                return self.walk_class();
            }
            if self.is_kw("abstract") && self.at_is_kw(1, "class") {
                let t = self.cur();
                self.blank(t.start, t.end);
                self.bump();
                return self.walk_class();
            }
            self.walk_expr_until(&[Pk::Semi])?;
            if self.is_p(Pk::Semi) {
                self.bump();
            }
            return Ok(());
        }
        // `export declare ...`
        if self.at_is_kw(1, "declare") {
            self.bump(); // export
            return self.walk_declare();
        }
        // `export const/let/var/function/class/abstract class`
        self.bump(); // export
        if self.is_kw("const") && self.at_is_kw(1, "enum") {
            return Err("const enums are not pure type erasure".to_string());
        }
        if self.is_kw("const") || self.is_kw("let") || self.is_kw("var") {
            return self.walk_var_stmt();
        }
        if self.is_kw("function") {
            return self.walk_function(false);
        }
        if self.is_kw("async") && self.at_is_kw(1, "function") {
            return self.walk_function(true);
        }
        if self.is_kw("class") {
            return self.walk_class();
        }
        if self.is_kw("abstract") && self.at_is_kw(1, "class") {
            let t = self.cur();
            self.blank(t.start, t.end);
            self.bump();
            return self.walk_class();
        }
        // `export { ... }` / `export * from ...` — keep, blank type specifiers.
        while !self.is_p(Pk::Semi) && !self.is_eof() {
            if self.cur().nl_before && self.is_stmt_boundary_ident() {
                break;
            }
            if self.is_p(Pk::LBrace) {
                self.blank_named_specifier_types()?;
                continue;
            }
            self.bump();
        }
        if self.is_p(Pk::Semi) {
            self.bump();
        }
        Ok(())
    }

    // ---- type-only declarations (fully erased) ----

    fn erase_interface(&mut self) -> R {
        // interface Name<..> [extends A, B] { ...balanced... }
        let start = self.cur().start;
        // find the body `{` at depth 0, then blank through its matching `}`.
        let mut depth = 0i32; // parens/brackets/angles
        while !self.is_eof() {
            if depth == 0 && self.is_p(Pk::LBrace) {
                let end = self.skip_balanced_braces()?;
                self.blank(start, end);
                return Ok(());
            }
            match self.kind() {
                Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::Lt) => depth += 1,
                Tk::Punct(Pk::Shl) => depth += 2,
                Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => depth -= 1,
                Tk::Punct(pk) if is_gt_family(pk) => {
                    self.eat_gt();
                    depth -= 1;
                    continue;
                }
                _ => {}
            }
            self.bump();
        }
        Err("unterminated interface declaration".to_string())
    }

    fn erase_type_alias(&mut self) -> R {
        // type Name<..> = <type> ;
        let start = self.cur().start;
        self.bump(); // type
        self.bump(); // Name
        if self.is_p(Pk::Lt) {
            self.skip_balanced_angle()?; // (span blanked separately, harmless)
        }
        if !self.is_p(Pk::Eq) {
            return Err("malformed type alias (expected `=`)".to_string());
        }
        self.bump(); // =
        let end = self.skip_type(&[Pk::Semi], true)?;
        self.blank(start, end);
        if self.is_p(Pk::Semi) {
            self.bump();
        }
        Ok(())
    }

    /// Erase a simple statement (no block body) through `;`/ASI.
    fn erase_stmt_to_end(&mut self) -> R {
        let start = self.cur().start;
        let mut depth = 0i32;
        let mut consumed = false;
        while !self.is_eof() {
            if depth == 0 {
                if self.is_p(Pk::Semi) {
                    let end = self.cur().end;
                    self.bump();
                    self.blank(start, end);
                    return Ok(());
                }
                if consumed && self.cur().nl_before {
                    // ASI: end before this token.
                    let end = self.toks[self.pos - 1].end;
                    self.blank(start, end);
                    return Ok(());
                }
            }
            consumed = true;
            match self.kind() {
                Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::LBrace) => {
                    depth += 1
                }
                Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => {
                    depth -= 1
                }
                _ => {}
            }
            self.bump();
        }
        let end = self.toks[self.pos - 1].end;
        self.blank(start, end);
        Ok(())
    }

    /// Erase a declaration that may carry a `{...}` block body (interface).
    fn erase_stmt_to_end_with_block(&mut self) -> R {
        self.bump(); // export
        self.erase_interface()
    }

    fn walk_declare(&mut self) -> R {
        // `declare` — fully erased.
        let n1 = self.at(1);
        let w1 = if matches!(n1.kind, Tk::Ident) { self.text(n1) } else { "" };
        match w1 {
            "global" | "module" | "namespace" | "class" | "enum" | "abstract" | "interface" => {
                // Block form: blank through the first depth-0 `{...}` body.
                let start = self.cur().start;
                let mut depth = 0i32;
                while !self.is_eof() {
                    if depth == 0 && self.is_p(Pk::LBrace) {
                        let end = self.skip_balanced_braces()?;
                        self.blank(start, end);
                        return Ok(());
                    }
                    match self.kind() {
                        Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::Lt) => {
                            depth += 1
                        }
                        Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => depth -= 1,
                        Tk::Punct(pk) if is_gt_family(pk) => {
                            self.eat_gt();
                            depth -= 1;
                            continue;
                        }
                        _ => {}
                    }
                    self.bump();
                }
                Err("unterminated declare block".to_string())
            }
            "const" | "let" | "var" | "function" | "type" => self.erase_stmt_to_end(),
            _ => Err(format!("unsupported `declare {w1}` form")),
        }
    }

    // ---- functions ----

    fn walk_function(&mut self, is_async: bool) -> R {
        let start = self.cur().start; // async or function
        if is_async {
            self.bump(); // async
        }
        self.bump(); // function
        if self.is_p(Pk::Star) {
            self.bump(); // generator
        }
        if matches!(self.kind(), Tk::Ident) {
            self.bump(); // name
        }
        if self.is_p(Pk::Lt) {
            self.skip_balanced_angle()?;
        }
        self.walk_params()?;
        // optional return type
        self.erase_optional_annotation(&[Pk::LBrace, Pk::Semi], false)?;
        if self.is_p(Pk::LBrace) {
            return self.walk_block();
        }
        // No body: an overload signature — erase the entire declaration.
        let end = if self.is_p(Pk::Semi) {
            let e = self.cur().end;
            self.bump();
            e
        } else {
            self.toks[self.pos.saturating_sub(1)].end
        };
        self.blank(start, end);
        Ok(())
    }

    /// Parameter list `( ... )`. Blanks TS-only param syntax; refuses parameter
    /// properties and parameter decorators.
    fn walk_params(&mut self) -> R {
        self.expect(Pk::LParen)?;
        while !self.is_p(Pk::RParen) && !self.is_eof() {
            if self.is_p(Pk::At) {
                return Err("parameter decorators are not pure type erasure".to_string());
            }
            // Parameter properties (`constructor(private x)`) — refuse.
            if matches!(self.kind(), Tk::Ident)
                && matches!(self.cur_text(), "public" | "private" | "protected" | "readonly")
            {
                return Err("parameter properties are not pure type erasure".to_string());
            }
            // A `this` type parameter is entirely TS-only: blank it and its
            // trailing comma (Node removes the whole parameter).
            if self.is_kw("this")
                && (self.at_is_p(1, Pk::Colon)
                    || self.at_is_p(1, Pk::Comma)
                    || self.at_is_p(1, Pk::RParen))
            {
                let start = self.cur().start;
                self.bump(); // this
                let mut end = self.toks[self.pos - 1].end;
                if self.is_p(Pk::Colon) {
                    self.bump();
                    end = self.skip_type(&[Pk::Comma, Pk::RParen], false)?;
                }
                if self.is_p(Pk::Comma) {
                    end = self.cur().end;
                    self.bump();
                }
                self.blank(start, end);
                continue;
            }
            if self.is_p(Pk::Ellipsis) {
                self.bump(); // rest
            }
            self.walk_binding_target()?;
            // optional `?` (TS-only) — blank.
            if self.is_p(Pk::Question) {
                let t = self.cur();
                self.blank(t.start, t.end);
                self.bump();
            }
            // optional annotation `: type`.
            self.erase_optional_annotation(&[Pk::Comma, Pk::RParen, Pk::Eq], false)?;
            // optional default.
            if self.is_p(Pk::Eq) {
                self.bump();
                self.walk_expr_until(&[Pk::Comma, Pk::RParen])?;
            }
            if self.is_p(Pk::Comma) {
                self.bump();
            }
        }
        self.expect(Pk::RParen)
    }

    // ---- classes ----

    fn walk_class(&mut self) -> R {
        self.bump(); // class
        if matches!(self.kind(), Tk::Ident) && !self.is_kw("extends") && !self.is_kw("implements") {
            self.bump(); // name
        }
        if self.is_p(Pk::Lt) {
            self.skip_balanced_angle()?;
        }
        if self.is_kw("extends") {
            self.bump();
            // Superclass expression (may carry type args with no call parens).
            self.walk_heritage_expr()?;
        }
        if self.is_kw("implements") {
            // Blank `implements TypeList` up to the class body `{`.
            let start = self.cur().start;
            let mut depth = 0i32;
            while !self.is_eof() {
                if depth == 0 && self.is_p(Pk::LBrace) {
                    break;
                }
                match self.kind() {
                    Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::Lt) => {
                        depth += 1
                    }
                    Tk::Punct(Pk::Shl) => depth += 2,
                    Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => depth -= 1,
                    Tk::Punct(pk) if is_gt_family(pk) => {
                        self.eat_gt();
                        depth -= 1;
                        continue;
                    }
                    _ => {}
                }
                self.bump();
            }
            let end = self.toks[self.pos.saturating_sub(1)].end;
            self.blank(start, end);
        }
        self.walk_class_body()
    }

    /// The `extends` superclass: a left-hand-side expression that may end in
    /// type arguments (`extends Base<T>`) with no following call.
    fn walk_heritage_expr(&mut self) -> R {
        let mut after_operand = false;
        loop {
            if self.is_eof() {
                return Err("unterminated extends clause".to_string());
            }
            if self.is_p(Pk::LBrace) && after_operand {
                return Ok(()); // class body
            }
            if self.is_kw("implements") && after_operand {
                return Ok(());
            }
            match self.kind() {
                Tk::Punct(Pk::Lt) if after_operand => {
                    // Heritage type args — blank (no `(` requirement here).
                    if self.try_blank_type_args_no_call() {
                        after_operand = true;
                    } else {
                        return Err("ambiguous `<` in extends clause".to_string());
                    }
                }
                Tk::Punct(Pk::LParen) if after_operand => {
                    self.walk_call_args()?;
                    after_operand = true;
                }
                Tk::Punct(Pk::LParen) => {
                    self.bump();
                    self.walk_expr_until(&[Pk::RParen])?;
                    self.expect(Pk::RParen)?;
                    after_operand = true;
                }
                Tk::Punct(Pk::LBracket) if after_operand => {
                    self.bump();
                    self.walk_expr_until(&[Pk::RBracket])?;
                    self.expect(Pk::RBracket)?;
                    after_operand = true;
                }
                Tk::Punct(Pk::Dot) | Tk::Punct(Pk::QDot) => {
                    self.bump();
                    if matches!(self.kind(), Tk::Ident | Tk::Private) {
                        self.bump();
                    }
                    after_operand = true;
                }
                Tk::Ident => {
                    self.bump();
                    after_operand = true;
                }
                _ => return Err("unexpected token in extends clause".to_string()),
            }
        }
    }

    fn walk_class_body(&mut self) -> R {
        self.expect(Pk::LBrace)?;
        while !self.is_p(Pk::RBrace) && !self.is_eof() {
            if self.is_p(Pk::Semi) {
                self.bump();
                continue;
            }
            self.walk_class_member()?;
        }
        self.expect(Pk::RBrace)
    }

    fn walk_class_member(&mut self) -> R {
        let member_start = self.cur().start;
        if self.is_p(Pk::At) {
            return Err("member decorators are not pure type erasure".to_string());
        }
        // Modifiers: blank TS-only ones; keep `static`.
        while let Tk::Ident = self.kind() {
            let w = self.cur_text();
            match w {
                "public" | "private" | "protected" | "readonly" | "abstract" | "override"
                | "declare" => {
                    // Only a modifier if followed by more member syntax (not
                    // if it is itself the member name, e.g. `private()` or
                    // `readonly = 1`).
                    if self.modifier_is_modifier() {
                        let t = self.cur();
                        self.blank(t.start, t.end);
                        self.bump();
                        continue;
                    }
                    break;
                }
                "static" => {
                    if self.modifier_is_modifier() {
                        self.bump(); // keep static
                        continue;
                    }
                    break;
                }
                _ => break,
            }
        }
        // Index signature `[key: string]: T;` — pure type, blank whole member.
        if self.is_p(Pk::LBracket) && self.at_is_ident(1) && self.at_is_p(2, Pk::Colon) {
            let mut depth = 0i32;
            while !self.is_eof() {
                match self.kind() {
                    Tk::Punct(Pk::LBracket) => depth += 1,
                    Tk::Punct(Pk::RBracket) => depth -= 1,
                    Tk::Punct(Pk::Semi) if depth == 0 => {
                        let end = self.cur().end;
                        self.bump();
                        self.blank(member_start, end);
                        return Ok(());
                    }
                    _ => {}
                }
                if depth == 0 && self.cur().nl_before && self.pos > 0 && !self.is_p(Pk::LBracket) {
                    let end = self.toks[self.pos - 1].end;
                    self.blank(member_start, end);
                    return Ok(());
                }
                self.bump();
            }
            return Err("unterminated index signature".to_string());
        }
        // get/set/async/generator prefixes (kept) — only when a name follows.
        if (self.is_kw("get") || self.is_kw("set") || self.is_kw("async"))
            && self.accessor_prefix_has_name()
        {
            self.bump();
        }
        if self.is_p(Pk::Star) {
            self.bump();
        }
        // Member name.
        match self.kind() {
            Tk::Ident | Tk::Private | Tk::Str | Tk::Num => self.bump(),
            Tk::Punct(Pk::LBracket) => {
                self.bump();
                self.walk_expr_until(&[Pk::RBracket])?;
                self.expect(Pk::RBracket)?;
            }
            _ => {
                return Err(format!(
                    "unexpected class member {:?} at byte {}",
                    self.kind(),
                    self.cur().start
                ));
            }
        }
        // `?` / `!` markers (TS-only) — blank.
        if self.is_p(Pk::Question) || self.is_p(Pk::Bang) {
            let t = self.cur();
            self.blank(t.start, t.end);
            self.bump();
        }
        // Method type params.
        if self.is_p(Pk::Lt) {
            self.skip_balanced_angle()?;
        }
        if self.is_p(Pk::LParen) {
            // Method.
            self.walk_params()?;
            self.erase_optional_annotation(&[Pk::LBrace, Pk::Semi], false)?;
            if self.is_p(Pk::LBrace) {
                return self.walk_block();
            }
            // No body: overload / abstract signature — blank whole member.
            let end = if self.is_p(Pk::Semi) {
                let e = self.cur().end;
                self.bump();
                e
            } else {
                self.toks[self.pos.saturating_sub(1)].end
            };
            self.blank(member_start, end);
            Ok(())
        } else {
            // Field.
            self.erase_optional_annotation(&[Pk::Eq, Pk::Semi, Pk::RBrace, Pk::Comma], true)?;
            if self.is_p(Pk::Eq) {
                self.bump();
                self.walk_expr_until(&[Pk::Semi, Pk::RBrace, Pk::Comma])?;
            }
            if self.is_p(Pk::Semi) || self.is_p(Pk::Comma) {
                self.bump();
            }
            Ok(())
        }
    }

    /// A modifier keyword is a real modifier (not the member name) unless the
    /// next token indicates the keyword IS the name.
    fn modifier_is_modifier(&self) -> bool {
        !matches!(
            self.at(1).kind,
            Tk::Punct(Pk::LParen)   // method named e.g. `static()`
                | Tk::Punct(Pk::Eq)     // field `readonly = 1`
                | Tk::Punct(Pk::Colon)  // field `private: T`
                | Tk::Punct(Pk::Semi)
                | Tk::Punct(Pk::RBrace)
                | Tk::Punct(Pk::Question)
                | Tk::Punct(Pk::Bang)
        )
    }

    fn accessor_prefix_has_name(&self) -> bool {
        matches!(
            self.at(1).kind,
            Tk::Ident | Tk::Private | Tk::Str | Tk::Num | Tk::Punct(Pk::LBracket)
        ) && !self.at_is_p(1, Pk::LParen)
    }

    // ---- expressions ----

    /// Walk an expression, keeping tokens and erasing type positions, stopping
    /// (without consuming) at a depth-0 token in `stops`, at a template
    /// continuation, at Eof, or at an ASI boundary.
    fn walk_expr_until(&mut self, stops: &[Pk]) -> R {
        let mut after_operand = false;
        loop {
            let t = self.cur();
            match t.kind {
                Tk::Eof | Tk::TemplateMiddle | Tk::TemplateTail => return Ok(()),
                Tk::Punct(pk) => {
                    if stops.contains(&pk) {
                        return Ok(());
                    }
                    // ASI: a newline before a token that starts a new statement.
                    if after_operand && t.nl_before && self.asi_stops_expr() {
                        return Ok(());
                    }
                    match pk {
                        Pk::LParen => {
                            if after_operand {
                                self.walk_call_args()?;
                            } else {
                                self.walk_paren_or_arrow(stops)?;
                            }
                            after_operand = true;
                        }
                        Pk::LBracket => {
                            if after_operand {
                                self.bump();
                                self.walk_expr_until(&[Pk::RBracket])?;
                                self.expect(Pk::RBracket)?;
                            } else {
                                self.walk_array_literal()?;
                            }
                            after_operand = true;
                        }
                        Pk::LBrace => {
                            if after_operand {
                                return Err("unexpected `{` in expression".to_string());
                            }
                            self.walk_object_literal()?;
                            after_operand = true;
                        }
                        Pk::Bang => {
                            if after_operand {
                                // Non-null assertion — blank.
                                self.blank(t.start, t.end);
                                self.bump();
                                // still after an operand
                            } else {
                                self.bump(); // logical not
                            }
                        }
                        Pk::Lt => {
                            if after_operand {
                                if self.try_blank_call_type_args() {
                                    // stays after_operand; next token is `(`
                                } else {
                                    self.bump(); // less-than
                                    after_operand = false;
                                }
                            } else if self.try_generic_arrow(stops)? {
                                after_operand = true;
                            } else {
                                return Err(
                                    "`<` in operand position (type assertion or JSX) unsupported"
                                        .to_string(),
                                );
                            }
                        }
                        Pk::Dot | Pk::QDot => {
                            self.bump();
                            match self.kind() {
                                Tk::Ident | Tk::Private => {
                                    self.bump();
                                    after_operand = true;
                                }
                                Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) => {
                                    // `?.(` / `?.[` — handled next loop iteration.
                                    after_operand = true;
                                }
                                _ => after_operand = true,
                            }
                        }
                        Pk::Arrow => {
                            // Arrow with a body we reach directly (e.g. `x => ...`).
                            self.bump();
                            if self.is_p(Pk::LBrace) {
                                self.walk_block()?;
                            } else {
                                self.walk_expr_until(stops)?;
                            }
                            after_operand = true;
                        }
                        Pk::PlusPlus | Pk::MinusMinus => {
                            // prefix or postfix — either way keep; operand state
                            // is preserved for postfix, reset for prefix.
                            self.bump();
                        }
                        _ => {
                            // Any other operator/punctuator: keep and expect an
                            // operand next.
                            self.bump();
                            after_operand = false;
                        }
                    }
                }
                Tk::Ident => {
                    let w = self.text(t);
                    if after_operand && (w == "as" || w == "satisfies") && !t.nl_before {
                        self.erase_as_type()?;
                        // stays after_operand
                    } else if w == "function" {
                        self.walk_function_expr()?;
                        after_operand = true;
                    } else if w == "class" {
                        self.walk_class()?;
                        after_operand = true;
                    } else if w == "new"
                        || matches!(
                            w,
                            "typeof" | "void" | "delete" | "await" | "yield" | "in" | "instanceof"
                        )
                    {
                        self.bump();
                        after_operand = false;
                    } else {
                        // identifier or value keyword (true/false/null/this/...)
                        self.bump();
                        after_operand = true;
                    }
                }
                Tk::Num | Tk::Str | Tk::Regex | Tk::TemplateFull => {
                    self.bump();
                    after_operand = true;
                }
                Tk::Private => {
                    self.bump();
                    after_operand = true;
                }
                Tk::TemplateHead => {
                    self.walk_template()?;
                    after_operand = true;
                }
            }
        }
    }

    fn asi_stops_expr(&self) -> bool {
        // Conservative ASI: a newline before an identifier that starts a new
        // statement, or before `}`.
        match self.kind() {
            Tk::Ident => !matches!(self.cur_text(), "as" | "satisfies" | "in" | "instanceof"),
            _ => false,
        }
    }

    fn walk_template(&mut self) -> R {
        // cur is TemplateHead.
        self.bump();
        loop {
            self.walk_expr_until(&[])?;
            match self.kind() {
                Tk::TemplateMiddle => {
                    self.bump();
                    continue;
                }
                Tk::TemplateTail => {
                    self.bump();
                    return Ok(());
                }
                _ => return Err("malformed template literal".to_string()),
            }
        }
    }

    fn walk_call_args(&mut self) -> R {
        self.expect(Pk::LParen)?;
        while !self.is_p(Pk::RParen) && !self.is_eof() {
            self.walk_expr_until(&[Pk::Comma, Pk::RParen])?;
            if self.is_p(Pk::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(Pk::RParen)
    }

    fn walk_array_literal(&mut self) -> R {
        self.expect(Pk::LBracket)?;
        while !self.is_p(Pk::RBracket) && !self.is_eof() {
            if self.is_p(Pk::Comma) {
                self.bump(); // elision
                continue;
            }
            self.walk_expr_until(&[Pk::Comma, Pk::RBracket])?;
            if self.is_p(Pk::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(Pk::RBracket)
    }

    fn walk_object_literal(&mut self) -> R {
        self.expect(Pk::LBrace)?;
        while !self.is_p(Pk::RBrace) && !self.is_eof() {
            if self.is_p(Pk::Comma) {
                self.bump();
                continue;
            }
            if self.is_p(Pk::Ellipsis) {
                self.bump();
                self.walk_expr_until(&[Pk::Comma, Pk::RBrace])?;
                continue;
            }
            // get/set/async/generator method prefixes.
            if (self.is_kw("get") || self.is_kw("set") || self.is_kw("async"))
                && self.accessor_prefix_has_name()
            {
                self.bump();
            }
            if self.is_p(Pk::Star) {
                self.bump();
            }
            // Key.
            match self.kind() {
                Tk::Ident | Tk::Str | Tk::Num | Tk::Private => self.bump(),
                Tk::Punct(Pk::LBracket) => {
                    self.bump();
                    self.walk_expr_until(&[Pk::RBracket])?;
                    self.expect(Pk::RBracket)?;
                }
                _ => return Err("bad object literal key".to_string()),
            }
            if self.is_p(Pk::LParen) || self.is_p(Pk::Lt) {
                // Method.
                if self.is_p(Pk::Lt) {
                    self.skip_balanced_angle()?;
                }
                self.walk_params()?;
                self.erase_optional_annotation(&[Pk::LBrace], false)?;
                self.walk_block()?;
            } else if self.is_p(Pk::Colon) {
                // Property `key: value` — colon KEPT (not a type).
                self.bump();
                self.walk_expr_until(&[Pk::Comma, Pk::RBrace])?;
            } else if self.is_p(Pk::Eq) {
                // Shorthand default (pattern context) — keep.
                self.bump();
                self.walk_expr_until(&[Pk::Comma, Pk::RBrace])?;
            }
            // shorthand `{ a }` needs nothing.
            if self.is_p(Pk::Comma) {
                self.bump();
            }
        }
        self.expect(Pk::RBrace)
    }

    fn walk_function_expr(&mut self) -> R {
        self.bump(); // function
        if self.is_p(Pk::Star) {
            self.bump();
        }
        if matches!(self.kind(), Tk::Ident) {
            self.bump(); // name
        }
        if self.is_p(Pk::Lt) {
            self.skip_balanced_angle()?;
        }
        self.walk_params()?;
        self.erase_optional_annotation(&[Pk::LBrace], false)?;
        self.walk_block()
    }

    /// At `(` in operand position: decide parenthesized-expression vs arrow.
    fn walk_paren_or_arrow(&mut self, stops: &[Pk]) -> R {
        let close = self.scan_matching_paren(self.pos);
        let after = close + 1;
        let is_arrow = if self.toks[after].kind == Tk::Punct(Pk::Arrow) {
            true
        } else if self.toks[after].kind == Tk::Punct(Pk::Colon) {
            // `(params): ReturnType =>` — look for `=>` after the return type.
            let type_end = self.scan_type_end(after + 1, &[Pk::Arrow, Pk::LBrace, Pk::Semi]);
            self.toks[type_end].kind == Tk::Punct(Pk::Arrow)
        } else {
            false
        };
        if is_arrow {
            self.walk_params()?;
            self.erase_optional_annotation(&[Pk::Arrow, Pk::LBrace], false)?;
            self.expect(Pk::Arrow)?;
            if self.is_p(Pk::LBrace) { self.walk_block() } else { self.walk_expr_until(stops) }
        } else {
            self.bump(); // (
            self.walk_expr_until(&[Pk::RParen])?;
            self.expect(Pk::RParen)
        }
    }

    /// `<T,>(params) => body` in operand position.
    fn try_generic_arrow(&mut self, stops: &[Pk]) -> Result<bool, String> {
        // cur is `<`. Scan a type-arg-shaped angle span; require `(` after and
        // an eventual `=>`.
        let Some((after_angle, _)) = self.scan_type_args_span(self.pos) else {
            return Ok(false);
        };
        if self.toks[after_angle].kind != Tk::Punct(Pk::LParen) {
            return Ok(false);
        }
        let close = self.scan_matching_paren(after_angle);
        let after = close + 1;
        let is_arrow = if self.toks[after].kind == Tk::Punct(Pk::Arrow) {
            true
        } else if self.toks[after].kind == Tk::Punct(Pk::Colon) {
            let type_end = self.scan_type_end(after + 1, &[Pk::Arrow, Pk::LBrace, Pk::Semi]);
            self.toks[type_end].kind == Tk::Punct(Pk::Arrow)
        } else {
            false
        };
        if !is_arrow {
            return Ok(false);
        }
        // Blank the type-params, then walk the arrow.
        self.skip_balanced_angle()?;
        self.walk_params()?;
        self.erase_optional_annotation(&[Pk::Arrow, Pk::LBrace], false)?;
        self.expect(Pk::Arrow)?;
        if self.is_p(Pk::LBrace) {
            self.walk_block()?;
        } else {
            self.walk_expr_until(stops)?;
        }
        Ok(true)
    }

    /// After an operand, a `<...>` type-argument list IFF it scans as a type
    /// list and is immediately followed by `(` (a call). Otherwise `<` is
    /// less-than. Blanks the angle span and leaves the cursor at `(`.
    fn try_blank_call_type_args(&mut self) -> bool {
        if let Some((after_angle, end_byte)) = self.scan_type_args_span(self.pos)
            && self.toks[after_angle].kind == Tk::Punct(Pk::LParen)
        {
            let start = self.cur().start;
            self.blank(start, end_byte);
            self.pos = after_angle;
            return true;
        }
        false
    }

    /// Blank a `<...>` type-argument span with no following-call requirement
    /// (heritage clauses). Returns false if it does not scan as a type list.
    fn try_blank_type_args_no_call(&mut self) -> bool {
        if let Some((after_angle, end_byte)) = self.scan_type_args_span(self.pos) {
            let start = self.cur().start;
            self.blank(start, end_byte);
            self.pos = after_angle;
            return true;
        }
        false
    }

    /// `expr as Type` / `expr satisfies Type`: blank the operator and a simple
    /// following type. Refuses type forms that begin with `(`/`{` (which would
    /// need a full type grammar to delimit soundly).
    fn erase_as_type(&mut self) -> R {
        let start = self.cur().start;
        self.bump(); // as / satisfies
        if !matches!(self.kind(), Tk::Ident | Tk::Num | Tk::Str) {
            return Err("`as`/`satisfies` with a non-simple type is unsupported".to_string());
        }
        let mut depth = 0i32; // parens/brackets/braces/angles inside the type
        let mut last_end = self.cur().end;
        loop {
            let t = self.cur();
            if depth == 0 {
                match t.kind {
                    Tk::Ident | Tk::Num | Tk::Str => {
                        last_end = t.end;
                        self.bump();
                    }
                    Tk::Punct(Pk::Dot) => {
                        last_end = t.end;
                        self.bump();
                    }
                    Tk::Punct(Pk::Lt) => {
                        depth += 1;
                        last_end = t.end;
                        self.bump();
                    }
                    Tk::Punct(Pk::Shl) => {
                        depth += 2;
                        last_end = t.end;
                        self.bump();
                    }
                    Tk::Punct(Pk::LBracket) => {
                        depth += 1;
                        last_end = t.end;
                        self.bump();
                    }
                    Tk::Punct(Pk::Pipe) | Tk::Punct(Pk::Amp) => {
                        last_end = t.end;
                        self.bump();
                    }
                    _ => break,
                }
            } else {
                match t.kind {
                    Tk::Eof => break,
                    Tk::Punct(Pk::LParen)
                    | Tk::Punct(Pk::LBracket)
                    | Tk::Punct(Pk::LBrace)
                    | Tk::Punct(Pk::Lt) => {
                        depth += 1;
                        last_end = t.end;
                        self.bump();
                    }
                    Tk::Punct(Pk::Shl) => {
                        depth += 2;
                        last_end = t.end;
                        self.bump();
                    }
                    Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => {
                        depth -= 1;
                        last_end = t.end;
                        self.bump();
                    }
                    Tk::Punct(pk) if is_gt_family(pk) => {
                        last_end = self.eat_gt();
                        depth -= 1;
                    }
                    _ => {
                        last_end = t.end;
                        self.bump();
                    }
                }
            }
        }
        self.blank(start, last_end);
        Ok(())
    }

    // ---- type consumption primitives ----

    /// Consume a type starting at the cursor, stopping at a depth-0 token in
    /// `stops` (and, if `asi`, at a newline). Returns the byte offset of the
    /// type's end (for blanking `[annotation_start, end]`).
    fn skip_type(&mut self, stops: &[Pk], asi: bool) -> Result<usize, String> {
        let mut depth = 0i32;
        let mut last_end = self.cur().start; // empty until we consume something
        let mut consumed_any = false;
        loop {
            let t = self.cur();
            if depth == 0 {
                if let Tk::Punct(pk) = t.kind
                    && stops.contains(&pk)
                {
                    break;
                }
                if asi && consumed_any && t.nl_before {
                    break;
                }
            }
            match t.kind {
                Tk::Eof => break,
                Tk::Punct(Pk::LParen)
                | Tk::Punct(Pk::LBracket)
                | Tk::Punct(Pk::LBrace)
                | Tk::Punct(Pk::Lt) => {
                    depth += 1;
                    last_end = t.end;
                    self.bump();
                }
                Tk::Punct(Pk::Shl) => {
                    depth += 2;
                    last_end = t.end;
                    self.bump();
                }
                Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                    last_end = t.end;
                    self.bump();
                }
                Tk::Punct(pk) if is_gt_family(pk) => {
                    if depth == 0 {
                        break;
                    }
                    last_end = self.eat_gt();
                    depth -= 1;
                }
                _ => {
                    last_end = t.end;
                    self.bump();
                }
            }
            consumed_any = true;
        }
        if !consumed_any {
            return Err("empty type annotation".to_string());
        }
        Ok(last_end)
    }

    /// Blank a balanced `<...>` span at the cursor (type params / type args).
    /// Returns the end byte offset. The cursor must be at `<`.
    fn skip_balanced_angle(&mut self) -> Result<usize, String> {
        let start = self.cur().start;
        let mut ang = 0i32;
        let mut pbb = 0i32;
        loop {
            let t = self.cur();
            match t.kind {
                Tk::Eof => return Err("unterminated `<...>`".to_string()),
                Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::LBrace) => {
                    pbb += 1;
                    self.bump();
                }
                Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => {
                    if pbb == 0 {
                        return Err("unbalanced `)` in `<...>`".to_string());
                    }
                    pbb -= 1;
                    self.bump();
                }
                Tk::Punct(Pk::Lt) if pbb == 0 => {
                    ang += 1;
                    self.bump();
                }
                Tk::Punct(Pk::Shl) if pbb == 0 => {
                    ang += 2;
                    self.bump();
                }
                Tk::Punct(pk) if pbb == 0 && is_gt_family(pk) => {
                    let end = self.eat_gt();
                    ang -= 1;
                    if ang == 0 {
                        self.blank(start, end);
                        return Ok(end);
                    }
                }
                _ => self.bump(),
            }
        }
    }

    /// Balanced `{...}` skip at the cursor; returns end byte offset. Cursor at `{`.
    fn skip_balanced_braces(&mut self) -> Result<usize, String> {
        let mut depth = 0i32;
        loop {
            let t = self.cur();
            match t.kind {
                Tk::Eof => return Err("unterminated `{...}`".to_string()),
                Tk::Punct(Pk::LBrace) => {
                    depth += 1;
                    self.bump();
                }
                Tk::Punct(Pk::RBrace) => {
                    depth -= 1;
                    self.bump();
                    if depth == 0 {
                        return Ok(t.end);
                    }
                }
                _ => self.bump(),
            }
        }
    }

    // ---- pure (non-mutating) lookahead scanners ----

    /// Index of the `)` matching the `(` at token index `from`.
    fn scan_matching_paren(&self, from: usize) -> usize {
        let mut depth = 0i32;
        let mut i = from;
        while i < self.toks.len() {
            match self.toks[i].kind {
                Tk::Punct(Pk::LParen) => depth += 1,
                Tk::Punct(Pk::RParen) => {
                    depth -= 1;
                    if depth == 0 {
                        return i;
                    }
                }
                Tk::Eof => return i,
                _ => {}
            }
            i += 1;
        }
        self.toks.len() - 1
    }

    /// Index of the first depth-0 token in `stops`, scanning a type from `from`.
    fn scan_type_end(&self, from: usize, stops: &[Pk]) -> usize {
        let mut depth = 0i32;
        let mut i = from;
        while i < self.toks.len() {
            let t = self.toks[i];
            if depth == 0
                && let Tk::Punct(pk) = t.kind
                && stops.contains(&pk)
            {
                return i;
            }
            match t.kind {
                Tk::Eof => return i,
                Tk::Punct(Pk::LParen)
                | Tk::Punct(Pk::LBracket)
                | Tk::Punct(Pk::LBrace)
                | Tk::Punct(Pk::Lt) => depth += 1,
                Tk::Punct(Pk::Shl) => depth += 2,
                Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => {
                    depth -= 1
                }
                Tk::Punct(pk) if is_gt_family(pk) => {
                    depth -= gt_count(pk);
                }
                _ => {}
            }
            i += 1;
        }
        self.toks.len() - 1
    }

    /// Purely scan a `<...>` type-argument list at token index `from` (a `<`).
    /// Returns (index just past the closing `>`, byte offset of that close) iff
    /// every token is type-shaped and the angles balance exactly at a token
    /// boundary. Otherwise None (treat `<` as an operator).
    fn scan_type_args_span(&self, from: usize) -> Option<(usize, usize)> {
        let mut ang = 0i32;
        let mut pbb = 0i32;
        let mut i = from;
        while i < self.toks.len() {
            let t = self.toks[i];
            match t.kind {
                Tk::Eof => return None,
                Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::LBrace) => pbb += 1,
                Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => {
                    if pbb == 0 {
                        return None;
                    }
                    pbb -= 1;
                }
                Tk::Punct(Pk::Lt) if pbb == 0 => ang += 1,
                Tk::Punct(Pk::Shl) if pbb == 0 => ang += 2,
                Tk::Punct(pk) if pbb == 0 && is_gt_family(pk) => {
                    let c = gt_count(pk);
                    ang -= c;
                    if ang < 0 {
                        return None; // over-closes mid-token
                    }
                    if ang == 0 {
                        return Some((i + 1, t.end));
                    }
                }
                _ => {
                    if !self.is_type_shaped(t) {
                        return None;
                    }
                }
            }
            i += 1;
        }
        None
    }

    /// Whether a token may appear inside a type-argument list (used to keep the
    /// `<`-disambiguation from swallowing real comparison/arithmetic).
    fn is_type_shaped(&self, t: Token) -> bool {
        match t.kind {
            Tk::Ident | Tk::Num | Tk::Str => true,
            Tk::Punct(pk) => matches!(
                pk,
                Pk::Dot
                    | Pk::Comma
                    | Pk::Lt
                    | Pk::Shl
                    | Pk::Gt
                    | Pk::Shr
                    | Pk::UShr
                    | Pk::Ge
                    | Pk::ShrEq
                    | Pk::UShrEq
                    | Pk::LBracket
                    | Pk::RBracket
                    | Pk::LParen
                    | Pk::RParen
                    | Pk::LBrace
                    | Pk::RBrace
                    | Pk::Pipe
                    | Pk::Amp
                    | Pk::Colon
                    | Pk::Question
                    | Pk::Arrow
                    | Pk::Ellipsis
                    | Pk::Eq
                    | Pk::Semi
            ),
            _ => false,
        }
    }
}

/// Number of leading `>` in a gt-family punctuator.
fn gt_count(pk: Pk) -> i32 {
    match pk {
        Pk::Gt | Pk::Ge => 1,
        Pk::Shr | Pk::ShrEq => 2,
        Pk::UShr | Pk::UShrEq => 3,
        _ => 0,
    }
}
