// trust-ts-strip: the non-erasable transform tier.
//
// A source-to-source lowering that ERASES types AND lowers `enum` and
// `namespace`/`module` declarations to the runtime JavaScript the TypeScript
// transpilers (Node `--experimental-transform-types`, Bun) emit — matching
// their OBSERVABLE runtime behaviour (object shape, forward/reverse enum
// mappings, exported-vs-local namespace members), not their byte output.
//
// STRATEGY. A depth-0 token walk (`transform_scope`) rewrites enum/namespace
// declarations into equivalent JavaScript, keeping every other statement
// verbatim; the emitted JavaScript still carries TypeScript type syntax inside
// kept member bodies, so a single final pass through the PROVEN eraser
// (`crate::strip`) elides all remaining types. Enum bodies are fully generated
// (no residual types); namespace member bodies are kept as text and cleaned by
// the final pass.
//
// SOUNDNESS. The walk only lowers a construct whose runtime it can reproduce
// EXACTLY; everything else is a `Refused` for the whole file. Two backstops
// make a wrong lowering non-producible: (1) any enum/namespace the walk does
// NOT lower (e.g. nested inside a function body) survives into the final eraser
// pass, which REFUSES it — a miss can only cost coverage, never soundness; and
// (2) parameter properties, decorators, import-/export-equals and other
// non-erasable residue in kept bodies are refused by that same final pass.
// Refusing is always sound; a wrong transform is not producible.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::StripOutcome;
use crate::lexer::{self, Pk, Tk, Token};

/// The public entry: lower enums/namespaces, then erase types via the eraser.
pub(crate) fn transform(src: &str) -> StripOutcome {
    let combined = match transform_scope(src, &Scope::Top) {
        Ok(s) => s,
        Err(reason) => return StripOutcome::Refused(reason),
    };
    // Final pass: the proven eraser elides every remaining type position and
    // refuses any construct the structural walk left non-erasable (including an
    // enum/namespace it could not confidently lower). Its refusal is our
    // refusal — fail-closed.
    crate::strip(&combined)
}

/// The lowering scope for a walked region.
enum Scope<'a> {
    /// The module top level: enum/namespace lower with `var` and no parent
    /// attachment; a top-level `export` marker on them is dropped (unobservable
    /// with no importer). Every non-enum/namespace statement — including
    /// ordinary top-level `export` — is kept verbatim for the eraser +
    /// downstream module-lowering.
    Top,
    /// Inside a namespace object named `.0`: enum/namespace lower with `let` and
    /// (when exported) attach to the object; `export const|function|class`
    /// members attach their binding to the object; non-exported members stay
    /// local.
    Namespace(&'a str),
}

/// How an enum/namespace binding is introduced and (optionally) attached.
#[derive(Clone, Copy)]
enum Nesting<'a> {
    /// Top-level (`var NAME;` … `(NAME || (NAME = {}))`).
    TopVar,
    /// Nested but not exported (`let NAME;` … `(NAME || (NAME = {}))`).
    LocalLet,
    /// Nested and exported from parent object `.0`
    /// (`let NAME;` … `(NAME = PARENT.NAME || (PARENT.NAME = {}))`).
    ExportAttach(&'a str),
}

type R<T> = Result<T, String>;

// ---------------------------------------------------------------------------
// Token helpers
// ---------------------------------------------------------------------------

fn text(src: &str, t: Token) -> &str {
    &src[t.start..t.end]
}
fn is_kw(src: &str, t: Token, w: &str) -> bool {
    matches!(t.kind, Tk::Ident) && text(src, t) == w
}
fn is_ident(t: Token) -> bool {
    matches!(t.kind, Tk::Ident)
}
fn is_p(t: Token, pk: Pk) -> bool {
    t.kind == Tk::Punct(pk)
}

/// Index of the `}` matching the `{` at token index `open`.
fn match_brace(toks: &[Token], open: usize) -> Option<usize> {
    let mut d = 0i32;
    for (i, t) in toks.iter().enumerate().skip(open) {
        match t.kind {
            Tk::Punct(Pk::LBrace) => d += 1,
            Tk::Punct(Pk::RBrace) => {
                d -= 1;
                if d == 0 {
                    return Some(i);
                }
            }
            Tk::Eof => return None,
            _ => {}
        }
    }
    None
}

/// Index of the `)` matching the `(` at token index `open`.
fn match_paren(toks: &[Token], open: usize) -> Option<usize> {
    let mut d = 0i32;
    for (i, t) in toks.iter().enumerate().skip(open) {
        match t.kind {
            Tk::Punct(Pk::LParen) => d += 1,
            Tk::Punct(Pk::RParen) => {
                d -= 1;
                if d == 0 {
                    return Some(i);
                }
            }
            Tk::Eof => return None,
            _ => {}
        }
    }
    None
}

/// The first `{` at paren/bracket-depth 0 from `from` (function/class body).
fn body_brace_after(toks: &[Token], from: usize) -> Option<usize> {
    let mut d = 0i32;
    for (i, t) in toks.iter().enumerate().skip(from) {
        match t.kind {
            Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) => d += 1,
            Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => d -= 1,
            Tk::Punct(Pk::LBrace) if d == 0 => return Some(i),
            Tk::Eof => return None,
            _ => {}
        }
    }
    None
}

/// The first depth-0 `;` from `from` (declaration terminator). `stop_at` bounds
/// the search (exclusive). Depth counts (), [], {}.
fn semi_after(toks: &[Token], from: usize, stop_at: usize) -> Option<usize> {
    let mut d = 0i32;
    let mut i = from;
    while i < stop_at {
        match toks[i].kind {
            Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::LBrace) => d += 1,
            Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => {
                if d == 0 {
                    return None;
                }
                d -= 1;
            }
            Tk::Punct(Pk::Semi) if d == 0 => return Some(i),
            Tk::Eof => return None,
            _ => {}
        }
        i += 1;
    }
    None
}

// ---------------------------------------------------------------------------
// The scope walker
// ---------------------------------------------------------------------------

/// Walk `src` in `scope`, lowering depth-0 enum/namespace declarations and
/// keeping everything else verbatim. Returns JavaScript that still carries
/// TypeScript types in kept member bodies (elided by the final eraser pass).
fn transform_scope(src: &str, scope: &Scope) -> R<String> {
    let toks = lexer::lex(src).map_err(|e| format!("lex: {e}"))?;
    let mut out = String::new();
    let mut copied = 0usize; // next source byte to flush verbatim
    let mut i = 0usize;
    let mut depth = 0i32;
    let mut prev: Option<Tk> = None;

    while i < toks.len() {
        let t = toks[i];
        if matches!(t.kind, Tk::Eof) {
            break;
        }
        let stmt_pos =
            depth == 0 && !matches!(prev, Some(Tk::Punct(Pk::Dot)) | Some(Tk::Punct(Pk::QDot)));

        if stmt_pos {
            // Ambient `declare …` — emits no runtime code; drop the whole
            // statement (block form to its matching `}`, else to `;`).
            if is_kw(src, t, "declare") {
                let end_i = declare_end(&toks, i)?;
                out.push_str(&src[copied..t.start]);
                copied = toks[end_i].end;
                i = end_i + 1;
                prev = Some(Tk::Punct(Pk::Semi));
                continue;
            }
            // `export …`
            if is_kw(src, t, "export") {
                match handle_export(src, &toks, i, scope, &mut out, &mut copied)? {
                    Some(next_i) => {
                        i = next_i;
                        prev = Some(Tk::Punct(Pk::Semi));
                        continue;
                    }
                    None => { /* not a lowered form — copy `export` verbatim */ }
                }
            } else if let Some(sp) = local_special(src, &toks, i, scope)? {
                out.push_str(&src[copied..toks[sp.start_i].start]);
                out.push_str(&sp.lowered);
                copied = toks[sp.end_i].end;
                i = sp.end_i + 1;
                prev = Some(Tk::Punct(Pk::Semi));
                continue;
            } else if let Some(cstart) = class_start_after(src, &toks, i) {
                // A non-exported class: lower parameter properties if any. A
                // class with none (`None`) falls through to the verbatim copy.
                if let Some((close, txt)) = rewrite_class(src, &toks, cstart)? {
                    out.push_str(&src[copied..t.start]);
                    out.push_str(&txt);
                    copied = toks[close].end;
                    i = close + 1;
                    prev = Some(Tk::Punct(Pk::Semi));
                    continue;
                }
            }
        }

        match t.kind {
            Tk::Punct(Pk::LBrace) | Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) => depth += 1,
            Tk::Punct(Pk::RBrace) | Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => depth -= 1,
            _ => {}
        }
        prev = Some(t.kind);
        i += 1;
    }
    out.push_str(&src[copied..]);
    Ok(out)
}

/// End token index of an ambient `declare …` statement at index `i`.
fn declare_end(toks: &[Token], i: usize) -> R<usize> {
    // Block forms (namespace/module/global/class/enum/interface/abstract) end
    // at their first depth-0 `{…}`; simple forms end at `;`.
    if let Some(open) = block_before_semi(toks, i + 1) {
        return match_brace(toks, open).ok_or_else(|| "unterminated declare block".to_string());
    }
    match semi_after(toks, i + 1, toks.len()) {
        Some(s) => Ok(s),
        None => Err("unterminated declare statement".to_string()),
    }
}

/// A depth-0 `{` reached before any depth-0 `;` from `from` (block-form probe).
fn block_before_semi(toks: &[Token], from: usize) -> Option<usize> {
    let mut d = 0i32;
    let mut i = from;
    while i < toks.len() {
        match toks[i].kind {
            Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) => d += 1,
            Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => d -= 1,
            Tk::Punct(Pk::LBrace) if d == 0 => return Some(i),
            Tk::Punct(Pk::Semi) if d == 0 => return None,
            Tk::Eof => return None,
            _ => {}
        }
        i += 1;
    }
    None
}

// ---------------------------------------------------------------------------
// Special (enum/namespace) recognition + lowering
// ---------------------------------------------------------------------------

struct Lowered {
    start_i: usize,
    end_i: usize,
    lowered: String,
}

/// A non-exported enum/namespace at token `i` (statement position), if any.
fn local_special(src: &str, toks: &[Token], i: usize, scope: &Scope) -> R<Option<Lowered>> {
    let nest = match scope {
        Scope::Top => Nesting::TopVar,
        Scope::Namespace(_) => Nesting::LocalLet,
    };
    // `enum NAME {` / `const enum NAME {`
    if is_kw(src, toks[i], "enum")
        && let Some((name_i, open, close)) = enum_shape(toks, i)
    {
        let js = lower_enum(src, toks, name_i, open, close, nest)?;
        return Ok(Some(Lowered { start_i: i, end_i: close, lowered: js }));
    }
    if is_kw(src, toks[i], "const")
        && is_kw(src, toks[i + 1], "enum")
        && let Some((name_i, open, close)) = enum_shape(toks, i + 1)
    {
        let js = lower_enum(src, toks, name_i, open, close, nest)?;
        return Ok(Some(Lowered { start_i: i, end_i: close, lowered: js }));
    }
    // `namespace NAME {` — the `module` keyword is refused (Node's transpiler
    // rejects it: "`module` keyword is not supported. Use `namespace`").
    if is_kw(src, toks[i], "namespace")
        && let Some((name_i, open, close)) = namespace_shape(toks, i)?
    {
        let js = lower_namespace(src, toks, name_i, open, close, nest)?;
        return Ok(Some(Lowered { start_i: i, end_i: close, lowered: js }));
    }
    if is_kw(src, toks[i], "module") && namespace_shape(toks, i)?.is_some() {
        return Err("`module` declaration keyword (refused: use `namespace`)".to_string());
    }
    Ok(None)
}

/// `enum NAME { … }` shape from the `enum` keyword at `kw`.
fn enum_shape(toks: &[Token], kw: usize) -> Option<(usize, usize, usize)> {
    let name_i = kw + 1;
    if !is_ident(toks[name_i]) {
        return None;
    }
    if !is_p(toks[name_i + 1], Pk::LBrace) {
        return None;
    }
    let open = name_i + 1;
    let close = match_brace(toks, open)?;
    Some((name_i, open, close))
}

/// `namespace NAME { … }` shape (identifier name only; dotted/string refused).
fn namespace_shape(toks: &[Token], kw: usize) -> R<Option<(usize, usize, usize)>> {
    let name_i = kw + 1;
    if !is_ident(toks[name_i]) {
        return Ok(None);
    }
    if is_p(toks[name_i + 1], Pk::Dot) {
        return Err("dotted namespace (`namespace A.B`) not supported".to_string());
    }
    if !is_p(toks[name_i + 1], Pk::LBrace) {
        return Ok(None);
    }
    let open = name_i + 1;
    let close = match_brace(toks, open).ok_or_else(|| "unterminated namespace body".to_string())?;
    Ok(Some((name_i, open, close)))
}

/// Emit the `var/let NAME; (function (NAME) { … })(…);` wrapper.
fn wrap_iife(name: &str, body: &str, nest: Nesting) -> String {
    let (decl, arg) = match nest {
        Nesting::TopVar => ("var".to_string(), format!("{name} || ({name} = {{}})")),
        Nesting::LocalLet => ("let".to_string(), format!("{name} || ({name} = {{}})")),
        Nesting::ExportAttach(parent) => {
            ("let".to_string(), format!("{name} = {parent}.{name} || ({parent}.{name} = {{}})"))
        }
    };
    format!("{decl} {name};\n(function ({name}) {{\n{body}}})({arg});\n")
}

/// Lower an enum declaration to its runtime IIFE.
fn lower_enum(
    src: &str,
    toks: &[Token],
    name_i: usize,
    open: usize,
    close: usize,
    nest: Nesting,
) -> R<String> {
    let name = text(src, toks[name_i]);
    let members = parse_enum_members(src, toks, open + 1, close)?;
    let mut body = String::new();
    let mut next_auto: Option<f64> = Some(0.0);
    for m in &members {
        let key_lit = &m.key_lit; // e.g. "\"A\"" or "\"a-b\""
        match &m.init {
            EnumInit::Num(text_span) => {
                body.push_str(&format!(
                    "    {name}[{name}[{key_lit}] = {text_span}] = {key_lit};\n"
                ));
                next_auto = m.num_value.map(|v| v + 1.0);
            }
            EnumInit::Str(text_span) => {
                body.push_str(&format!("    {name}[{key_lit}] = {text_span};\n"));
                next_auto = None; // a string member breaks numeric auto-increment
            }
            EnumInit::Auto => {
                let v = next_auto
                    .ok_or_else(|| format!("enum member `{key_lit}` needs an initializer"))?;
                let lit = format_int_value(v)?;
                body.push_str(&format!("    {name}[{name}[{key_lit}] = {lit}] = {key_lit};\n"));
                next_auto = Some(v + 1.0);
            }
        }
    }
    Ok(wrap_iife(name, &body, nest))
}

/// Lower a namespace declaration to its runtime IIFE (body transformed).
fn lower_namespace(
    src: &str,
    toks: &[Token],
    name_i: usize,
    open: usize,
    close: usize,
    nest: Nesting,
) -> R<String> {
    let name = text(src, toks[name_i]);
    // The body substring between the braces is re-walked in Namespace scope.
    let body_src = &src[toks[open].end..toks[close].start];
    let body_out = transform_scope(body_src, &Scope::Namespace(name))?;
    // Indent the body one level for readability (semantically inert).
    let mut indented = String::new();
    for line in body_out.lines() {
        if line.is_empty() {
            indented.push('\n');
        } else {
            indented.push_str("    ");
            indented.push_str(line);
            indented.push('\n');
        }
    }
    Ok(wrap_iife(name, &indented, nest))
}

// ---------------------------------------------------------------------------
// Enum member parsing
// ---------------------------------------------------------------------------

enum EnumInit {
    Auto,
    Num(String),
    Str(String),
}

struct EnumMember {
    key_lit: String,
    init: EnumInit,
    num_value: Option<f64>,
}

/// Parse enum members in tokens `[from, close)`. Members are comma-separated;
/// each is `KEY` or `KEY = INIT`, KEY an identifier or string literal, INIT a
/// numeric literal (optionally signed) or a string literal. Anything else
/// (computed/non-constant) refuses.
fn parse_enum_members(src: &str, toks: &[Token], from: usize, close: usize) -> R<Vec<EnumMember>> {
    let mut out = Vec::new();
    let mut i = from;
    while i < close {
        // Skip separators / trailing comma.
        if is_p(toks[i], Pk::Comma) {
            i += 1;
            continue;
        }
        // Key.
        let key_lit = match toks[i].kind {
            Tk::Ident => {
                let name = text(src, toks[i]);
                format!("\"{name}\"")
            }
            Tk::Str => text(src, toks[i]).to_string(),
            _ => {
                return Err(format!(
                    "enum member key must be an identifier or string (byte {})",
                    toks[i].start
                ));
            }
        };
        i += 1;
        // Optional initializer.
        let (init, num_value) = if is_p(toks[i], Pk::Eq) {
            i += 1;
            let init_start = i;
            // Member spans up to the next depth-0 comma or the closing brace.
            let init_end = enum_member_end(toks, i, close);
            let parsed = classify_enum_init(src, toks, init_start, init_end)?;
            i = init_end;
            parsed
        } else {
            (EnumInit::Auto, None)
        };
        out.push(EnumMember { key_lit, init, num_value });
    }
    Ok(out)
}

/// Token index of a member's end: the next depth-0 comma, or `close`.
fn enum_member_end(toks: &[Token], from: usize, close: usize) -> usize {
    let mut d = 0i32;
    let mut i = from;
    while i < close {
        match toks[i].kind {
            Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::LBrace) => d += 1,
            Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => d -= 1,
            Tk::Punct(Pk::Comma) if d == 0 => return i,
            _ => {}
        }
        i += 1;
    }
    close
}

/// Classify an enum initializer in `[from, end)` as a numeric literal
/// (optionally signed) or a single string literal, else refuse.
fn classify_enum_init(
    src: &str,
    toks: &[Token],
    from: usize,
    end: usize,
) -> R<(EnumInit, Option<f64>)> {
    let n = end - from;
    if n == 0 {
        return Err("empty enum initializer".to_string());
    }
    // A lone string literal → string member (forward-only, no reverse map).
    if n == 1 && matches!(toks[from].kind, Tk::Str) {
        return Ok((EnumInit::Str(text(src, toks[from]).to_string()), None));
    }
    // A numeric literal, optionally with a single leading unary +/-.
    let (sign, num_i) = if n == 2 && (is_p(toks[from], Pk::Minus) || is_p(toks[from], Pk::Plus)) {
        let s = if is_p(toks[from], Pk::Minus) { -1.0 } else { 1.0 };
        (s, from + 1)
    } else if n == 1 {
        (1.0, from)
    } else {
        return Err("computed / non-constant enum member (refused)".to_string());
    };
    if !matches!(toks[num_i].kind, Tk::Num) {
        return Err("computed / non-constant enum member (refused)".to_string());
    }
    let raw = text(src, toks[num_i]);
    let value =
        parse_js_number(raw).ok_or_else(|| format!("unparseable numeric enum member `{raw}`"))?;
    let signed = sign * value;
    // Emit the verbatim source span so the engine computes the exact value.
    let span = &src[toks[from].start..toks[end - 1].end];
    Ok((EnumInit::Num(span.to_string()), Some(signed)))
}

/// Parse a JavaScript numeric literal to `f64` (dec/hex/oct/bin/float/exp,
/// numeric separators). BigInt (`n` suffix) is rejected.
fn parse_js_number(raw: &str) -> Option<f64> {
    if raw.ends_with('n') {
        return None; // BigInt not permitted in enums
    }
    let cleaned: String = raw.chars().filter(|c| *c != '_').collect();
    let lower = cleaned.to_ascii_lowercase();
    let parse_radix = |body: &str, radix: u32| -> Option<f64> {
        if body.is_empty() {
            return None;
        }
        u128::from_str_radix(body, radix).ok().map(|v| v as f64)
    };
    if let Some(rest) = lower.strip_prefix("0x") {
        return parse_radix(rest, 16);
    }
    if let Some(rest) = lower.strip_prefix("0o") {
        return parse_radix(rest, 8);
    }
    if let Some(rest) = lower.strip_prefix("0b") {
        return parse_radix(rest, 2);
    }
    cleaned.parse::<f64>().ok()
}

/// Format an integer-valued `f64` as a JavaScript number literal for an
/// auto-increment member. Fractional auto values refuse (rare, keeps emit exact).
fn format_int_value(v: f64) -> R<String> {
    if v.is_finite() && v.fract() == 0.0 && v.abs() < 9_007_199_254_740_992.0 {
        Ok(format!("{}", v as i64))
    } else {
        Err(format!("non-integer enum auto-increment value {v} (refused)"))
    }
}

// ---------------------------------------------------------------------------
// export handling (namespace members + top-level enum/namespace)
// ---------------------------------------------------------------------------

/// Handle an `export …` at token `i` (statement position, depth 0). Emits to
/// `out`, advancing `copied`. Returns `Some(next_i)` when the export was lowered
/// / consumed, `None` when it must be copied verbatim by the caller, or `Err`
/// on a refused form.
fn handle_export(
    src: &str,
    toks: &[Token],
    i: usize,
    scope: &Scope,
    out: &mut String,
    copied: &mut usize,
) -> R<Option<usize>> {
    let j = i + 1; // token after `export`
    let t1 = toks[j];

    // `export declare …` — ambient, emits nothing.
    if is_kw(src, t1, "declare") {
        let end_i = declare_end(toks, j)?;
        out.push_str(&src[*copied..toks[i].start]);
        *copied = toks[end_i].end;
        return Ok(Some(end_i + 1));
    }

    // `export enum` / `export const enum`
    let enum_kw = if is_kw(src, t1, "enum") {
        Some(j)
    } else if is_kw(src, t1, "const") && is_kw(src, toks[j + 1], "enum") {
        Some(j + 1)
    } else {
        None
    };
    if let Some(kw) = enum_kw
        && let Some((name_i, open, close)) = enum_shape(toks, kw)
    {
        let nest = export_nesting(scope);
        let js = lower_enum(src, toks, name_i, open, close, nest)?;
        out.push_str(&src[*copied..toks[i].start]);
        out.push_str(&js);
        *copied = toks[close].end;
        return Ok(Some(close + 1));
    }

    // `export namespace` (the `module` keyword is refused, matching Node)
    if is_kw(src, t1, "namespace")
        && let Some((name_i, open, close)) = namespace_shape(toks, j)?
    {
        let nest = export_nesting(scope);
        let js = lower_namespace(src, toks, name_i, open, close, nest)?;
        out.push_str(&src[*copied..toks[i].start]);
        out.push_str(&js);
        *copied = toks[close].end;
        return Ok(Some(close + 1));
    }
    if is_kw(src, t1, "module") && namespace_shape(toks, j)?.is_some() {
        return Err("`export module` declaration (refused: use `namespace`)".to_string());
    }

    // `export [abstract] class` at the TOP level with parameter properties —
    // rewrite them, keeping `export` (module-lowering drops it). A class with no
    // parameter properties stays verbatim. (Namespace-scope classes attach to
    // the object and are handled in `handle_namespace_export`.)
    if let (Scope::Top, Some(cstart)) = (scope, class_start_after(src, toks, j)) {
        return match rewrite_class(src, toks, cstart)? {
            Some((close, txt)) => {
                out.push_str(&src[*copied..toks[i].start]);
                out.push_str("export ");
                out.push_str(&txt);
                *copied = toks[close].end;
                Ok(Some(close + 1))
            }
            None => Ok(None), // no parameter properties — copy `export class …` verbatim
        };
    }

    // Remaining forms differ by scope.
    match scope {
        // At the top level everything else stays verbatim: the eraser elides
        // type-only exports and module-lowering drops the `export` record.
        Scope::Top => Ok(None),
        Scope::Namespace(obj) => handle_namespace_export(src, toks, i, j, obj, out, copied),
    }
}

/// The nesting an exported enum/namespace uses: top-level drops the export;
/// inside a namespace it attaches to the object.
fn export_nesting<'a>(scope: &'a Scope) -> Nesting<'a> {
    match scope {
        Scope::Top => Nesting::TopVar,
        Scope::Namespace(obj) => Nesting::ExportAttach(obj),
    }
}

/// Handle a namespace-body `export` of a value binding (const/function/class),
/// a re-export list, or a type-only export. `i` is `export`, `j` is the token
/// after it.
fn handle_namespace_export(
    src: &str,
    toks: &[Token],
    i: usize,
    j: usize,
    obj: &str,
    out: &mut String,
    copied: &mut usize,
) -> R<Option<usize>> {
    let t1 = toks[j];

    // `export const …;` — keep the declaration (types elided later), attach
    // each binding to the namespace object.
    if is_kw(src, t1, "const") {
        let semi = semi_after(toks, j + 1, toks.len())
            .ok_or_else(|| "export const without terminating `;` (refused)".to_string())?;
        let names = declarator_names(src, toks, j + 1, semi)?;
        if names.is_empty() {
            return Err("export const with no simple binding (refused)".to_string());
        }
        out.push_str(&src[*copied..toks[i].start]);
        out.push_str(&src[toks[j].start..toks[semi].end]); // `const … ;` verbatim
        for name in &names {
            out.push_str(&format!("\n{obj}.{name} = {name};"));
        }
        *copied = toks[semi].end;
        return Ok(Some(semi + 1));
    }

    // `export let|var` — a reassignable binding would drift from the object
    // property; refuse (sound).
    if is_kw(src, t1, "let") || is_kw(src, t1, "var") {
        return Err("exported `let`/`var` namespace member (refused: reassignment)".to_string());
    }

    // `export [async] function [*] NAME (…) …`
    let fn_kw = if is_kw(src, t1, "function") {
        Some(j)
    } else if is_kw(src, t1, "async") && is_kw(src, toks[j + 1], "function") {
        Some(j + 1)
    } else {
        None
    };
    if let Some(fkw) = fn_kw {
        let mut k = fkw + 1;
        if is_p(toks[k], Pk::Star) {
            k += 1; // generator
        }
        if !is_ident(toks[k]) {
            return Err("exported function without a name (refused)".to_string());
        }
        let name = text(src, toks[k]).to_string();
        let lparen = k + 1;
        if !is_p(toks[lparen], Pk::LParen) {
            return Err("malformed exported function (refused)".to_string());
        }
        let rparen = match_paren(toks, lparen)
            .ok_or_else(|| "unterminated function parameter list".to_string())?;
        // Guard an object-literal return type (ambiguous body brace) → refuse.
        if is_p(toks[rparen + 1], Pk::Colon) && is_p(toks[rparen + 2], Pk::LBrace) {
            return Err("exported function with object return type (refused)".to_string());
        }
        let body_open = body_brace_after(toks, rparen + 1)
            .ok_or_else(|| "exported function without a body (refused)".to_string())?;
        let body_close =
            match_brace(toks, body_open).ok_or_else(|| "unterminated function body".to_string())?;
        out.push_str(&src[*copied..toks[i].start]);
        out.push_str(&src[toks[j].start..toks[body_close].end]); // decl minus `export`
        out.push_str(&format!("\n{obj}.{name} = {name};"));
        *copied = toks[body_close].end;
        return Ok(Some(body_close + 1));
    }

    // `export [abstract] class NAME …` — parameter properties are lowered
    // (rewrite_class), else the class is kept verbatim; either way the binding
    // attaches to the namespace object.
    if let Some(cstart) = class_start_after(src, toks, j) {
        let name = class_name(src, toks, cstart)
            .ok_or_else(|| "exported class without a name (refused)".to_string())?
            .to_string();
        let (body_close, class_text) = match rewrite_class(src, toks, cstart)? {
            Some((close, txt)) => (close, txt),
            None => {
                let body_open = body_brace_after(toks, cstart + 1)
                    .ok_or_else(|| "exported class without a body (refused)".to_string())?;
                let close = match_brace(toks, body_open)
                    .ok_or_else(|| "unterminated class body".to_string())?;
                (close, src[toks[j].start..toks[close].end].to_string())
            }
        };
        out.push_str(&src[*copied..toks[i].start]);
        out.push_str(&class_text); // decl minus `export`
        out.push_str(&format!("\n{obj}.{name} = {name};"));
        *copied = toks[body_close].end;
        return Ok(Some(body_close + 1));
    }

    // `export type …` / `export interface …` — type-only: keep without the
    // `export` marker so the final eraser elides it (an `export` inside the IIFE
    // would be a syntax error).
    if is_kw(src, t1, "type") || is_kw(src, t1, "interface") {
        out.push_str(&src[*copied..toks[i].start]);
        // Emit from the `type`/`interface` keyword; the eraser removes the rest.
        // Bound: block form (interface) → matching `}`, alias (`type`) → `;`.
        let end_i = if is_kw(src, t1, "interface") {
            let open = body_brace_after(toks, j + 1)
                .ok_or_else(|| "unterminated interface (refused)".to_string())?;
            match_brace(toks, open).ok_or_else(|| "unterminated interface".to_string())?
        } else {
            semi_after(toks, j + 1, toks.len())
                .ok_or_else(|| "export type without `;` (refused)".to_string())?
        };
        out.push_str(&src[toks[j].start..toks[end_i].end]);
        *copied = toks[end_i].end;
        return Ok(Some(end_i + 1));
    }

    // `export { … }`, `export default`, `export *`, `import …` — ESM-style
    // module declarations are NOT permitted inside a namespace (both Node's
    // transpiler and Bun reject them). Refuse (sound).
    if is_p(t1, Pk::LBrace) || is_kw(src, t1, "default") || is_p(t1, Pk::Star) {
        return Err("ESM-style export inside a namespace (refused: not permitted)".to_string());
    }

    Err(format!("unsupported namespace export at byte {} (refused)", toks[j].start))
}

/// Simple binding identifiers of a `const` declarator list in `[from, semi)`.
/// A destructuring pattern refuses.
fn declarator_names(src: &str, toks: &[Token], from: usize, semi: usize) -> R<Vec<String>> {
    let mut names = Vec::new();
    let mut i = from;
    let mut depth = 0i32;
    let mut expect_binding = true;
    while i < semi {
        let t = toks[i];
        match t.kind {
            Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::LBrace) => {
                if expect_binding && depth == 0 {
                    return Err("destructuring export binding (refused)".to_string());
                }
                depth += 1;
            }
            Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => depth -= 1,
            Tk::Punct(Pk::Comma) if depth == 0 => expect_binding = true,
            Tk::Ident if expect_binding && depth == 0 => {
                names.push(text(src, t).to_string());
                expect_binding = false;
            }
            _ => {
                if depth == 0 {
                    expect_binding = false;
                }
            }
        }
        i += 1;
    }
    Ok(names)
}

// ---------------------------------------------------------------------------
// Parameter-property class lowering
// ---------------------------------------------------------------------------

/// The start-token index of a class declaration at `j` (`class` or the
/// `abstract` of `abstract class`), else None.
fn class_start_after(src: &str, toks: &[Token], j: usize) -> Option<usize> {
    if is_kw(src, toks[j], "class")
        || (is_kw(src, toks[j], "abstract") && is_kw(src, toks[j + 1], "class"))
    {
        Some(j)
    } else {
        None
    }
}

/// The declared name of a class starting at `start_i` (`class`/`abstract`).
fn class_name<'a>(src: &'a str, toks: &[Token], start_i: usize) -> Option<&'a str> {
    let class_i = if is_kw(src, toks[start_i], "abstract") { start_i + 1 } else { start_i };
    let name_i = class_i + 1;
    if is_ident(toks[name_i]) { Some(text(src, toks[name_i])) } else { None }
}

fn is_gt_fam(pk: Pk) -> bool {
    matches!(pk, Pk::Gt | Pk::Shr | Pk::UShr | Pk::Ge | Pk::ShrEq | Pk::UShrEq)
}
fn gt_cnt(pk: Pk) -> i32 {
    match pk {
        Pk::Gt | Pk::Ge => 1,
        Pk::Shr | Pk::ShrEq => 2,
        Pk::UShr | Pk::UShrEq => 3,
        _ => 0,
    }
}

/// Index just past a balanced `<…>` starting at the `<` token `i`.
fn skip_angle(toks: &[Token], i: usize) -> usize {
    let mut ang = 0i32;
    let mut pbb = 0i32;
    let mut k = i;
    while k < toks.len() {
        match toks[k].kind {
            Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::LBrace) => pbb += 1,
            Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => pbb -= 1,
            Tk::Punct(Pk::Lt) if pbb == 0 => ang += 1,
            Tk::Punct(Pk::Shl) if pbb == 0 => ang += 2,
            Tk::Punct(pk) if pbb == 0 && is_gt_fam(pk) => {
                ang -= gt_cnt(pk);
                if ang <= 0 {
                    return k + 1;
                }
            }
            Tk::Eof => return k,
            _ => {}
        }
        k += 1;
    }
    k
}

/// Whether a class starting at `class_i` (the `class` keyword) is DERIVED — a
/// heritage `extends` (skipping any `<…>` type parameters, and treating an
/// `implements`-only clause as a base class).
fn has_extends(src: &str, toks: &[Token], class_i: usize) -> bool {
    let name_i = class_i + 1;
    let mut k = if is_ident(toks[name_i]) { name_i + 1 } else { class_i + 1 };
    if is_p(toks[k], Pk::Lt) {
        k = skip_angle(toks, k);
    }
    while k < toks.len() {
        let t = toks[k];
        if is_p(t, Pk::LBrace) || is_kw(src, t, "implements") || matches!(t.kind, Tk::Eof) {
            return false;
        }
        if is_kw(src, t, "extends") {
            return true;
        }
        k += 1;
    }
    false
}

/// Whether the class body `(body_open, body_close)` has a field member — a
/// depth-0 `;` or `=` (fields end with `;` or carry an `= init`; methods end at
/// `}`, and parameter defaults sit inside the parens). Conservative: a static
/// field, index signature, or abstract-method `;` also trips it (over-refusal is
/// sound).
fn class_has_field_signal(toks: &[Token], body_open: usize, body_close: usize) -> bool {
    let mut depth = 0i32;
    let mut i = body_open + 1;
    while i < body_close {
        match toks[i].kind {
            Tk::Punct(Pk::LBrace) | Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) => depth += 1,
            Tk::Punct(Pk::RBrace) | Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => depth -= 1,
            Tk::Punct(Pk::Semi) if depth == 0 => return true,
            Tk::Punct(Pk::Eq) if depth == 0 => return true,
            _ => {}
        }
        i += 1;
    }
    false
}

struct Ctor {
    lparen: usize,
    rparen: usize,
    body_open: usize,
    body_close: usize,
}

/// Locate the constructor of a class body `(body_open, body_close)`, if any: an
/// `Ident("constructor")` at member level (class-body depth 0) followed by `(`.
fn find_constructor(
    src: &str,
    toks: &[Token],
    body_open: usize,
    body_close: usize,
) -> Option<Ctor> {
    let mut depth = 0i32;
    let mut i = body_open + 1;
    while i < body_close {
        let t = toks[i];
        if depth == 0 && is_kw(src, t, "constructor") && is_p(toks[i + 1], Pk::LParen) {
            let lparen = i + 1;
            let rparen = match_paren(toks, lparen)?;
            let ctor_body_open = body_brace_after(toks, rparen + 1)?;
            let ctor_body_close = match_brace(toks, ctor_body_open)?;
            return Some(Ctor {
                lparen,
                rparen,
                body_open: ctor_body_open,
                body_close: ctor_body_close,
            });
        }
        match t.kind {
            Tk::Punct(Pk::LBrace) | Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) => depth += 1,
            Tk::Punct(Pk::RBrace) | Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    None
}

fn is_modifier_kw(src: &str, t: Token) -> bool {
    matches!(t.kind, Tk::Ident)
        && matches!(text(src, t), "public" | "private" | "protected" | "readonly" | "override")
}

/// A leading modifier keyword at `i` is a real modifier (not the parameter's own
/// name) iff the next token continues a binding: another identifier (a further
/// modifier or the name) or a destructuring pattern head.
fn param_mod_continues(toks: &[Token], i: usize) -> bool {
    matches!(toks[i + 1].kind, Tk::Ident)
        || is_p(toks[i + 1], Pk::LBrace)
        || is_p(toks[i + 1], Pk::LBracket)
}

/// Token index of the end of a parameter starting at `from`: the next depth-0
/// comma, or `rparen`.
fn param_end(toks: &[Token], from: usize, rparen: usize) -> usize {
    let mut d = 0i32;
    let mut i = from;
    while i < rparen {
        match toks[i].kind {
            Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) | Tk::Punct(Pk::LBrace) => d += 1,
            Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) | Tk::Punct(Pk::RBrace) => d -= 1,
            Tk::Punct(Pk::Comma) if d == 0 => return i,
            _ => {}
        }
        i += 1;
    }
    rparen
}

struct CtorParams {
    /// Parameter-property binding names, in parameter order.
    props: Vec<String>,
    /// Byte ranges of the access-modifier tokens to delete from the param list.
    modifier_spans: Vec<(usize, usize)>,
}

/// Parse a constructor's parameters `(lparen, rparen)`, collecting parameter
/// properties (access-modifier-prefixed params) and the modifier byte ranges to
/// strip. A destructuring or rest parameter property, or a parameter decorator,
/// refuses.
fn parse_ctor_params(src: &str, toks: &[Token], lparen: usize, rparen: usize) -> R<CtorParams> {
    let mut props = Vec::new();
    let mut modifier_spans = Vec::new();
    let mut i = lparen + 1;
    while i < rparen {
        if is_p(toks[i], Pk::Comma) {
            i += 1;
            continue;
        }
        if is_p(toks[i], Pk::At) {
            return Err("parameter decorator (refused)".to_string());
        }
        // Leading access-modifier run.
        let mut mods = Vec::new();
        while is_modifier_kw(src, toks[i]) && param_mod_continues(toks, i) {
            mods.push((toks[i].start, toks[i].end));
            i += 1;
        }
        if !mods.is_empty() {
            // A parameter property: the binding must be a plain identifier.
            if is_p(toks[i], Pk::Ellipsis) {
                return Err("rest parameter property (refused)".to_string());
            }
            if !is_ident(toks[i]) {
                return Err("destructuring parameter property (refused)".to_string());
            }
            props.push(text(src, toks[i]).to_string());
            modifier_spans.extend(mods);
        }
        i = param_end(toks, i, rparen);
    }
    Ok(CtorParams { props, modifier_spans })
}

/// The byte offset after which to inject parameter-property assignments in a
/// DERIVED class: immediately after the sole top-level `super(...)` call
/// (after its terminating `;`, else after `)`). Refuses when the super() point
/// is not uniquely, unconditionally locatable.
fn super_injection_byte(
    src: &str,
    toks: &[Token],
    body_open: usize,
    body_close: usize,
) -> R<usize> {
    let mut depth = 0i32;
    let mut supers: Vec<(usize, i32)> = Vec::new();
    let mut i = body_open + 1;
    while i < body_close {
        let t = toks[i];
        if matches!(t.kind, Tk::Ident) && text(src, t) == "super" && is_p(toks[i + 1], Pk::LParen) {
            supers.push((i, depth));
        }
        match t.kind {
            Tk::Punct(Pk::LBrace) | Tk::Punct(Pk::LParen) | Tk::Punct(Pk::LBracket) => depth += 1,
            Tk::Punct(Pk::RBrace) | Tk::Punct(Pk::RParen) | Tk::Punct(Pk::RBracket) => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    if supers.len() != 1 {
        return Err(
            "derived class with zero or multiple super() calls (refused: uncertain injection point)"
                .to_string(),
        );
    }
    let (sidx, sdepth) = supers[0];
    if sdepth != 0 {
        return Err(
            "super() not at the constructor's top level (refused: uncertain injection point)"
                .to_string(),
        );
    }
    let lp = sidx + 1;
    let rp = match_paren(toks, lp).ok_or_else(|| "unterminated super() call".to_string())?;
    if is_p(toks[rp + 1], Pk::Semi) { Ok(toks[rp + 1].end) } else { Ok(toks[rp].end) }
}

/// Rewrite a class declaration's parameter properties: strip the access
/// modifiers from constructor parameters and inject `this.x = x;` assignments —
/// at the start of the body for a base class, immediately after `super(...)` for
/// a derived class. Returns `(body-close token index, rewritten class text)`
/// when the class HAS parameter properties, `None` when it has none (emit
/// verbatim), or `Err` for an unlowerable shape (uncertain super() point,
/// destructuring/rest parameter property, parameter decorator).
fn rewrite_class(src: &str, toks: &[Token], start_i: usize) -> R<Option<(usize, String)>> {
    let class_i = if is_kw(src, toks[start_i], "abstract") { start_i + 1 } else { start_i };
    let Some(body_open) = body_brace_after(toks, class_i + 1) else {
        return Ok(None); // no locatable body — leave to the eraser
    };
    let Some(body_close) = match_brace(toks, body_open) else {
        return Ok(None);
    };
    let Some(ctor) = find_constructor(src, toks, body_open, body_close) else {
        return Ok(None); // no constructor → no parameter properties
    };
    let parsed = parse_ctor_params(src, toks, ctor.lparen, ctor.rparen)?;
    if parsed.props.is_empty() {
        return Ok(None); // constructor but no parameter properties
    }
    // The engines order parameter-property assignments BEFORE class field
    // initializers, but a kept native field initializes at the START of the body
    // (before the injected assignments) — so a class mixing parameter properties
    // with an explicit field would reorder own-property enumeration. Refuse that
    // combination (sound). A depth-0 `;`/`=` in the body is the field signal
    // (methods end at `}`, param defaults sit inside the parens).
    if class_has_field_signal(toks, body_open, body_close) {
        return Err(
            "parameter property combined with an explicit class field (refused: field/param ordering)"
                .to_string(),
        );
    }
    // Injection point: after super(...) for a derived class, else start of body.
    let inject_at = if has_extends(src, toks, class_i) {
        super_injection_byte(src, toks, ctor.body_open, ctor.body_close)?
    } else {
        toks[ctor.body_open].end
    };
    let mut injection = String::from(" ");
    for name in &parsed.props {
        injection.push_str(&format!("this.{name} = {name}; "));
    }
    // Rebuild the class text [start_i.start, body_close.end], deleting the
    // modifier spans (all in the param list) and inserting the injection (in the
    // body, after every modifier span).
    let class_start = toks[start_i].start;
    let class_end = toks[body_close].end;
    let mut cuts = parsed.modifier_spans;
    cuts.sort_unstable();
    let mut out = String::new();
    let mut pos = class_start;
    for (cs, ce) in &cuts {
        out.push_str(&src[pos..*cs]);
        pos = *ce;
    }
    out.push_str(&src[pos..inject_at]);
    out.push_str(&injection);
    out.push_str(&src[inject_at..class_end]);
    Ok(Some((body_close, out)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::StripOutcome;

    fn js(src: &str) -> String {
        match transform(src) {
            StripOutcome::Js(s) => s,
            StripOutcome::Refused(r) => panic!("unexpected refusal for {src:?}: {r}"),
        }
    }
    fn refused(src: &str) -> String {
        match transform(src) {
            StripOutcome::Refused(r) => r,
            StripOutcome::Js(s) => panic!("expected refusal for {src:?}, got Js: {s}"),
        }
    }

    #[test]
    fn erasable_passthrough_matches_strip() {
        // On pure-erasure input, transform equals strip.
        let src = "const x: number = 1;\nfunction f(a: string): string { return a; }\nconsole.log(x, f(\"y\"));\n";
        assert_eq!(transform(src), crate::strip(src));
    }

    #[test]
    fn enum_numeric_reverse_map() {
        let out = js("enum E { A, B = 5, C }\nconsole.log(E.A);\n");
        assert!(out.contains("var E;"));
        assert!(out.contains(r#"E[E["A"] = 0] = "A";"#), "{out}");
        assert!(out.contains(r#"E[E["B"] = 5] = "B";"#), "{out}");
        assert!(out.contains(r#"E[E["C"] = 6] = "C";"#), "{out}");
        assert!(out.contains("(E || (E = {}));"));
    }

    #[test]
    fn enum_string_forward_only() {
        let out = js("enum D { Up = \"UP\", Down = \"DOWN\" }\n");
        assert!(out.contains(r#"D["Up"] = "UP";"#), "{out}");
        assert!(out.contains(r#"D["Down"] = "DOWN";"#), "{out}");
        // No reverse map for string members.
        assert!(!out.contains(r#"D[D["Up"]"#), "{out}");
    }

    #[test]
    fn enum_hex_and_negative() {
        let out = js("enum H { A = 0xFF, B = -3, C }\n");
        assert!(out.contains(r#"E"#) || out.contains("H"));
        assert!(out.contains(r#"H[H["A"] = 0xFF] = "A";"#), "{out}");
        assert!(out.contains(r#"H[H["B"] = -3] = "B";"#), "{out}");
        assert!(out.contains(r#"H[H["C"] = -2] = "C";"#), "{out}");
    }

    #[test]
    fn const_enum_treated_as_regular() {
        let out = js("const enum CE { A, B = 5 }\n");
        assert!(out.contains("var CE;"), "{out}");
        assert!(out.contains(r#"CE[CE["A"] = 0] = "A";"#), "{out}");
    }

    #[test]
    fn namespace_exported_const_and_function() {
        let out = js(
            "namespace N { export const x = 1; export function f() { return x + 1; } let p = 2; }\n",
        );
        assert!(out.contains("var N;"), "{out}");
        assert!(out.contains("N.x = x;"), "{out}");
        assert!(out.contains("N.f = f;"), "{out}");
        assert!(!out.contains("N.p"), "non-exported member leaked: {out}");
    }

    #[test]
    fn nested_namespace() {
        let out = js("namespace A { export namespace B { export const v = 42; } }\n");
        assert!(out.contains("var A;"), "{out}");
        assert!(out.contains("B = A.B || (A.B = {})"), "{out}");
        assert!(out.contains("B.v = v;"), "{out}");
    }

    #[test]
    fn refuses_computed_enum() {
        assert!(refused("enum E { A = someFn() }\n").contains("computed"));
        assert!(refused("enum E { A = 1 << 2 }\n").contains("computed"));
    }

    #[test]
    fn refuses_export_let_in_namespace() {
        assert!(refused("namespace N { export let c = 0; }\n").contains("reassignment"));
    }

    #[test]
    fn refuses_module_keyword() {
        // Node's transpiler rejects `module` (use `namespace`), so we refuse it.
        assert!(refused("module M { export const x = 1; }\n").contains("module"));
    }

    #[test]
    fn refuses_esm_export_list_in_namespace() {
        // `export { … }` is not permitted inside a namespace (both engines reject).
        assert!(refused("namespace N { const a = 1; export { a }; }\n").contains("ESM"));
    }

    #[test]
    fn dotted_namespace_refused() {
        assert!(refused("namespace A.B { export const x = 1; }\n").contains("dotted"));
    }

    #[test]
    fn contextual_keyword_identifiers_pass_through() {
        // `namespace`/`module`/`enum`-as-property must NOT be lowered.
        let out =
            js("const namespace = 5; const o = { enum: 1 }; console.log(namespace, o.enum);\n");
        assert!(out.contains("const namespace = 5"), "{out}");
        assert!(!out.contains("(function"), "spurious lowering: {out}");
    }

    #[test]
    fn parameter_property_base_class_lowered() {
        // Base class: `this.x = x;` injected at the START of the body; the
        // modifier + type are stripped from the parameter.
        let out = js("class P { constructor(private x: number, public readonly y: string) {} }\n");
        assert!(out.contains("this.x = x;"), "{out}");
        assert!(out.contains("this.y = y;"), "{out}");
        assert!(!out.contains("private"), "modifier leaked: {out}");
        assert!(!out.contains("readonly"), "modifier leaked: {out}");
        // The constructor keyword survives; its params are plain bindings.
        assert!(out.contains("constructor("), "{out}");
    }

    #[test]
    fn parameter_property_derived_class_after_super() {
        // Derived class: `this.id = id;` injected immediately AFTER super(...).
        let out = js(
            "class B { constructor(n: number) {} }\nclass D extends B { constructor(public id: number) { super(id); } }\n",
        );
        let sup = out.find("super(id)").expect("super call present");
        let inj = out.find("this.id = id;").expect("injection present");
        assert!(inj > sup, "injection must follow super(): {out}");
    }

    #[test]
    fn parameter_property_with_default() {
        let out = js("class C { constructor(private n: number = 5) {} }\n");
        assert!(out.contains("this.n = n;"), "{out}");
        assert!(out.contains("= 5"), "default preserved: {out}");
    }

    #[test]
    fn refuses_destructuring_parameter_property() {
        // A destructuring binding as a parameter property refuses.
        assert!(
            refused("class C { constructor(private { a }: { a: number }) {} }\n")
                .contains("destructuring")
        );
    }

    #[test]
    fn parameter_property_in_namespace_class() {
        let out = js("namespace N { export class C { constructor(private x: number) {} } }\n");
        assert!(out.contains("this.x = x;"), "{out}");
        assert!(out.contains("N.C = C;"), "{out}");
    }
}
