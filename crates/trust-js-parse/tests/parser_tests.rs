// trust-js-parse: unit tests per grammar area — lexer vectors (astral
// identifiers, escapes, templates, regex disambiguation), ASI, cover-grammar
// reparses, and each early-error rule positive+negative, plus totality
// (no-panic fuzz over mangled corpus-like inputs) and the recursion bound.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_parse::{parse_script, ParseOutcome};

fn accepts(src: &str, strict: bool) {
    match parse_script(src, strict) {
        ParseOutcome::Script(_) => {}
        other => panic!("expected accept for {src:?} (strict={strict}), got {other:?}"),
    }
}

fn rejects(src: &str, strict: bool) {
    match parse_script(src, strict) {
        ParseOutcome::EarlyError { .. } => {}
        other => panic!("expected early error for {src:?} (strict={strict}), got {other:?}"),
    }
}

fn unsupported(src: &str, strict: bool) {
    match parse_script(src, strict) {
        ParseOutcome::Unsupported { .. } => {}
        other => panic!("expected unsupported for {src:?} (strict={strict}), got {other:?}"),
    }
}

// ---- lexer ---------------------------------------------------------------

#[test]
fn lexer_astral_and_escaped_identifiers() {
    accepts("var 𝕫 = 1; 𝕫;", false);
    accepts("var \\u{1D6A4} = 1;", false); // 𝚤 mathematical italic small dotless i
    accepts("var $_\u{200C}\u{200D}x;", false); // ZWNJ/ZWJ hidden joiners? (in continue)
    accepts("var a\\u0061;", false);
    rejects("var \\u0030abc;", false); // escape must be ID_Start
    rejects("var a\\u0020b;", false); // escape must be ID_Continue
    rejects("var ☃;", false); // snowman is not ID_Start
    rejects("va\\u0072 x;", false); // escaped keyword is not the keyword; `var x` unreachable
}

#[test]
fn lexer_numeric_literals() {
    accepts("0x1F; 0o17; 0b101; 1_000_000; 1e9; .5; 5.; 0.5e-3; 10n; 0x10n;", false);
    rejects("1__0;", false);
    rejects("1_;", false);
    rejects("0x;", false);
    rejects("1e;", false);
    rejects("3in x;", false); // no identifier immediately after number
    rejects("10.5n;", false);
    rejects("012n;", false);
    accepts("012;", false);
    rejects("012;", true);
    accepts("08; 09.5;", false);
    rejects("08;", true);
}

#[test]
fn lexer_strings_and_escapes() {
    accepts(r#"'a\n\t\x41A\u{1F600}';"#, false);
    accepts("'line\\\ncontinued';", false);
    rejects("'\\u{110000}';", false); // out of range
    rejects("'\\xZZ';", false);
    rejects("'unterminated", false);
    rejects("'newline\nin string';", false);
    accepts("'\\07';", false);
    rejects("'\\07';", true);
    accepts("'\\8';", false);
    rejects("'\\8';", true);
}

#[test]
fn lexer_templates() {
    accepts("`abc`;", false);
    accepts("`a${1}b${2}c`;", false);
    accepts("`${`inner${x}`}`;", false);
    accepts("`multi\nline`;", false);
    rejects("`unterminated", false);
    rejects("`\\01`;", false); // octal escape in untagged template: always error
    accepts("tag`\\01`;", false); // tagged: cooked=undefined is fine
    accepts("tag`\\xZZ`;", false);
    rejects("`\\xZZ`;", false);
}

#[test]
fn lexer_regex_vs_division() {
    accepts("var a = b / c / d;", false);
    accepts("var r = /abc/g;", false);
    accepts("var r = /=start/;", false); // /= re-lexed as regex
    accepts("if (x) /re/.test(y);", false);
    accepts("var x = a++ / b;", false);
    rejects("var r = /ab\ncd/;", false); // newline in regex
    rejects("var r = /a/gg;", false); // duplicate flag
    rejects("var r = /a/q;", false); // unknown flag
    rejects("var r = /a/uv;", false); // u+v exclusive
    rejects("var r = /(a/;", false); // unterminated group
    rejects("var r = /a{2,1}/;", false); // range out of order
    accepts("var r = /a{1,2}b*c+?[d-f]\\d(?:g|h)(?=i)$/m;", false);
}

#[test]
fn lexer_hashbang_and_html_comments() {
    accepts("#!/usr/bin/env node\nvar x = 1;", false);
    unsupported("<!-- annexB comment\nvar x;", false);
    unsupported("-->\nvar x;", false);
    accepts("var a = 1; var b = a-->2;", false); // a-- > 2, not a comment
}

// ---- ASI -----------------------------------------------------------------

#[test]
fn asi_basics() {
    accepts("var a = 1\nvar b = 2", false);
    accepts("a = b\n(c).d()", false); // no ASI before '('
    rejects("a b", false); // no line break, no ASI
    accepts("do x; while (0) y;", false); // do-while special ASI
    accepts("x\n++\ny", false); // restricted production: two statements
    rejects("return\n1", false); // top-level return: spec rejects (node --check accepts; oracle artifact)
}

#[test]
fn asi_restricted_productions() {
    rejects("throw\nnew Error();", false);
    accepts("function f() { return\n1; }", false); // return; 1;
    accepts("function* g() { yield\n1; }", false); // yield; 1;
    rejects("x\n=> 1;", false); // no newline before =>
    rejects("break\n", false);
}

#[test]
fn asi_break_continue_labels() {
    // label after newline does not attach
    accepts("a: while (0) { continue\na; }", false); // continue; a;
    accepts("a: while (0) { break a; }", false);
    rejects("while (0) { break missing; }", false);
}

// ---- cover grammars ------------------------------------------------------

#[test]
fn cover_paren_arrow_reparse() {
    accepts("(a, b) => a + b;", false);
    accepts("() => 1;", false);
    accepts("(a = 1, [b, c] = [], {d} = {}, ...rest) => a;", false);
    accepts("(a) => (b) => c;", false);
    rejects("();", false);
    rejects("(a,);", false);
    rejects("(...a);", false);
    rejects("(1) => x;", false);
    rejects("(a.b) => x;", false);
    rejects("(a, a) => x;", false); // arrows always unique params
    accepts("({a = 1}) => a;", false);
    rejects("({a = 1});", false);
    accepts("({a = 1} = {});", false);
    rejects("1 + (a) => b;", false); // arrow only at AssignmentExpression
    rejects("(a, b) = c;", false);
    accepts("(a) = c;", false);
}

#[test]
fn cover_async_call_vs_arrow() {
    accepts("async(x);", false);
    accepts("async(x) => x;", false);
    accepts("async () => 1;", false);
    accepts("async x => x;", false);
    accepts("async(a, b, ...c) => a;", false);
    accepts("var r = async(1, 2);", false);
    rejects("async({a = 1});", false);
    accepts("async({a = 1}) => a;", false);
    accepts("async\nx => x;", false); // async; then arrow — both statements parse
    rejects("async x\n=> x;", false);
}

#[test]
fn cover_destructuring_assignment() {
    accepts("[a, b] = [1, 2];", false);
    accepts("({a, b: {c}} = o);", false);
    accepts("[a = 1, [b], {c}] = x;", false);
    accepts("[...a] = x;", false);
    rejects("[...a, b] = x;", false);
    rejects("[...a,] = x;", false);
    accepts("[a,] = x;", false);
    accepts("({...a} = x);", false);
    rejects("({...a, b} = x);", false);
    rejects("({...{}} = x);", false);
    accepts("[(a)] = x;", false);
    rejects("[({a})] = x;", false);
    rejects("({a: 1} = x);", false);
    rejects("[a + b] = x;", false);
    rejects("a?.b = 1;", false);
    unsupported("f() = 1;", false); // spec rejects; V8 parses + late ReferenceError
    rejects("1 = 2;", false);
}

// ---- early errors: declarations & scopes ---------------------------------

#[test]
fn ee_duplicate_lexical() {
    rejects("let a; let a;", false);
    rejects("let a; var a;", false);
    rejects("var a; let a;", false);
    accepts("var a; var a;", false);
    rejects("let a; class a {}", false);
    rejects("{ let a; { var a; } }", false);
    accepts("{ let a; } var a;", false);
    accepts("function f(a) { var a; }", false);
    rejects("function f(a) { let a; }", false);
    rejects("const c = 1; function c() {}", false);
    accepts("function f() {} function f() {}", false);
    rejects("{ let f; function f() {} }", false);
    unsupported("{ function f() {} function f() {} }", false);
    rejects("{ function f() {} function f() {} }", true);
}

#[test]
fn ee_let_const_restrictions() {
    rejects("let let;", false);
    rejects("const let = 1;", false);
    rejects("let [let] = [];", false);
    rejects("const c;", false);
    rejects("let [a];", false);
    rejects("var [a];", false);
    accepts("let a;", false);
    rejects("class let {}", false);
}

#[test]
fn ee_catch() {
    accepts("try {} catch (e) { var x; }", false);
    unsupported("try {} catch (e) { var e; }", false);
    rejects("try {} catch ([e]) { var e; }", false);
    rejects("try {} catch (e) { let e; }", false);
    rejects("try {} catch (e = 1) {}", false);
    accepts("try {} catch ({a, b}) {}", false);
    rejects("try {}", false);
}

// ---- early errors: strict mode -------------------------------------------

#[test]
fn ee_strict_bindings_and_targets() {
    rejects("eval = 1;", true);
    rejects("arguments = 1;", true);
    accepts("eval = 1;", false);
    rejects("var eval;", true);
    rejects("function arguments() {}", true);
    rejects("eval++;", true);
    rejects("--arguments;", true);
    rejects("var implements;", true);
    accepts("var implements;", false);
    rejects("({}).x = eval = 1;", true);
    accepts("x = eval;", true); // reference is fine
}

#[test]
fn ee_strict_retroactive_directive() {
    rejects("function f(a, a) { 'use strict'; }", false);
    accepts("function f(a, a) {}", false);
    rejects("function f(a, a) {}", true);
    rejects("function eval() { 'use strict'; }", false);
    rejects("function f(eval) { 'use strict'; }", false);
    rejects("function f(a = 1) { 'use strict'; }", false); // non-simple params
    accepts("function f(a) { 'use strict'; }", false);
    rejects("'\\01'; 'use strict';", false); // octal escape in prologue
    accepts("'\\01'; 'not a directive';", false);
    accepts("'use\\x20strict'; with (o) x;", false); // escaped: not a directive
    rejects("'use strict'; with (o) x;", false);
}

#[test]
fn ee_yield_await_contexts() {
    accepts("function* g() { yield 1; yield* x; }", false);
    rejects("function* g(a = yield) {}", false);
    rejects("function* g(yield) {}", false);
    rejects("function* g() { var yield; }", false);
    accepts("function f(yield) {}", false);
    rejects("function f(yield) {}", true);
    accepts("async function f() { await x; }", false);
    rejects("async function f(a = await x) {}", false);
    rejects("async function f(await) {}", false);
    accepts("var await = 1;", false);
    accepts("var await = 1;", true); // await is not strict-reserved in scripts
    accepts("function* yield() {}", false); // declaration name uses outer [?Yield]
    accepts("async function await() {}", false); // declaration name uses outer [?Await]
    accepts("({ *g() { yield 1; } });", false);
    accepts("(a = yield) => x;", false); // sloppy: yield is a plain identifier here
    accepts("function* g() { (x) => x; }", false);
    rejects("function* g() { (a = yield) => x; }", false);
    rejects("async function f() { (a = await 1) => x; }", false);
}

#[test]
fn ee_break_continue_return() {
    rejects("break;", false);
    rejects("continue;", false);
    rejects("return;", false);
    accepts("while (0) break;", false);
    accepts("switch (x) { case 1: break; }", false);
    rejects("switch (x) { case 1: continue; }", false);
    rejects("a: { continue a; }", false); // continue target must be iteration
    accepts("a: while (0) continue a;", false);
    accepts("a: b: while (0) continue a;", false);
    rejects("a: a: while (0);", false); // duplicate label
    rejects("function f() { while (0) { break lab; } }", false);
    rejects("lab: function f() { break lab; }", false); // labels don't cross functions
    accepts("function f() { return 1; }", false);
}

#[test]
fn ee_new_target_super() {
    rejects("new.target;", false);
    accepts("function f() { new.target; }", false);
    accepts("function f() { () => new.target; }", false);
    rejects("() => new.target;", false);
    rejects("super.x;", false);
    rejects("super();", false);
    accepts("class C { m() { super.x; } }", false);
    rejects("class C { m() { super(); } }", false);
    accepts("class C extends B { constructor() { super(); } }", false);
    rejects("class C { constructor() { super(); } }", false);
    accepts("class C extends B { constructor() { () => super(); } }", false);
    rejects("function f() { super.x; }", false);
    accepts("({ m() { super.x; } });", false);
    rejects("({ f: function () { super.x; } });", false);
}

#[test]
fn ee_getters_setters() {
    accepts("({ get x() {}, set x(v) {} });", false);
    rejects("({ get x(a) {} });", false);
    rejects("({ set x() {} });", false);
    rejects("({ set x(a, b) {} });", false);
    rejects("({ set x(...v) {} });", false);
    accepts("class C { get x() {} set x(v) {} }", false);
    rejects("class C { get x(a) {} }", false);
}

#[test]
fn ee_object_literal_proto() {
    rejects("({__proto__: 1, __proto__: 2});", false);
    rejects("({'__proto__': 1, __proto__: 2});", false);
    accepts("({__proto__: 1, ['__proto__']: 2});", false);
    accepts("({__proto__, __proto__});", false); // shorthand doesn't count
    accepts("({__proto__: 1, __proto__() {}});", false); // method doesn't count
    accepts("({__proto__: a, __proto__: b} = x);", false); // pattern exemption
    rejects("f({__proto__: 1, __proto__: 2});", false);
}

#[test]
fn ee_class_rules() {
    rejects("class C { constructor() {} constructor() {} }", false);
    rejects("class C { get constructor() {} }", false);
    rejects("class C { *constructor() {} }", false);
    rejects("class C { static prototype() {} }", false);
    rejects("class C { static prototype = 1; }", false);
    rejects("class C { constructor = 1; }", false);
    rejects("class C { 'constructor'() {} 'constructor'() {} }", false);
    accepts("class C { static constructor() {} }", false);
    accepts("class C { ['constructor']() {} constructor() {} }", false);
    rejects("class C { #constructor; }", false);
    rejects("class C { #x; #x; }", false);
    accepts("class C { get #x() {} set #x(v) {} }", false);
    rejects("class C { get #x() {} static set #x(v) {} }", false);
    rejects("class C { x = arguments; }", false);
    accepts("class C { x = function() { return arguments; }; }", false);
    rejects("class C { static { arguments; } }", false);
    rejects("class C { static { return; } }", false);
    rejects("class C { static { await 1; } }", false);
    accepts("class C { static { new.target; } }", false);
    rejects("class C {}; this.#x;", false);
    accepts("class C { #x; m() { return this.#x; } }", false);
    rejects("class C { m() { return this.#y; } }", false);
    accepts("class Outer { #x; m() { return class Inner { n() { return this.#x; } }; } }", false);
}

#[test]
fn ee_invalid_targets_and_updates() {
    rejects("++1;", false);
    unsupported("f()++;", false); // spec rejects; V8 parses + late ReferenceError
    accepts("++a.b;", false);
    accepts("++(a);", false);
    rejects("a && b = c;", false);
    rejects("a = b++ = c;", false);
    accepts("a = b = c;", false);
    unsupported("for (f() of x);", false); // spec rejects; V8 parses
    accepts("for (a.b of x);", false);
    accepts("for ([a, b] of x);", false);
    accepts("for ({a} of x);", false);
}

#[test]
fn ee_for_variants() {
    accepts("for (var i = 0; i < 3; i++);", false);
    accepts("for (let x of xs);", false);
    accepts("for (const [a, b] in o);", false);
    rejects("for (let x = 1 of xs);", false);
    rejects("for (let x = 1 in o);", false);
    unsupported("for (var x = 1 in o);", false);
    rejects("for (var x = 1 in o);", true);
    rejects("for (var [a] = 1 in o);", false);
    accepts("for (let in o);", false); // sloppy: let as identifier in for-in
    rejects("for (let of xs);", false);
    rejects("for (async of xs);", false);
    accepts("for (async.x of xs);", false);
    rejects("for await (const x of xs);", false);
    accepts("async function f() { for await (const x of xs); }", false);
    rejects("async function f() { for await (const x in o); }", false);
    accepts("for (a in b);", false);
    rejects("for (a, b in o);", false); // no `in` in Expression[~In] head
    accepts("for ((a in b);;);", false);
}

#[test]
fn ee_statement_position_restrictions() {
    rejects("if (1) let x;", false);
    rejects("while (0) let [a] = [];", false);
    rejects("while (0) class C {};", false);
    rejects("while (0) function f() {}", false);
    unsupported("if (1) function f() {}", false);
    rejects("if (1) function f() {}", true);
    accepts("l: function f() {}", false);
    rejects("l: function f() {}", true);
    rejects("l: function* g() {}", false);
    accepts("if (1) var x;", false);
    accepts("let\n[a] = [];", true); // no ASI restriction after let
}

#[test]
fn ee_optional_chain_and_exponent() {
    rejects("a?.b`t`;", false);
    rejects("new a?.b();", false);
    accepts("new (a?.b)();", false);
    rejects("a ?? b || c;", false);
    rejects("a && b ?? c;", false);
    accepts("(a ?? b) || c;", false);
    rejects("-a ** b;", false);
    rejects("void a ** b;", false);
    accepts("(-a) ** b;", false);
    accepts("a ** -b;", false);
    accepts("++a ** b;", false);
}

#[test]
fn ee_private_names() {
    rejects("#x;", false);
    rejects("#x in o;", false);
    accepts("class C { #x; m() { return #x in o; } }", false);
    rejects("class C { #x; m() { return #y in o; } }", false);
    rejects("class C { #x; m() { delete this.#x; } }", false);
    accepts("class C { #x; m(o) { return o.#x; } }", false);
    rejects("(#x) in o;", false);
}

#[test]
fn ee_import_export_in_script() {
    rejects("import x from 'm';", false);
    rejects("export default 1;", false);
    rejects("import.meta;", false);
    accepts("import('m');", false);
    accepts("import('m', { with: {} });", false);
}

// ---- totality ------------------------------------------------------------

#[test]
fn totality_no_panics_on_mangled_inputs() {
    let seeds = [
        "class C extends B { #x = 1; static { this.y } }",
        "async function* g(a = 1, {b} = {}) { for await (const x of xs) yield x; }",
        "tag`a${(x, {y = 1}) => [/re/g, `${z}`]}b`;",
        "({a = 1} = x); [(a), ...b] = c; l: for (;;) continue l;",
        "'use strict'; var x = 08;",
        "new new a?.b`t`(); #x in y; super();",
    ];
    let mut lcg: u64 = 0x243F6A8885A308D3;
    for seed in seeds {
        for cut in 0..seed.len() {
            if !seed.is_char_boundary(cut) {
                continue;
            }
            let _ = parse_script(&seed[..cut], false);
            let _ = parse_script(&seed[cut..], true);
        }
        // Random single-byte mutations (kept at char boundaries).
        for _ in 0..200 {
            lcg = lcg.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let bytes: Vec<char> = seed.chars().collect();
            let i = (lcg >> 33) as usize % bytes.len();
            let repl = ['(', ')', '{', '}', '`', '/', '\\', '#', '\'', '"', '$', '\n']
                [(lcg >> 20) as usize % 12];
            let mut m: Vec<char> = bytes;
            m[i] = repl;
            let s: String = m.into_iter().collect();
            let _ = parse_script(&s, (lcg & 1) == 0);
        }
    }
}

#[test]
fn totality_depth_bound_is_refusal_not_overflow() {
    let deep_parens = format!("{}x{}", "(".repeat(5000), ")".repeat(5000));
    unsupported(&deep_parens, false);
    let deep_arrays = format!("{}1{}", "[".repeat(5000), "]".repeat(5000));
    unsupported(&deep_arrays, false);
    let deep_blocks = format!("{}{}", "{".repeat(5000), "}".repeat(5000));
    unsupported(&deep_blocks, false);
    let deep_unary = format!("{}1;", "!".repeat(5000));
    unsupported(&deep_unary, false);
    // Depth within bounds still parses.
    let ok = format!("{}x{};", "(".repeat(50), ")".repeat(50));
    accepts(&ok, false);
}

#[test]
fn directive_prologue_and_program_strictness() {
    accepts("'use strict'; x = 1;", false);
    rejects("'use strict'; x = 010;", false);
    rejects("'a'; 'use strict'; with (o) x;", false);
    accepts("('use strict'); with (o) x;", false);
    accepts("'use strict' + 1; with (o) x;", false);
    rejects("function f() { 'use strict'; with (o) x; }", false);
    accepts("function f() { 'x'; with (o) x; }", false);
}

// ---- later-wave surfaces (measured in by the S0 sweep) -------------------

#[test]
fn using_declarations() {
    accepts("function f() { using x = r(); }", false);
    accepts("function f() { using a = p(), b = q(); }", false);
    accepts("{ using x = r(); }", false);
    rejects("using x = r();", false); // not at script top level
    rejects("function f() { using x; }", false); // initializer required
    accepts("function f() { using [a] = r(); }", true); // not a using decl: member assignment `using[a]`
    rejects("switch (0) { case 0: using x = r(); }", false);
    accepts("switch (0) { case 0: { using x = r(); } }", false);
    accepts("async function f() { await using x = r(); }", false);
    rejects("function f() { await using x = r(); }", false);
    accepts("function f() { for (using x of xs); }", false);
    accepts("function f() { for (using of = null;;) break; }", false);
    rejects("function f() { for (using x in o); }", false);
    accepts("async function f() { for (await using x of xs); }", false);
    accepts("function f() { using\nx = 1; }", false); // no-LT: plain identifier + ASI
}

#[test]
fn import_source_forms() {
    accepts("() => { import.source('m'); };", false);
    rejects("new import.source('m');", false);
    unsupported("() => { import.defer('m'); };", false);
}

#[test]
fn regex_vmode_and_modifiers() {
    accepts("var r = /[abc]/v;", false);
    accepts("var r = /[a-z0-9]/v;", false);
    accepts("var r = /[\\q{ab|c}]/v;", false);
    accepts("var r = /[[a][b]]/v;", false);
    accepts("var r = /[\\p{L}&&\\p{Lu}]/v;", false);
    accepts("var r = /[\\p{L}--[aeiou]]/v;", false);
    rejects("var r = /[^\\q{ab}]/v;", false); // strings in negated class
    rejects("var r = /[a&&b--c]/v;", false); // mixed operators
    rejects("var r = /[(]/v;", false); // reserved punctuator
    rejects("var r = /[a!!b]/v;", false); // doubled punctuator
    accepts("var r = /(?i:a)(?-m:b)(?s-i:c)/;", false);
    rejects("var r = /(?x:a)/;", false);
    rejects("var r = /(?i-i:a)/;", false);
    rejects("var r = /(?:a)*{2}/;", false);
    accepts("var r = /\\p{Script=Latin}\\p{L}/u;", false);
    rejects("var r = /\\p{ Lowercase }/u;", false); // known-invalid spelling
    unsupported("var r = /\\p{Bogus_Property}/u;", false); // unknown name: sound refusal
    accepts("var r = /(?<a>x)|(?<a>y)/;", false); // dup names across alternatives
    rejects("var r = /(?<a>x)(?<a>y)/;", false); // dup names same alternative
    accepts("var r = /(?<\\u0061>x)\\k<a>/;", false); // escaped group name
}

// ---- module goal (ECMA-262 §16.2) ----------------------------------------

fn mod_accepts(src: &str) {
    match trust_js_parse::parse_module(src) {
        ParseOutcome::Script(_) => {}
        other => panic!("expected module accept for {src:?}, got {other:?}"),
    }
}

fn mod_rejects(src: &str) {
    match trust_js_parse::parse_module(src) {
        ParseOutcome::EarlyError { .. } => {}
        other => panic!("expected module early error for {src:?}, got {other:?}"),
    }
}

fn mod_unsupported(src: &str) {
    match trust_js_parse::parse_module(src) {
        ParseOutcome::Unsupported { .. } => {}
        other => panic!("expected module unsupported for {src:?}, got {other:?}"),
    }
}

#[test]
fn module_import_export_declarations_accept() {
    // Side-effect, default, namespace, named (with `as`, string names).
    mod_accepts("import './mod.js';");
    mod_accepts("import d from './mod.js';");
    mod_accepts("import * as ns from './mod.js';");
    mod_accepts("import { a, b as c } from './mod.js';");
    mod_accepts("import d, { a } from './mod.js';");
    mod_accepts("import d, * as ns from './mod.js';");
    mod_accepts("import { default as x, \"str name\" as y } from './mod.js';");
    mod_accepts("import {} from './mod.js';");
    // Exports: variable/function/class/default, re-exports, star.
    mod_accepts("const x = 1; export { x };");
    mod_accepts("export const y = 1;");
    mod_accepts("export function f() {} export default class {}");
    mod_accepts("export * from './mod.js';");
    mod_accepts("export * as ns from './mod.js';");
    mod_accepts("export { a, b as c } from './mod.js';");
    mod_accepts("const q = 1; export { q as \"external\" };");
    mod_accepts("export default 1 + 2;");
    mod_accepts("export default function g() {} export { g };");
    // Module-goal features: top-level await, import.meta.
    mod_accepts("await 1; import.meta.url;");
    mod_accepts("for await (const x of []) {}");
    // `new import.meta()` is legal (import.meta is a MemberExpression), even
    // though `new import(x)` is not.
    mod_accepts("new import.meta();");
    mod_rejects("new import('x');");
    // Forward reference from an export to a later declaration is legal.
    mod_accepts("export { later }; const later = 1;");
    // A module is a valid Script-shaped program of ordinary statements too.
    mod_accepts("var a = 1; function f(){ return a; } f();");
}

#[test]
fn module_early_errors_reject() {
    // A nested import declaration is a SyntaxError (not module top level).
    mod_rejects("{ import x from './y.js'; }");
    mod_rejects("function f() { import x from './y.js'; }");
    mod_rejects("if (true) import x from './y.js';");
    // export of an undeclared local name.
    mod_rejects("export { nope };");
    // Duplicate exported names (incl. two defaults).
    mod_rejects("const a = 1, b = 2; export { a as x }; export { b as x };");
    mod_rejects("export default 1; export default 2;");
    // Duplicate lexical declarations across import + let.
    mod_rejects("import x from './y.js'; let x = 1;");
    mod_rejects("function f(){} function f(){}");
    // new.target at module top level (outside any function).
    mod_rejects("new.target;");
    // `await` / `yield` as a plain binding at module top level.
    mod_rejects("var await = 1;");
    mod_rejects("var yield = 1;");
    // A from-less export whose local name is a string literal.
    mod_rejects("export { \"foo\" };");
    // import.meta remains invalid outside modules.
    match parse_script("import.meta.url;", false) {
        ParseOutcome::EarlyError { .. } => {}
        other => panic!("import.meta must be an early error in a script, got {other:?}"),
    }
}

#[test]
fn module_unsupported_refusals_are_sound() {
    // Import attributes are a grammar surface we refuse rather than judge.
    mod_unsupported("import x from './y.js' with { type: 'json' };");
    mod_unsupported("export * from './y.js' with { type: 'json' };");
    // A module export name string with a lone surrogate is unrepresentable.
    mod_unsupported("export { x as \"\\uD800\" }; const x = 1;");
}

#[test]
fn module_and_script_goals_diverge_where_expected() {
    // Top-level import/export are module-only: a Script rejects them.
    match parse_script("export const x = 1;", false) {
        ParseOutcome::EarlyError { .. } => {}
        other => panic!("expected script reject for top-level export, got {other:?}"),
    }
    // A plain program is accepted by both goals identically.
    mod_accepts("1 + 1;");
    accepts("1 + 1;", false);
}

#[test]
fn string_property_keys_have_utf16_semantics() {
    use trust_js_parse::{parse_script, ParseOutcome};
    // A surrogate PAIR in a key composes to the astral character (it must
    // parse as a Script — the exact key value is exercised by the interp).
    assert!(matches!(
        parse_script(r#"({ "😀": 1 });"#, false),
        ParseOutcome::Script(_)
    ));
    // A LONE surrogate key is unrepresentable in the cooked AST: sound
    // refusal, never a silently mis-keyed property.
    assert!(matches!(
        parse_script(r#"({ "\uD800": 1 });"#, false),
        ParseOutcome::Unsupported { .. }
    ));
    // Lone surrogates in ordinary string VALUES stay in-grammar (the
    // evaluator decodes the raw text at the code-unit level).
    assert!(matches!(
        parse_script(r#"var s = "\uD800";"#, false),
        ParseOutcome::Script(_)
    ));
}
