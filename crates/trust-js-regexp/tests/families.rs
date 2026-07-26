//! Construct-family unit tests with spec-derived vectors (ES2025 §22.2).
//! Semantics corners were additionally cross-checked against Node v24.5.0
//! (V8 13.6, Unicode 16.0); the env-gated differential harness re-verifies
//! every family against the live engine.
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_regexp::{compile, CompileError, ExecError};

fn u16v(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn str_of(units: &[u16], s: usize, e: usize) -> String {
    String::from_utf16_lossy(&units[s..e])
}

/// exec_at(input, 0) and render as (index, [group0, group1, …]).
#[track_caller]
fn exec(p: &str, f: &str, input: &str) -> Option<(usize, Vec<Option<String>>)> {
    let pat = compile(&u16v(p), f)
        .unwrap_or_else(|e| panic!("compile of {p:?} /{f}/ failed: {e:?}"));
    let inp = u16v(input);
    let r = pat
        .exec_at(&inp, 0)
        .unwrap_or_else(|e| panic!("exec of {p:?} /{f}/ on {input:?} failed: {e:?}"));
    r.map(|m| {
        let mut groups = vec![Some(str_of(&inp, m.index, m.end))];
        for c in &m.captures {
            groups.push(c.map(|(s, e)| str_of(&inp, s, e)));
        }
        (m.index, groups)
    })
}

#[track_caller]
fn check(p: &str, f: &str, input: &str, expected: Option<(usize, &[Option<&str>])>) {
    let got = exec(p, f, input);
    let expected = expected.map(|(i, g)| {
        (i, g.iter().map(|o| o.map(|s| s.to_string())).collect::<Vec<_>>())
    });
    assert_eq!(got, expected, "pattern {p:?} /{f}/ on {input:?}");
}

#[track_caller]
fn check_syntax(p: &str, f: &str) {
    match compile(&u16v(p), f) {
        Err(CompileError::Syntax(_)) => {}
        other => panic!("expected Syntax for {p:?} /{f}/, got {other:?}"),
    }
}

#[track_caller]
fn check_unsupported(p: &str, f: &str) {
    match compile(&u16v(p), f) {
        Err(CompileError::Unsupported(_)) => {}
        other => panic!("expected Unsupported for {p:?} /{f}/, got {other:?}"),
    }
}

const M: Option<&str> = None; // "missing" (undefined) capture

#[test]
fn literals_and_alternation() {
    check("abc", "", "xabcy", Some((1, &[Some("abc")])));
    check("ab|abc", "", "abc", Some((0, &[Some("ab")]))); // leftmost alternative wins
    check("a|b", "", "b", Some((0, &[Some("b")])));
    check("", "", "x", Some((0, &[Some("")])));
    check("x", "", "y", None);
    // Alternation backtracks into later alternatives on continuation failure.
    check("(a|ab)c", "", "abc", Some((0, &[Some("abc"), Some("ab")])));
}

#[test]
fn quantifier_basics() {
    check("a*", "", "aaa", Some((0, &[Some("aaa")])));
    check("a*?", "", "aaa", Some((0, &[Some("")])));
    check("a+?", "", "aaa", Some((0, &[Some("a")])));
    check("a{2,3}", "", "aaaa", Some((0, &[Some("aaa")])));
    check("a{2,3}?", "", "aaaa", Some((0, &[Some("aa")])));
    check("a{2}", "", "a", None);
    check("a{0}", "", "b", Some((0, &[Some("")])));
    check("(a+)(a*)", "", "aaa", Some((0, &[Some("aaa"), Some("aaa"), Some("")])));
    check("a??b", "", "ab", Some((0, &[Some("ab")])));
}

#[test]
fn empty_repetition_and_capture_reset() {
    // RepeatMatcher: optional empty iterations fail; c(x) keeps pre-attempt
    // captures (undefined if never completed).
    check("(a*)*", "", "b", Some((0, &[Some(""), M])));
    check("(a*)+", "", "b", Some((0, &[Some(""), Some("")])));
    check("()*", "", "", Some((0, &[Some(""), M])));
    check("(a?)*", "", "a", Some((0, &[Some("a"), Some("a")])));
    check("(|a)*", "", "aa", Some((0, &[Some("aa"), Some("a")])));
    check("(a|)*", "", "aa", Some((0, &[Some("aa"), Some("a")])));
    check("(a*)*", "", "aa", Some((0, &[Some("aa"), Some("aa")])));
    check("(a+)*", "", "aa", Some((0, &[Some("aa"), Some("aa")])));
    check("(?:)*", "", "", Some((0, &[Some("")])));
    // The classic capture-reset vector (Abrahams/Boyer):
    check(
        "(z)((a+)?(b+)?(c))*",
        "",
        "zaacbbbcac",
        Some((0, &[Some("zaacbbbcac"), Some("z"), Some("ac"), Some("a"), M, Some("c")])),
    );
    // min>0 mandatory iterations carry no empty check.
    check("(?:){3}", "", "x", Some((0, &[Some("")])));
    // Backreference to a group completed within the same iteration.
    check("(?:(a)\\1)+", "", "aa", Some((0, &[Some("aa"), Some("a")])));
}

#[test]
fn assertions() {
    check("^a", "", "ba", None);
    check("^a", "m", "b\na", Some((2, &[Some("a")])));
    check("a$", "", "ab", None);
    check("a$", "m", "a\nb", Some((0, &[Some("a")])));
    check("a$", "m", "a\u{2028}b", Some((0, &[Some("a")]))); // LS terminates lines
    check("^b", "m", "a\rb", Some((2, &[Some("b")])));
    check("\\bfoo\\b", "", "a foo b", Some((2, &[Some("foo")])));
    check("\\Bar", "", "bar", Some((1, &[Some("ar")])));
    check("\\bar", "", "bar", None);
    check("\\B\\B", "", "", Some((0, &[Some("")]))); // no word chars at all
    check("\\b", "", "", None);
}

#[test]
fn lookahead() {
    check("a(?=b)", "", "ab", Some((0, &[Some("a")])));
    check("a(?=b)", "", "ac", None);
    check("a(?!b)", "", "ac", Some((0, &[Some("a")])));
    check("(?=(a+))a", "", "aaa", Some((0, &[Some("a"), Some("aaa")])));
    // Negative lookahead discards inner captures on success.
    check("(?!(a)b)a", "", "ac", Some((0, &[Some("a"), M])));
    check("(?=(a+))\\1b", "", "aab", Some((0, &[Some("aab"), Some("aa")])));
    // No backtracking into a committed lookahead: with retry this would
    // match ("a" + "aa"); the first (greedy) inner match is final.
    check("(?=(a+))a\\1", "", "aaa", None);
}

#[test]
fn lookbehind() {
    check("(?<=ab)c", "", "abc", Some((2, &[Some("c")])));
    check("(?<=(a)b)c", "", "abc", Some((2, &[Some("c"), Some("a")])));
    check("(?<!a)b", "", "ab", None);
    check("(?<!x)b", "", "ab", Some((1, &[Some("b")])));
    check("(?<=\\d{3})f", "", "123f", Some((3, &[Some("f")])));
    // Lookbehind body matches backwards; nested lookahead flips forward.
    check("(?<=a(?=b))b", "", "ab", Some((1, &[Some("b")])));
    // Backward greedy quantifier captures maximally to the left.
    check("(?<=(a+))b", "", "aaab", Some((3, &[Some("b"), Some("aaa")])));
    check("(?<=(a+)(b+))c", "", "aabbc",
        Some((4, &[Some("c"), Some("aa"), Some("bb")])));
}

#[test]
fn classes_simple() {
    check("[a-c]+", "", "cabx", Some((0, &[Some("cab")])));
    check("[^a]", "", "ab", Some((1, &[Some("b")])));
    check("[\\d]+", "", "x42y", Some((1, &[Some("42")])));
    check("[\\b]", "", "\u{8}", Some((0, &[Some("\u{8}")])));
    check("[a-]", "", "-", Some((0, &[Some("-")])));
    check("[-a]", "", "-", Some((0, &[Some("-")])));
    check("[a-b-c]+", "", "b-c", Some((0, &[Some("b-c")])));
    check("[--0]", "", ".", Some((0, &[Some(".")]))); // range '-'..'0'
    check("[]", "", "x", None); // empty class never matches
    check("[^]", "", "x", Some((0, &[Some("x")]))); // matches anything
    check("[\\-]", "", "-", Some((0, &[Some("-")])));
    check("[\\w-]+", "", "a-b", Some((0, &[Some("a-b")])));
}

#[test]
fn dot_and_flags() {
    check(".", "", "\n", None);
    check(".", "s", "\n", Some((0, &[Some("\n")])));
    check(".", "", "\u{2029}", None);
    check(".", "u", "\u{1F600}", Some((0, &[Some("\u{1F600}")]))); // 2 units
    // Non-unicode dot consumes one code UNIT of an astral char.
    let pat = compile(&u16v("."), "").unwrap();
    let inp = u16v("\u{1F600}");
    let m = pat.exec_at(&inp, 0).unwrap().unwrap();
    assert_eq!((m.index, m.end), (0, 1));
}

#[test]
fn ignore_case_non_unicode() {
    check("abc", "i", "AbC", Some((0, &[Some("AbC")])));
    // ß uppercases to "SS" (two units): canonicalizes to itself.
    check("\u{df}", "i", "\u{df}", Some((0, &[Some("\u{df}")])));
    check("\u{df}", "i", "SS", None);
    // Final sigma ς and σ both canonicalize to Σ.
    check("\u{3c3}", "i", "\u{3c2}", Some((0, &[Some("\u{3c2}")])));
    check("\u{3c3}", "i", "\u{3a3}", Some((0, &[Some("\u{3a3}")])));
    // ASCII asymmetry: K (Kelvin) does not fold to k without unicode.
    check("k", "i", "\u{212a}", None);
    check("\u{17f}", "i", "s", None); // ſ: non-ASCII never canonizes to ASCII
    check("[^k]", "i", "\u{212a}", Some((0, &[Some("\u{212a}")])));
}

#[test]
fn ignore_case_unicode() {
    check("k", "iu", "\u{212a}", Some((0, &[Some("\u{212a}")])));
    check("s", "iu", "\u{17f}", Some((0, &[Some("\u{17f}")])));
    check("[^k]", "iu", "\u{212a}", None);
    check("\\w", "iu", "\u{17f}", Some((0, &[Some("\u{17f}")])));
    check("\\w", "i", "\u{17f}", None); // ui extension needs unicode
    check("\\W", "iu", "\u{17f}", None);
    // Deseret has non-BMP simple case pairs.
    check("\u{10400}", "iu", "\u{10428}", Some((0, &[Some("\u{10428}")])));
    // u-mode asymmetric class corner: [\P{Lu}] vs [^\p{Lu}].
    check("[\\P{Lu}]", "iu", "A", Some((0, &[Some("A")])));
    check("[^\\p{Lu}]", "iu", "A", None);
}

#[test]
fn backreferences() {
    check("(a)\\1", "", "aa", Some((0, &[Some("aa"), Some("a")])));
    check("(a)\\1", "", "ab", None);
    check("(a)?\\1", "", "b", Some((0, &[Some(""), M]))); // unset ref matches empty
    check("\\1(a)", "", "aa", Some((0, &[Some("a"), Some("a")])));
    check("(a)\\1", "i", "aA", Some((0, &[Some("aA"), Some("a")])));
    check("(\\w+)\\s\\1", "", "hey hey you", Some((0, &[Some("hey hey"), Some("hey")])));
    check("(a|b)*\\1", "", "abab", Some((0, &[Some(""), M])));
}

#[test]
fn named_groups() {
    check("(?<x>a)\\k<x>", "", "aa", Some((0, &[Some("aa"), Some("a")])));
    check("(?<x>a)|(?<x>b)", "", "b", Some((0, &[Some("b"), M, Some("b")])));
    check("(?<\u{61}>a)", "", "a", Some((0, &[Some("a"), Some("a")])));
    let p = compile(&u16v("(?<x>a)|(?<x>b)"), "").unwrap();
    assert_eq!(p.group_names(), &[("x".to_string(), 1), ("x".to_string(), 2)]);
    assert_eq!(p.n_captures(), 2);
    // \u escape in a group name, even without the u flag.
    check("(?<\\u0061b>x)\\k<ab>", "", "xx", Some((0, &[Some("xx"), Some("x")])));
}

#[test]
fn unicode_mode_surrogates() {
    check("\\u{1F600}", "u", "\u{1F600}", Some((0, &[Some("\u{1F600}")])));
    check("\\uD83D\\uDE00", "u", "\u{1F600}", Some((0, &[Some("\u{1F600}")])));
    check("\u{1F600}{2}", "u", "\u{1F600}\u{1F600}", Some((0, &[Some("\u{1F600}\u{1F600}")])));
    // Without u, the quantifier binds the trail surrogate alone.
    check("\u{1F600}{2}", "", "\u{1F600}\u{1F600}", None);
    // A lone lead surrogate in the input is matchable in u mode.
    let pat = compile(&u16v("\\uD83D"), "u").unwrap();
    let lone: Vec<u16> = vec![0xD83D, 0x0041];
    assert!(pat.exec_at(&lone, 0).unwrap().is_some());
    // But not when the input pairs it with a trail.
    let paired: Vec<u16> = vec![0xD83D, 0xDE00];
    assert!(pat.exec_at(&paired, 0).unwrap().is_none());
}

#[test]
fn property_escapes() {
    check("\\p{L}", "u", "a", Some((0, &[Some("a")])));
    check("\\p{L}", "u", "1", None);
    check("\\P{L}", "u", "1", Some((0, &[Some("1")])));
    check("\\p{Lu}", "u", "A", Some((0, &[Some("A")])));
    check("\\p{Script=Greek}", "u", "\u{3b1}", Some((0, &[Some("\u{3b1}")])));
    check("\\p{sc=Grek}", "u", "\u{3b1}", Some((0, &[Some("\u{3b1}")])));
    // U+0342 is sc=Inherited but scx includes Greek.
    check("\\p{scx=Greek}", "u", "\u{342}", Some((0, &[Some("\u{342}")])));
    check("\\p{sc=Greek}", "u", "\u{342}", None);
    check("\\p{Alphabetic}", "u", "a", Some((0, &[Some("a")])));
    check("\\p{AHex}", "u", "f", Some((0, &[Some("f")])));
    check("\\p{Any}", "u", "\u{10FFFF}", Some((0, &[Some("\u{10FFFF}")])));
    check("\\p{ASCII}", "u", "\u{80}", None);
    check("\\p{Assigned}", "u", "\u{378}", None); // U+0378 unassigned
    check("\\p{gc=Nd}+", "u", "\u{660}42", Some((0, &[Some("\u{660}42")])));
    check("\\p{Lu}", "iu", "a", Some((0, &[Some("a")]))); // folded match
}

#[test]
fn v_mode_class_sets() {
    check("[[a-z]&&[^aeiou]]", "v", "b", Some((0, &[Some("b")])));
    check("[[a-z]&&[^aeiou]]", "v", "a", None);
    check("[\\p{L}--\\p{Lu}]", "v", "a", Some((0, &[Some("a")])));
    check("[\\p{L}--\\p{Lu}]", "v", "A", None);
    // A bare range is not a ClassSetOperand: [a-c--b] is a SyntaxError;
    // the nested form works.
    check_syntax("[a-c--b]", "v");
    check("[[a-c]--b]", "v", "b", None);
    check("[[a-c]--b]", "v", "c", Some((0, &[Some("c")])));
    check("[^a-c]", "v", "d", Some((0, &[Some("d")])));
    check("[[ab][cd]]", "v", "d", Some((0, &[Some("d")])));
    check("[a&&a&&a]", "v", "a", Some((0, &[Some("a")])));
    check("[\\q{ab|c}]", "v", "ab", Some((0, &[Some("ab")])));
    check("[\\q{ab|c}]", "v", "c", Some((0, &[Some("c")])));
    check("[\\q{ab|a}]b", "v", "ab", Some((0, &[Some("ab")]))); // backtrack to shorter string
    check("[\\q{ab|a}]+", "v", "aab", Some((0, &[Some("aab")])));
    check("[\\q{}]", "v", "x", Some((0, &[Some("")]))); // empty string member
    check("[\\q{a}--a]", "v", "a", None);
    check("[\\q{ab}&&\\q{ab|c}]", "v", "ab", Some((0, &[Some("ab")])));
    check("[\\q{ab}&&\\q{c}]", "v", "ab", None);
    // v+i folds sets before complement: [\P{Lu}] and [^\p{Lu}] agree.
    check("[\\P{Lu}]", "iv", "A", None);
    check("[^\\p{Lu}]", "iv", "A", None);
    check("[\\p{Lu}]", "iv", "a", Some((0, &[Some("a")])));
}

#[test]
fn v_mode_string_properties() {
    // Flag sequence (RGI_Emoji_Flag_Sequence ⊂ RGI_Emoji): 🇺🇸.
    check("\\p{RGI_Emoji}", "v", "\u{1F1FA}\u{1F1F8}",
        Some((0, &[Some("\u{1F1FA}\u{1F1F8}")])));
    // Keycap sequence: #️⃣ = # + VS16 + COMBINING ENCLOSING KEYCAP.
    check("\\p{Emoji_Keycap_Sequence}", "v", "#\u{FE0F}\u{20E3}",
        Some((0, &[Some("#\u{FE0F}\u{20E3}")])));
    // Basic_Emoji single: ⌚.
    check("\\p{Basic_Emoji}", "v", "\u{231A}", Some((0, &[Some("\u{231A}")])));
    // Longest string preferred: ZWJ family sequence beats its first emoji.
    check("^\\p{RGI_Emoji}", "v",
        "\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F466}",
        Some((0, &[Some("\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F466}")])));
}

#[test]
fn modifiers() {
    check("(?i:a)b", "", "AB", None);
    check("(?i:a)b", "", "Ab", Some((0, &[Some("Ab")])));
    check("(?-i:a)b", "i", "aB", Some((0, &[Some("aB")])));
    check("(?-i:a)b", "i", "Ab", None);
    check("(?i:(?-i:a)b)", "", "aB", Some((0, &[Some("aB")])));
    check("(?m:^b)", "", "a\nb", Some((2, &[Some("b")])));
    check("(?s:.)", "", "\n", Some((0, &[Some("\n")])));
    check("(?i:(?i:a))", "", "A", Some((0, &[Some("A")])));
    // Modifiers switch the \b word set (ui extension) region-locally.
    check("(?i:\\w)", "u", "\u{17f}", Some((0, &[Some("\u{17f}")])));
}

#[test]
fn exec_surface() {
    let pat = compile(&u16v("a"), "").unwrap();
    let inp = u16v("xa");
    assert!(pat.exec_sticky_at(&inp, 0).unwrap().is_none());
    assert!(pat.exec_sticky_at(&inp, 1).unwrap().is_some());
    assert!(pat.exec_at(&inp, 0).unwrap().is_some());
    assert!(pat.exec_at(&inp, 3).unwrap().is_none()); // start > len
    assert!(pat.exec_at(&inp, 2).unwrap().is_none()); // start == len
    let empty = compile(&u16v(""), "").unwrap();
    assert!(empty.exec_at(&inp, 2).unwrap().is_some()); // empty match at end
    let p = compile(&u16v("(?<n>a)|b"), "giy").unwrap();
    assert!(p.flags().global && p.flags().ignore_case && p.flags().sticky);
    assert_eq!(p.flags_str(), "giy");
    assert_eq!(p.source_units(), &u16v("(?<n>a)|b")[..]);
}

#[test]
fn syntax_errors_both_grammars() {
    for (p, f) in [
        ("^*", ""), ("$*", ""), ("\\b*", ""), ("(?<=a)*", ""), ("a**", ""),
        ("*a", ""), ("+a", ""), ("{1}", ""), ("a{2,1}", ""), ("[z-a]", ""),
        ("(", ""), (")", ""), ("a)", ""), ("[a", ""), ("\\", ""),
        ("(?<1a>x)", ""), ("(?i)a", ""), ("(?x:a)", ""), ("(?ii:a)", ""),
        ("(?i-i:a)", ""), ("(?-:a)", ""), ("(?<a>x)(?<a>y)", ""),
        ("(?<a>x)((?<a>y)|z)", ""), ("(?<a>x)\\k<b>", ""),
        // u-mode strictness
        ("{", "u"), ("}", "u"), ("]", "u"), ("a{", "u"), ("\\a", "u"),
        ("\\_", "u"), ("\\-", "u"), ("\\8", "u"), ("\\1", "u"), ("\\01", "u"),
        ("\\c5", "u"), ("\\c", "u"), ("[a-\\d]", "u"), ("\\p{Bogus}", "u"),
        ("\\p{Lu=true}", "u"), ("\\p{RGI_Emoji}", "u"), ("\\u{110000}", "u"),
        ("(?=a)*", "u"), ("a{,2}", "u"), ("\\k", "u"), ("\\q", "u"),
        ("\\x1", "u"), ("\\u{2", "u"), ("\\p", "u"),
        // v-mode strictness
        ("[a-]", "v"), ("[-a]", "v"), ("[--]", "v"), ("[::]", "v"),
        ("[&&]", "v"), ("[ab--c]", "v"), ("[a--b&&c]", "v"), ("[a-b--c]", "v"),
        ("[^\\q{ab}]", "v"), ("\\P{RGI_Emoji}", "v"), ("[\\d-x]", "v"),
        ("[a&&&b]", "v"), ("[/]", "v"),
        // flags
        ("a", "uu"), ("a", "uv"), ("a", "z"),
    ] {
        check_syntax(p, f);
    }
}

#[test]
fn annex_b_refusals() {
    for p in [
        "(?=a)*", "(?!a)?", "a{,2}", "{", "}", "]", "a{", "[a-\\d]",
        "[\\d-a]", "\\c5", "\\c", "[\\c5]", "[\\c]", "\\8", "\\9", "\\1",
        "\\01", "\\p{L}", "\\u{2}", "\\x1", "\\a", "\\_", "\\k<a>", "\\k",
        "[\\1]", "[\\q{a}]",
    ] {
        check_unsupported(p, "");
    }
    // Resource refusals.
    check_unsupported("a{4294967296}", "");
    check_unsupported(&format!("{}a{}", "(".repeat(500), ")".repeat(500)), "");
}

#[test]
fn budget_redos_guard() {
    // Catastrophic backtracking must return Budget, never hang.
    let p = compile(&u16v("(a+)+$"), "").unwrap();
    let inp = u16v(&format!("{}!", "a".repeat(64)));
    assert_eq!(p.exec_at(&inp, 0), Err(ExecError::Budget));

    let p2 = compile(&u16v("(a|a)+$"), "").unwrap();
    assert_eq!(p2.exec_at(&inp, 0), Err(ExecError::Budget));

    // A custom budget is honored.
    let p3 = compile(&u16v("a*"), "").unwrap();
    let long = u16v(&"a".repeat(100));
    assert_eq!(p3.exec_at_with_budget(&long, 0, 10), Err(ExecError::Budget));

    // Huge mandatory empty iteration counts terminate via budget.
    let p4 = compile(&u16v("(?:a?){1000000000}b"), "").unwrap();
    assert_eq!(p4.exec_at(&u16v(""), 0), Err(ExecError::Budget));
}
