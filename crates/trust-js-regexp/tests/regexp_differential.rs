//! Differential validation against a real engine (Node) through the
//! trust-js-trace driver.
//!
//! Env-gated: set `TRUST_JS_NODE` to a node binary to run; otherwise the
//! test SKIPS LOUDLY. For every (pattern, flags, input[, start]) triple the
//! harness runs `new RegExp(p, f).exec(input)` in Node (via the trace
//! driver's firewalled projection) and compares verdicts and results:
//!
//! - our `Unsupported` / `Budget` → counted as a refusal (sound, allowed);
//! - our `Syntax` must meet a Node SyntaxError (verdict agreement);
//! - a compiled pattern's match/no-match, index, captures, and named-group
//!   values must agree exactly. Disagreements must be ZERO.
//!
//! The battery spans every construct family (incl. adversarial
//! backtracking) plus, when present, corpus-derived triples scraped from
//! test262 (tests/data/corpus_triples.json — see scripts/
//! scrape_test262_regexp.py).
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::io::Write as _;
use std::path::PathBuf;
use std::process::Command;

use trust_js_regexp::{compile, CompileError, ExecError, Pattern};

// ---------------------------------------------------------------------------
// Battery
// ---------------------------------------------------------------------------

/// (pattern, flags, inputs) — expanded to one triple per input.
const FAMILIES: &[(&str, &str, &[&str])] = &[
    // -- literals / alternation --------------------------------------------
    ("abc", "", &["abc", "xabcy", "ab", ""]),
    ("ab|abc", "", &["abc", "ab", "b"]),
    ("a|b|c", "", &["cab", "z"]),
    ("(a|ab)(c|bcd)(d*)", "", &["abcd", "acd"]),
    ("", "", &["", "abc"]),
    ("x", "", &["y", "xx"]),
    ("a.c", "", &["abc", "a\nc", "ac"]),
    ("\\.", "", &[".", "a"]),
    // -- quantifiers -------------------------------------------------------
    ("a*", "", &["aaa", "", "baa"]),
    ("a+", "", &["aaa", "b", "ba"]),
    ("a?", "", &["a", ""]),
    ("a*?", "", &["aaa"]),
    ("a+?", "", &["aaa"]),
    ("a??", "", &["a", ""]),
    ("a{2}", "", &["aaa", "a"]),
    ("a{2,}", "", &["aaaa", "a"]),
    ("a{2,3}", "", &["aaaa", "aa", "a"]),
    ("a{2,3}?", "", &["aaaa"]),
    ("a{0}", "", &["b", ""]),
    ("(a+)(a*)", "", &["aaa"]),
    ("(a*)(a+)", "", &["aaa"]),
    ("x(?:abc)*y", "", &["xy", "xabcy", "xabcabcy"]),
    ("(?:ab){1,2}?b", "", &["abab", "abb"]),
    // -- empty repetition / capture reset ----------------------------------
    ("(a*)*", "", &["b", "aa", ""]),
    ("(a*)+", "", &["b", "aa"]),
    ("(a+)*", "", &["aa", ""]),
    ("(a?)*", "", &["a", "b"]),
    ("()*", "", &[""]),
    ("(?:)*", "", &[""]),
    ("(|a)*", "", &["aa", ""]),
    ("(a|)*", "", &["aa", ""]),
    ("(a||b)*", "", &["ab", "ba"]),
    ("(?:a?b??)*", "", &["aabb", "ab"]),
    ("(z)((a+)?(b+)?(c))*", "", &["zaacbbbcac"]),
    ("(?:){3}", "", &["x"]),
    ("(?:(a)|b)+", "", &["ab", "ba", "aa"]),
    ("((a)|b)*", "", &["ab", "ba"]),
    ("(?:(a)\\1)+", "", &["aa", "aaaa"]),
    ("(a*)b\\1+", "", &["baaaac", "abab"]),
    // -- assertions --------------------------------------------------------
    ("^a", "", &["ab", "ba"]),
    ("^a", "m", &["b\na", "ba"]),
    ("a$", "", &["ba", "ab"]),
    ("a$", "m", &["a\nb", "b\ra", "x"]),
    ("^$", "", &["", "a"]),
    ("^$", "m", &["a\n\nb"]),
    ("^a$", "m", &["b\na\nc"]),
    ("\\bfoo", "", &["foo", " foo", "xfoo"]),
    ("foo\\b", "", &["foo.", "foob"]),
    ("\\Bar", "", &["bar", " ar"]),
    ("\\b", "", &["", "a", " "]),
    ("\\B", "", &["", "a", "ab"]),
    ("\\b.\\b", "", &["a", "ab", "a b"]),
    ("\\bſ\\b", "iu", &["ſ", "aſ"]),
    ("\\bK\\b", "iu", &["K", "xK"]),
    // -- lookahead ---------------------------------------------------------
    ("a(?=b)", "", &["ab", "ac"]),
    ("a(?!b)", "", &["ab", "ac"]),
    ("(?=(a+))", "", &["aaa", "b"]),
    ("(?=(a+))a\\1", "", &["aaa", "aaaa"]),
    ("(?=(a+))\\1b", "", &["aab", "ab"]),
    ("(?!(a)b)a", "", &["ac", "ab"]),
    ("a(?=b(?=c))", "", &["abc", "abd"]),
    ("(?!x)*", "u", &["x"]), // syntax both (quantified assertion, u)
    // -- lookbehind --------------------------------------------------------
    ("(?<=ab)c", "", &["abc", "xbc"]),
    ("(?<!a)b", "", &["ab", "cb", "b"]),
    ("(?<=(a)b)c", "", &["abc"]),
    ("(?<=(a+))b", "", &["aaab", "b"]),
    ("(?<=(a+)(b+))c", "", &["aabbc"]),
    ("(?<=a(?=b))b", "", &["ab"]),
    ("(?<=(a)\\1)b", "", &["aab", "ab"]),
    ("(?<=^a)b", "", &["ab", "xab"]),
    ("(?<!(a))b\\1", "", &["cb", "ab"]),
    ("x(?<=[ab]{3})", "", &["abax", "abx"]),
    // -- classes (non-v) ---------------------------------------------------
    ("[a-c]+", "", &["cabx", "xyz"]),
    ("[^a-c]+", "", &["cabx", "xyz"]),
    ("[abc-]", "", &["-", "d"]),
    ("[-abc]", "", &["-", "d"]),
    ("[a-b-c]+", "", &["b-c", "abc-"]),
    ("[--0]+", "", &["-./0", "1"]),
    ("[\\b]", "", &["\u{8}", "b"]),
    ("[\\]]", "", &["]", "["]),
    ("[\\-]", "", &["-"]),
    ("[]", "", &["x", ""]),
    ("[^]", "", &["x", "\n"]),
    ("[\\d]+", "", &["x42y", "abc"]),
    ("[\\w-]+", "", &["a-b_c", "!!"]),
    ("[\\s\\S]", "", &["\n", "a"]),
    ("[a-f]{3}", "i", &["ACE", "acg"]),
    ("[^a]", "i", &["A", "b"]),
    // -- dot / flags -------------------------------------------------------
    (".", "", &["\n", "\r", "\u{2028}", "\u{2029}", "a"]),
    (".", "s", &["\n", "\u{2029}"]),
    (".+", "", &["ab\ncd"]),
    (".+", "s", &["ab\ncd"]),
    (".", "u", &["\u{1F600}"]),
    (".", "", &["\u{1F600}"]),
    (".{2}", "u", &["\u{1F600}a", "\u{1F600}"]),
    // -- case-insensitivity (non-unicode) ----------------------------------
    ("abc", "i", &["AbC", "ABD"]),
    ("ß", "i", &["ß", "SS", "ss"]),
    ("σ", "i", &["ς", "Σ", "σ", "x"]),
    ("ς", "i", &["σ", "Σ"]),
    ("k", "i", &["K", "\u{212A}"]),
    ("ſ", "i", &["s", "S", "ſ"]),
    ("s", "i", &["ſ", "S"]),
    ("[^k]", "i", &["\u{212A}", "k"]),
    ("İ", "i", &["i", "İ"]),
    ("ᎠᎡ", "i", &["ꭰꭱ", "ᎠᎡ"]),
    // -- case-insensitivity (unicode) --------------------------------------
    ("k", "iu", &["\u{212A}", "K"]),
    ("s", "iu", &["ſ", "S"]),
    ("ſ", "iu", &["s", "K"]),
    ("[^k]", "iu", &["\u{212A}", "x"]),
    ("İ", "iu", &["i", "İ"]),
    ("\u{10400}", "iu", &["\u{10428}", "\u{10400}"]),
    ("σ", "iu", &["ς", "Σ"]),
    ("\\w+", "iu", &["ſK", "ab"]),
    ("\\W", "iu", &["ſ", "!"]),
    ("[\\w]+", "iu", &["ſK_9"]),
    ("[^\\w]", "iu", &["ſ", "!"]),
    ("\\w", "i", &["ſ", "\u{212A}", "a"]),
    // -- \d \s \w exact sets ----------------------------------------------
    ("\\d+", "", &["042", "٤٢", "４２"]), // ASCII only: arabic/fullwidth digits excluded
    ("\\D+", "", &["abc٤", "42"]),
    ("\\s+", "", &[" \t\r\n\u{b}\u{c}", "\u{a0}\u{feff}", "\u{2028}\u{2029}", "\u{1680}", "\u{180e}", "\u{85}", "a"]),
    ("\\S+", "", &["\u{180e}\u{85}", " "]),
    ("\\w+", "", &["a_Z9", "é"]),
    ("\\W+", "", &["é!", "a"]),
    ("[\\s]", "", &["\u{205f}", "\u{200b}"]),
    // -- backreferences ----------------------------------------------------
    ("(a)\\1", "", &["aa", "ab"]),
    ("(a)?\\1", "", &["b", "aa"]),
    ("\\1(a)", "", &["aa", "a"]),
    ("(a)\\1", "i", &["aA", "Aa"]),
    ("(ß)\\1", "i", &["ßß", "ßSS"]),
    ("(ſ)\\1", "iu", &["ſs", "sſ"]),
    ("(\\w+)\\s\\1", "", &["hey hey you", "ab ba"]),
    ("(a|b)*\\1", "", &["abab", "abb"]),
    ("((a)|(b))*\\2\\3", "", &["abab"]),
    ("(?:(a)|(b))\\1\\2", "", &["aa", "bb"]),
    // -- named groups ------------------------------------------------------
    ("(?<x>a)\\k<x>", "", &["aa", "ab"]),
    ("(?<x>a)|(?<x>b)", "", &["a", "b", "c"]),
    ("(?<first>\\w+) (?<last>\\w+)", "", &["ann bell"]),
    ("\\k<x>(?<x>a)", "", &["a", "ba"]),
    ("(?<\\u0061b>x)\\k<ab>", "", &["xx"]),
    ("(?<π>a)", "u", &["a"]),
    ("((?<x>a))|(?<x>b)", "", &["b", "a"]),
    // Invalid GroupSpecifier names: a non-ID_Start start is a SyntaxError in
    // BOTH modes. Regression: the dog-emoji lead surrogate U+D83D truncates
    // to 0x3D ('='), which once misrouted `(?<🐕>…)` into a lookbehind and
    // wrongly accepted the bad name (parser::parse_group low-byte compare).
    // The fox-emoji lead surrogate is U+D83E (→ '>'), so it never collided —
    // both must be rejected identically. 𝟚 (U+1D7DA) is ID_Continue but not
    // ID_Start, so it is invalid as the first name character.
    ("(?<\u{1f415}>dog)", "", &["dog"]),
    ("(?<\u{1f415}>dog)", "u", &["dog"]),
    ("(?<\u{1f98a}>fox)", "", &["fox"]),
    ("(?<\u{1f98a}>fox)", "u", &["fox"]),
    ("(?<\u{1d7da}the>the)", "", &["the"]),
    ("(?<\u{1d7da}the>the)", "u", &["the"]),
    // -- unicode mode / surrogates ----------------------------------------
    ("\\u{1F600}", "u", &["\u{1F600}", "x"]),
    ("\\uD83D\\uDE00", "u", &["\u{1F600}"]),
    ("\u{1F600}{2}", "u", &["\u{1F600}\u{1F600}", "\u{1F600}"]),
    ("\u{1F600}{2}", "", &["\u{1F600}\u{1F600}"]),
    ("[\u{1F600}-\u{1F64F}]", "u", &["\u{1F603}", "z"]),
    ("[^\u{1F600}]", "u", &["\u{1F601}", "\u{1F600}"]),
    ("\\u0041", "", &["A"]),
    ("\\x41", "", &["A"]),
    ("\\cJ", "", &["\n"]),
    ("\\0", "", &["\u{0}", "0"]),
    ("\\$", "", &["$"]),
    ("\\u{41}", "u", &["A"]),
    // -- property escapes --------------------------------------------------
    ("\\p{L}+", "u", &["abÇδ", "12"]),
    ("\\P{L}+", "u", &["12!", "ab"]),
    ("\\p{Lu}", "u", &["A", "a"]),
    ("\\p{Lu}", "iu", &["a", "A", "1"]),
    ("\\p{General_Category=Letter}", "u", &["a", "1"]),
    ("\\p{gc=Nd}+", "u", &["٤٢42", "x"]),
    ("\\p{Nd}", "u", &["４", "x"]),
    ("\\p{Script=Greek}+", "u", &["αβγ", "abc"]),
    ("\\p{sc=Grek}", "u", &["α", "a"]),
    ("\\p{scx=Greek}", "u", &["\u{342}", "a"]),
    ("\\p{sc=Greek}", "u", &["\u{342}"]),
    ("\\p{Script=Han}", "u", &["漢", "a"]),
    ("\\p{Alphabetic}", "u", &["a", "1"]),
    ("\\p{White_Space}+", "u", &[" \u{a0}", "a"]),
    ("\\p{AHex}+", "u", &["0aF", "g"]),
    ("\\p{XID_Start}", "u", &["a", "1"]),
    ("\\p{Emoji}", "u", &["\u{1F600}", "a"]),
    ("\\p{Extended_Pictographic}", "u", &["\u{1F600}", "a"]),
    ("\\p{Any}", "u", &["\u{10FFFF}", ""]),
    ("\\p{Assigned}", "u", &["\u{378}", "a"]),
    ("\\p{ASCII}", "u", &["\u{7f}", "\u{80}"]),
    ("[\\p{L}\\d]+", "u", &["a1é", "!"]),
    ("[^\\p{L}]", "u", &["1", "a"]),
    ("[\\P{Lu}]", "iu", &["A", "a"]),
    ("[^\\p{Lu}]", "iu", &["A", "!"]),
    ("\\P{Lu}", "iu", &["A", "!"]),
    // -- v-mode class sets -------------------------------------------------
    ("[[a-z]&&[^aeiou]]+", "v", &["bcd", "ae"]),
    ("[\\p{L}--\\p{Lu}]+", "v", &["ab", "AB"]),
    ("[[a-c]--b]", "v", &["b", "c"]),
    ("[[ab][cd]]+", "v", &["adbc", "e"]),
    ("[a&&a&&a]", "v", &["a", "b"]),
    ("[^a-c]", "v", &["d", "a"]),
    ("[^[a-c]]", "v", &["d", "b"]),
    ("[\\q{ab|c}]+", "v", &["abc", "x"]),
    ("[\\q{ab|a}]b", "v", &["ab", "aab"]),
    ("[\\q{}]x", "v", &["x", "y"]),
    ("[\\q{a}--a]", "v", &["a"]),
    ("[\\q{ab}&&\\q{ab|c}]", "v", &["ab", "c"]),
    ("[[a-z]--[aeiou]]+", "v", &["xyz", "ea"]),
    ("[\\p{Lu}]", "iv", &["a", "A"]),
    ("[\\P{Lu}]", "iv", &["A", "!"]),
    ("[^\\p{Lu}]", "iv", &["A", "!"]),
    ("[\\w--k]", "iv", &["\u{212A}", "j"]),
    ("[Kk]", "iv", &["\u{212A}", "x"]),
    ("\\p{RGI_Emoji}", "v", &["\u{1F1FA}\u{1F1F8}", "\u{231A}", "a"]),
    ("\\p{Emoji_Keycap_Sequence}", "v", &["#\u{FE0F}\u{20E3}", "#"]),
    ("\\p{Basic_Emoji}+", "v", &["\u{231A}\u{231B}", "\u{00A9}\u{FE0F}"]),
    ("^\\p{RGI_Emoji}$", "v", &["\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F466}"]),
    ("[\\p{RGI_Emoji}]", "v", &["\u{1F1FA}\u{1F1F8}x"]),
    ("[\\p{Basic_Emoji}\\q{xy}]+", "v", &["\u{231A}xy", "x"]),
    // -- modifiers ---------------------------------------------------------
    ("(?i:a)b", "", &["Ab", "AB", "ab"]),
    ("(?-i:a)b", "i", &["aB", "Ab"]),
    ("(?i:(?-i:a)b)", "", &["aB", "Ab"]),
    ("(?m:^b)", "", &["a\nb"]),
    ("(?s:.)(.)", "", &["\n\n", "\na"]),
    ("(?i:σ)", "", &["ς", "Σ"]),
    ("(?i:\\w)", "u", &["ſ", "a"]),
    ("(?i:(a)\\1)", "", &["aA"]),
    ("(?ims-:a.$)", "", &["A\n"]),
    ("(?i:a)(?:b)(?i:c)", "", &["AbC", "ABC"]),
    // -- adversarial backtracking (small enough for the live engine) -------
    ("(a+)+$", "", &["aaaaaaaaaaaaaaaa!", "aaaaaaaaaaaaaaaa"]),
    ("(a|a)+$", "", &["aaaaaaaaaaaa!"]),
    ("(a*)*c", "", &["aaaaaaaaaaaaaaab"]),
    ("(x+x+)+y", "", &["xxxxxxxxxx", "xxxxxxxxxxy"]),
    ("(?:a|ab)*c", "", &["ababababababababc"]),
    // -- syntax errors (verdict agreement rows) ----------------------------
    ("^*", "", &["x"]),
    ("a**", "", &["x"]),
    ("a{2,1}", "", &["x"]),
    ("[z-a]", "", &["x"]),
    ("(?<a>x)(?<a>y)", "", &["x"]),
    ("(?<a>x)((?<a>y)|z)", "", &["x"]),
    ("(?<a>x)\\k<b>", "", &["x"]),
    ("(?i-i:a)", "", &["x"]),
    ("(?q:a)", "", &["x"]),
    ("]", "u", &["x"]),
    ("a{", "u", &["x"]),
    ("\\a", "u", &["x"]),
    ("\\8", "u", &["x"]),
    ("\\p{Bogus}", "u", &["x"]),
    ("\\p{RGI_Emoji}", "u", &["x"]),
    ("[a-\\d]", "u", &["x"]),
    ("\\u{110000}", "u", &["x"]),
    ("[a-]", "v", &["x"]),
    ("[&&]", "v", &["x"]),
    ("[ab--c]", "v", &["x"]),
    ("[^\\q{ab}]", "v", &["x"]),
    ("\\P{RGI_Emoji}", "v", &["x"]),
    ("[a-c--b]", "v", &["x"]),
    // -- Annex-B refusal rows (Node accepts; we refuse soundly) ------------
    ("\\8", "", &["8"]),
    ("\\1", "", &["\u{1}"]),
    ("{", "", &["{"]),
    ("]", "", &["]"]),
    ("a{,2}", "", &["a{,2}"]),
    ("(?=a)*", "", &["a"]),
    ("[a-\\d]", "", &["a"]),
    ("\\c5", "", &["\\c5"]),
    ("\\a", "", &["a"]),
    ("\\k<a>", "", &["k<a>"]),
    ("\\p{L}", "", &["p{L}"]),
];

/// Sticky/global start-offset cases: (pattern, flags, input, start).
const START_CASES: &[(&str, &str, &str, usize)] = &[
    ("a", "y", "xa", 1),
    ("a", "y", "xa", 0),
    ("a", "g", "axa", 1),
    ("^a", "g", "a\na", 1),
    ("\\bb", "g", "ab ba", 2),
    ("(?<=a)b", "y", "ab", 1),
    (".", "gu", "\u{1F600}a", 2),
    (".", "yu", "\u{1F600}a", 2),
    ("", "y", "ab", 2),
    ("a$", "y", "ba", 1),
    // Mid-surrogate-pair lastIndex rounds down to the code point start.
    (".", "gu", "\u{1F600}a", 1),
    (".", "yu", "\u{1F600}a", 1),
    ("a", "gu", "\u{1F600}a", 1),
    (".", "g", "\u{1F600}a", 1), // non-unicode: the trail unit itself
];

fn u16v(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

struct Triple {
    pattern: Vec<u16>,
    flags: String,
    input: Vec<u16>,
    start: usize,
    origin: &'static str,
}

fn battery() -> Vec<Triple> {
    let mut v = Vec::new();
    for (p, f, inputs) in FAMILIES {
        for input in *inputs {
            v.push(Triple {
                pattern: u16v(p),
                flags: f.to_string(),
                input: u16v(input),
                start: 0,
                origin: "family",
            });
        }
    }
    for (p, f, input, start) in START_CASES {
        v.push(Triple {
            pattern: u16v(p),
            flags: f.to_string(),
            input: u16v(input),
            start: *start,
            origin: "family",
        });
    }
    // Lone-surrogate inputs (not expressible as &str).
    let lone_cases: Vec<(Vec<u16>, &str, Vec<u16>)> = vec![
        (u16v("\\uD83D"), "u", vec![0xD83D, 0x41]),
        (u16v("\\uD83D"), "u", vec![0xD83D, 0xDE00]),
        (u16v("."), "u", vec![0xDE00]),
        (u16v("[\\uD800-\\uDBFF]"), "u", vec![0xD83D, 0xDE00]),
        (u16v("[\\uD800-\\uDBFF]"), "", vec![0xD83D, 0xDE00]),
        (u16v("\\uDE00"), "u", vec![0xD83D, 0xDE00]),
    ];
    for (pattern, f, input) in lone_cases {
        v.push(Triple {
            pattern,
            flags: f.to_string(),
            input,
            start: 0,
            origin: "family",
        });
    }
    // Corpus-derived triples (best-effort test262 scrape), if generated.
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data/corpus_triples.json");
    if let Ok(text) = std::fs::read_to_string(&corpus) {
        let val: serde_json::Value = serde_json::from_str(&text).expect("corpus json");
        for row in val.as_array().expect("corpus array") {
            let row = row.as_array().unwrap();
            let units = |v: &serde_json::Value| -> Vec<u16> {
                v.as_array()
                    .unwrap()
                    .iter()
                    .map(|x| x.as_u64().unwrap() as u16)
                    .collect()
            };
            v.push(Triple {
                pattern: units(&row[0]),
                flags: row[1].as_str().unwrap().to_string(),
                input: units(&row[2]),
                start: 0,
                origin: "corpus",
            });
        }
    }
    v
}

// ---------------------------------------------------------------------------
// Node oracle via the trace driver
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq)]
enum NodeOut {
    Syntax,
    OtherThrow(String),
    NoMatch,
    Match {
        index: usize,
        groups: Vec<Option<Vec<u16>>>, // [0] = whole match
        named: Option<Vec<(Vec<u16>, Option<Vec<u16>>)>>,
    },
    TooLong,
}

fn units_json(u: &[u16]) -> String {
    let items: Vec<String> = u.iter().map(|x| x.to_string()).collect();
    format!("[{}]", items.join(","))
}

fn gen_js(chunk: &[&Triple]) -> String {
    let mut js = String::new();
    js.push_str(
        r#"'use strict';
function fromUnits(a) { let s = ""; for (let i = 0; i < a.length; i++) s += String.fromCharCode(a[i]); return s; }
function toUnits(s) { if (s === undefined || s === null) return null; const r = []; for (let i = 0; i < s.length; i++) r.push(s.charCodeAt(i)); return r; }
function runCase(p, f, inp, start) {
  let out;
  try {
    const re = new RegExp(fromUnits(p), f);
    if (f.includes("g") || f.includes("y")) re.lastIndex = start;
    const r = re.exec(fromUnits(inp));
    if (r === null) out = { r: null };
    else {
      const a = []; for (let i = 0; i < r.length; i++) a.push(toUnits(r[i]));
      let g = null;
      if (r.groups !== undefined) {
        g = [];
        for (const k of Object.keys(r.groups)) g.push([toUnits(k), toUnits(r.groups[k])]);
      }
      out = { r: { i: r.index, a, g } };
    }
  } catch (e) {
    out = { x: (e instanceof SyntaxError) ? "syntax" : ("other:" + e.constructor.name) };
  }
  let s = JSON.stringify(out);
  if (s.length > 3900) s = JSON.stringify({ x: "toolong" });
  console.log(s);
}
"#,
    );
    for t in chunk {
        js.push_str(&format!(
            "runCase({}, {}, {}, {});\n",
            units_json(&t.pattern),
            serde_json::to_string(&t.flags).unwrap(),
            units_json(&t.input),
            t.start
        ));
    }
    js
}

fn run_node_chunk(node: &str, driver: &std::path::Path, chunk: &[&Triple], tag: usize) -> Vec<NodeOut> {
    let dir = std::env::temp_dir().join(format!(
        "trust-js-regexp-diff-{}-{}",
        std::process::id(),
        tag
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let js_path = dir.join("cases.js");
    std::fs::write(&js_path, gen_js(chunk)).unwrap();
    let manifest_path = dir.join("manifest.json");
    let manifest = serde_json::json!({
        "includes": [],
        "source": js_path.to_str().unwrap(),
        "mode": "bare",
        "kind": "script",
    });
    let mut f = std::fs::File::create(&manifest_path).unwrap();
    f.write_all(serde_json::to_string(&manifest).unwrap().as_bytes())
        .unwrap();
    drop(f);

    let out = Command::new(node)
        .arg(driver)
        .arg(&manifest_path)
        .output()
        .expect("spawn node trace driver");
    let stdout = String::from_utf8_lossy(&out.stdout);
    const SENTINEL: &str = "__TRUST_JS_TRACE_V1__";
    let line = stdout
        .lines()
        .find(|l| l.starts_with(SENTINEL))
        .unwrap_or_else(|| panic!("no trace sentinel in driver output: {stdout}"));
    let trace: serde_json::Value = serde_json::from_str(&line[SENTINEL.len()..]).unwrap();
    assert_eq!(
        trace["completion"]["k"], "normal",
        "driver completion not normal: {}",
        trace["completion"]
    );
    let mut outs = Vec::new();
    for ev in trace["events"].as_array().unwrap() {
        if ev["k"] != "stdout" {
            continue;
        }
        let projected = ev["v"][0]["v"].as_str().expect("projected string");
        // Undo the driver's escapeString (JSON-compatible escaping).
        let payload: String =
            serde_json::from_str(&format!("\"{projected}\"")).expect("unescape projection");
        let val: serde_json::Value = serde_json::from_str(&payload).expect("payload json");
        outs.push(parse_node_out(&val));
    }
    std::fs::remove_dir_all(&dir).ok();
    outs
}

fn parse_node_out(v: &serde_json::Value) -> NodeOut {
    if let Some(x) = v.get("x").and_then(|x| x.as_str()) {
        return match x {
            "syntax" => NodeOut::Syntax,
            "toolong" => NodeOut::TooLong,
            other => NodeOut::OtherThrow(other.to_string()),
        };
    }
    let r = v.get("r").expect("r");
    if r.is_null() {
        return NodeOut::NoMatch;
    }
    let units = |v: &serde_json::Value| -> Option<Vec<u16>> {
        if v.is_null() {
            None
        } else {
            Some(
                v.as_array()
                    .unwrap()
                    .iter()
                    .map(|x| x.as_u64().unwrap() as u16)
                    .collect(),
            )
        }
    };
    let groups = r["a"]
        .as_array()
        .unwrap()
        .iter()
        .map(&units)
        .collect::<Vec<_>>();
    let named = if r["g"].is_null() {
        None
    } else {
        Some(
            r["g"].as_array()
                .unwrap()
                .iter()
                .map(|pair| {
                    let pair = pair.as_array().unwrap();
                    (units(&pair[0]).unwrap(), units(&pair[1]))
                })
                .collect(),
        )
    };
    NodeOut::Match {
        index: r["i"].as_u64().unwrap() as usize,
        groups,
        named,
    }
}

// ---------------------------------------------------------------------------
// Our side + comparison
// ---------------------------------------------------------------------------

enum OurOut {
    Syntax,
    Refused(String),
    NoMatch,
    Match {
        index: usize,
        groups: Vec<Option<Vec<u16>>>,
        named: Option<Vec<(Vec<u16>, Option<Vec<u16>>)>>,
    },
}

fn run_ours(t: &Triple) -> OurOut {
    let pat: Pattern = match compile(&t.pattern, &t.flags) {
        Ok(p) => p,
        Err(CompileError::Syntax(_)) => return OurOut::Syntax,
        Err(CompileError::Unsupported(m)) => return OurOut::Refused(m),
    };
    let sticky = t.flags.contains('y');
    let r = if sticky {
        pat.exec_sticky_at(&t.input, t.start)
    } else {
        pat.exec_at(&t.input, t.start)
    };
    match r {
        Err(ExecError::Budget) => OurOut::Refused("budget".into()),
        Err(ExecError::Unsupported(m)) => OurOut::Refused(m),
        Ok(None) => OurOut::NoMatch,
        Ok(Some(m)) => {
            let mut groups = vec![Some(t.input[m.index..m.end].to_vec())];
            for c in &m.captures {
                groups.push(c.map(|(s, e)| t.input[s..e].to_vec()));
            }
            // Reconstruct the groups object: one property per distinct name
            // in group-number order; value = the participating group.
            let named = if pat.group_names().is_empty() {
                None
            } else {
                let mut named: Vec<(Vec<u16>, Option<Vec<u16>>)> = Vec::new();
                for (name, gi) in pat.group_names() {
                    let name_units = u16v(name);
                    let val = m.captures[*gi as usize - 1].map(|(s, e)| t.input[s..e].to_vec());
                    if let Some(entry) = named.iter_mut().find(|(n, _)| *n == name_units) {
                        if entry.1.is_none() {
                            entry.1 = val;
                        }
                    } else {
                        named.push((name_units, val));
                    }
                }
                Some(named)
            };
            OurOut::Match {
                index: m.index,
                groups,
                named,
            }
        }
    }
}

fn fmt_triple(t: &Triple) -> String {
    format!(
        "/{}/{} on {:?} start {} [{}]",
        String::from_utf16_lossy(&t.pattern),
        t.flags,
        String::from_utf16_lossy(&t.input),
        t.start,
        t.origin
    )
}

#[test]
fn differential_against_node() {
    let Ok(node) = std::env::var("TRUST_JS_NODE") else {
        eprintln!("==============================================================");
        eprintln!("SKIPPED: regexp differential (set TRUST_JS_NODE=<node binary>)");
        eprintln!("==============================================================");
        return;
    };
    let driver = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-js-trace/js/trace_driver.mjs")
        .canonicalize()
        .expect("trace driver path");

    let triples = battery();
    assert!(
        triples.len() >= 800,
        "battery too small: {} triples",
        triples.len()
    );

    let mut node_outs: Vec<NodeOut> = Vec::new();
    let refs: Vec<&Triple> = triples.iter().collect();
    for (tag, chunk) in refs.chunks(250).enumerate() {
        let outs = run_node_chunk(&node, &driver, chunk, tag);
        assert_eq!(outs.len(), chunk.len(), "driver event count mismatch");
        node_outs.extend(outs);
    }

    let (mut agree, mut refused, mut skipped) = (0u32, 0u32, 0u32);
    let mut refusal_reasons: Vec<String> = Vec::new();
    let mut disagreements: Vec<String> = Vec::new();
    for (t, n) in triples.iter().zip(node_outs.iter()) {
        let ours = run_ours(t);
        match (ours, n) {
            (OurOut::Refused(reason), _) => {
                refused += 1;
                refusal_reasons.push(format!("{}: {reason}", fmt_triple(t)));
            }
            (_, NodeOut::TooLong) | (_, NodeOut::OtherThrow(_)) => skipped += 1,
            (OurOut::Syntax, NodeOut::Syntax) => agree += 1,
            (OurOut::Syntax, _) => {
                disagreements.push(format!("{}: we say Syntax, node matched", fmt_triple(t)));
            }
            (_, NodeOut::Syntax) => {
                disagreements.push(format!("{}: node says Syntax, we compiled", fmt_triple(t)));
            }
            (OurOut::NoMatch, NodeOut::NoMatch) => agree += 1,
            (OurOut::NoMatch, NodeOut::Match { .. }) => {
                disagreements.push(format!("{}: we NoMatch, node matched", fmt_triple(t)));
            }
            (OurOut::Match { .. }, NodeOut::NoMatch) => {
                disagreements.push(format!("{}: we matched, node NoMatch", fmt_triple(t)));
            }
            (
                OurOut::Match { index, groups, named },
                NodeOut::Match { index: ni, groups: ng, named: nn },
            ) => {
                if index != *ni || groups != *ng || !named_eq(&named, nn) {
                    disagreements.push(format!(
                        "{}: match detail mismatch (ours i={index} {groups:?} {named:?}; node i={ni} {ng:?} {nn:?})",
                        fmt_triple(t)
                    ));
                } else {
                    agree += 1;
                }
            }
        }
    }

    let total = triples.len();
    let corpus_n = triples.iter().filter(|t| t.origin == "corpus").count();
    eprintln!("regexp differential: {total} triples ({corpus_n} corpus-derived)");
    eprintln!(
        "  agree {agree} / refused {refused} / skipped {skipped} / DISAGREE {}",
        disagreements.len()
    );
    for r in refusal_reasons.iter().take(30) {
        eprintln!("  refusal: {r}");
    }
    for d in disagreements.iter().take(40) {
        eprintln!("  DISAGREEMENT: {d}");
    }
    assert!(
        disagreements.is_empty(),
        "{} differential disagreements",
        disagreements.len()
    );
}

fn named_eq(
    a: &Option<Vec<(Vec<u16>, Option<Vec<u16>>)>>,
    b: &Option<Vec<(Vec<u16>, Option<Vec<u16>>)>>,
) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => {
            let mut x = x.clone();
            let mut y = y.clone();
            x.sort();
            y.sort();
            x == y
        }
        _ => false,
    }
}
