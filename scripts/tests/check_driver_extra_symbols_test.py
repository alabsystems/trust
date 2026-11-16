#!/usr/bin/env python3
"""Controls for scripts/check_driver_extra_symbols.py (push row `fast.driver-extra-symbols`).

Three layers, each against the real checker (a copy in a throwaway repository, or the
module loaded from its file; no logic is restated here):

  * the tokenizer and the two list readers, on the value forms that make a name differ
    from its string (`Underscore: "_"`, a raw string, an escape, a `{` inside a string);
  * the verdict, end to end, in throwaway git repositories: a clean tree, the measured
    collision, collisions by VALUE under different names, a same-name pair that is NOT a
    collision, the generated digit and letter prefill, a repeat inside one list, a driver
    this check has never heard of, and every way the reading can stop being trustworthy
    (a macro that drifted from the model, a count the compiler's pin contradicts);
  * which tree is judged: the working tree, `--rev`, and the pushed trees through
    TRUST_PUSHED_REFS in both directions (a bad push from a clean checkout is refused, a
    good push from a dirty checkout is not).

Last, the checkout's own two lists are read and compared with an independent line reader,
so a parser that quietly read less than the file holds cannot pass.

The repositories are built under a temporary directory with an empty HOME and no global
or system git config; nothing of this checkout is modified.
"""

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

import importlib.util
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
REPO = SCRIPTS.parent
CHECKER = SCRIPTS / "check_driver_extra_symbols.py"
SPEC = importlib.util.spec_from_file_location("check_driver_extra_symbols", CHECKER)
check = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = check
SPEC.loader.exec_module(check)

ZERO = "0" * 40

# The statements the checker pins, as the macro source holds them (layout differs on
# purpose: the comparison is over tokens).
SYMBOLS_MACRO = """\
mod kw {
    syn::custom_keyword!(Keywords);
    syn::custom_keyword!(Symbols);
    // a comment between two of them changes nothing
    syn::custom_keyword!(AppendOnly);
}
fn symbols_with_errors() {
    let prefill_ints = 0..=9;
    let prefill_letters = ('A'..='Z').chain('a'..='z');
    let value = match &symbol.value {
        Value::SameAsName => name.to_string(),
        Value::String(lit) => lit.value(),
        Value::Env(..) => continue,
    };
    for s in prefill_ints.map(|n| n.to_string()).chain(prefill_letters.map(|c| c.to_string())) {
        entries.insert(Span::call_site(), &s, &mut errors);
    }
    quote! {
        pub(crate) fn with_extra_symbols(extra_symbols: &[&'static str]) -> Self {
            Interner::prefill(&[#prefill_stream], extra_symbols,)
        }
    };
}
"""

# 2 keywords + 4 non-env symbols = 6, which the pin below states.
SYMBOL_RS = """\
symbols! {
    // `}` and `{` in a comment, and in a value below, must not end a section
    Keywords {
        Underscore:         "_",
        As:                 "as",
    }
    Symbols {
        Vec,
        bsq: "\\\\'",
        env_CFG_RELEASE: env!("CFG_RELEASE"),
        proc_dash_macro: "proc-macro",
        root: "{{root}}",
    }
    AppendOnly {
        VecDeque,
        BinaryHeap,
    }
}
const _: () = assert!(SYMBOL_DIGITS_BASE == 6, "preinterned symbol indices moved");
"""

LIST_HEAD = """\
#![allow(non_upper_case_globals)]
#[doc(no_inline)]
pub use rustc_span::sym::*;

macro_rules! val {
    ($name:ident) => {
        stringify!($name)
    };
    ($name:ident $value:literal) => {
        $value
    };
}

macro_rules! generate {
    ($($name:ident $(: $value:literal)? ,)*) => {
        /// To be supplied to `rustc_interface::Config`
        pub const EXTRA_SYMBOLS: &[&str] = &[
            $(
                val!($name $($value)?),
            )*
        ];
    };
}

"""


def list_file(*entries):
    return LIST_HEAD + "generate! {\n" + "".join(f"    {entry},\n" for entry in entries) + "}\n"


BASE = {
    "compiler/rustc_macros/src/symbols.rs": SYMBOLS_MACRO,
    "compiler/rustc_span/src/symbol.rs": SYMBOL_RS,
    "compiler/rustc_span/src/lib.rs": """\
impl SessionGlobals {
    pub fn new(edition: Edition, extra_symbols: &[&'static str], sm: Option<Inputs>) -> SessionGlobals {
        SessionGlobals { symbol_interner: symbol::Interner::with_extra_symbols(extra_symbols) }
    }
}
pub fn create_session_globals_then<R>(edition: Edition, extra_symbols: &[&'static str], f: impl FnOnce() -> R) -> R {
    let session_globals = SessionGlobals::new(edition, extra_symbols, None);
    SESSION_GLOBALS.set(&session_globals, f)
}
pub fn create_default_session_globals_then<R>(f: impl FnOnce() -> R) -> R {
    create_session_globals_then(edition::DEFAULT_EDITION, &[], None, f)
}
""",
    "compiler/rustc_interface/src/interface.rs": """\
pub struct Config {
    /// An extra set of symbols to add to the symbol interner
    pub extra_symbols: Vec<&'static str>,
}
pub fn run_compiler(config: Config) {
    util::run_in_thread_pool_with_globals(config.opts.edition, &config.extra_symbols, |gcx| {});
}
""",
    "compiler/rustc_interface/src/util.rs": """\
pub(crate) fn run_in_thread_pool_with_globals(edition: Edition, extra_symbols: &[&'static str], f: F) {
    rustc_span::create_session_globals_then(
        edition,
        extra_symbols,
        || f(CurrentGcx::new()),
    )
}
""",
    "compiler/rustc_driver_impl/src/lib.rs": "fn config() -> Config { Config { register_lints: None, extra_symbols: Vec::new(), } }\n",
    "src/librustdoc/lib.rs": "fn main_args() { rustc_span::create_session_globals_then(options.edition, &[], None, || {}) }\n",
    "src/tools/tippy/clippy_utils/src/sym.rs": list_file("Any", 'CRLF: "\\r\\n"', "abs"),
    "src/tools/tippy/src/driver.rs": """\
use rustc_span::create_session_globals_then; // an import is not a call
impl rustc_driver::Callbacks for ClippyCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        config.extra_symbols = sym::EXTRA_SYMBOLS.into();
    }
}
""",
    "src/tools/miri/src/sym.rs": list_file("sys_mutex_lock", "sys_mutex_unlock"),
    "src/tools/miri/src/bin/miri.rs": "fn config(config: &mut Config) { config.extra_symbols = miri::sym::EXTRA_SYMBOLS.into(); }\n",
}

TIPPY_LIST = "src/tools/tippy/clippy_utils/src/sym.rs"
MIRI_LIST = "src/tools/miri/src/sym.rs"


class Fixture(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="driver-extra-symbols-test."))
        self.addCleanup(shutil.rmtree, self.tmp, ignore_errors=True)
        (self.tmp / "home").mkdir()
        # Hermetic under the hook: it exports TRUST_PUSHED_REFS / TRUST_PUSH_REMOTE, and
        # an operator's git config must not reach the fixture commits.
        self.env = {
            key: value
            for key, value in os.environ.items()
            if not key.startswith(("TRUST_", "GIT_"))
        }
        self.env.update(
            HOME=str(self.tmp / "home"),
            GIT_CONFIG_GLOBAL=os.devnull,
            GIT_CONFIG_NOSYSTEM="1",
            GIT_AUTHOR_NAME="fixture",
            GIT_AUTHOR_EMAIL="fixture@example.invalid",
            GIT_COMMITTER_NAME="fixture",
            GIT_COMMITTER_EMAIL="fixture@example.invalid",
        )
        self.repo = self.tmp / "repo"
        (self.repo / "scripts").mkdir(parents=True)
        shutil.copy(CHECKER, self.repo / "scripts" / CHECKER.name)
        self.git("init", "-q", "-b", "main")
        self.write(BASE)
        self.base = self.commit("base")

    def git(self, *args):
        proc = subprocess.run(
            ["git", "-C", str(self.repo), "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", *args],
            capture_output=True, text=True, env=self.env,
        )
        self.assertEqual(proc.returncode, 0, f"git {' '.join(args)}: {proc.stderr}")
        return proc.stdout.strip()

    def write(self, files):
        for rel, text in files.items():
            path = self.repo / rel
            if text is None:
                path.unlink()
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")

    def commit(self, message):
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def run_check(self, *args, pushed=None):
        env = dict(self.env)
        if pushed is not None:
            env["TRUST_PUSHED_REFS"] = pushed
        proc = subprocess.run(
            [sys.executable, "-B", str(self.repo / "scripts" / CHECKER.name), *args],
            capture_output=True, text=True, env=env, cwd=str(self.tmp),
        )
        return proc.returncode, proc.stdout + proc.stderr

    def expect(self, code, *needles, files=None, args=(), pushed=None, absent=()):
        if files:
            self.write(files)
        got, output = self.run_check(*args, pushed=pushed)
        self.assertEqual(got, code, output)
        for needle in needles:
            self.assertIn(needle, output)
        for needle in absent:
            self.assertNotIn(needle, output)
        return output


class Tokenizer(unittest.TestCase):
    def values(self, source):
        return [tok.text for tok in check.lex(source, "<test>") if tok.kind == "str"]

    def test_a_string_token_carries_its_decoded_value(self):
        self.assertEqual(self.values(r'"\r\n"'), ["\r\n"])
        self.assertEqual(self.values(r'"\""'), ['"'])
        self.assertEqual(self.values(r'"\\\'"'), ["\\'"])
        self.assertEqual(self.values("r\"\\'\""), ["\\'"])
        self.assertEqual(self.values('r#"a"b"#'), ['a"b'])
        self.assertEqual(self.values(r'"\x41\u{1F600}\u{00_e9}\0"'), ["A\U0001F600\u00e9\0"])
        self.assertEqual(self.values('"a\\\n      b"'), ["ab"])

    def test_a_cooked_and_a_raw_spelling_of_one_string_are_equal(self):
        self.assertEqual(self.values(r'"\\\'"'), self.values("r\"\\'\""))

    def test_comments_vanish_and_strings_shield_their_braces(self):
        tokens = check.lex('a /* x /* nested } */ { */ , "}{" // tail }\n b', "<test>")
        self.assertEqual([(t.kind, t.text) for t in tokens], [("ident", "a"), ("punct", ","), ("str", "}{"), ("ident", "b")])

    def test_character_literals_lifetimes_and_trust_primes(self):
        kinds = [(t.kind, t.text) for t in check.lex("'a' '\\'' b'x' &'static str x' == y''", "<test>")]
        self.assertEqual(
            kinds,
            [("lit", "'a'"), ("lit", "'\\''"), ("lit", "b'x'"), ("punct", "&"), ("lifetime", "'static"), ("ident", "str"),
             ("ident", "x"), ("punct", "'"), ("punct", "="), ("punct", "="), ("ident", "y"), ("punct", "'"), ("punct", "'")],
        )

    def test_byte_and_c_strings_are_not_symbol_values(self):
        self.assertEqual([t.kind for t in check.lex('b"x" c"y" br#"z"#', "<test>")], ["lit", "lit", "lit"])

    def test_what_cannot_be_read_is_an_error_naming_the_line(self):
        for source, what in (('"never closed', "never closes"), ("/* open", "never closes"), ('"\\q"', "unknown escape")):
            with self.assertRaises(check.GateError) as caught:
                check.lex("\n\n" + source, "f.rs")
            self.assertIn("f.rs:3", str(caught.exception))
            self.assertIn(what, str(caught.exception))

    def test_line_numbers_survive_multi_line_tokens(self):
        tokens = check.lex('/* one\n two */ a "x\ny" b\n c', "<test>")
        self.assertEqual([(t.text, t.line) for t in tokens], [("a", 2), ("x\ny", 2), ("b", 3), ("c", 4)])


class Readers(unittest.TestCase):
    def test_predefined_set_is_what_the_macro_builds(self):
        pre = check.read_predefined(SYMBOL_RS, SYMBOLS_MACRO)
        self.assertEqual(pre.counts, {"Keywords": 2, "Symbols": 4, "prefill": 62, "AppendOnly": 2})
        self.assertEqual(pre.pin, 6)
        self.assertEqual([entry.name for entry in pre.env], ["env_CFG_RELEASE"])
        self.assertEqual(len(pre.by_value), 2 + 4 + 62 + 2)
        for value, section, name in (
            ("_", "Keywords", "Underscore"), ("as", "Keywords", "As"), ("Vec", "Symbols", "Vec"),
            ("\\'", "Symbols", "bsq"), ("proc-macro", "Symbols", "proc_dash_macro"), ("{{root}}", "Symbols", "root"),
            ("VecDeque", "AppendOnly", "VecDeque"), ("0", "prefill", "0"), ("9", "prefill", "9"),
            ("A", "prefill", "A"), ("Z", "prefill", "Z"), ("a", "prefill", "a"), ("z", "prefill", "z"),
        ):
            self.assertEqual(pre.by_value[value][:2], (section, name))
        # A NAME is not a predefined string unless it is also a value.
        for name in ("Underscore", "As", "bsq", "proc_dash_macro", "root", "env_CFG_RELEASE", "CFG_RELEASE"):
            self.assertNotIn(name, pre.by_value)
        self.assertEqual(pre.repeats, [])

    def test_a_count_the_pin_contradicts_gives_no_verdict(self):
        for text, what in (
            (SYMBOL_RS.replace("== 6", "== 7"), "SYMBOL_DIGITS_BASE == 7"),
            (SYMBOL_RS.replace("        Vec,\n", ""), "counts 5"),
            (SYMBOL_RS.replace("const _: () = assert!(SYMBOL_DIGITS_BASE == 6", "const _: () = assert!(true"), "no `SYMBOL_DIGITS_BASE"),
        ):
            with self.assertRaises(check.GateError) as caught:
                check.read_predefined(text, SYMBOLS_MACRO)
            self.assertIn(what, str(caught.exception))

    def test_a_value_the_macro_would_refuse_gives_no_verdict(self):
        for old, new, what in (
            ('root: "{{root}}"', "root: 7", "cannot read"),
            ('root: "{{root}}"', 'root: concat!("a", "b")', "cannot read"),
            ('As:                 "as",', "As,", "has no `: \"value\"`"),
            ("    AppendOnly {\n        VecDeque,", '    AppendOnly {\n        VecDeque: env!("X"),', "cannot read"),
            ("    AppendOnly {", "    Extra { x, }\n    AppendOnly {", "`symbols!` holds `Extra`"),
        ):
            self.assertIn(old, SYMBOL_RS)
            with self.assertRaises(check.GateError) as caught:
                check.read_predefined(SYMBOL_RS.replace(old, new), SYMBOLS_MACRO)
            self.assertIn(what, str(caught.exception))

    def test_a_repeat_inside_the_predefined_list_is_reported(self):
        text = SYMBOL_RS.replace("        BinaryHeap,\n", '        Again: "as",\n        Nine: "9",\n')
        repeats = check.read_predefined(text, SYMBOLS_MACRO).repeats
        self.assertEqual(len(repeats), 2)
        self.assertIn("Keywords `As`", repeats[0])
        self.assertIn("the generated prefill", repeats[1])

    def test_every_pinned_macro_statement_is_load_bearing(self):
        for what, source in check.SYMBOLS_MACRO_MODEL:
            line = source.split(";")[0].split(",")[0].strip()
            self.assertIn(line, SYMBOLS_MACRO, what)
            with self.assertRaises(check.GateError) as caught:
                check.read_predefined(SYMBOL_RS, SYMBOLS_MACRO.replace(line, "let changed = ()"))
            self.assertIn("no longer contains " + what, str(caught.exception))
        # ... and a different prefill RANGE is a different macro, not a formatting change.
        with self.assertRaises(check.GateError):
            check.read_predefined(SYMBOL_RS, SYMBOLS_MACRO.replace("0..=9", "0..=15"))

    def test_driver_list_values(self):
        entries = check.read_driver_list(
            list_file("Any", 'CRLF: "\\r\\n"', "BACKSLASH_SINGLE_QUOTE: r\"\\'\"", 'Cargo_toml: "Cargo.toml"', 'DOUBLE_QUOTE: "\\""'),
            "sym.rs",
        )
        self.assertEqual(
            [(entry.name, entry.value) for entry in entries],
            [("Any", "Any"), ("CRLF", "\r\n"), ("BACKSLASH_SINGLE_QUOTE", "\\'"), ("Cargo_toml", "Cargo.toml"), ("DOUBLE_QUOTE", '"')],
        )
        self.assertEqual(check.read_driver_list(list_file(), "sym.rs"), [])

    def test_a_driver_list_this_check_cannot_read_gives_no_verdict(self):
        good = list_file("Any", "abs")
        for text, what in (
            (good.replace("    abs,\n", "    abs\n"), "has no `,`"),
            (good.replace("    abs,\n", "    abs: 3,\n"), "cannot read"),
            (good.replace("    abs,\n", '    abs: b"abs",\n'), "cannot read"),
            (good.replace("    abs,\n", '    abs: env!("X"),\n'), "cannot read"),
            (good + "generate! {\n    more,\n}\n", "exactly one `generate! { .. }` call, found 2"),
            (LIST_HEAD, "exactly one `generate! { .. }` call, found 0"),
            (good.replace("stringify!($name)", "concat!(stringify!($name), \"!\")"), "no longer contains `val!`"),
            (good.replace("$(: $value:literal)? ,)*", "$(= $value:literal)? ,)*"), "no longer contains `generate!`'s matcher"),
            (good.replace("pub const EXTRA_SYMBOLS: &[&str] = &[", "pub const OTHER: &[&str] = &["), "no longer contains `EXTRA_SYMBOLS`"),
        ):
            with self.assertRaises(check.GateError) as caught:
                check.read_driver_list(text, "sym.rs")
            self.assertIn(what, str(caught.exception))


class Verdict(Fixture):
    def test_clean_tree(self):
        output = self.expect(
            0,
            "SUBJECT: the working tree at",
            "predefined: 70 strings",
            "Keywords 2 + Symbols 4 = 6 (the file's own SYMBOL_DIGITS_BASE pin)",
            'NOT JUDGED  `env_CFG_RELEASE` (line 10) = env!("CFG_RELEASE")',
            "driver tippy: 3 extra symbols in src/tools/tippy/clippy_utils/src/sym.rs; handed to the interner at src/tools/tippy/src/driver.rs:4",
            "driver miri: 2 extra symbols",
            "check_driver_extra_symbols: OK",
            absent=("COLLISION", "UNREAD", "REPEAT"),
        )
        self.assertRegex(output, r"mechanism: \d+ use\(s\) of it in 8 file\(s\)")

    def test_the_measured_collision_names_both_sides(self):
        output = self.expect(
            1,
            '`BinaryHeap` (src/tools/tippy/clippy_utils/src/sym.rs:27) = "BinaryHeap" is pre-interned by rustc_span: '
            "AppendOnly `BinaryHeap`, compiler/rustc_span/src/symbol.rs:16",
            '`VecDeque` (src/tools/tippy/clippy_utils/src/sym.rs:29) = "VecDeque" is pre-interned by rustc_span: '
            "AppendOnly `VecDeque`, compiler/rustc_span/src/symbol.rs:15",
            "check_driver_extra_symbols: FAIL — 2 finding(s).",
            "duplicate symbols in the rustc symbol list and the extra symbols added by the driver",
            files={TIPPY_LIST: list_file("Any", "BinaryHeap", "CLIPPY_ARGS", "VecDeque", "abs")},
        )
        self.assertEqual(output.count("COLLISION"), 2)

    def test_the_string_is_compared_not_the_name(self):
        # Different names, one string: each is a collision.
        output = self.expect(
            1,
            '`Blank` (src/tools/tippy/clippy_utils/src/sym.rs:26) = "_" is pre-interned by rustc_span: Keywords `Underscore`',
            '`PM` (src/tools/tippy/clippy_utils/src/sym.rs:27) = "proc-macro" is pre-interned by rustc_span: Symbols `proc_dash_macro`',
            "`RAW` (src/tools/tippy/clippy_utils/src/sym.rs:28) = \"\\\\'\" is pre-interned by rustc_span: Symbols `bsq`",
            '`Root` (src/tools/tippy/clippy_utils/src/sym.rs:29) = "{{root}}" is pre-interned by rustc_span: Symbols `root`',
            files={TIPPY_LIST: list_file('Blank: "_"', 'PM: "proc-macro"', "RAW: r\"\\'\"", 'Root: "{{root}}"')},
        )
        self.assertEqual(output.count("COLLISION"), 4)

    def test_one_name_two_strings_is_not_a_collision(self):
        # `As` the keyword is "as"; a driver's `As` is "As". `Underscore`, `bsq` and
        # `env_CFG_RELEASE` are names of predefined entries, not their strings.
        self.expect(
            0,
            "driver tippy: 5 extra symbols",
            files={TIPPY_LIST: list_file("As", "Underscore", "bsq", "env_CFG_RELEASE", 'Vec2: "vec"')},
            absent=("COLLISION",),
        )

    def test_the_generated_digits_and_letters_are_predefined(self):
        output = self.expect(
            1,
            '`A` (src/tools/miri/src/sym.rs:26) = "A" is pre-interned by rustc_span: one of the generated digit and letter symbols',
            '`nine` (src/tools/miri/src/sym.rs:27) = "9" is pre-interned',
            '`z` (src/tools/miri/src/sym.rs:28) = "z" is pre-interned',
            "driver tippy: 3 extra symbols",
            files={MIRI_LIST: list_file("A", 'nine: "9"', "z", 'ten: "10"', "AA")},
        )
        self.assertEqual(output.count("COLLISION"), 3)

    def test_a_string_twice_in_one_list_panics_too(self):
        self.expect(
            1,
            '`Second` (src/tools/tippy/clippy_utils/src/sym.rs:27) = "abs" is also `abs` (line 26) in the same list',
            files={TIPPY_LIST: list_file("abs", 'Second: "abs"')},
            absent=("COLLISION",),
        )

    def test_two_drivers_may_share_a_string(self):
        self.expect(0, files={TIPPY_LIST: list_file("shared"), MIRI_LIST: list_file("shared")}, absent=("REPEAT",))

    def test_a_driver_this_check_has_never_heard_of_is_refused(self):
        for label, body in (
            ("its own list", "fn config(config: &mut Config) { config.extra_symbols = newdrv::sym::EXTRA_SYMBOLS.into(); }\n"),
            ("an inline list", 'fn config(config: &mut Config) { config.extra_symbols = vec!["VecDeque"]; }\n'),
            ("a field initializer", 'fn config() -> Config { Config { extra_symbols: vec!["x"], } }\n'),
            ("a push", 'fn config(config: &mut Config) { config.extra_symbols.push("x"); }\n'),
            ("a wrapper", "fn run(extra_symbols: &[&'static str]) {}\n"),
            ("a forwarded field", "fn run(config: Config) { helper(config.edition, config.extra_symbols, 1); }\n"),
            ("a shorthand initializer", "fn config(extra_symbols: Vec<&'static str>) -> Config { Config { extra_symbols, ..base() } }\n"),
            ("session globals", 'fn main() { rustc_span::create_session_globals_then(edition, &["x"], None, || {}) }\n'),
            ("a turbofish", 'fn main() { create_session_globals_then::<()>(edition, EXTRA, None, || {}) }\n'),
            ("SessionGlobals::new", "fn main() { let g = SessionGlobals::new(edition, crate::EXTRA, None); }\n"),
        ):
            with self.subTest(label):
                output = self.expect(1, "UNREAD      src/tools/newdrv/src/main.rs:1:", files={"src/tools/newdrv/src/main.rs": body})
                self.assertIn("add it to DRIVERS", output)
        # The same file with no extra symbols is nobody's business.
        self.expect(
            0,
            files={"src/tools/newdrv/src/main.rs": "fn c() -> Config { Config { extra_symbols: Vec::new() } }\n"
                   "fn m() { rustc_span::create_session_globals_then(e, &[], None, || {}); let g = SessionGlobals::new(e, &[], None); }\n"},
            absent=("UNREAD",),
        )

    def test_a_list_reference_counts_only_in_the_file_drivers_names(self):
        # tippy's own spelling, in a file DRIVERS does not name for any driver.
        self.expect(
            1,
            "UNREAD      src/tools/tippy/src/main.rs:1:",
            files={"src/tools/tippy/src/main.rs": "fn c(config: &mut Config) { config.extra_symbols = sym::EXTRA_SYMBOLS.into(); }\n"},
        )

    def test_the_scan_stops_where_the_docstring_says(self):
        body = 'fn config(config: &mut Config) { config.extra_symbols = vec!["VecDeque"]; }\n'
        self.expect(
            0,
            files={"tests/ui-fulldeps/own_config.rs": body, "vendor/dep/src/lib.rs": body,
                   "src/llvm-project/x.rs": body, "src/doc/book/x.rs": body, "docs/x.rs": body},
            absent=("UNREAD",),
        )
        for inside in ("crates/a/src/lib.rs", "targo-trust/src/x.rs", "library/std/src/x.rs", "compiler/rustc_x/src/lib.rs"):
            with self.subTest(inside):
                self.expect(1, f"UNREAD      {inside}:1:", files={inside: body})
                self.write({inside: None})

    def test_an_untracked_file_is_part_of_the_working_tree(self):
        self.expect(0)
        self.write({"src/tools/newdrv/src/main.rs": 'fn c(config: &mut Config) { config.extra_symbols = vec!["x"]; }\n'})
        self.assertEqual(self.git("status", "--porcelain", "--", "src/tools/newdrv"), "?? src/tools/newdrv/")
        self.expect(1, "UNREAD      src/tools/newdrv/src/main.rs:1:")

    def test_drivers_rows_the_tree_contradicts(self):
        self.expect(
            0,
            "driver miri: ABSENT from this tree",
            "driver tippy: 3 extra symbols",
            files={MIRI_LIST: None, "src/tools/miri/src/bin/miri.rs": None},
        )
        self.expect(1, "driver miri: MISSING LIST", files={"src/tools/miri/src/bin/miri.rs": BASE["src/tools/miri/src/bin/miri.rs"]})
        self.expect(
            1,
            "NOT HANDED OVER",
            files={MIRI_LIST: BASE[MIRI_LIST], "src/tools/miri/src/bin/miri.rs": "fn config(config: &mut Config) {}\n"},
        )

    def test_what_cannot_be_judged_is_exit_2_never_a_pass(self):
        for label, files, what in (
            ("no predefined list", {"compiler/rustc_span/src/symbol.rs": None}, "compiler/rustc_span/src/symbol.rs is absent"),
            ("no macro", {"compiler/rustc_macros/src/symbols.rs": None}, "compiler/rustc_macros/src/symbols.rs is absent"),
            ("a drifted macro", {"compiler/rustc_macros/src/symbols.rs": SYMBOLS_MACRO.replace("('A'..='Z')", "('A'..='F')")},
             "no longer contains the letter prefill"),
            ("a stale pin", {"compiler/rustc_span/src/symbol.rs": SYMBOL_RS.replace("== 6", "== 9")}, "SYMBOL_DIGITS_BASE == 9"),
            ("an unreadable list", {TIPPY_LIST: list_file("Any").replace("    Any,\n", "    Any: 1,\n")}, "cannot read"),
            ("an untokenizable site", {"src/tools/tippy/src/driver.rs": 'fn f() { config.extra_symbols = "open; }\n'}, "cannot tokenize"),
        ):
            with self.subTest(label):
                output = self.expect(2, what, "COULD NOT JUDGE", files=files, absent=("check_driver_extra_symbols: OK",))
                self.assertNotIn("FAIL", output)
                self.git("checkout", "-q", "--", ".")

    def test_list_prints_what_was_read(self):
        output = self.expect(0, '  extra       CRLF = "\\r\\n"', "  extra       sys_mutex_lock = \"sys_mutex_lock\"", args=("--list",))
        self.assertIn("  list         src/tools/tippy/src/driver.rs:4: extra_symbols = sym : : EXTRA_SYMBOLS . into ( )", output)
        self.assertIn("  empty        compiler/rustc_driver_impl/src/lib.rs:1: extra_symbols : Vec : : new ( )", output)
        self.assertIn("  declaration  compiler/rustc_interface/src/interface.rs:3:", output)
        self.assertIn("  pass-through compiler/rustc_interface/src/interface.rs:6: config . extra_symbols ,", output)


class WhichTree(Fixture):
    def setUp(self):
        super().setUp()
        self.git("checkout", "-q", "-b", "topic")
        self.write({TIPPY_LIST: list_file("Any", "VecDeque")})
        self.bad = self.commit("a colliding list")
        self.git("checkout", "-q", "main")

    def test_rev_reads_the_commit_not_the_checkout(self):
        self.expect(0, "SUBJECT: the working tree at")
        self.expect(1, "SUBJECT: the tree(s) of topic (--rev), not the working tree", "COLLISION   `VecDeque`", args=("--rev", "topic"))
        self.expect(0, f"SUBJECT: the tree(s) of {self.base} (--rev)", args=("--rev", self.base))
        output = self.expect(1, "--- main", "--- topic", args=("--rev", "main", "--rev", "topic"))
        self.assertEqual(output.count("COLLISION"), 1)
        self.expect(2, "does not name a tree", "COULD NOT JUDGE", args=("--rev", "no-such-ref"))

    def test_a_bad_push_from_a_clean_checkout_is_refused(self):
        self.expect(0)  # the checkout itself is clean and on main
        self.expect(
            1,
            f"SUBJECT: the pushed trees (TRUST_PUSHED_REFS: refs/heads/topic {self.bad[:12]}), not the working tree",
            "COLLISION   `VecDeque`",
            pushed=f"refs/heads/topic {self.bad} refs/heads/main {self.base}\n",
        )

    def test_a_good_push_from_a_dirty_checkout_is_not_refused(self):
        self.write({TIPPY_LIST: list_file("Any", "BinaryHeap")})  # uncommitted
        self.expect(1, "SUBJECT: the working tree at", "COLLISION   `BinaryHeap`")
        self.expect(
            0,
            "not the working tree",
            pushed=f"refs/heads/main {self.base} refs/heads/main {ZERO}\n",
            absent=("COLLISION",),
        )

    def test_every_pushed_tree_is_judged_and_deletions_are_not(self):
        output = self.expect(
            1,
            f"--- refs/heads/main {self.base[:12]}",
            f"--- refs/heads/topic {self.bad[:12]}",
            "1 deletion(s) not judged",
            pushed=(
                f"refs/heads/main {self.base} refs/heads/main {ZERO}\n"
                f"refs/heads/topic {self.bad} refs/heads/topic {ZERO}\n"
                f"(delete) {ZERO} refs/heads/gone {self.base}\n"
            ),
        )
        self.assertEqual(output.count("COLLISION"), 1)
        self.expect(0, "SKIPPED: deletion(s) only", pushed=f"(delete) {ZERO} refs/heads/gone {self.base}\n")

    def test_two_refs_at_one_tree_are_judged_once(self):
        output = self.expect(
            1,
            f"refs/heads/topic {self.bad[:12]}, refs/tags/t {self.bad[:12]}",
            pushed=f"refs/heads/topic {self.bad} refs/heads/topic {ZERO}\nrefs/tags/t {self.bad} refs/tags/t {ZERO}\n",
        )
        self.assertEqual(output.count("COLLISION"), 1)

    def test_a_push_this_check_cannot_read_is_not_a_pass(self):
        self.expect(2, "malformed TRUST_PUSHED_REFS line", pushed="refs/heads/main not-a-sha refs/heads/main also-not\n")
        self.expect(2, "does not name a tree", pushed=f"refs/heads/main {'1' * 40} refs/heads/main {ZERO}\n")


class ThisCheckout(unittest.TestCase):
    """The real lists are read whole: an independent line reader must agree."""

    LINE = re.compile(r"^    ([A-Za-z_][A-Za-z0-9_]*)(?::\s*(.+?))?,\s*(?://.*)?$")

    def names_by_line(self, text, opener):
        body = text.split(opener, 1)[1].split("\n}\n", 1)[0]
        return [match.group(1) for match in map(self.LINE.match, body.splitlines()) if match]

    def read(self, rel):
        path = REPO / rel
        if not path.is_file():
            self.skipTest(f"{rel} is not in this checkout")
        return path.read_text(encoding="utf-8")

    def test_tippy_and_miri_lists(self):
        for driver in check.DRIVERS:
            with self.subTest(driver.name):
                text = self.read(driver.list_path)
                entries = check.read_driver_list(text, driver.list_path)
                self.assertEqual([entry.name for entry in entries], self.names_by_line(text, "generate! {\n"))
                self.assertGreater(len(entries), 0)
                by_name = {entry.name: entry.value for entry in entries}
                for name, value in (("CRLF", "\r\n"), ("LF", "\n"), ("DOUBLE_QUOTE", '"'), ("BACKSLASH_SINGLE_QUOTE", "\\'")):
                    if name in by_name:
                        self.assertEqual(by_name[name], value)

    def test_predefined_list(self):
        pre = check.read_predefined(self.read(check.SYMBOL_RS), self.read(check.SYMBOLS_MACRO_RS))
        self.assertEqual(pre.counts["Keywords"] + pre.counts["Symbols"], pre.pin)
        self.assertEqual(pre.repeats, [])
        for value, name in (("_", "Underscore"), ("$crate", "DollarCrate"), ("{{root}}", "PathRoot"), ("as", "As")):
            self.assertEqual(pre.by_value[value][:2], ("Keywords", name))
        for value in ("0", "9", "A", "Z", "a", "z", "Vec"):
            self.assertIn(value, pre.by_value)
        for name in ("Underscore", "DollarCrate", "PathRoot"):
            self.assertNotIn(name, pre.by_value)

    def test_every_use_of_the_mechanism_in_this_checkout_is_read(self):
        for rel in list(check.MECHANISM) + [path for driver in check.DRIVERS for path in driver.site_paths]:
            with self.subTest(rel):
                sites = check.classify_sites(rel, check.lex(self.read(rel), rel))
                self.assertGreater(len(sites), 0, "the file no longer names the mechanism; DRIVERS / MECHANISM is stale")
                self.assertEqual([site for site in sites if site.kind == "unread"], [])


if __name__ == "__main__":
    unittest.main()
