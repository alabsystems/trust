#!/usr/bin/env python3
"""Every Trust run-make fixture must LEX as Rust — build-free, no toolchain.

WHY THIS EXISTS. `90fe4d2c62` added a two-line Clean comment to
`tests/run-make/trust-ir-emit-clean-origin/foo.rs` ending in a grave-accented
`gate`. A `clean { ... }` island is a true parser island, but its contents still
travel as Rust TOKEN TREES, and a grave accent starts no Rust token. The recipe
died at its FIRST compilation, before a single assertion ran, and nothing caught
it: no `push`-profile lane runs run-make (`tests/run_trust_comprehensive_harness.sh
--list push` carried no run-make row), and the whole suite needs a stage1 that
costs hours. Repaired by `691169cd1b` six hours later.

The bug class is narrow and does not need a compiler to see: a fixture that does
not LEX. This walks the Trust run-make sources and reports, per source:

  * unknown-start-of-token  -- a character that begins no Rust token (a grave
    accent, a backslash, a stray non-XID codepoint). The historical defect.
  * unterminated-*          -- string, raw string, byte/C string, character
    literal, or block comment that never closes.
  * overlong-char-literal   -- the respelling the repair commit considered and
    rejected, which lexes as a character literal of four codepoints.

TWO SOURCE POPULATIONS, because the recipes carry two.

  1. ON-DISK fixtures: every `*.rs` under `tests/run-make/trust-*/`, `rmake.rs`
     included. This is the population the historical defect lived in.
  2. INLINE sources: a recipe may `rfs::write("foo.rs", r#"..."#)` and compile
     the result at runtime. A grave accent there is INSIDE a raw string literal,
     so `rmake.rs` itself lexes perfectly and population 1 sees nothing. Five of
     the raw-string sources in the tree carry Clean islands. They are extracted
     with the same lexer (raw-string literals are found by tokenizing, not by
     regex) and judged by the predicate `looks_like_rust_source` below.

WHAT THIS DOES **NOT** COVER -- read before trusting a green.

  * It is a LEXER, not a parser and not a compiler. `fn f(` that never closes,
    an unknown attribute, a type error, a failed proof obligation, a wrong
    assertion in `rmake.rs` -- all lex fine and all pass here. It pins exactly
    one thing: that the FIRST compilation cannot die on a token.
  * The Clean island's CONTENTS are checked only as Rust token trees, which is
    all the Rust lexer sees. A Clean *syntax* error inside an island lexes fine
    and is not caught.
  * Population 2 is a HEURISTIC. A raw string that writes Rust source without
    matching `looks_like_rust_source` is silently not checked. A miss there is a
    coverage gap, never a false alarm; `--list` prints what was actually read so
    the population can be audited.
  * It reads the WORKING TREE, not the range being pushed.
  * `--with-trustc` runs the real thing (`-Zparse-crate-root-only`) over the same
    population and is the exactness cross-check -- 83/83 agree, measured
    2026-09-12. It is deliberately NOT the push row: it needs a `trustc` a fresh
    clone may not have, and it took 158s against a push profile whose whole
    measured budget is 15.7s. A gate that fails open on a missing toolchain, or
    that costs ten times the budget, is worse than a build-free floor that
    always runs.

Usage:
    scripts/check_run_make_fixture_lex.py
    scripts/check_run_make_fixture_lex.py --list
    scripts/check_run_make_fixture_lex.py --selftest
    scripts/check_run_make_fixture_lex.py --with-trustc /path/to/trustc

Exit codes:
    0   every source in both populations lexes
    1   at least one source does not lex (or a selftest mutation was not caught)

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
RUN_MAKE = REPO_ROOT / "tests" / "run-make"
FIXTURE_GLOB = "trust-*"

# Every ASCII character that can BEGIN a Rust token. Identifier starts, digits,
# and the literal prefixes are handled before this set is consulted; what is
# left is punctuation. Sourced from `rustc_lexer::TokenKind`'s single-character
# arms. The grave accent and the backslash are deliberately absent -- that
# absence IS the check.
PUNCT_START = set(";,.()[]{}@#~?:$=!<>-&|+*/^%")

# `rustc_lexer::is_whitespace`, which is Pattern_White_Space.
WHITESPACE = set(
    "\t\n\x0b\x0c\r "
    "\u0085\u200e\u200f\u2028\u2029"
)


@dataclass
class Finding:
    origin: str  # human-readable source name
    line: int
    col: int
    kind: str
    detail: str

    def __str__(self) -> str:
        return f"{self.origin}:{self.line}:{self.col}: {self.kind}: {self.detail}"


def _is_ident_start(ch: str) -> bool:
    # Rust identifiers are XID_Start (plus `_`). Python's `str.isidentifier`
    # is XID-based, so a single-character probe answers the same question.
    return ch == "_" or ch.isidentifier()


def _is_ident_continue(ch: str) -> bool:
    return ch == "_" or ("a" + ch).isidentifier()


def _prologue_len(src: str) -> int:
    """Bytes of shebang + cargo frontmatter to skip before lexing.

    rustc consumes both before the lexer proper (`FrontmatterAllowed`). Measured
    2026-09-12 on `src/tools/targo/tests/testsuite/script/rustc_fixtures/
    content-contains-whitespace.rs`: without this, the TOML frontmatter is lexed
    as Rust and its `#` comments report as Rust defects, while trustc accepts
    the file.
    """
    i = 0
    n = len(src)
    if src.startswith("#!") and not src.startswith("#!["):
        nl = src.find("\n", i)
        i = n if nl < 0 else nl + 1
    j = i
    while j < n and src[j] in " \t\r\n":
        j += 1
    line_end = src.find("\n", j)
    line_end = n if line_end < 0 else line_end
    opener = src[j:line_end].rstrip()
    dashes = len(opener) - len(opener.lstrip("-"))
    # The infostring may be attached with no space (`---cargo`), which is the
    # spelling the targo fixture uses.
    if dashes >= 3:
        k = line_end + 1
        while k < n:
            e = src.find("\n", k)
            e = n if e < 0 else e
            cand = src[k:e].rstrip()
            if len(cand) >= dashes and set(cand) == {"-"}:
                return e + 1 if e < n else n
            k = e + 1
        return i  # unterminated frontmatter: leave it to the lexer
    return i


def lex_findings(src: str, origin: str) -> list[Finding]:
    """Report every place `src` fails to lex as Rust. Empty list == it lexes."""
    findings: list[Finding] = []
    n = len(src)
    i = _prologue_len(src)
    # Trust prime notation is byte-exact adjacency to the PREVIOUS identifier
    # token; every other token kind clears it, exactly as `trust_last_ident_end`
    # does in `compiler/rustc_parse/src/lexer/mod.rs`.
    last_ident_end: int | None = None

    # Line/col are computed on demand; sources here are small.
    def pos(idx: int) -> tuple[int, int]:
        line = src.count("\n", 0, idx) + 1
        bol = src.rfind("\n", 0, idx) + 1
        return line, idx - bol + 1

    def add(idx: int, kind: str, detail: str) -> None:
        line, col = pos(idx)
        findings.append(Finding(origin, line, col, kind, detail))

    while i < n:
        c = src[i]

        if c in WHITESPACE:
            i += 1
            continue

        # ---- comments ------------------------------------------------------
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            nl = src.find("\n", i)
            i = n if nl < 0 else nl + 1
            last_ident_end = None
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "*":
            start = i
            depth = 0
            while i < n:
                if src.startswith("/*", i):
                    depth += 1
                    i += 2
                elif src.startswith("*/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
            if depth != 0:
                add(start, "unterminated-block-comment", "block comment never closed")
                break
            continue

        # ---- literal prefixes ----------------------------------------------
        # b"" br"" b'' c"" cr"" r"" r#""# r#ident
        prefix_len = 0
        if c in "bc" and i + 1 < n:
            if src[i + 1] == '"':
                prefix_len = 1
            elif src[i + 1] == "r" and i + 2 < n and src[i + 2] in '"#':
                prefix_len = 1
            elif c == "b" and src[i + 1] == "'":
                prefix_len = 1

        j = i + prefix_len
        # raw string: r"..." / r#"..."# (any hash count), or raw ident r#name
        if j < n and src[j] == "r" and j + 1 < n and src[j + 1] in '"#':
            k = j + 1
            hashes = 0
            while k < n and src[k] == "#":
                hashes += 1
                k += 1
            if k < n and src[k] == '"':
                close = '"' + "#" * hashes
                end = src.find(close, k + 1)
                if end < 0:
                    add(i, "unterminated-raw-string", "raw string never closed")
                    break
                i = end + len(close)
                last_ident_end = None
                continue
            if prefix_len == 0 and hashes == 1 and k < n and _is_ident_start(src[k]):
                # raw identifier r#type
                i = k
                while i < n and _is_ident_continue(src[i]):
                    i += 1
                last_ident_end = i
                continue
            add(
                i,
                "malformed-raw-prefix",
                "raw-literal prefix followed by neither a quote nor an identifier",
            )
            i = j + 1
            continue

        # plain / byte / C string: "..." with backslash escapes
        if j < n and src[j] == '"':
            k = j + 1
            closed = False
            while k < n:
                if src[k] == "\\":
                    k += 2
                    continue
                if src[k] == '"':
                    closed = True
                    k += 1
                    break
                k += 1
            if not closed:
                add(i, "unterminated-string", "string literal never closed")
                break
            i = k
            last_ident_end = None
            continue

        # char literal, lifetime, or Trust prime (or byte char b'x')
        if j < n and src[j] == "'":
            # A `b'` prefix owns the quote: `ensures b' == b` is a byte constant
            # in Trust exactly as in Rust (measured: trustc E0763), NOT a prime.
            adjacent = prefix_len == 0 and last_ident_end == i
            nxt = _scan_quote(
                src, j, j, add, ident_adjacent=adjacent, byte=prefix_len == 1
            )
            # A prime consumes exactly the quote and itself becomes the new
            # adjacency anchor, so `x''` folds one prime at a time.
            last_ident_end = nxt if adjacent and nxt == j + 1 else None
            i = nxt
            continue

        # ---- identifiers and numbers ---------------------------------------
        if _is_ident_start(c):
            i += 1
            while i < n and _is_ident_continue(src[i]):
                i += 1
            last_ident_end = i
            continue
        if c.isdigit():
            i += 1
            while i < n and (_is_ident_continue(src[i]) or src[i] == "."):
                # `1..2` is a range, not a float: stop before a second dot.
                if src[i] == "." and (i + 1 >= n or not src[i + 1].isdigit()):
                    break
                i += 1
            last_ident_end = None
            continue

        # ---- punctuation -----------------------------------------------------
        if c in PUNCT_START:
            i += 1
            last_ident_end = None
            continue

        add(
            i,
            "unknown-start-of-token",
            f"character {c!r} (U+{ord(c):04X}) begins no Rust token",
        )
        i += 1

    return findings


def _unterminated_kind(byte: bool) -> str:
    return "unterminated-byte-literal" if byte else "unterminated-char-literal"


_SIMPLE_ESCAPES = set("nrt0\\'\"")


def _char_body_is_valid(body: str) -> bool:
    """Does `body` (between the quotes) form ONE valid Rust character?

    Mirrors `rustc_lexer::unescape::check_for_errors(.., Mode::Char, ..)` at the
    granularity this checker needs: the fatal cases are "not exactly one
    codepoint" and "not a recognized escape".
    """
    if not body:
        return False
    if body[0] != "\\":
        return len(body) == 1
    if len(body) < 2:
        return False
    e = body[1]
    if e in _SIMPLE_ESCAPES:
        return len(body) == 2
    if e == "x":
        return len(body) == 4 and all(ch in "0123456789abcdefABCDEF" for ch in body[2:])
    if e == "u":
        return (
            len(body) >= 4
            and body[2] == "{"
            and body[-1] == "}"
            and all(ch in "0123456789abcdefABCDEF_" for ch in body[3:-1])
        )
    return False


def _scan_quote(
    src: str,
    tok_start: int,
    q: int,
    add,
    ident_adjacent: bool = False,
    byte: bool = False,
) -> int:
    """Scan from a `'` at index `q`. Returns the index to resume lexing at.

    Mirrors `rustc_lexer::lifetime_or_char` AND the Trust post-state PRIME rule
    in `compiler/rustc_parse/src/lexer/mod.rs` (two-language design D2 / ruling
    Q9): a quote IMMEDIATELY adjacent to a preceding identifier token, which
    does not form a valid lifetime or a valid character literal, is a one-char
    prime token and lexing resumes right after it. `ensures x' >= x` is
    therefore legal Trust, and a checker that did not model this would report
    every `ensures`/`invariant` clause in the tree.

    `ident_adjacent` is the checker's stand-in for `trust_last_ident_end ==
    Some(start)`: byte-exact adjacency to the previous identifier.
    """
    n = len(src)
    k = q + 1
    if k >= n:
        if not ident_adjacent:
            add(tok_start, _unterminated_kind(byte), "quote at end of input")
        return n

    first = src[k]
    second = src[k + 1] if k + 1 < n else ""

    # rustc_lexer::lifetime_or_char's `can_be_a_lifetime`
    if second != "'" and (_is_ident_start(first) or first.isdigit()):
        e = k + 1
        while e < n and _is_ident_continue(src[e]):
            e += 1
        if e < n and src[e] == "'":
            # `'abc'`: a TERMINATED char literal of more than one codepoint.
            if ident_adjacent and (e + 1 >= n or not _is_ident_continue(src[e + 1])):
                return q + 1  # prime
            add(
                tok_start,
                "overlong-char-literal",
                f"character literal of {e - k} codepoints",
            )
            return e + 1
        return e  # lifetime / loop label

    # rustc_lexer::single_quoted_string
    if second == "'" and first != "\\":
        return k + 2  # one-symbol literal, always valid

    p = k
    terminated = False
    while p < n:
        ch = src[p]
        if ch == "'":
            p += 1
            terminated = True
            break
        if ch == "/":
            break
        if ch == "\n" and not (p + 1 < n and src[p + 1] == "'"):
            break
        if ch == "\\":
            p += 2
            continue
        p += 1

    if not terminated:
        if ident_adjacent:
            return q + 1  # prime
        add(tok_start, _unterminated_kind(byte), "quote never closed on this line")
        return q + 1

    body = src[q + 1 : p - 1]
    if _char_body_is_valid(body):
        return p
    suffixed = p < n and _is_ident_continue(src[p])
    if ident_adjacent and not suffixed:
        return q + 1  # prime
    add(
        tok_start,
        "overlong-char-literal"
        if len(body) > 1 and not body.startswith("\\")
        else "invalid-char-literal",
        f"character literal {body!r} is not one valid Rust character",
    )
    return p


# --------------------------------------------------------------------------
# population 2: inline Rust sources written by a recipe at runtime
# --------------------------------------------------------------------------

_SOURCE_ITEM_WORDS = (
    "fn ",
    "pub fn ",
    "mod ",
    "pub mod ",
    "struct ",
    "pub struct ",
    "enum ",
    "pub enum ",
    "impl ",
    "const ",
    "pub const ",
    "static ",
    "pub static ",
    "use ",
    "clean ",
    "trait ",
    "type ",
    "extern ",
    "unsafe ",
)


def looks_like_rust_source(body: str) -> bool:
    """The DECLARED predicate for "this raw string is a Rust source file".

    Stated rather than inferred, because a miss here is silent. A body counts
    when it carries an inner attribute or a line that opens a Rust item.
    """
    if "#![" in body:
        return True
    for raw in body.splitlines():
        line = raw.strip()
        if any(line.startswith(w) for w in _SOURCE_ITEM_WORDS):
            return True
        if line.startswith("clean {") or line.startswith("clean{"):
            return True
    return False


def raw_string_literals(src: str) -> list[tuple[int, str]]:
    """Every raw-string literal in `src`, as (start offset, body).

    Found by scanning with the same lexer rules, so an `r#"` inside a comment or
    an ordinary string is not mistaken for one.
    """
    out: list[tuple[int, str]] = []
    n = len(src)
    i = 0
    while i < n:
        c = src[i]
        if c in WHITESPACE:
            i += 1
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            nl = src.find("\n", i)
            i = n if nl < 0 else nl + 1
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "*":
            depth = 0
            while i < n:
                if src.startswith("/*", i):
                    depth += 1
                    i += 2
                elif src.startswith("*/", i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
            continue
        prefix = 0
        if c in "bc" and i + 1 < n and src[i + 1] == "r" and i + 2 < n and src[i + 2] in '"#':
            prefix = 1
        j = i + prefix
        if j < n and src[j] == "r" and j + 1 < n and src[j + 1] in '"#':
            k = j + 1
            hashes = 0
            while k < n and src[k] == "#":
                hashes += 1
                k += 1
            if k < n and src[k] == '"':
                close = '"' + "#" * hashes
                end = src.find(close, k + 1)
                if end < 0:
                    return out
                out.append((k + 1, src[k + 1 : end]))
                i = end + len(close)
                continue
        if j < n and src[j] == '"':
            k = j + 1
            while k < n:
                if src[k] == "\\":
                    k += 2
                    continue
                if src[k] == '"':
                    k += 1
                    break
                k += 1
            i = k
            continue
        if j < n and src[j] == "'":
            i = _scan_quote(src, i, j, lambda *a, **kw: None)
            continue
        if _is_ident_start(c):
            i += 1
            while i < n and _is_ident_continue(src[i]):
                i += 1
            continue
        i += 1
    return out


@dataclass
class Source:
    origin: str
    text: str
    path: Path
    inline: bool


def collect_sources(root: Path = RUN_MAKE) -> list[Source]:
    sources: list[Source] = []
    for d in sorted(root.glob(FIXTURE_GLOB)):
        if not d.is_dir():
            continue
        for f in sorted(d.rglob("*.rs")):
            rel = f.relative_to(REPO_ROOT)
            # `newline=""` matters: Path.read_text translates a bare CR to a
            # newline, which SPLITS a line comment and exposes its contents
            # to the lexer. Measured 2026-09-12 on
            # `src/tools/tippy/tests/ui/four_forward_slashes_bare_cr.rs`.
            with open(f, encoding="utf-8", errors="surrogateescape", newline="") as fh:
                text = fh.read()
            sources.append(Source(str(rel), text, f, inline=False))
            if f.name == "rmake.rs":
                for off, body in raw_string_literals(text):
                    if not looks_like_rust_source(body):
                        continue
                    line = text.count("\n", 0, off) + 1
                    sources.append(
                        Source(
                            f"{rel}:{line} (inline raw-string source)",
                            body,
                            f,
                            inline=True,
                        )
                    )
    return sources


def run_check(sources: list[Source]) -> list[Finding]:
    findings: list[Finding] = []
    for s in sources:
        findings.extend(lex_findings(s.text, s.origin))
    return findings


# --------------------------------------------------------------------------
# --with-trustc: the exactness cross-check (not the push row)
# --------------------------------------------------------------------------

_TRUSTC_LEX_ERRORS = (
    "unknown start of token",
    "unterminated",
    "character literal may only contain one codepoint",
)


def run_with_trustc(trustc: str, sources: list[Source]) -> int:
    rc = 0
    agree = 0
    with tempfile.TemporaryDirectory() as td:
        for s in sources:
            p = Path(td) / "probe.rs"
            p.write_text(s.text, encoding="utf-8", errors="surrogateescape")
            r = subprocess.run(
                [trustc, "-Zparse-crate-root-only", "--edition", "2021", str(p)],
                capture_output=True,
                text=True,
                cwd=td,
                env={**os.environ, "RUSTC_BOOTSTRAP": "1"},
            )
            bad = any(e in r.stderr for e in _TRUSTC_LEX_ERRORS)
            mine = bool(lex_findings(s.text, s.origin))
            if bad == mine:
                agree += 1
                print(f"ok        {s.origin}: lexes={not mine}")
            else:
                rc = 1
                print(f"DISAGREE  {s.origin}: trustc_lex_error={bad} lexer={mine}")
                for ln in r.stderr.splitlines()[:6]:
                    print(f"          {ln}")
    print(f"\n{agree}/{len(sources)} sources agree with {trustc}")
    return rc


# --------------------------------------------------------------------------
# --selftest: mutation proof, including the historical defect verbatim
# --------------------------------------------------------------------------

_GRAVE = "`"

HISTORICAL_ISLAND = (
    "mod m {\n"
    "    clean {\n"
    "        def cleanWsum (a : UInt64) (b : UInt64) : UInt64 := a + b\n"
    "\n"
    "        -- W2 gate widening: the other two carrier-gate targets, at the exact\n"
    "        -- UInt carriers the reflector admits. Both must publish at tier "
    + _GRAVE
    + "gate"
    + _GRAVE
    + ".\n"
    "        def cleanSnd (a : UInt64) (b : UInt64) : UInt64 := b\n"
    "    }\n"
    "}\n"
)

REPAIRED_ISLAND = HISTORICAL_ISLAND.replace(_GRAVE + "gate" + _GRAVE, "gate")

MUTATIONS: list[tuple[str, str, str]] = [
    (
        "historical 90fe4d2c62: grave accent in a Clean island comment",
        HISTORICAL_ISLAND,
        "unknown-start-of-token",
    ),
    (
        "the respelling 691169cd1b rejected: 'gate' inside an island",
        HISTORICAL_ISLAND.replace(_GRAVE + "gate" + _GRAVE, "'gate'"),
        "overlong-char-literal",
    ),
    (
        "backslash outside a string",
        "fn f() { let x = \\ 1; }\n",
        "unknown-start-of-token",
    ),
    (
        "unterminated string literal",
        'fn f() { let s = "oops;\n}\n',
        "unterminated-string",
    ),
    (
        "unterminated raw string",
        'fn f() { let s = r#"oops; }\n',
        "unterminated-raw-string",
    ),
    (
        "unterminated block comment",
        "fn f() {}\n/* never closed\n",
        "unterminated-block-comment",
    ),
    (
        "stray quote NOT adjacent to an identifier is not a prime",
        "fn f() { let _ = ' ; }\n",
        "unterminated-char-literal",
    ),
    (
        "a `b'` prefix is a byte constant, not a prime (measured: trustc E0763)",
        "pub fn f(b: u64) -> u64\n    ensures b' == b\n{\n    b\n}\n",
        "unterminated-byte-literal",
    ),
    (
        "typographic quotes pasted from a document",
        "fn f() { let s = “x”; }\n",
        "unknown-start-of-token",
    ),
]

# Bodies that MUST lex -- the false-positive half of the mutation proof.
CONTROLS: list[tuple[str, str]] = [
    ("the repaired island", REPAIRED_ISLAND),
    (
        "lifetimes and loop labels",
        "fn f<'a>(x: &'a u8) -> &'a u8 { 'outer: loop { break 'outer x } }\n",
    ),
    (
        "char literals and escapes",
        "fn f() { let a = 'x'; let b = '\\''; let c = '\\u{1F600}'; let d = b'\\n'; }\n",
    ),
    ("nested block comments", "/* a /* b */ c */ fn f() {}\n"),
    (
        "raw strings and raw identifiers",
        'fn f() { let r#type = r#"a "b" c"#; let s = r##"x"#y"##; }\n',
    ),
    ("ranges and float suffixes", "fn f() { for _ in 1..2 {} let x = 1.5e-3f64; let y = 0xFF_u8; }\n"),
    ("non-ASCII identifiers", "fn été() -> u8 { 1 }\n"),
    ("byte and C strings", 'fn f() { let a = b"x"; let b = c"y"; let c = br#"z"#; }\n'),
    (
        "emoji inside a comment and a string",
        'fn f() { /* \U0001F600 */ let s = "\U0001F600"; }\n',
    ),
    ("generic close then lifetime", "fn f<T: Iterator<Item = &'static str>>(_: T) {}\n"),
    # The distinction the historical defect turns on: a grave accent inside a
    # RUST comment is legal and must not be reported. The island's `--` lines
    # are Lean comments, which the Rust lexer does not see as comments at all,
    # so the same character there is the defect.
    (
        "grave accent inside a Rust line and doc comment",
        "/// tier " + _GRAVE + "gate" + _GRAVE + "\n// also " + _GRAVE + "here" + _GRAVE + "\npub fn f() {}\n",
    ),
    # Trust post-state prime notation (D2/Q9). A checker that did not model the
    # prime rule would report every `ensures`/`invariant` clause in the tree;
    # this body is `tests/run-make/trust-e9-kernel-discharge-transport/cited.rs`
    # reduced to its clause.
    (
        "post-state prime in an ensures clause",
        "pub fn keep(x: u64) -> u64\n    ensures x' >= x by u64_ge_refl\n{\n    x\n}\n",
    ),
    ("chained primes", "pub fn f(x: u64) -> u64\n    ensures x'' == x\n{\n    x\n}\n"),
    ("prime is not a lifetime and not a char", "fn f() { let _ = balance' == amount'; }\n"),
]


def selftest() -> int:
    rc = 0
    for name, body, expect in MUTATIONS:
        kinds = {f.kind for f in lex_findings(body, "<mutation>")}
        if expect in kinds:
            print(f"CAUGHT   {name} -> {expect}")
        else:
            rc = 1
            print(f"MISSED   {name}: expected {expect}, got {sorted(kinds) or 'nothing'}")
    for name, body in CONTROLS:
        got = lex_findings(body, "<control>")
        if got:
            rc = 1
            print(f"FALSE+   {name}: {got[0]}")
        else:
            print(f"clean    {name}")

    # The population must be non-empty, or every mutation above proves nothing
    # about the tree: a check that reads zero sources passes unconditionally.
    sources = collect_sources()
    on_disk = sum(1 for s in sources if not s.inline)
    inline = sum(1 for s in sources if s.inline)
    if on_disk < 10 or inline < 5:
        rc = 1
        print(f"POPULATION too small: on_disk={on_disk} inline={inline}")
    else:
        print(f"clean    population: {on_disk} on-disk sources, {inline} inline sources")

    # And the historical fixture must be in it by path, not by luck.
    want = "tests/run-make/trust-ir-emit-clean-origin/foo.rs"
    if not any(s.origin == want for s in sources):
        rc = 1
        print(f"POPULATION does not contain {want}")
    else:
        print(f"clean    population contains {want}")

    # The inline half must reach the island-bearing recipes, or the five
    # raw-string sources this check exists for are silently unread.
    inline_islands = sum(
        1 for s in sources if s.inline and ("clean {" in s.text or "clean{" in s.text)
    )
    if inline_islands < 5:
        rc = 1
        print(f"POPULATION carries only {inline_islands} inline Clean-island sources (want >= 5)")
    else:
        print(f"clean    population carries {inline_islands} inline Clean-island sources")
    return rc


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--list", action="store_true", help="print the population and exit 0")
    ap.add_argument("--selftest", action="store_true", help="mutation-prove the checker")
    ap.add_argument("--with-trustc", metavar="TRUSTC", help="cross-check against the real lexer")
    args = ap.parse_args()

    if args.selftest:
        rc = selftest()
        print("SELFTEST: " + ("PASS" if rc == 0 else "FAIL"))
        return rc

    sources = collect_sources()
    if not sources:
        print(f"ERROR: no sources found under {RUN_MAKE}/{FIXTURE_GLOB}", file=sys.stderr)
        return 1

    if args.list:
        for s in sources:
            print(f"{'inline' if s.inline else 'ondisk'}  {len(s.text):6d}B  {s.origin}")
        print(
            f"\n{len(sources)} sources "
            f"({sum(1 for s in sources if not s.inline)} on-disk, "
            f"{sum(1 for s in sources if s.inline)} inline)"
        )
        return 0

    if args.with_trustc:
        return run_with_trustc(args.with_trustc, sources)

    findings = run_check(sources)
    if findings:
        print("run-make fixtures that do not LEX as Rust:\n", file=sys.stderr)
        for f in findings:
            print(f"  {f}", file=sys.stderr)
        print(
            "\nA fixture that does not lex dies at the recipe's FIRST compilation,"
            "\nbefore a single assertion runs. Fix the token, not the assertion.",
            file=sys.stderr,
        )
        return 1
    print(
        f"OK: {len(sources)} Trust run-make sources lex "
        f"({sum(1 for s in sources if not s.inline)} on-disk, "
        f"{sum(1 for s in sources if s.inline)} inline)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
