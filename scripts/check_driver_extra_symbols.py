#!/usr/bin/env python3
"""check_driver_extra_symbols.py — a driver's extra symbol may not repeat a pre-interned one.

WHY THIS EXISTS. `rustc_span` pre-interns a fixed list of strings (the
`symbols!` invocation in `compiler/rustc_span/src/symbol.rs`). A driver built
on the compiler may hand the interner MORE strings when it creates a session
(`rustc_interface::Config::extra_symbols`); tippy and miri each keep such a
list. `Interner::prefill` panics when a string is in both:

    duplicate symbols in the rustc symbol list and the extra symbols added by
    the driver: [[66, 105, 110, 97, 114, 121, 72, 101, 97, 112], [86, 101, 99,
    68, 101, 113, 117, 101]]

That is "BinaryHeap" and "VecDeque", and it is the measured case: `c73702b157`
added both to `symbol.rs` while tippy's list had named them since July. It
reached main with `35f9d0897f` on 2026-10-09, and from then on EVERY
tippy-driver start that created a session died -- a lint run and a dependency
passthrough alike -- while everything that looked at tippy stayed green:

  * the compiler builds (the two lists are in different crates and only meet
    at run time);
  * `x.py check` type-checks tippy (push row `scoped.compiler-check`), and a
    name defined twice is not a type error: tippy's own constant shadows the
    glob re-export of rustc_span's;
  * `tippy-driver --version`, which the toolchain output contract runs,
    returns before the interner exists.

No push lane builds or starts tippy, so nothing noticed for three days, and
`scripts/promote-toolchain.sh` sealed `trust-2615acef` with a tippy that could
not start. aterm's merge gate found it, one step before promotion.

The defect needs no compiler to see. It is a set intersection of two source
lists, so this reads both and names every collision, in about a second.

WHAT IS COMPARED: THE STRINGS, as the interner does. A name is not its string:
`Underscore: "_"`, `CRLF: "\\r\\n"`, `BACKSLASH_SINGLE_QUOTE: r"\\'"`. So both
lists are tokenized (comments, cooked and raw string literals, escapes) and
each entry's VALUE is taken the way its macro takes it. The predefined set is
what `compiler/rustc_macros/src/symbols.rs` builds, read from that file and
not from memory:

  * `Keywords { Name: "value", .. }`            -> the value
  * `Symbols { name, name: "value", .. }`       -> the name, or the value
  * the generated prefill                       -> "0".."9", "A".."Z", "a".."z"
  * `AppendOnly { .. }` (Trust's index-stable tail) -> as `Symbols`
  * `name: env!("VAR")` in `Symbols`            -> known only at build time.
    NOT JUDGED; each one is printed. Today that is `env_CFG_RELEASE`.

A driver's set is the body of its `generate! { .. }` call: `name,` is
`stringify!(name)`, `name: "value",` is the value.

TWO THINGS KEEP THIS FROM BEING A GUESS, and both fail the check when they stop
holding (exit 2, "could not judge"), rather than letting it read less:

  1. THE MODEL IS PINNED TO THE MACROS. The statements this reading depends on
     (the digit and letter prefill, the three section keywords, how a value is
     taken; `val!` and `generate!`'s matcher on the driver side) are compared,
     token for token, with the macro source of the tree being judged. A macro
     that changed is re-read by a person, and `SYMBOLS_MACRO_MODEL` /
     `LIST_MACRO_MODEL` below are updated in the same commit.
  2. THE PARSE IS CROSS-CHECKED AGAINST THE COMPILER'S OWN COUNT. `symbol.rs`
     asserts `SYMBOL_DIGITS_BASE == <n>` at compile time, and that is by
     construction the number of `Keywords` plus non-`env!` `Symbols` entries.
     This check counts the same entries and must get the same number.

EVERY DRIVER, NOT ONLY THE TWO KNOWN ONES. `DRIVERS` names tippy's and miri's
lists. So that a third driver cannot grow a list this check never reads, every
use of the mechanism under compiler/, library/, src/, crates/ and targo-trust/
is found (`git grep`) and classified from its tokens:

  * `extra_symbols: Vec::new()` and `create_session_globals_then(e, &[], ..)`
    -- no extra symbols; fine anywhere;
  * `<x>.extra_symbols = <path>::EXTRA_SYMBOLS.into();` in a file `DRIVERS`
    names -- that driver handing over the list this check reads;
  * declarations and pass-throughs of the parameter inside the four files that
    ARE the mechanism (`MECHANISM`);
  * anything else is UNREAD and fails: a new list, a wrapper, a `.push(..)`.
    Teach `DRIVERS` (or the classifier) about it in the commit that adds it.

A driver whose list and site files are all absent from a tree is reported
ABSENT and not judged (an old base, a tool removed). A list nobody hands to the
interner, or a hand-over whose list is missing, fails.

A string listed twice inside ONE driver's list panics the same way (the
interner's check is over the whole chain), so that is reported too.

WHICH TREE IS JUDGED. With TRUST_PUSHED_REFS set (the pre-push hook exports
git's `<local_ref> <local_sha> <remote_ref> <remote_sha>` lines) every
non-deletion pushed commit is judged from its own tree in the object store --
`git push origin topic:main` from a clean checkout of something else is judged
as what it publishes, and local work in progress blocks nothing. Deletions have
no tree (an all-deletion push prints `SKIPPED: `). With the variable unset or
empty the working tree is judged. `--rev REV` judges that commit instead,
without a checkout. A `SUBJECT:` line always says which reading was taken.
Either way the checker that runs is this file, from the checkout.

WHAT THIS DOES **NOT** COVER -- read before trusting a green.

  * It compares source lists. It does not build or start anything: a driver
    that cannot start for any OTHER reason is `scripts/promote-toolchain.sh`'s
    tool-start gate, which runs each shipped driver before a seal.
  * `env!()`-valued predefined symbols (above).
  * `first-party/*` are separate repositories behind gitlinks and are not
    scanned. None names the mechanism (measured 2026-10-12 at the pins of
    2615acefeb: 0 files in all nine).
  * `vendor/`, `tests/`, `src/llvm-project` and `src/doc` are not scanned: a
    test that builds its own `Config` is not a shipped driver.
  * The scan finds the mechanism by its names (`extra_symbols`,
    `create_session_globals_then`, `SessionGlobals::new`). A call spelled
    through an alias or split across those names is not found.
  * A driver that keeps its list in another shape than `generate! { .. }` is
    not read; it is refused (UNREAD or a model mismatch), never passed.

Usage:
    scripts/check_driver_extra_symbols.py                # working tree, or the push
    scripts/check_driver_extra_symbols.py --rev REV      # that commit, from git objects
    scripts/check_driver_extra_symbols.py --list         # also print everything read

Exit codes:
    0   no extra symbol repeats a predefined one, in any judged tree
    1   a collision, a repeat inside one list, an unread use of the mechanism,
        or a `DRIVERS` row the tree contradicts
    2   could not judge: unreadable input, a macro that no longer matches the
        model, a parse the compiler's own count contradicts, bad usage

Tests: scripts/tests/check_driver_extra_symbols_test.py (push row
`fast.driver-extra-symbols-test`).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import subprocess
import sys
from typing import Dict, List, NamedTuple, Optional, Sequence, Tuple

SYMBOL_RS = "compiler/rustc_span/src/symbol.rs"
SYMBOLS_MACRO_RS = "compiler/rustc_macros/src/symbols.rs"


class Driver(NamedTuple):
    """One driver that hands the interner extra symbols.

    `list_path` holds its `generate! { .. }` call; `site_paths` are the files
    whose `<x>.extra_symbols = <path>::EXTRA_SYMBOLS.into();` hands it over.
    """

    name: str
    list_path: str
    site_paths: Tuple[str, ...]


DRIVERS: Tuple[Driver, ...] = (
    Driver("tippy", "src/tools/tippy/clippy_utils/src/sym.rs", ("src/tools/tippy/src/driver.rs",)),
    Driver("miri", "src/tools/miri/src/sym.rs", ("src/tools/miri/src/bin/miri.rs",)),
)

# The mechanism itself: where the parameter is declared and passed along. A
# declaration or a bare pass-through anywhere else is a wrapper this check
# cannot follow, and is UNREAD.
MECHANISM: Tuple[str, ...] = (
    "compiler/rustc_interface/src/interface.rs",
    "compiler/rustc_interface/src/util.rs",
    "compiler/rustc_macros/src/symbols.rs",
    "compiler/rustc_span/src/lib.rs",
)

SCAN_ROOTS: Tuple[str, ...] = ("compiler", "library", "src", "crates", "targo-trust")
SCAN_EXCLUDE: Tuple[str, ...] = ("src/llvm-project", "src/doc")
NEEDLES: Tuple[str, ...] = ("extra_symbols", "create_session_globals_then", "SessionGlobals::new")

# What this check's reading of `symbols!` depends on, as Rust source. Compared
# token for token with SYMBOLS_MACRO_RS in the tree being judged.
SYMBOLS_MACRO_MODEL: Tuple[Tuple[str, str], ...] = (
    (
        "the three sections",
        "syn::custom_keyword!(Keywords); syn::custom_keyword!(Symbols); syn::custom_keyword!(AppendOnly);",
    ),
    ("the digit prefill", "let prefill_ints = 0..=9;"),
    ("the letter prefill", "let prefill_letters = ('A'..='Z').chain('a'..='z');"),
    (
        "the prefill loop (digits, then letters, each as a one-character string)",
        "for s in prefill_ints.map(|n| n.to_string()).chain(prefill_letters.map(|c| c.to_string())) {",
    ),
    (
        "how a listed symbol's value is taken",
        "Value::SameAsName => name.to_string(), Value::String(lit) => lit.value(),",
    ),
)

# The same for a driver's list file.
LIST_MACRO_MODEL: Tuple[Tuple[str, str], ...] = (
    (
        "`val!` (a bare name is stringified, a literal is taken as written)",
        "macro_rules! val { ($name:ident) => { stringify!($name) }; ($name:ident $value:literal) => { $value }; }",
    ),
    ("`generate!`'s matcher", "macro_rules! generate { ($($name:ident $(: $value:literal)? ,)*) => {"),
    ("`EXTRA_SYMBOLS`", "pub const EXTRA_SYMBOLS: &[&str] = &[ $( val!($name $($value)?), )* ];"),
)

PREFILL: Tuple[str, ...] = tuple(
    [str(d) for d in range(10)]
    + [chr(c) for c in range(ord("A"), ord("Z") + 1)]
    + [chr(c) for c in range(ord("a"), ord("z") + 1)]
)

ZERO_SHA = re.compile(r"^0+$")
HEX_SHA = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")


class GateError(Exception):
    """A read the verdict depends on could not be made. Always fails closed."""


# --------------------------------------------------------------------------
# A Rust tokenizer: exactly enough to read a macro call's entries and to
# classify a use of the mechanism. Comments vanish; a string literal is ONE
# token carrying its decoded value, so a brace or a comma inside one is inert.
# --------------------------------------------------------------------------


class Tok(NamedTuple):
    kind: str  # ident | str | lit | lifetime | punct
    text: str  # str: the DECODED value; everything else: the source text
    line: int


_RAW_STRING = re.compile(r'(b|c)?r(#*)"')
_COOKED_STRING = re.compile(r'(b|c)?"')
_SIMPLE_ESCAPES = {"n": "\n", "r": "\r", "t": "\t", "\\": "\\", "0": "\0", "'": "'", '"': '"'}


def _ident_start(ch: str) -> bool:
    return ch == "_" or ch.isalpha()


def _ident_continue(ch: str) -> bool:
    return ch == "_" or ch.isalnum()


def lex(text: str, path: str) -> List[Tok]:
    """`text` as tokens. Anything this cannot read is a GateError naming the line."""
    toks: List[Tok] = []
    i, n, line = 0, len(text), 1

    def fail(what: str) -> GateError:
        return GateError(f"{path}:{line}: cannot tokenize: {what}")

    while i < n:
        ch = text[i]
        if ch == "\n":
            line += 1
            i += 1
            continue
        if ch.isspace():
            i += 1
            continue
        if text.startswith("//", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
            continue
        if text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                raise fail("a block comment that never closes")
            line += text.count("\n", i, j)
            i = j
            continue

        raw = _RAW_STRING.match(text, i)
        if raw:
            closer = '"' + raw.group(2)
            end = text.find(closer, raw.end())
            if end < 0:
                raise fail("a raw string literal that never closes")
            kind = "lit" if raw.group(1) else "str"
            body = text[raw.end():end]
            toks.append(Tok(kind, body if kind == "str" else text[i:end + len(closer)], line))
            line += text.count("\n", i, end)
            i = end + len(closer)
            continue

        cooked = _COOKED_STRING.match(text, i)
        if cooked:
            out: List[str] = []
            j = cooked.end()
            while True:
                if j >= n:
                    raise fail("a string literal that never closes")
                c = text[j]
                if c == '"':
                    break
                if c != "\\":
                    out.append(c)
                    j += 1
                    continue
                if j + 1 >= n:
                    raise fail("a string literal that never closes")
                esc = text[j + 1]
                if esc in _SIMPLE_ESCAPES:
                    out.append(_SIMPLE_ESCAPES[esc])
                    j += 2
                elif esc == "x":
                    digits = text[j + 2:j + 4]
                    if not re.fullmatch(r"[0-9a-fA-F]{2}", digits):
                        raise fail(f"a malformed \\x escape in a string literal: {text[j:j + 4]!r}")
                    out.append(chr(int(digits, 16)))
                    j += 4
                elif esc == "u":
                    close = text.find("}", j)
                    digits = text[j + 3:close].replace("_", "") if text.startswith("{", j + 2) and close > 0 else ""
                    if not re.fullmatch(r"[0-9a-fA-F]{1,6}", digits):
                        raise fail("a malformed \\u{..} escape in a string literal")
                    out.append(chr(int(digits, 16)))
                    j = close + 1
                elif esc in "\r\n":
                    # A line continuation: the newline and the next line's
                    # leading whitespace are not part of the value.
                    j += 1
                    while j < n and text[j] in " \t\r\n":
                        j += 1
                else:
                    raise fail(f"an unknown escape in a string literal: \\{esc}")
            if cooked.group(1):
                toks.append(Tok("lit", text[i:j + 1], line))
            else:
                toks.append(Tok("str", "".join(out), line))
            line += text.count("\n", i, j)
            i = j + 1
            continue

        if ch == "'" and i > 0 and (
            _ident_continue(text[i - 1]) or (text[i - 1] == "'" and bool(toks) and toks[-1] == Tok("punct", "'", line))
        ):
            # Trust's contract grammar: `ensures x' == value`, `balance'' == balance'`
            # (a primed name is the post-state). No Rust literal or lifetime starts
            # right after an identifier character, so this is never one of those.
            toks.append(Tok("punct", ch, line))
            i += 1
            continue

        if ch == "'" or text.startswith("b'", i):
            q = i + (1 if ch == "b" else 0)
            if q + 1 >= n:
                raise fail("a stray single quote")
            if text[q + 1] == "\\":
                j = q + 3
                while j < n and text[j] != "'" and text[j] != "\n":
                    j += 1
                if j >= n or text[j] != "'":
                    raise fail("a character literal that never closes")
                toks.append(Tok("lit", text[i:j + 1], line))
                i = j + 1
                continue
            if q + 2 < n and text[q + 2] == "'" and text[q + 1] not in "'\n":
                toks.append(Tok("lit", text[i:q + 3], line))
                i = q + 3
                continue
            if ch == "'" and _ident_start(text[q + 1]):
                j = q + 2
                while j < n and _ident_continue(text[j]):
                    j += 1
                toks.append(Tok("lifetime", text[i:j], line))
                i = j
                continue
            if ch == "'":
                raise fail("a single quote that starts neither a character literal nor a lifetime")
            # `b` followed by a quote that opens no byte literal: an identifier `b`.

        if _ident_start(ch):
            j = i + 1
            if text.startswith("r#", i) and i + 2 < n and _ident_start(text[i + 2]):
                j = i + 3
            while j < n and _ident_continue(text[j]):
                j += 1
            toks.append(Tok("ident", text[i:j], line))
            i = j
            continue

        if ch.isdigit():
            j = i + 1
            while j < n and (_ident_continue(text[j]) or (text[j] == "." and j + 1 < n and text[j + 1].isdigit())):
                j += 1
            toks.append(Tok("lit", text[i:j], line))
            i = j
            continue

        toks.append(Tok("punct", ch, line))
        i += 1
    return toks


def _is(tok: Optional[Tok], kind: str, text: str) -> bool:
    return tok is not None and tok.kind == kind and tok.text == text


def _at(tokens: Sequence[Tok], index: int) -> Optional[Tok]:
    return tokens[index] if 0 <= index < len(tokens) else None


def _shape(tokens: Sequence[Tok]) -> List[Tuple[str, str]]:
    return [(t.kind, t.text) for t in tokens]


def _model(source: str) -> List[Tuple[str, str]]:
    return _shape(lex(source, "<model>"))


def _contains(tokens: Sequence[Tok], wanted: Sequence[Tuple[str, str]]) -> bool:
    have = _shape(tokens)
    width = len(wanted)
    first = wanted[0]
    for start in range(len(have) - width + 1):
        if have[start] == first and have[start:start + width] == list(wanted):
            return True
    return False


_OPEN = {"(": ")", "[": "]", "{": "}"}
_CLOSE = frozenset(_OPEN.values())


def _group_end(tokens: Sequence[Tok], open_index: int, path: str) -> int:
    """Index of the token closing the group opened at `open_index`."""
    depth = 0
    for index in range(open_index, len(tokens)):
        tok = tokens[index]
        if tok.kind != "punct":
            continue
        if tok.text in _OPEN:
            depth += 1
        elif tok.text in _CLOSE:
            depth -= 1
            if depth == 0:
                return index
    raise GateError(f"{path}:{tokens[open_index].line}: a `{tokens[open_index].text}` that never closes")


def macro_call_body(tokens: Sequence[Tok], name: str, path: str) -> List[Tok]:
    """The tokens between the braces of the ONE `name! { .. }` call in a file.

    (`macro_rules! name { .. }`, the definition, is `name {` with no `!` between.)
    """
    calls = [
        index
        for index, tok in enumerate(tokens)
        if _is(tok, "ident", name)
        and _is(_at(tokens, index + 1), "punct", "!")
        and _is(_at(tokens, index + 2), "punct", "{")
    ]
    if len(calls) != 1:
        raise GateError(
            f"{path}: expected exactly one `{name}! {{ .. }}` call, found {len(calls)}; "
            "this check reads that call and nothing else"
        )
    opener = calls[0] + 2
    return list(tokens[opener + 1:_group_end(tokens, opener, path)])


class Entry(NamedTuple):
    name: str
    value: Optional[str]  # None: `env!("VAR")`, known only at build time
    line: int
    env: Optional[str]


def parse_entries(
    body: Sequence[Tok], path: str, section: str, *, env_ok: bool, value_required: bool, comma_required: bool
) -> List[Entry]:
    """`name`, `name: "value"` and (where allowed) `name: env!("VAR")`, comma separated."""
    entries: List[Entry] = []
    index, count = 0, len(body)
    while index < count:
        head = body[index]
        if head.kind != "ident":
            raise GateError(f"{path}:{head.line}: in {section}: expected a symbol name, found `{head.text}`")
        name, line = head.text, head.line
        value: Optional[str] = name
        env: Optional[str] = None
        index += 1
        has_value = _is(_at(body, index), "punct", ":")
        if has_value:
            index += 1
            tok = _at(body, index)
            if tok is not None and tok.kind == "str":
                value = tok.text
                index += 1
            elif (
                env_ok
                and _is(tok, "ident", "env")
                and _is(_at(body, index + 1), "punct", "!")
                and _is(_at(body, index + 2), "punct", "(")
                and _at(body, index + 3) is not None
                and body[index + 3].kind == "str"
                and _is(_at(body, index + 4), "punct", ")")
            ):
                value, env = None, body[index + 3].text
                index += 5
            else:
                shown = "nothing" if tok is None else f"`{tok.text}`"
                raise GateError(
                    f"{path}:{line}: in {section}: `{name}` has a value this check cannot read ({shown}); "
                    "only a string literal" + (' or `env!("VAR")`' if env_ok else "") + " is a symbol's value"
                )
        elif value_required:
            raise GateError(f"{path}:{line}: in {section}: `{name}` has no `: \"value\"`")
        if index < count:
            if not _is(body[index], "punct", ","):
                raise GateError(
                    f"{path}:{body[index].line}: in {section}: expected `,` after `{name}`, found `{body[index].text}`"
                )
            index += 1
        elif comma_required:
            raise GateError(f"{path}:{line}: in {section}: the last entry `{name}` has no `,`, which the macro's matcher needs")
        entries.append(Entry(name, value, line, env))
    return entries


class Predefined(NamedTuple):
    section: str  # Keywords | Symbols | AppendOnly | prefill
    name: str
    line: int  # 0 for the generated prefill


class PredefinedSet(NamedTuple):
    by_value: Dict[str, Predefined]
    counts: Dict[str, int]
    env: List[Entry]
    pin: int
    repeats: List[str]


def _require_model(tokens: Sequence[Tok], model: Sequence[Tuple[str, str]], path: str, whose: str) -> None:
    for what, source in model:
        if not _contains(tokens, _model(source)):
            raise GateError(
                f"{path}: {whose} no longer contains {what}:\n"
                f"        {source}\n"
                "    This check's reading of the list is a model of that macro. Re-read the macro, then update\n"
                "    the model in scripts/check_driver_extra_symbols.py in the same commit; do not delete the row."
            )


def read_predefined(symbol_text: str, macro_text: str) -> PredefinedSet:
    """Every string `symbols!` pre-interns, as rustc_macros builds the list."""
    _require_model(lex(macro_text, SYMBOLS_MACRO_RS), SYMBOLS_MACRO_MODEL, SYMBOLS_MACRO_RS, "the `symbols!` macro")
    tokens = lex(symbol_text, SYMBOL_RS)
    body = macro_call_body(tokens, "symbols", SYMBOL_RS)

    sections: Dict[str, List[Tok]] = {}
    order = ("Keywords", "Symbols", "AppendOnly")
    index = 0
    while index < len(body):
        head = body[index]
        expected = order[len(sections)] if len(sections) < len(order) else None
        if head.kind != "ident" or head.text != expected or not _is(_at(body, index + 1), "punct", "{"):
            raise GateError(
                f"{SYMBOL_RS}:{head.line}: `symbols!` holds `{head.text}` where "
                + (f"the `{expected} {{ .. }}` section" if expected else "nothing more")
                + " was expected"
            )
        closer = _group_end(body, index + 1, SYMBOL_RS)
        sections[head.text] = list(body[index + 2:closer])
        index = closer + 1
    for needed in order[:2]:
        if needed not in sections:
            raise GateError(f"{SYMBOL_RS}: `symbols!` has no `{needed} {{ .. }}` section")

    listed: List[Tuple[str, Entry]] = []
    for entry in parse_entries(
        sections["Keywords"], SYMBOL_RS, "Keywords", env_ok=False, value_required=True, comma_required=False
    ):
        listed.append(("Keywords", entry))
    env: List[Entry] = []
    for entry in parse_entries(
        sections["Symbols"], SYMBOL_RS, "Symbols", env_ok=True, value_required=False, comma_required=False
    ):
        if entry.value is None:
            env.append(entry)
        else:
            listed.append(("Symbols", entry))
    numbered = len(listed)  # what the macro has interned when it reaches "0"
    tail = parse_entries(
        sections.get("AppendOnly", []), SYMBOL_RS, "AppendOnly", env_ok=False, value_required=False, comma_required=False
    )

    pins = [
        index
        for index, tok in enumerate(tokens)
        if _is(tok, "ident", "SYMBOL_DIGITS_BASE")
        and _is(_at(tokens, index + 1), "punct", "=")
        and _is(_at(tokens, index + 2), "punct", "=")
        and _at(tokens, index + 3) is not None
        and tokens[index + 3].kind == "lit"
        and tokens[index + 3].text.isdigit()
    ]
    if not pins:
        raise GateError(
            f"{SYMBOL_RS}: no `SYMBOL_DIGITS_BASE == <n>` assertion. That compile-time pin is what this check's\n"
            "    parse of the list is cross-checked against; without it the parse is unverified."
        )
    pin = int(tokens[pins[0] + 3].text)
    if numbered != pin:
        raise GateError(
            f"{SYMBOL_RS}: this check counts {numbered} `Keywords` + non-`env!` `Symbols` entries, and the file's own\n"
            f"    compile-time pin says SYMBOL_DIGITS_BASE == {pin}. One of the two is wrong about the list, so no\n"
            "    verdict is given. (A tree whose pin is stale does not build either.)"
        )

    by_value: Dict[str, Predefined] = {}
    repeats: List[str] = []

    def add(section: str, name: str, value: str, line: int) -> None:
        earlier = by_value.get(value)
        if earlier is not None:
            where = "the generated prefill" if earlier.section == "prefill" else f"{earlier.section} `{earlier.name}` (line {earlier.line})"
            repeats.append(f"{section} `{name}` (line {line}) = {value!r} repeats {where}")
            return
        by_value[value] = Predefined(section, name, line)

    for section, entry in listed:
        add(section, entry.name, entry.value or "", entry.line)
    for value in PREFILL:
        add("prefill", value, value, 0)
    for entry in tail:
        add("AppendOnly", entry.name, entry.value or "", entry.line)

    counts = {
        "Keywords": sum(1 for section, _ in listed if section == "Keywords"),
        "Symbols": sum(1 for section, _ in listed if section == "Symbols"),
        "prefill": len(PREFILL),
        "AppendOnly": len(tail),
    }
    return PredefinedSet(by_value, counts, env, pin, repeats)


def read_driver_list(text: str, path: str) -> List[Entry]:
    """The extra symbols a driver's `generate! { .. }` call declares, in order."""
    tokens = lex(text, path)
    _require_model(tokens, LIST_MACRO_MODEL, path, "the list file")
    return parse_entries(
        macro_call_body(tokens, "generate", path),
        path,
        "`generate!`",
        env_ok=False,
        value_required=False,
        comma_required=True,
    )


# --------------------------------------------------------------------------
# Every use of the mechanism, classified.
# --------------------------------------------------------------------------


class Site(NamedTuple):
    path: str
    line: int
    kind: str  # empty | list | declaration | pass-through | unread
    text: str


_EMPTY_EXPRS = [_model(source) for source in ("Vec::new()", "vec![]", "&[]")]
_TYPE_EXPRS = [_model(source) for source in ("&[&'static str]", "Vec<&'static str>")]
_LIST_TAIL = _model("EXTRA_SYMBOLS.into()")


def _expr_end(tokens: Sequence[Tok], start: int) -> int:
    """One past the expression at `start`: a `,` or `;` at depth 0, or the enclosing closer."""
    depth = 0
    index = start
    while index < len(tokens):
        tok = tokens[index]
        if tok.kind == "punct":
            if tok.text in _OPEN:
                depth += 1
            elif tok.text in _CLOSE:
                if depth == 0:
                    return index
                depth -= 1
            elif depth == 0 and tok.text in (",", ";"):
                return index
        index += 1
    return index


def _call_args(tokens: Sequence[Tok], open_index: int) -> Optional[List[List[Tok]]]:
    """The arguments of the call whose `(` is at `open_index`, split at depth-0 commas."""
    args: List[List[Tok]] = []
    current: List[Tok] = []
    depth = 0
    index = open_index + 1
    while index < len(tokens):
        tok = tokens[index]
        if tok.kind == "punct":
            if tok.text in _OPEN:
                depth += 1
            elif tok.text in _CLOSE:
                if depth == 0:
                    if current or args:
                        args.append(current)
                    return args
                depth -= 1
            elif tok.text == "," and depth == 0:
                args.append(current)
                current = []
                index += 1
                continue
        current.append(tok)
        index += 1
    return None


def _source(tokens: Sequence[Tok]) -> str:
    return " ".join(repr(t.text) if t.kind == "str" else t.text for t in tokens)


def _is_list_reference(expr: Sequence[Tok]) -> bool:
    shape = _shape(expr)
    width = len(_LIST_TAIL)
    if len(shape) <= width or shape[-width:] != _LIST_TAIL:
        return False
    return all(kind == "ident" or (kind, text) == ("punct", ":") for kind, text in shape[:-width])


def classify_sites(path: str, tokens: Sequence[Tok]) -> List[Site]:
    """Each use of the extra-symbol mechanism in one file."""
    mechanism = path in MECHANISM
    list_site = any(path in driver.site_paths for driver in DRIVERS)
    sites: List[Site] = []
    for index, tok in enumerate(tokens):
        if tok.kind != "ident":
            continue
        if tok.text == "extra_symbols":
            after, after2 = _at(tokens, index + 1), _at(tokens, index + 2)
            field = _is(after, "punct", ":") and not _is(after2, "punct", ":")
            assign = _is(after, "punct", "=") and not _is(after2, "punct", "=")
            if field or assign:
                expr = list(tokens[index + 2:_expr_end(tokens, index + 2)])
                shape = _shape(expr)
                shown = f"extra_symbols {after.text} {_source(expr)}"
                if shape in _EMPTY_EXPRS:
                    kind = "empty"
                elif field and mechanism and shape in _TYPE_EXPRS:
                    kind = "declaration"
                elif assign and list_site and _is_list_reference(expr):
                    kind = "list"
                else:
                    kind = "unread"
                sites.append(Site(path, tok.line, kind, shown))
            else:
                passed = mechanism and after is not None and after.kind == "punct" and after.text in (",", ")")
                shown = _source(tokens[max(0, index - 2):index + 2])
                sites.append(Site(path, tok.line, "pass-through" if passed else "unread", shown))
            continue

        callee = None
        if tok.text == "create_session_globals_then":
            callee = "create_session_globals_then"
        elif (
            tok.text == "new"
            and _is(_at(tokens, index - 1), "punct", ":")
            and _is(_at(tokens, index - 2), "punct", ":")
            and _is(_at(tokens, index - 3), "ident", "SessionGlobals")
        ):
            callee = "SessionGlobals::new"
        if callee is None or _is(_at(tokens, index - 1), "ident", "fn"):
            continue
        opener = index + 1
        if (
            _is(_at(tokens, opener), "punct", ":")
            and _is(_at(tokens, opener + 1), "punct", ":")
            and _is(_at(tokens, opener + 2), "punct", "<")
        ):
            depth = 0
            for probe in range(opener + 2, len(tokens)):
                if _is(tokens[probe], "punct", "<"):
                    depth += 1
                elif _is(tokens[probe], "punct", ">"):
                    depth -= 1
                    if depth == 0:
                        opener = probe + 1
                        break
        if not _is(_at(tokens, opener), "punct", "("):
            continue  # an import or a path, not a call
        args = _call_args(tokens, opener)
        second = args[1] if args is not None and len(args) >= 2 else None
        shown = f"{callee}(.., {_source(second) if second is not None else '?'}, ..)"
        if second is not None and _shape(second) in _EMPTY_EXPRS:
            kind = "empty"
        elif second is not None and mechanism and _shape(second) == [("ident", "extra_symbols")]:
            kind = "pass-through"
        else:
            kind = "unread"
        sites.append(Site(path, tok.line, kind, shown))
    return sites


# --------------------------------------------------------------------------
# The two readings of a tree.
# --------------------------------------------------------------------------

_GIT_ENV: Optional[Dict[str, str]] = None


def git_env() -> Dict[str, str]:
    """The environment minus git's repository-local variables (GIT_DIR and friends)."""
    global _GIT_ENV
    if _GIT_ENV is None:
        proc = subprocess.run(["git", "rev-parse", "--local-env-vars"], capture_output=True, text=True)
        if proc.returncode != 0:
            raise GateError(f"`git rev-parse --local-env-vars` failed: {proc.stderr.strip()}")
        local = set(proc.stdout.split())
        _GIT_ENV = {key: value for key, value in os.environ.items() if key not in local}
    return _GIT_ENV


def run_git(cwd: pathlib.Path, args: Sequence[str], ok: Sequence[int] = (0,)) -> Tuple[int, bytes]:
    proc = subprocess.run(["git", "-C", str(cwd), *args], capture_output=True, env=git_env())
    if proc.returncode not in ok:
        err = proc.stderr.decode("utf-8", "replace").strip()
        raise GateError(f"`git -C {cwd} {' '.join(args)}` failed (exit {proc.returncode}): {err}")
    return proc.returncode, proc.stdout


def _scan_args() -> List[str]:
    args = ["grep", "-l", "-z", "-I", "-F"]
    for needle in NEEDLES:
        args += ["-e", needle]
    return args


def _scan_pathspecs() -> List[str]:
    return ["--", *SCAN_ROOTS, *[f":(exclude){path}" for path in SCAN_EXCLUDE]]


def _decode(raw: bytes, path: str) -> str:
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise GateError(f"{path}: not UTF-8: {error}") from None


class WorkingTree:
    """Files as they sit on disk: tracked, and untracked but not ignored."""

    def __init__(self, root: pathlib.Path) -> None:
        self.root = root

    def read(self, path: str) -> Optional[str]:
        target = self.root / path
        if not target.exists():
            return None
        if not target.is_file():
            raise GateError(f"{path}: not a regular file in the working tree")
        return _decode(target.read_bytes(), path)

    def candidates(self) -> List[str]:
        _, out = run_git(self.root, [*_scan_args(), "--untracked", *_scan_pathspecs()], ok=(0, 1))
        return sorted(name for name in out.decode("utf-8", "surrogateescape").split("\0") if name.endswith(".rs"))


class CommittedTree:
    """Files as one commit's tree holds them, read from the object store."""

    def __init__(self, root: pathlib.Path, tree: str) -> None:
        self.root, self.tree = root, tree

    def read(self, path: str) -> Optional[str]:
        _, out = run_git(self.root, ["ls-tree", "-z", self.tree, "--", path])
        rows = [row for row in out.decode("utf-8", "surrogateescape").split("\0") if row]
        if not rows:
            return None
        meta, _, name = rows[0].partition("\t")
        fields = meta.split()
        if len(rows) != 1 or name != path or len(fields) != 3 or fields[1] != "blob" or fields[0] not in ("100644", "100755"):
            raise GateError(f"{path}: not a regular file in the pushed tree ({meta})")
        _, blob = run_git(self.root, ["cat-file", "blob", fields[2]])
        return _decode(blob, path)

    def candidates(self) -> List[str]:
        _, out = run_git(self.root, [*_scan_args(), self.tree, *_scan_pathspecs()], ok=(0, 1))
        prefix = self.tree + ":"
        names = []
        for name in out.decode("utf-8", "surrogateescape").split("\0"):
            if not name:
                continue
            if not name.startswith(prefix):
                raise GateError(f"`git grep` printed a name outside the tree it was given: {name!r}")
            names.append(name[len(prefix):])
        return sorted(name for name in names if name.endswith(".rs"))


# --------------------------------------------------------------------------
# The verdict for one tree.
# --------------------------------------------------------------------------


def _quoted(value: str) -> str:
    return '"' + value.encode("unicode_escape").decode("ascii").replace('"', '\\"') + '"'


def judge(tree, listing: bool) -> Tuple[List[str], int]:
    """(report lines, findings) for one tree. A GateError means it could not be judged."""
    out: List[str] = []
    findings = 0

    symbol_text = tree.read(SYMBOL_RS)
    macro_text = tree.read(SYMBOLS_MACRO_RS)
    if symbol_text is None or macro_text is None:
        missing = SYMBOL_RS if symbol_text is None else SYMBOLS_MACRO_RS
        raise GateError(f"{missing} is absent; there is no predefined list to compare with")
    predefined = read_predefined(symbol_text, macro_text)
    counts = predefined.counts
    out.append(
        f"predefined: {len(predefined.by_value)} strings from {SYMBOL_RS}: Keywords {counts['Keywords']} + Symbols "
        f"{counts['Symbols']} = {predefined.pin} (the file's own SYMBOL_DIGITS_BASE pin), {counts['prefill']} generated "
        f"digits and letters, AppendOnly {counts['AppendOnly']}"
    )
    for entry in predefined.env:
        out.append(f"  NOT JUDGED  `{entry.name}` (line {entry.line}) = env!(\"{entry.env}\"): its string exists only at build time")
    for repeat in predefined.repeats:
        findings += 1
        out.append(f"  REPEAT      {repeat} (the `symbols!` macro refuses this too)")

    sites: List[Site] = []
    for path in tree.candidates():
        text = tree.read(path)
        if text is None:
            raise GateError(f"{path}: found by the scan and then absent")
        sites.extend(classify_sites(path, lex(text, path)))

    for driver in DRIVERS:
        list_text = tree.read(driver.list_path)
        handed = [site for site in sites if site.kind == "list" and site.path in driver.site_paths]
        present = [path for path in driver.site_paths if tree.read(path) is not None]
        if list_text is None and not present:
            out.append(f"driver {driver.name}: ABSENT from this tree ({driver.list_path} and its site file(s)); not judged")
            continue
        if list_text is None:
            findings += 1
            out.append(
                f"driver {driver.name}: MISSING LIST  {', '.join(present)} exist(s) but {driver.list_path} does not. "
                "Update DRIVERS in scripts/check_driver_extra_symbols.py to where the list lives now."
            )
            continue
        entries = read_driver_list(list_text, driver.list_path)
        where = ", ".join(f"{site.path}:{site.line}" for site in handed)
        out.append(f"driver {driver.name}: {len(entries)} extra symbols in {driver.list_path}; handed to the interner at {where or 'NO SITE'}")
        if not handed:
            findings += 1
            out.append(
                f"  NOT HANDED OVER  no `<x>.extra_symbols = <path>::EXTRA_SYMBOLS.into();` in {', '.join(driver.site_paths)}. "
                "Either the driver changed how it passes its list (then it shows as UNREAD below) or the list is dead; "
                "update DRIVERS in scripts/check_driver_extra_symbols.py."
            )
        seen: Dict[str, Entry] = {}
        for entry in entries:
            value = entry.value or ""
            if listing:
                out.append(f"  extra       {entry.name} = {_quoted(value)}")
            hit = predefined.by_value.get(value)
            if hit is not None:
                findings += 1
                origin = (
                    "one of the generated digit and letter symbols"
                    if hit.section == "prefill"
                    else f"{hit.section} `{hit.name}`, {SYMBOL_RS}:{hit.line}"
                )
                out.append(
                    f"  COLLISION   `{entry.name}` ({driver.list_path}:{entry.line}) = {_quoted(value)} is pre-interned by rustc_span: {origin}"
                )
            earlier = seen.get(value)
            if earlier is not None:
                findings += 1
                out.append(
                    f"  REPEAT      `{entry.name}` ({driver.list_path}:{entry.line}) = {_quoted(value)} is also `{earlier.name}` "
                    f"(line {earlier.line}) in the same list"
                )
            seen.setdefault(value, entry)

    tally: Dict[str, int] = {}
    for site in sites:
        tally[site.kind] = tally.get(site.kind, 0) + 1
    files = len({site.path for site in sites})
    summary = ", ".join(f"{tally[kind]} {kind}" for kind in ("list", "empty", "declaration", "pass-through", "unread") if kind in tally)
    out.append(f"mechanism: {len(sites)} use(s) of it in {files} file(s) under {' '.join(SCAN_ROOTS)}: {summary or 'none'}")
    for site in sites:
        if site.kind == "unread":
            findings += 1
            out.append(
                f"  UNREAD      {site.path}:{site.line}: `{site.text}` passes extra symbols in a way this check does not read. "
                "If it is a new driver's list, add it to DRIVERS; never leave a list unread."
            )
        elif listing:
            out.append(f"  {site.kind:<13}{site.path}:{site.line}: {site.text}")
    return out, findings


REMEDY = """\
    Every start of that driver panics in `Interner::prefill`
    ("duplicate symbols in the rustc symbol list and the extra symbols added by the driver"),
    whatever it was asked to do; its `--version` still answers, so nothing else shows it.
    Fix: delete the name from the DRIVER's list. Its list file re-exports `rustc_span::sym::*`,
    so `sym::<Name>` then resolves to rustc_span's constant for the same string.
    See docs/FROZEN_STD_SYMBOL_INDEX_ABI.md, section 4a."""


def report(verdicts: Sequence[Tuple[str, Optional[List[str]], int, Optional[str]]]) -> int:
    """Print each tree's verdict; 0 clean, 1 findings, 2 a tree that could not be judged."""
    findings = sum(count for _, _, count, _ in verdicts)
    unjudged = [label for label, _, _, error in verdicts if error is not None]
    for label, lines, _, error in verdicts:
        if label:
            print(f"--- {label}")
        for line in lines or []:
            print(line)
        if error is not None:
            print(f"  ERROR       {error}")
    sys.stdout.flush()  # the verdict goes to stderr; keep it AFTER the rows it summarizes
    if findings:
        print(f"check_driver_extra_symbols: FAIL — {findings} finding(s).\n{REMEDY}", file=sys.stderr)
        return 1
    if unjudged:
        print(
            f"check_driver_extra_symbols: COULD NOT JUDGE {len(unjudged)} tree(s) — not a pass (see ERROR above)",
            file=sys.stderr,
        )
        return 2
    print("check_driver_extra_symbols: OK — no extra symbol repeats a predefined one")
    return 0


def _judge_one(label: str, tree, listing: bool) -> Tuple[str, Optional[List[str]], int, Optional[str]]:
    try:
        lines, findings = judge(tree, listing)
    except GateError as error:
        return (label, None, 0, str(error))
    return (label, lines, findings, None)


def is_toplevel(path: pathlib.Path) -> bool:
    if not path.is_dir():
        return False
    try:
        _, out = run_git(path, ["rev-parse", "--show-toplevel"])
    except GateError:
        return False
    return pathlib.Path(out.decode("utf-8", "surrogateescape").strip()).resolve() == path.resolve()


def parse_pushed_refs(raw: str) -> List[Tuple[str, str]]:
    """(local_ref, local_sha) per TRUST_PUSHED_REFS line; malformed input is a GateError."""
    pushed = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 4 or not HEX_SHA.match(fields[1]) or not HEX_SHA.match(fields[3]):
            raise GateError(
                f"malformed TRUST_PUSHED_REFS line {line!r}; expected `<local_ref> <local_sha> <remote_ref> <remote_sha>`"
            )
        pushed.append((fields[0], fields[1]))
    return pushed


def judge_commits(root: pathlib.Path, named: Sequence[Tuple[str, str]], listing: bool, subject: str) -> int:
    """One verdict per DISTINCT tree among `named` (label, commit-ish)."""
    labels: Dict[str, List[str]] = {}
    verdicts: List[Tuple[str, Optional[List[str]], int, Optional[str]]] = []
    for label, commit in named:
        try:
            _, out = run_git(root, ["rev-parse", "--verify", "--quiet", f"{commit}^{{tree}}"])
        except GateError:
            verdicts.append((label, None, 0, f"{commit} does not name a tree in {root}; a push this check cannot read is not a pass"))
            continue
        labels.setdefault(out.decode("ascii").strip(), []).append(label)
    names = ", ".join(label for group in labels.values() for label in group) or "none readable"
    print(f"SUBJECT: {subject.format(names=names)}", flush=True)
    many = len(labels) + len(verdicts) > 1
    for tree, group in labels.items():
        verdicts.append(_judge_one(", ".join(group) if many else "", CommittedTree(root, tree), listing))
    return report(verdicts)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], add_help=True)
    parser.add_argument("--rev", action="append", default=[], metavar="REV", help="judge this commit's tree from git objects (repeatable)")
    parser.add_argument("--list", action="store_true", help="also print every extra symbol and every use of the mechanism that was read")
    try:
        args = parser.parse_args(argv)
    except SystemExit as stop:
        return 0 if stop.code == 0 else 2
    root = pathlib.Path(__file__).resolve().parents[1]
    try:
        if not is_toplevel(root):
            raise GateError(f"{root} is not the top of a git worktree; this check enumerates sources with git")
        if args.rev:
            return judge_commits(
                root, [(rev, rev) for rev in args.rev], args.list, "the tree(s) of {names} (--rev), not the working tree"
            )
        raw = os.environ.get("TRUST_PUSHED_REFS", "")
        if raw.strip():
            pushed = parse_pushed_refs(raw)
            live = [(f"{ref} {sha[:12]}", sha) for ref, sha in pushed if not ZERO_SHA.match(sha)]
            deletions = len(pushed) - len(live)
            if not live:
                print(f"SUBJECT: the pushed trees (TRUST_PUSHED_REFS: {deletions} deletion(s), nothing else)", flush=True)
                print("SKIPPED: deletion(s) only, no tree pushed — nothing to judge")
                return 0
            extra = f"; {deletions} deletion(s) not judged" if deletions else ""
            return judge_commits(
                root, live, args.list, "the pushed trees (TRUST_PUSHED_REFS: {names}" + extra + "), not the working tree"
            )
        print(f"SUBJECT: the working tree at {root} (no push in flight: TRUST_PUSHED_REFS unset or empty)", flush=True)
        return report([_judge_one("", WorkingTree(root), args.list)])
    except GateError as error:
        print(f"check_driver_extra_symbols: COULD NOT JUDGE — {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
