#!/usr/bin/env python3
"""VF3's census of current proved rows by fragment (proven-core plan VF3, SBC M0.7).

Plan of record: docs/plans/2026-10-15-proven-core.md, VF3 («a committed census of proved rows by
fragment, restricted to functions the producer admits»; accept «A script regenerates the census
under `docs/trust-core/denominators/` byte for byte») and Theorem 3's measure («"Proved (calculus)"
rows over the census denominator, per fragment, with `vacuous-pre` rows counted apart»). VF5's
accept item 5 takes its N from this census.

The record is docs/trust-core/denominators/vf3-proved-census.tsv. It is not an E0.12 Stage 0.5
record (those are the `*.toml` files scripts/trust_core/denominators.py registers); it sits beside
them because VF3 names that directory. It changes only through this script:

  python3.14 scripts/trust_core/vf3_census.py --write --rev <commit>   measure at <commit>, write
  python3.14 scripts/trust_core/vf3_census.py --check                  re-measure at the record's
                                                                        pin; exit 1 on any drift
  python3.14 scripts/trust_core/vf3_census.py --current                is the record stale at HEAD?

Every number is recomputed from git objects at the pin (common.GitTree), never from a working
tree, so a re-run on any clone that holds the pin reproduces the record byte for byte.

WHAT A ROW IS. The census reads the committed expectations of the compiler's own UI suite: what the
tree asserts trustc proves today, without building a compiler. A ROW is one block

    note: Trust verification: P proved, F failed, U unknown, T timed out, R runtime-checked[, A assumed (requires)] out of N obligation(s)
      --> $DIR/<file>.rs:L:C

in an expected `.stderr` of a test under tests/ui/ (one row per test, revision and anchored line).
A row is PROVED iff F = U = T = R = 0, P >= 1 and P + A = N. Any other count word, or counts that do
not add up, is a hard error (exit 2), never a skipped row.

THE PRODUCER RESTRICTION. A row is `admitted` iff its revision's flags make `-Ztrust-ir-lower=strict`
effective (the last `-Ztrust-ir-lower` spelling is `strict` and `-Ztrust-verify` is not `off`) and
its stderr carries no `-Ztrust-ir-lower=strict:` error: under strict, a body the THIR producer
cannot fully lower, or whose trust-ir disagrees with its MIR, is a compile error
(compiler/rustc_session/src/options.rs `trust_ir_lower`). Every other row is `unmeasured`: a
coverage-only skip leaves no mark in the stderr, so admission is not known from the tree. An
unmeasured row is never counted as admitted, and a restricted count that has unmeasured rows in
its fragment is published as `blocked`, never as a measured N.

THE FRAGMENT is source-syntactic: the anchored item's signature and body are read from the test's
`.rs` and every construct the classifier recognises names the smallest fragment that contains it
(the row's `features` column lists them). The fragments are the plan's: F1 scalar acyclic
(VF5: bool and integers up to 64 bits, acyclic control, + - and multiplication by a constant,
/ %); F1-bv (VF7's extension: bitwise operations, shifts, wrapping and nonlinear arithmetic, casts,
wider integers); F2 loops, calls and contracts (VF8); F3 references, raw pointers and unsafe (VF9);
F4 aggregates, slices, std and unwinding (VF10); `outside` (floats, closures, generics, traits,
async). The row's fragment is the largest its features need. A construct the classifier does not
recognise is the feature `unrecognised:<token>` and puts the row `outside`, so an approximation
only ever moves a row up the ladder, never into F1.

VACUOUS-PRE. A row whose function has a `requires` clause (or an `assumed (requires)` count) is
labelled `vacuous-pre`: no kernel-checked witness `∃ args μ. pre_f args μ` exists in this tree
(plan, "Non-vacuity of a row"). Such rows are counted apart.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

SCHEMA = "trust.core.vf3-census.v1"
RECORD_REL = "docs/trust-core/denominators/vf3-proved-census.tsv"
SCRIPT_REL = "scripts/trust_core/vf3_census.py"
UI_ROOT = "tests/ui/"
FRAGMENTS = ("F1", "F1-bv", "F2", "F3", "F4", "outside")
RANK = {f: i for i, f in enumerate(FRAGMENTS)}

REPORT = re.compile(r"^note: Trust verification: (?P<counts>.*) out of (?P<total>\d+) obligation\(s\)$")
COUNT = re.compile(r"^(\d+) (proved|failed|unknown|timed out|runtime-checked|assumed \(requires\))$")
ANCHOR = re.compile(r"^\s*--> \$DIR/(?P<path>[^:]+):(?P<line>\d+):(?P<col>\d+)$")
KERNEL = re.compile(r"^\s*= note: of which (\d+) kernel-certified by the clean CIC kernel")
STRICT_ERROR = "-Ztrust-ir-lower=strict:"
HEADER = re.compile(r"^\s*//@\s*(?:\[(?P<revs>[^\]]+)\])?\s*(?P<key>[a-z-]+)\s*(?::\s*(?P<value>.*))?$")


class CensusError(Exception):
    """An expectation the census cannot read. Exit 2: never a skipped row."""


# --------------------------------------------------------------------------
# lexing Rust source (comments dropped, literals kept as one token)
# --------------------------------------------------------------------------

TOKEN = re.compile(r"""
    (?P<ws>\s+)
  | (?P<line_comment>//[^\n]*)
  | (?P<block_comment>/\*)
  | (?P<raw_str>b?r(?P<hashes>\#*)")
  | (?P<str>b?"(?:\\.|[^"\\])*")
  | (?P<char>b?'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^'\\\n])')
  | (?P<lifetime>'[A-Za-z_][A-Za-z0-9_]*)
  | (?P<float>\d[\d_]*\.\d[\d_]*(?:[eE][+-]?\d+)?(?:f32|f64)?|\d[\d_]*(?:f32|f64)\b)
  | (?P<int>0x[0-9a-fA-F_]+|0o[0-7_]+|0b[01_]+|\d[\d_]*)(?P<suffix>(?:[iu](?:8|16|32|64|128|size))?)
  | (?P<ident>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<punct>\.\.=|\.\.\.|<<=|>>=|::|->|=>|==|!=|<=|>=|&&|\|\||<<|>>|\+=|-=|\*=|/=|%=|\^=|&=|\|=|\.\.|[-+*/%^!&|=<>@.,;:\#$?~()\[\]{}])
""", re.VERBOSE)


@dataclass(frozen=True)
class Tok:
    kind: str  # ident, int, float, str, char, lifetime, punct
    text: str
    line: int


def lex(text: str) -> list[Tok]:
    out, pos, line = [], 0, 1
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m:
            out.append(Tok("punct", text[pos], line))
            line += text[pos] == "\n"
            pos += 1
            continue
        kind = m.lastgroup if m.lastgroup not in ("hashes", "suffix") else None
        for name in ("ws", "line_comment", "block_comment", "raw_str", "str", "char", "lifetime", "float", "int", "ident", "punct"):
            if m.group(name) is not None:
                kind = name
                break
        end = m.end()
        if kind == "block_comment":
            depth, end = 1, pos + 2
            while depth and end < len(text):
                if text.startswith("/*", end):
                    depth, end = depth + 1, end + 2
                elif text.startswith("*/", end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
        elif kind == "raw_str":
            close = '"' + m.group("hashes")
            found = text.find(close, end)
            end = len(text) if found < 0 else found + len(close)
            kind = "str"
        if kind not in ("ws", "line_comment", "block_comment"):
            out.append(Tok(kind, text[pos:end], line))
        line += text.count("\n", pos, end)
        pos = end
    return out


# --------------------------------------------------------------------------
# the fragment classifier
# --------------------------------------------------------------------------

SCALAR_TYPES = {"bool", "i8", "i16", "i32", "i64", "isize", "u8", "u16", "u32", "u64", "usize"}
WIDE_TYPES = {"i128", "u128"}
FLOAT_TYPES = {"f32", "f64"}
# Inherent integer methods whose value is a scalar: bit-vector semantics (VF7's extension of F1).
SCALAR_BV_METHODS = {
    "wrapping_add", "wrapping_sub", "wrapping_mul", "wrapping_neg", "wrapping_shl", "wrapping_shr",
    "rotate_left", "rotate_right", "count_ones", "count_zeros", "leading_zeros", "trailing_zeros",
    "leading_ones", "trailing_ones", "swap_bytes", "reverse_bits", "is_power_of_two", "saturating_add",
    "saturating_sub", "saturating_mul", "rem_euclid", "div_euclid", "abs", "signum", "pow", "min",
    "max", "is_negative", "is_positive", "abs_diff", "unsigned_abs",
}
KEYWORDS_F1 = {"let", "mut", "if", "else", "return", "true", "false", "const", "pub", "fn", "crate", "in"}
KEYWORD_FEATURES = {
    "loop": ("F2", "loop"), "while": ("F2", "loop"), "for": ("F2", "loop"), "break": ("F2", "loop"),
    "continue": ("F2", "loop"), "unsafe": ("F3", "unsafe"), "async": ("outside", "async"),
    "await": ("outside", "async"), "dyn": ("outside", "dyn"), "impl": ("outside", "impl-trait"),
    "move": ("outside", "closure"), "static": ("F3", "static"), "match": None, "as": ("F1-bv", "cast"),
    "struct": ("F4", "local-item"), "enum": ("F4", "local-item"), "where": ("outside", "generic"),
    "self": ("F4", "self"), "Self": ("F4", "self"), "super": ("F4", "path"), "ref": ("F3", "ref-pattern"),
    "yield": ("outside", "coroutine"), "type": ("outside", "local-item"), "trait": ("outside", "local-item"),
    "use": ("F4", "local-item"), "mod": ("F4", "local-item"), "extern": ("outside", "extern"),
}
OPERAND_END = {"ident", "int", "float", "str", "char"}
LIT_PATTERN = {"_", "|", "..=", "..", "true", "false", "-"}


def is_operand_end(prev: Tok | None) -> bool:
    if prev is None:
        return False
    if prev.kind == "ident":
        return prev.text not in {"return", "in", "if", "else", "match", "let", "mut", "as", "while", "for", "loop"}
    return prev.kind in OPERAND_END or prev.text in (")", "]", "}") or prev.kind == "int"


class Features:
    def __init__(self) -> None:
        self.found: dict[str, str] = {}

    def add(self, fragment: str, name: str) -> None:
        if name not in self.found or RANK[fragment] > RANK[self.found[name]]:
            self.found[name] = fragment

    def fragment(self) -> str:
        return max(self.found.values(), key=RANK.__getitem__, default="F1")

    def listed(self) -> str:
        return ",".join(sorted(self.found)) or "-"


def classify_type(toks: list[Tok], feats: Features) -> None:
    """A parameter or return type, as tokens."""
    if not toks:
        return
    texts = [t.text for t in toks]
    if texts == ["(", ")"]:
        return
    if texts[0] == "&" or texts[0] == "&&":
        feats.add("F3", "ref-type")
        rest = toks[1:]
        while rest and (rest[0].kind == "lifetime" or rest[0].text == "mut"):
            rest = rest[1:]
        classify_type(rest, feats)
        return
    if texts[0] == "*" and len(texts) > 1 and texts[1] in ("const", "mut"):
        feats.add("F3", "raw-pointer-type")
        classify_type(toks[2:], feats)
        return
    if len(toks) == 1 and toks[0].kind == "ident":
        name = toks[0].text
        if name in SCALAR_TYPES:
            return
        if name in WIDE_TYPES:
            feats.add("F1-bv", "wide-int")
        elif name in FLOAT_TYPES:
            feats.add("outside", "float")
        elif name == "char":
            feats.add("F4", "char")
        elif name in ("str", "String"):
            feats.add("F4", "str")
        else:
            feats.add("F4", "adt-type")
        return
    if texts[0] == "[":
        feats.add("F4", "array-or-slice-type")
    elif texts[0] == "(":
        feats.add("F4", "tuple-type")
    elif texts[0] in ("impl", "dyn"):
        feats.add("outside", texts[0] if texts[0] == "dyn" else "impl-trait")
    elif texts[0] == "fn":
        feats.add("outside", "fn-pointer")
    else:
        feats.add("F4", "adt-type")


def split_depth0(toks: list[Tok], sep: str) -> list[list[Tok]]:
    parts, cur, depth = [], [], 0
    for t in toks:
        if t.text in ("(", "[", "{", "<"):
            depth += 1
        elif t.text in (")", "]", "}", ">"):
            depth -= 1
        elif t.text == ">>":
            depth -= 2
        if t.text == sep and depth == 0:
            parts.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur:
        parts.append(cur)
    return parts


@dataclass
class Item:
    name: str
    signature: list[Tok]  # from `fn` to the parameter list's close, inclusive
    params: list[Tok]
    ret: list[Tok]
    clauses: list[Tok]  # everything between the return type and the body's `{`
    body: list[Tok]
    attrs: list[str]


def find_item(source: str, line: int) -> Item | None:
    """The `fn` item whose span starts on `line` (1-based), or None when that line starts none."""
    toks = lex(source)
    start = next((i for i, t in enumerate(toks) if t.line == line), None)
    if start is None:
        return None
    i = start
    while i < len(toks) and toks[i].line == line and toks[i].text != "fn":
        i += 1
    if i >= len(toks) or toks[i].text != "fn" or toks[i].line != line:
        return None
    attrs = []
    j = start - 1
    while j >= 0 and toks[j].text == "]":  # attributes directly above the item
        depth, k = 0, j
        while k >= 0:
            depth += toks[k].text == "]"
            depth -= toks[k].text == "["
            if depth == 0:
                break
            k -= 1
        if k < 1 or toks[k - 1].text != "#":
            break
        attrs.append(" ".join(t.text for t in toks[k + 1:j]))
        j = k - 2
    name = toks[i + 1].text if i + 1 < len(toks) else "?"
    k = i + 2
    generic = []
    if k < len(toks) and toks[k].text == "<":
        depth = 0
        while k < len(toks):
            depth += toks[k].text == "<"
            depth -= toks[k].text == ">"
            depth -= 2 * (toks[k].text == ">>")
            generic.append(toks[k])
            k += 1
            if depth <= 0:
                break
    if k >= len(toks) or toks[k].text != "(":
        return None
    depth, p = 0, k
    while p < len(toks):
        depth += toks[p].text in ("(", "[", "{")
        depth -= toks[p].text in (")", "]", "}")
        if depth == 0:
            break
        p += 1
    params = toks[k + 1:p]
    q = p + 1
    ret = []
    if q < len(toks) and toks[q].text == "->":
        q += 1
        depth = 0
        while q < len(toks):
            t = toks[q]
            if depth == 0 and (t.text == "{" or (t.kind == "ident" and t.text in ("requires", "ensures", "where", "decreases"))):
                break
            depth += t.text in ("(", "[", "<")
            depth -= t.text in (")", "]", ">")
            ret.append(t)
            q += 1
    clauses = []
    depth = 0
    while q < len(toks) and not (toks[q].text == "{" and depth == 0):
        depth += toks[q].text in ("(", "[")
        depth -= toks[q].text in (")", "]")
        clauses.append(toks[q])
        q += 1
    if q >= len(toks):
        return None
    depth, b = 0, q
    while b < len(toks):
        depth += toks[b].text == "{"
        depth -= toks[b].text == "}"
        if depth == 0:
            break
        b += 1
    sig = toks[i:p + 1]
    item = Item(name, sig, params, ret, clauses, toks[q + 1:b], attrs)
    item.generic = generic  # type: ignore[attr-defined]
    return item


def defined_fns(source: str) -> set[str]:
    toks = lex(source)
    return {toks[i + 1].text for i, t in enumerate(toks[:-1]) if t.text == "fn" and toks[i + 1].kind == "ident"}


CONTRACT_FEATURES = ("requires", "ensures", "decreases")


def classify(item: Item, local_fns: set[str], before_fn: list[Tok]) -> tuple[str, str, str, bool]:
    """(fragment, body fragment, features, has_requires). The body fragment leaves out the
    function's own contract clauses: the fragment its safety rows alone would need."""
    feats = Features()
    for t in before_fn:
        if t.text in ("unsafe",):
            feats.add("F3", "unsafe")
        elif t.text in ("async",):
            feats.add("outside", "async")
        elif t.text == "extern":
            feats.add("outside", "extern")
    generic = getattr(item, "generic", [])
    if any(t.kind == "ident" for t in generic):
        feats.add("outside", "generic")
    for part in split_depth0(item.params, ","):
        texts = [t.text for t in part]
        if "self" in texts:
            feats.add("F3" if "&" in texts else "F4", "self")
            continue
        colon = next((n for n, t in enumerate(part) if t.text == ":" and n > 0), None)
        if colon is None:
            feats.add("outside", "unrecognised:param")
            continue
        pattern = part[:colon]
        if any(t.text in ("(", "[", "{") for t in pattern):
            feats.add("F4", "pattern-param")
        classify_type(part[colon + 1:], feats)
    classify_type(item.ret, feats)
    clause_words = {t.text for t in item.clauses if t.kind == "ident"}
    attr_words = " ".join(item.attrs)
    has_requires = "requires" in clause_words or re.search(r"\brequires\b", attr_words) is not None
    if has_requires:
        feats.add("F2", "requires")
    if "ensures" in clause_words or re.search(r"\bensures\b", attr_words):
        feats.add("F2", "ensures")
    if "decreases" in clause_words:
        feats.add("F2", "decreases")
    if "where" in clause_words:
        feats.add("outside", "generic")
    classify_body(item, local_fns, feats)
    body_only = Features()
    for name, frag in feats.found.items():
        if name not in CONTRACT_FEATURES:
            body_only.add(frag, name)
    return feats.fragment(), body_only.fragment(), feats.listed(), has_requires


def classify_body(item: Item, local_fns: set[str], feats: Features) -> None:
    body = item.body
    prev: Tok | None = None
    patterns: set[int] = set()  # token indices inside a `match` arm's pattern
    for n, t in enumerate(body):
        nxt = body[n + 1] if n + 1 < len(body) else None
        x = t.text
        if n in patterns:
            prev = t
            continue
        if t.kind == "str":
            feats.add("F4", "str")
        elif t.kind == "char":
            feats.add("F4", "char")
        elif t.kind == "float":
            feats.add("outside", "float")
        elif t.kind == "lifetime":
            feats.add("F2", "loop-label") if nxt is not None and nxt.text == ":" else feats.add("F3", "lifetime")
        elif t.kind == "int":
            suffix = re.search(r"(i128|u128)$", x)
            if suffix:
                feats.add("F1-bv", "wide-int")
        elif t.kind == "ident":
            if (nxt is not None and nxt.text == "!" and x not in KEYWORD_FEATURES and x not in KEYWORDS_F1
                    and (n + 2 >= len(body) or body[n + 2].text != "=")):
                feats.add("F4", f"macro:{x}")
            elif x in KEYWORD_FEATURES:
                hit = KEYWORD_FEATURES[x]
                if x == "match":
                    patterns |= classify_match(body, n, feats)
                elif hit is not None:
                    feats.add(*hit)
            elif x in KEYWORDS_F1:
                pass
            elif x in SCALAR_TYPES or x in WIDE_TYPES:
                if x in WIDE_TYPES:
                    feats.add("F1-bv", "wide-int")
                if nxt is not None and nxt.text == "::":
                    pass  # an associated constant or function of a scalar type; the next ident decides
            elif x in FLOAT_TYPES:
                feats.add("outside", "float")
            elif prev is not None and prev.text == ".":
                if nxt is not None and nxt.text in ("(", "::"):
                    if x in SCALAR_BV_METHODS:
                        feats.add("F1-bv", f"scalar-method:{x}")
                    elif x in local_fns:
                        feats.add("F2", "call")
                    else:
                        feats.add("F4", f"std-method:{x}")
                else:
                    feats.add("F4", "field")
            elif prev is not None and prev.text == "::":
                scalar_owner = n >= 2 and body[n - 2].text in SCALAR_TYPES | WIDE_TYPES
                if nxt is not None and nxt.text == "(":
                    if scalar_owner and x in SCALAR_BV_METHODS:
                        feats.add("F1-bv", f"scalar-method:{x}")
                    else:
                        feats.add("F4", f"path-call:{x}")
                elif not (scalar_owner and x in ("MAX", "MIN", "BITS")):
                    feats.add("F4", "path")
            elif nxt is not None and nxt.text == "(":
                if x == item.name:
                    feats.add("F2", "recursion")
                elif x in local_fns:
                    feats.add("F2", "call")
                elif x[:1].isupper():
                    feats.add("F4", "adt-constructor")
                else:
                    feats.add("F4", f"external-call:{x}")
            elif nxt is not None and nxt.text == "::":
                feats.add("F4", "path")
            elif x[:1].isupper():
                feats.add("F4", "adt-or-const")
        elif t.kind == "punct":
            if x in ("&", "&&"):
                if is_operand_end(prev):
                    if x == "&":
                        feats.add("F1-bv", "bitwise")
                else:
                    feats.add("F3", "borrow")
            elif x == "*":
                if not is_operand_end(prev):
                    feats.add("F3", "deref")
                else:
                    const = (prev is not None and prev.kind == "int") or (nxt is not None and nxt.kind == "int")
                    feats.add("F1" if const else "F1-bv", "mul-const" if const else "mul-nonlinear")
            elif x in ("|", "||"):
                if not is_operand_end(prev):
                    feats.add("outside", "closure")
                elif x == "|":
                    feats.add("F1-bv", "bitwise")
            elif x in ("^", "<<", ">>", "^=", "&=", "|=", "<<=", ">>="):
                feats.add("F1-bv", "bitwise" if x in ("^", "^=", "&=", "|=") else "shift")
            elif x == "*=":
                const = nxt is not None and nxt.kind == "int"
                feats.add("F1" if const else "F1-bv", "mul-const" if const else "mul-nonlinear")
            elif x == "[":
                feats.add("F4", "index-or-array")
            elif x == "?":
                feats.add("F4", "try")
            elif x == "(" and tuple_at(body, n, prev):
                feats.add("F4", "tuple")
            elif x in ("~", "@", "$", "#", "...") :
                feats.add("outside", f"unrecognised:{x}")
        prev = t


def tuple_at(body: list[Tok], n: int, prev: Tok | None) -> bool:
    """A `(` that opens a tuple (a depth-0 comma) rather than a call's arguments or a group."""
    if prev is not None and (prev.kind == "ident" and prev.text not in KEYWORDS_F1 | {"match"} or prev.text in (")", "]", ">", "!")):
        return False
    depth = 0
    for t in body[n:]:
        depth += t.text in ("(", "[", "{")
        depth -= t.text in (")", "]", "}")
        if depth == 0:
            return False
        if depth == 1 and t.text == ",":
            return True
    return False


def classify_match(body: list[Tok], n: int, feats: Features) -> set[int]:
    """A `match` stays in F1 only when every arm pattern is a literal, a range, `_` or `|` of them.
    Returns the indices of the arm patterns' tokens, which the body scan does not read again."""
    i = n + 1
    depth = 0
    while i < len(body) and not (body[i].text == "{" and depth == 0):
        depth += body[i].text in ("(", "[")
        depth -= body[i].text in (")", "]")
        i += 1
    depth, pattern, scalar, seen = 0, [], True, set()
    in_pattern = True
    for idx in range(i + 1, len(body)):
        t = body[idx]
        if depth == 0 and in_pattern and t.text not in ("=>", ",", "}"):
            seen.add(idx)
        if t.text in ("(", "[", "{"):
            depth += 1
        elif t.text in (")", "]", "}"):
            if depth == 0:
                break
            depth -= 1
        if depth != 0:
            continue
        if t.text == "=>":
            if not pattern or not all(p.kind == "int" or p.text in LIT_PATTERN for p in pattern):
                scalar = False
            pattern, in_pattern = [], False
        elif t.text == ",":
            pattern, in_pattern = [], True
        elif t.text == "}":
            in_pattern = True  # a block arm `=> { .. }` ends without a comma
        elif in_pattern:
            pattern.append(t)
    if not scalar:
        feats.add("F4", "match-adt")
    return seen


# --------------------------------------------------------------------------
# reading the UI suite
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Row:
    test: str
    revision: str
    line: int
    function: str
    fragment: str
    body_fragment: str
    features: str
    pre: str
    admission: str
    proved: int
    total: int
    kernel_certified: int


def parse_headers(source: str) -> tuple[list[str], dict[str, list[str]]]:
    """(revisions, flags per revision; key "" holds the flags every revision shares)."""
    revisions: list[str] = []
    flags: dict[str, list[str]] = {"": []}
    for raw in source.split("\n"):
        m = HEADER.match(raw)
        if not m:
            continue
        key, value = m.group("key"), (m.group("value") or "").strip()
        if key == "revisions" and not m.group("revs"):
            revisions = value.replace(",", " ").split()
        elif key == "compile-flags":
            for rev in ([r.strip() for r in m.group("revs").split(",")] if m.group("revs") else [""]):
                flags.setdefault(rev, []).extend(value.split())
    return revisions, flags


def strict_effective(flag_list: list[str]) -> bool:
    lower, verify = None, None
    joined = []
    it = iter(flag_list)
    for f in it:
        if f == "-Z":
            f = "-Z" + next(it, "")
        joined.append(f)
    for f in joined:
        if f.startswith("-Ztrust-ir-lower") and not f.startswith("-Ztrust-ir-lower-"):
            lower = f.partition("=")[2] or "on"
        elif f.startswith("-Ztrust-verify") and not f.startswith("-Ztrust-verify-"):
            verify = f.partition("=")[2] or "on"
    return lower == "strict" and verify != "off"


def stderr_revision(stderr_rel: str, test_rel: str, revisions: list[str]) -> str | None:
    stem = test_rel[:-3]
    middle = stderr_rel[len(stem):-len(".stderr")]
    if middle == "":
        return "*" if revisions else ""
    if middle.startswith(".") and middle[1:] in revisions:
        return middle[1:]
    return None  # a stderr of another test with a shared prefix, or a non-revision variant


def parse_report(stderr: str, where: str) -> list[tuple[int, str, int, int, int, bool]]:
    """(anchored line, anchored path, proved, total, kernel_certified, has_assumed) per block."""
    lines = stderr.split("\n")
    out = []
    for n, raw in enumerate(lines):
        m = REPORT.match(raw)
        if not m:
            if raw.startswith("note: Trust verification:"):
                raise CensusError(f"{where}:{n + 1}: unreadable report line: {raw}")
            continue
        counts: dict[str, int] = {}
        for part in m.group("counts").split(", "):
            c = COUNT.match(part)
            if not c or c.group(2) in counts:
                raise CensusError(f"{where}:{n + 1}: unknown count `{part}` in: {raw}")
            counts[c.group(2)] = int(c.group(1))
        for need in ("proved", "failed", "unknown", "timed out", "runtime-checked"):
            if need not in counts:
                raise CensusError(f"{where}:{n + 1}: no `{need}` count in: {raw}")
        total = int(m.group("total"))
        assumed = counts.get("assumed (requires)", 0)
        if sum(counts.values()) != total:
            raise CensusError(f"{where}:{n + 1}: counts do not add up to {total}: {raw}")
        a = ANCHOR.match(lines[n + 1]) if n + 1 < len(lines) else None
        if not a:
            raise CensusError(f"{where}:{n + 2}: a report with no `--> $DIR/...` anchor")
        kc = 0
        for follow in lines[n + 2:]:
            if follow.startswith(("note:", "error", "warning")):
                break
            k = KERNEL.match(follow)
            if k:
                kc = int(k.group(1))
        unproved = counts["failed"] + counts["unknown"] + counts["timed out"] + counts["runtime-checked"]
        proved = counts["proved"] if unproved == 0 and counts["proved"] >= 1 else 0
        out.append((int(a.group("line")), a.group("path"), proved, total, kc, assumed > 0))
    return out


def measure(tree) -> list[Row]:
    tests = [r for r in tree.files(UI_ROOT, (".rs",))]
    stderrs = tree.files(UI_ROOT, (".stderr",))
    tree.prefetch(stderrs)
    by_dir: dict[str, list[str]] = {}
    for s in stderrs:
        by_dir.setdefault(s.rsplit("/", 1)[0], []).append(s)
    rows: list[Row] = []
    sources: dict[str, str] = {}
    candidates = []
    for s in stderrs:
        text = tree.text(s) or ""
        if "note: Trust verification:" in text:
            candidates.append((s, text))
    tests_set = set(tests)
    for s, text in candidates:
        base = s[:-len(".stderr")]
        owner = base + ".rs" if base + ".rs" in tests_set else None
        if owner is None and "." in base.rsplit("/", 1)[1]:
            cand = base.rsplit(".", 1)[0] + ".rs"
            owner = cand if cand in tests_set else None
        if owner is None:
            raise CensusError(f"{s}: no test source owns this stderr")
        if owner not in sources:
            sources[owner] = tree.text(owner) or ""
        source = sources[owner]
        revisions, flags = parse_headers(source)
        rev = stderr_revision(s, owner, revisions)
        if rev is None:
            raise CensusError(f"{s}: not a revision of {owner} (revisions: {revisions})")
        targets = revisions if rev == "*" else [rev]
        admitted_flags = all(strict_effective(flags[""] + flags.get(r, [])) for r in targets) if targets else strict_effective(flags[""])
        local = defined_fns(source)
        all_toks = None
        for line, path, proved, total, kc, assumed in parse_report(text, s):
            anchored = owner.rsplit("/", 1)[0] + "/" + path
            if anchored != owner:
                raise CensusError(f"{s}: a report anchored in another file ({path})")
            if not proved:
                continue
            strict_err = any(STRICT_ERROR in blk and f"{path}:{line}:" in blk for blk in text.split("\n\n"))
            admission = "admitted" if admitted_flags and not strict_err else "unmeasured"
            item = find_item(source, line)
            if item is None:
                rows.append(Row(owner[len(UI_ROOT):], rev or "-", line, "?", "outside", "outside", "unrecognised:item",
                                "vacuous-pre" if assumed else "no-pre", admission, proved, total, kc))
                continue
            if all_toks is None:
                all_toks = lex(source)
            before = [t for t in all_toks if t.line == line]
            before = before[:next((n for n, t in enumerate(before) if t.text == "fn"), len(before))]
            fragment, body_fragment, features, has_requires = classify(item, local, before)
            pre = "vacuous-pre" if has_requires or assumed else "no-pre"
            rows.append(Row(owner[len(UI_ROOT):], rev or "-", line, item.name, fragment, body_fragment, features, pre,
                            admission, proved, total, kc))
    rows.sort(key=lambda r: (r.test, r.revision, r.line))
    return rows


# --------------------------------------------------------------------------
# rendering
# --------------------------------------------------------------------------

def render(rows: list[Row], pin: str) -> str:
    out = [
        f"# {SCHEMA}",
        f"# Generated by {SCRIPT_REL} --write --rev {pin}; a hand edit is drift (--check).",
        f"# measured_at_commit\t{pin}",
        "# row: a `Trust verification:` report of an expected tests/ui/**/*.stderr whose counts are all proved",
        "#   (failed = unknown = timed out = runtime-checked = 0, proved >= 1, proved + assumed (requires) = total).",
        "# fragment: source-syntactic, the largest fragment the row's features need (F1 < F1-bv < F2 < F3 < F4 < outside).",
        "# admission: `admitted` iff the revision runs -Ztrust-ir-lower=strict under verification and its stderr has",
        "#   no strict error at the row; else `unmeasured` (a producer skip leaves no mark in a stderr).",
        "# body-fragment: the fragment without the function's own requires/ensures/decreases (its safety rows alone).",
        "# pre: `vacuous-pre` iff the function has a `requires` (no kernel-checked witness of a precondition exists).",
        "# vf5-n: the producer-restricted proved rows per fragment; `blocked` while any row of that fragment is unmeasured.",
        "",
    ]
    out.append("kind\tscope\tfragment\tpre\tcount")
    for scope in ("all-proved", "admitted", "unmeasured"):
        tally = Counter((r.fragment, r.pre) for r in rows if scope == "all-proved" or r.admission == scope)
        for frag in FRAGMENTS:
            for pre in ("no-pre", "vacuous-pre"):
                out.append(f"summary\t{scope}\t{frag}\t{pre}\t{tally[(frag, pre)]}")
    body = Counter((r.body_fragment, r.pre) for r in rows)
    for frag in FRAGMENTS:
        for pre in ("no-pre", "vacuous-pre"):
            out.append(f"summary\tall-proved-by-body\t{frag}\t{pre}\t{body[(frag, pre)]}")
    for frag in FRAGMENTS:
        adm = sum(1 for r in rows if r.fragment == frag and r.admission == "admitted" and r.pre == "no-pre")
        unm = sum(1 for r in rows if r.fragment == frag and r.admission == "unmeasured")
        status = "measured" if unm == 0 else "blocked"
        reason = ("-" if unm == 0 else
                  f"{unm} proved row(s) of {frag} have unmeasured producer admission; unblock: a strict "
                  f"(-Ztrust-ir-lower=strict) revision of each such test, or a stage 1 run that records admission")
        out.append(f"vf5-n\t{frag}\t{status}\t{adm}\t{reason}")
    out.append("")
    out.append("kind\ttest\trevision\tline\tfunction\tfragment\tbody-fragment\tpre\tadmission\tproved/total\tkernel-certified\tfeatures")
    for r in rows:
        out.append(f"row\t{r.test}\t{r.revision}\t{r.line}\t{r.function}\t{r.fragment}\t{r.body_fragment}\t{r.pre}\t{r.admission}\t"
                   f"{r.proved}/{r.total}\t{r.kernel_certified}\t{r.features}")
    return "\n".join(out) + "\n"


def recorded_pin(text: str) -> str | None:
    m = re.search(r"^# measured_at_commit\t([0-9a-f]{40})$", text, re.M)
    return m.group(1) if m else None


def resolve(repo: Path, rev: str) -> str:
    sha = (C.git(repo, "rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}") or "").strip()
    if not C.HEX40.match(sha):
        raise CensusError(f"{rev}: not a commit in {repo}")
    return sha


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true", help="measure at --rev and write the record")
    mode.add_argument("--check", action="store_true", help="re-measure at the record's pin; exit 1 on drift")
    mode.add_argument("--current", action="store_true", help="re-measure at HEAD; exit 1 if the rows differ")
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[2])
    ap.add_argument("--record", type=Path, help=f"the record to write or check (default: <repo>/{RECORD_REL})")
    args = ap.parse_args(argv)
    record = args.record or args.repo / RECORD_REL
    try:
        if args.write:
            pin = resolve(args.repo, args.rev)
            text = render(measure(C.GitTree(args.repo, pin)), pin)
            record.parent.mkdir(parents=True, exist_ok=True)
            record.write_text(text, encoding="utf-8")
            print(f"vf3-census: wrote {record} at {pin}")
            return 0
        try:
            have = record.read_text(encoding="utf-8")
        except OSError as error:
            print(f"vf3-census: FAIL: no record: {error}", file=sys.stderr)
            return 1
        pin = recorded_pin(have)
        if pin is None:
            print(f"vf3-census: FAIL: {record} names no `measured_at_commit` pin", file=sys.stderr)
            return 1
        if args.check:
            resolve(args.repo, pin)
            want = render(measure(C.GitTree(args.repo, pin)), pin)
            label = f"the record re-measured at its pin {pin[:12]}"
        else:
            head = resolve(args.repo, "HEAD")
            want = render(measure(C.GitTree(args.repo, head)), pin)
            label = f"the census at HEAD {head[:12]}"
        if have == want:
            print(f"vf3-census: OK: {record} equals {label}, byte for byte")
            return 0
        diff = list(difflib.unified_diff(have.splitlines(), want.splitlines(), "record", label, lineterm="", n=0))
        print(f"vf3-census: {'FAIL: drift' if args.check else 'STALE'}: {record} differs from {label}", file=sys.stderr)
        for line in diff[:60]:
            print(line, file=sys.stderr)
        return 1
    except CensusError as error:
        print(f"vf3-census: ERROR: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
