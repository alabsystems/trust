#!/usr/bin/env python3
"""D0.3 checker: the MIR constructor and intrinsic table.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §3.4 D-4 ("The
translator", invariant I-RCC-TOTAL), §5.1 item 2 and §5.2 Stage 0.2 (D0.3, exit E0.6 "Zero
unmapped MIR enum variants; the count is published"). Table:
docs/trust-core/mir-constructor-table.toml. Document: docs/trust-core/MIR_CONSTRUCTOR_TABLE.md.
Review registry: docs/trust-core/reviews/mir_constructor_table.toml. Names mapped into:
docs/trust-core/core-vocabulary.toml.

The shared layers (pins, git, citations with the Trust-marker guard, uniqueness, the counts
block, reviewed judgments and their history) are scripts/trust_core/common.py's. This file
holds the table's own rules; each EXITS NON-ZERO when it fails. MIR_CONSTRUCTOR_TABLE.md's
Predicates section states them:

  PIN          common: the MiniRust clone at its pin, this repository's alignment, no
               replace ref or grafts; every rustc item the checker enumerates (in-scope
               enums, reached structs and aliases, containers, the phase enums, the case
               enum, #[rustc_intrinsic] items) is a marker-free region; constant-conversion
               evidence needs the complete op_to_const text to equal aligned upstream; the scope files and
               library/ at the design's D0.3 commit equal HEAD's.
  VOCABULARY   scripts/trust_core/core_vocabulary.py reports no violation.
  TABLE        keys, types, unique row keys, no repeated list element, no line citation in
               free text.
  SCOPE        the scope files, the design roots and the closure are derived; every other
               payload type is one [[boundary]] row; every named root or task-named enum that
               is not defined is one [[absent]] row, verified absent.
  UNIVERSE     every variant of an in-scope enum and every field of a [scope] container has
               a [[construct]] row, and no row names anything else; `at` is derived; rows of
               one construct partition its S phases (cases with one `otherwise`, or one case
               per variant of a case enum).
  PHASE        every non-header doc unit of the MirPhase docs, and every doc unit of an item
               read that matches [scope] phase_words, is cited whole by exactly one
               [[phase_rule]]; [[doc_pin]] covers all doc text read; `mir_phases` is derived
               from the variant rules, the holders and the [[phase_conflict]] rows (none
               stale); rows cover exactly the admitted S phases; semantic rules and
               `phase_semantics` agree both ways.
  DISPOSITION  exactly one disposition with only its own field; core names are vocabulary
               entries admitting the row's S phases; the vocabulary's MIR operators decide
               their rows; a refusal is declared and used; dispatch targets are in scope;
               nesting; retag rows' realizing rows carry (and never forbid) their names.
  MINIMIZE     every cited minimize line holds its arm; every hit of the declared search
               (`rs::E::V` of an in-scope or absent enum, `rs::sym::N`, `smir::E::V` of a
               [scope] smir_enums enum) is cited by a row or a [[stale_arm]]; a row whose
               `rs::` path minimize names cites that line; a row in the other refuse/translate
               class from its arms states a divergence with design citations.
  INTRINSIC    every #[rustc_intrinsic] fn under library/ has a row, none is stale, `path`,
               `at` and `fallback_is_spec` are derived; fallback needs the marker; a lowered
               intrinsic's names contain its lowered constructs' names.
  DIVERGENCE   a [[spec_divergence]] cites MiniRust's spec and rustc or the library, and the
               rows listing it are exactly its applies_to.
  DEFERRED     every [[deferred_check]] names row fields of this table and exits quoted by
               its design citations.
  DOC          the counts block regenerates; every line is in a `prose:` section, the counts
               block or the outline; every citation resolves; the pins are recorded.
  REVIEW       common.check_reviews over every row, the [scope] judgments, the table's
               comments, the prose sections and the outline.

Usage:
    scripts/trust_core/mir_constructor_table.py [--minirust DIR] [--repo DIR] [--table FILE]
        [--doc FILE] [--registry FILE] [--print-counts-table] [--write-counts]

Exit codes: 0 every predicate holds; 1 a violation; 2 a clone is missing or unreadable pins.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

RUST_URL = "https://github.com/rust-lang/rust"

tomllib = C.tomllib
REPO_ROOT = C.REPO_ROOT
TABLE_REL = "docs/trust-core/mir-constructor-table.toml"
DOC_REL = "docs/trust-core/MIR_CONSTRUCTOR_TABLE.md"
REGISTRY_REL = f"{C.REVIEWS_DIR}/mir_constructor_table.toml"
VOCAB_TABLE_REL = "docs/trust-core/core-vocabulary.toml"
DELIVERABLE = "mir_constructor_table"
SCHEMA = "trust.core.mir-constructor-table.v1"
COUNTS_BLOCK = "mir-constructor-table-counts"
READS = {"minirust": "minirust"}  # EXTERNAL_PINS source -> citation source whose content is read

SYNTAX_REL = "compiler/rustc_middle/src/mir/syntax.rs"
MIR_MODULE_DIR = "compiler/rustc_middle/src/mir/"
ABSENT_SEARCH_ROOT = "compiler/rustc_middle/src/"
INTRINSIC_ROOT = "library/"
# Under INTRINSIC_ROOT and outside the D0.3 snapshot comparison: the library lock records resolved
# package versions (trust-bignum's is the release version, so every release bump rewrites it)
# and declares no intrinsic; the intrinsics are read from the `.rs` files, which stay compared.
PIN_UNCOMPARED = ("library/Cargo.lock",)
MINIMIZE_DIR = "tooling/minimize/src/"
CASE_ENUM_FILES = {"GlobalAlloc": "compiler/rustc_middle/src/mir/interpret/mod.rs"}
# The design's two D0.3 lists: the anchor text and the word that ends each list.
DESIGN_LIST_ANCHORS = (("matches every `StatementKind`,", "exhaustively"), ("**D0.3, the MIR constructor table**", "plus the"))
MIR_PHASE_FAMILY = ("MirPhase", "AnalysisPhase", "RuntimePhase")
MIR_PHASES = ("Built", "Analysis(Initial)", "Analysis(PostCleanup)", "Runtime(Initial)", "Runtime(PostCleanup)", "Runtime(Optimized)")
S_PHASES = ("Built", "Promoted", "Runtime")
PRIMITIVES = frozenset("bool char str u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize f16 f32 f64 f128".split())
WRAPPERS = frozenset("Box Option Vec IndexVec SmallVec List ThinVec Spanned".split())  # generic wrappers traversed through
VOCAB_OPERATOR_ENUMS = ("BinOp", "UnOp", "CastKind", "PointerCoercion", "Operand", "RuntimeChecks")
DISPOSITIONS = ("core", "refusal", "no_op", "dispatch")
INTRINSIC_DISPOSITIONS = ("core", "refusal", "no_op", "fallback")
BOUNDARY_CLASSES = ("data", "index", "enum")
PHASE_RULE_KINDS = ("variant", "composition", "type-qualified", "condition-qualified", "out-of-scope", "semantic", "descriptive")
EFFECTLESS_KINDS = ("semantic", "descriptive")
CONFLICT_FOLLOWS = ("validator", "evidence")
ARM_CLASSES = ("refuses", "translates")
LOWERINGS = {"LowerIntrinsics": ("Built", "Promoted"), "MIR building": S_PHASES}  # lowering -> S phases the call is still a call
BODY_ENTRY = "body-entry"
HEADER_UNIT = re.compile(r"(?i)^(?:in addition to the semantic changes, )?(?:(?:beginning|starting) (?:in|with) this phase, )?"
                         r"(?:and )?the following variants? (?:are|is) (disallowed|allowed):$")
EXIT_ID = re.compile(r"^E\d+(?:\.\d+)+[a-z]?$")
FREE_TEXT_KEYS = ("note", "reason", "divergence", "core_extra_reason", "core_meaning", "upstream", "case", "claim", "replaces")

# kind -> (allowed keys, required keys, key of a row). Every row of every kind is a judgment.
ROWS = {
    "s_phase": ({"name", "mir_phase", "evidence"}, {"name", "mir_phase", "evidence"}, lambda r: r.get("name")),
    "absent": ({"name", "design_refs", "note"}, {"name", "note"}, lambda r: r.get("name")),
    "boundary": ({"type", "class", "note", "owner"}, {"type", "class", "note"}, lambda r: r.get("type")),
    "refusal": ({"name", "reason", "evidence"}, {"name", "reason", "evidence"}, lambda r: r.get("name")),
    "phase_rule": ({"id", "refs", "effect", "kind", "applies_to", "applies_to_enum", "except", "note", "s_phases", "owner_refs", "same_as"},
                   {"id", "refs", "effect", "kind"}, lambda r: r.get("id")),
    "phase_conflict": ({"id", "applies_to", "follows", "phases", "evidence", "reason"}, {"id", "applies_to", "follows", "phases", "evidence", "reason"},
                       lambda r: r.get("id")),
    "producer": ({"phase", "paths", "exclude", "evidence", "reason"}, {"phase", "paths", "evidence", "reason"}, lambda r: r.get("phase")),
    "retag_site": ({"id", "site", "mode", "realized_by", "core", "forbids", "reason", "evidence"}, {"id", "mode", "realized_by", "core", "reason"}, lambda r: r.get("id")),
    "body_entry": ({"name", "core", "evidence", "reason"}, {"name", "core", "evidence", "reason"}, lambda r: r.get("name")),
    "spec_divergence": ({"id", "minirust", "rust", "core_meaning", "applies_to", "upstream"}, {"id", "minirust", "rust", "core_meaning", "applies_to", "upstream"},
                        lambda r: r.get("id")),
    "doc_pin": ({"id", "sha256", "units", "note"}, {"id", "sha256", "units", "note"}, lambda r: r.get("id")),
    "stale_arm": ({"ref", "arm", "token", "reason"}, {"ref", "arm", "token", "reason"}, lambda r: f"{r.get('ref')} {r.get('token')}"),
    "deferred_check": ({"id", "claim", "fields", "replaces", "checked_by", "cites"}, {"id", "claim", "fields", "replaces", "checked_by", "cites"},
                       lambda r: r.get("id")),
    "construct": ({"mir", "at", "mir_phases", "s_phases", "case", "case_enum", "disposition", "core", "case_refusals", "refusal", "no_op", "dispatch",
                   "dispatch_via", "phase_semantics", "spec_divergence", "minimize", "arm_class", "seed_arms", "bridge", "evidence", "divergence",
                   "divergence_refs", "note"}, {"mir", "at", "mir_phases", "s_phases", "disposition", "minimize"},
                  lambda r: " ".join([str(r.get("mir")), ",".join(map(str, r.get("s_phases") or []))] + ([str(r["case"])] if "case" in r else []))),
    "intrinsic": ({"name", "path", "at", "fallback_is_spec", "case", "disposition", "core", "core_extra_reason", "refusal", "no_op", "lowering",
                   "lowered_to", "spec_divergence", "minimize", "arm_class", "evidence", "divergence", "divergence_refs", "note"},
                  {"name", "path", "at", "fallback_is_spec", "disposition", "minimize"},
                  lambda r: " ".join([str(r.get("path"))] + ([str(r["case"])] if "case" in r else []))),
}
SCOPE_KEYS = {"design_lists", "design_enums", "task_named", "containers", "smir_enums", "phase_words", "scope_files"}
SCOPE_JUDGMENTS = ("task_named", "containers", "smir_enums", "phase_words")
TOP_KEYS = {"schema", "design", "vocabulary", "scope"} | set(ROWS)
# Row fields that are citations: {ref, quote} lists, single {ref, quote}, and minimize {ref, arm} lists.
CITE_LISTS = {"evidence", "design_refs", "refs", "owner_refs", "dispatch_via", "bridge", "divergence_refs", "minirust", "rust", "cites"}
CITE_ONE = {"no_op", "site"}
ARM_LISTS = {"minimize", "seed_arms"}
JUDGMENT_KINDS = set(ROWS) | {"scope", "comments", "prose", "outline"}
# TABLE: the type of every field; a list's elements after the comma.
STR_LISTS = "applies_to except s_phases phases paths exclude realized_by core forbids fields checked_by mir_phases case_refusals " \
    "phase_semantics spec_divergence lowered_to".split()
TYPES = {**{k: (list, dict) for k in CITE_LISTS | ARM_LISTS}, **{k: (list, str) for k in STR_LISTS}, **{k: (dict, None) for k in CITE_ONE},
         "units": (int, None), "fallback_is_spec": (bool, None)}
ALLOWED_EMPTY = {("retag_site", "core"), ("retag_site", "realized_by"), ("producer", "exclude")}


@dataclass
class Result:
    violations: list = field(default_factory=list)
    counts: dict = field(default_factory=dict)
    table_text: str = ""


@dataclass
class Options:
    repo: Path = REPO_ROOT
    table: Path | None = None
    doc: Path | None = None
    registry: Path | None = None
    pins: Path | None = None
    clones: dict = field(default_factory=dict)
    trees: dict = field(default_factory=dict)  # citation source -> tree; mutation tests only
    check_pin_state: bool = True
    check_history: bool = True
    check_vocabulary: bool = True


# ============================================================================
# a Rust lexer and item reader
# ============================================================================


@dataclass(frozen=True)
class Tok:
    kind: str  # ident | lifetime | punct | str | char | num | doc | comment
    text: str
    line: int
    end_line: int


class LexError(ValueError):
    pass


def lex(src: str) -> list[Tok]:
    """Tokens of Rust source; comments are `doc`/`comment` tokens, never identifiers."""
    toks: list[Tok] = []
    i, n, line = 0, len(src), 1

    def add(kind: str, start: int, end: int, start_line: int) -> None:
        text = src[start:end]
        toks.append(Tok(kind, text, start_line, start_line + text.count("\n")))

    def word_before(k: int) -> bool:
        return k > 0 and re.match(r"[A-Za-z0-9_]", src[k - 1]) is not None

    while i < n:
        c = src[i]
        if c == "\n":
            line, i = line + 1, i + 1
            continue
        if c in " \t\r\f\v":
            i += 1
            continue
        start_line = line
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            text = src[i:j]
            add("doc" if (text.startswith("///") and not text.startswith("////")) or text.startswith("//!") else "comment", i, j, start_line)
            i = j
            continue
        if src.startswith("/*", i):
            depth, j = 0, i
            while j < n:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                    if depth == 0:
                        break
                else:
                    j += 1
            if depth:
                raise LexError(f"unterminated block comment at line {start_line}")
            text = src[i:j]
            add("doc" if (text.startswith("/**") and not text.startswith("/***") and text != "/**/") or text.startswith("/*!") else "comment", i, j, start_line)
            line, i = line + text.count("\n"), j
            continue
        m = re.match(r"(?:b|c)?r(#*)\"", src[i:i + 64])
        if m and not word_before(i):
            j = src.find('"' + m.group(1), i + m.end())
            if j < 0:
                raise LexError(f"unterminated raw string at line {start_line}")
            j += 1 + len(m.group(1))
            add("str", i, j, start_line)
            line, i = line + src[i:j].count("\n"), j
            continue
        if c == '"' or (c in "bc" and src[i + 1:i + 2] == '"' and not word_before(i)):
            j = i + (1 if c == '"' else 2)
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            if j >= n:
                raise LexError(f"unterminated string at line {start_line}")
            add("str", i, j + 1, start_line)
            line, i = line + src[i:j + 1].count("\n"), j + 1
            continue
        if c == "'" or (c == "b" and src[i + 1:i + 2] == "'" and not word_before(i)):
            k = i + (1 if c == "'" else 2)
            m = re.match(r"(?:\\(?:u\{[0-9A-Fa-f_]+\}|x[0-9A-Fa-f]{2}|.)|[^\\'\n])'", src[k:k + 16])
            if m:
                add("char", i, k + m.end(), start_line)
                i = k + m.end()
                continue
            m = re.match(r"'[A-Za-z_][A-Za-z0-9_]*", src[i:i + 128]) if c == "'" else None
            if m:
                add("lifetime", i, i + m.end(), start_line)
                i += m.end()
                continue
            raise LexError(f"unreadable quote at line {start_line}")
        if c.isalpha() or c == "_":
            m = re.match(r"(?:r#)?[A-Za-z_][A-Za-z0-9_]*", src[i:i + 256])
            add("ident", i, i + m.end(), start_line)
            i += m.end()
            continue
        if c.isdigit():
            m = re.match(r"[0-9][0-9A-Za-z_]*(?:\.[0-9][0-9A-Za-z_]*)?", src[i:i + 64])
            add("num", i, i + m.end(), start_line)
            i += m.end()
            continue
        p = next((p for p in ("::", "->", "=>", "..=", "...", "..") if src.startswith(p, i)), c)
        add("punct", i, i + len(p), start_line)
        i += len(p)
    return toks


OPEN = {"(": ")", "[": "]", "{": "}"}
CLOSE = {v: k for k, v in OPEN.items()}


def match_close(toks: list[Tok], i: int) -> int:
    stack = [toks[i].text]
    for j in range(i + 1, len(toks)):
        t = toks[j]
        if t.kind != "punct":
            continue
        if t.text in OPEN:
            stack.append(t.text)
        elif t.text in CLOSE:
            if not stack or stack[-1] != CLOSE[t.text]:
                raise LexError(f"unbalanced {t.text!r} at line {t.line}")
            stack.pop()
            if not stack:
                return j
    raise LexError(f"unclosed {toks[i].text!r} from line {toks[i].line}")


def skip_attribute(toks: list[Tok], i: int) -> int:
    j = i + 1 + (toks[i + 1].text == "!" if i + 1 < len(toks) else 0)
    if j >= len(toks) or toks[j].text != "[":
        raise LexError(f"`#` not starting an attribute at line {toks[i].line}")
    return match_close(toks, j) + 1


@dataclass
class TypePath:
    segments: tuple
    line: int

    @property
    def name(self) -> str:
        return self.segments[-1]


@dataclass
class Member:
    """A variant of an enum or a named field of a struct."""
    name: str
    line: int
    paths: list


@dataclass
class Item:
    kind: str  # enum | struct | type
    name: str
    line: int
    first: int  # the region: from the line the preceding code token ends on, to the item's last line
    last: int
    generics: list
    rel: str
    members: list = field(default_factory=list)


TYPE_KEYWORDS = frozenset("dyn impl for mut const fn unsafe extern where as pub crate self super Self in ref move static".split())


def type_paths(toks: list[Tok]) -> list[TypePath]:
    out, i = [], 0
    while i < len(toks):
        if toks[i].kind == "ident" and toks[i].text not in TYPE_KEYWORDS:
            segs, j = [toks[i].text], i + 1
            while j + 1 < len(toks) and toks[j].text == "::" and toks[j + 1].kind == "ident":
                segs.append(toks[j + 1].text)
                j += 2
            out.append(TypePath(tuple(segs), toks[i].line))
            i = j
        else:
            i += 1
    return out


def split_depth0(toks: list[Tok], angle: bool = True) -> list[list[Tok]]:
    parts, depth = [[]], 0
    for t in toks:
        if t.kind == "punct":
            if t.text in OPEN or (angle and t.text == "<"):
                depth += 1
            elif t.text in CLOSE or (angle and t.text == ">"):
                depth -= 1
                if depth < 0:
                    raise LexError(f"unbalanced {t.text!r} at line {t.line}")
            elif t.text == "," and depth == 0:
                parts.append([])
                continue
        parts[-1].append(t)
    if depth:
        raise LexError("unbalanced brackets in a split run")
    return [p for p in parts if p]


def strip_attrs(part: list[Tok]) -> list[Tok]:
    out, i = [], 0
    while i < len(part):
        if part[i].text == "#" and i + 1 < len(part) and part[i + 1].text in ("[", "!"):
            i = skip_attribute(part, i)
        else:
            out.append(part[i])
            i += 1
    return out


def read_fields(body: list[Tok]) -> list[Member]:
    out = []
    for part in map(strip_attrs, split_depth0(body)):
        k = 0
        if part and part[0].text == "pub":
            k = match_close(part, 1) + 1 if len(part) > 1 and part[1].text == "(" else 1
        if k + 1 < len(part) and part[k].kind == "ident" and part[k + 1].text == ":":
            out.append(Member(part[k].text, part[k].line, type_paths(part[k + 2:])))
    return out


def read_items(src: str, rel: str) -> tuple[list[Item], list[Tok]]:
    """Every `enum`, `struct` and `type X = ..;` item of a file, at any nesting (macro bodies too)."""
    toks = lex(src)
    code = [t for t in toks if t.kind not in ("doc", "comment")]
    items, i = [], 0
    while i < len(code):
        t = code[i]
        if not (t.kind == "ident" and t.text in ("enum", "struct", "type") and i + 1 < len(code) and code[i + 1].kind == "ident"):
            i += 1
            continue
        name, j, generics = code[i + 1], i + 2, []
        if j < len(code) and code[j].text == "<":
            depth, g = 0, j
            while j < len(code):
                depth += {"<": 1, ">": -1}.get(code[j].text, 0)
                if depth == 0:
                    break
                j += 1
            generics = [x.text for x in code[g + 1:j] if x.kind in ("ident", "lifetime")]
            j += 1
        while j < len(code) and code[j].text not in ("{", "(", ";", "="):
            j += 1
        if j >= len(code):
            break
        start = i  # back over `pub`, `pub(..)` and attributes to the preceding code token
        while True:
            if start >= 1 and code[start - 1].text == "pub":
                start -= 1
            elif start >= 4 and code[start - 1].text == ")" and code[start - 4].text == "pub" and code[start - 3].text == "(":
                start -= 4
            elif start >= 1 and code[start - 1].text == "]":
                k, depth = start - 1, 0
                while k >= 0:
                    depth += {"]": 1, "[": -1}.get(code[k].text, 0) if code[k].kind == "punct" else 0
                    if depth == 0:
                        break
                    k -= 1
                if k >= 1 and code[k - 1].text == "#":
                    start = k - 1
                elif k >= 2 and code[k - 1].text == "!" and code[k - 2].text == "#":
                    start = k - 2
                else:
                    break
            else:
                break
        first = code[start - 1].end_line if start else 1
        if t.text == "type":
            if code[j].text != "=":
                i += 1
                continue
            end = j
            while end < len(code) and code[end].text != ";":
                end += 1
            items.append(Item("type", name.text, name.line, first, code[min(end, len(code) - 1)].line, generics, rel,
                              [Member(name.text, name.line, type_paths(code[j + 1:end]))]))
            i = end + 1
            continue
        if code[j].text in (";", "="):
            items.append(Item(t.text, name.text, name.line, first, code[j].line, generics, rel))
            i = j + 1
            continue
        close = match_close(code, j)
        item = Item(t.text, name.text, name.line, first, code[close].line, generics, rel)
        if t.text == "enum":
            item.members = read_variants(code, j + 1, close)
        elif code[j].text == "{":
            item.members = read_fields(code[j + 1:close])
        else:
            item.members = [Member(str(k), p[0].line, type_paths(strip_attrs(p))) for k, p in enumerate(split_depth0(code[j + 1:close]))]
        items.append(item)
        i = j + 1
    return items, toks


def read_variants(code: list[Tok], i: int, stop: int) -> list[Member]:
    out = []
    while i < stop:
        while i < stop and code[i].text == "#":
            i = skip_attribute(code, i)
        if i >= stop:
            break
        if code[i].kind != "ident":
            raise LexError(f"expected a variant name at line {code[i].line}, found {code[i].text!r}")
        name, paths = code[i], []
        i += 1
        if i < stop and code[i].text in ("(", "{"):
            close = match_close(code, i)
            if code[i].text == "(":
                for part in split_depth0(code[i + 1:close]):
                    paths.extend(type_paths(strip_attrs(part)))
            else:
                paths = [p for f in read_fields(code[i + 1:close]) for p in f.paths]
            i = close + 1
        if i < stop and code[i].text == "=":
            while i < stop and code[i].text != ",":
                i += 1
        if i < stop and code[i].text != ",":
            raise LexError(f"expected `,` after variant {name.text} at line {code[i].line}, found {code[i].text!r}")
        i += 1
        out.append(Member(name.text, name.line, paths))
    return out


def read_function_region(src: str, name: str) -> tuple[int, int]:
    """The unique top-level function, including its attributes and preceding comments.

    Nested items and macro/string contents cannot supply a same-named definition.
    The span starts at the preceding item's closing line, like enum regions.
    """
    code = [t for t in lex(src) if t.kind not in ("doc", "comment")]
    regions, start, i = [], 0, 0
    while i < len(code):
        t = code[i]
        if t.text == "fn" and i + 1 < len(code) and code[i + 1].text == name:
            j, depth = i + 2, 0
            while j < len(code):
                token = code[j]
                if token.kind == "punct":
                    if token.text in ("(", "[") or (token.text == "{" and depth > 0):
                        j = match_close(code, j) + 1
                        continue
                    depth += {"<": 1, ">": -1}.get(token.text, 0)
                    if token.text in (";", "{") and depth == 0:
                        break
                j += 1
            if j == len(code) or code[j].text != "{":
                raise LexError(f"function {name} has no complete body")
            end = match_close(code, j)
            regions.append((code[start - 1].end_line if start else 1, code[end].end_line))
            i = start = end + 1
        elif t.kind == "punct" and t.text in OPEN:
            i = match_close(code, i) + 1
            if t.text == "{":
                start = i
        elif t.kind == "punct" and t.text == ";":
            i += 1
            start = i
        else:
            i += 1
    if len(regions) != 1:
        raise LexError(f"expected one top-level function {name}, found {len(regions)}")
    return regions[0]


def read_uses(toks: list[Tok]) -> dict:
    """`use` declarations: imported name (or alias) -> path segments (globs are not names)."""
    code = [t for t in toks if t.kind not in ("doc", "comment")]
    out: dict = {}

    def walk(run: list[Tok], prefix: tuple) -> None:
        segs, i = list(prefix), 0
        while i < len(run):
            if run[i].kind == "ident":
                segs.append(run[i].text)
                i += 1
                if i < len(run) and run[i].text == "::":
                    i += 1
                    continue
                out[run[i + 1].text if i + 1 < len(run) and run[i].text == "as" else segs[-1]] = tuple(segs)
                return
            if run[i].text == "{":
                for part in split_depth0(run[i + 1:match_close(run, i)], angle=False):
                    walk(part, tuple(segs))
                return
            i += 1

    i = 0
    while i < len(code):
        if code[i].kind == "ident" and code[i].text == "use":
            j = i + 1
            while j < len(code) and code[j].text != ";":
                j = match_close(code, j) + 1 if code[j].text == "{" else j + 1
            walk(code[i + 1:j], ())
            i = j
        i += 1
    return out


def doc_lines_of(toks: list[Tok]) -> list[tuple[int, str]]:
    """(line, text) of every `///`, `/** */` and `#[doc = "..."]` doc line of a file, in order."""
    out = []
    for k, t in enumerate(toks):
        if t.kind == "doc" and t.text.startswith("///"):
            out.append((t.line, t.text[3:]))
        elif t.kind == "doc" and t.text.startswith("/**"):
            out += [(t.line + n, re.sub(r"^\s*\*(?!\*)", "", piece) if n else piece) for n, piece in enumerate(t.text[3:-2].split("\n"))]
        elif t.text == "doc" and k >= 2 and toks[k - 1].text == "[" and toks[k - 2].text == "#" and k + 2 < len(toks) \
                and toks[k + 1].text == "=" and toks[k + 2].kind == "str":
            m = re.match(r'^[bc]?r?(#*)"(.*)"\1$', toks[k + 2].text, re.S)
            out += [(toks[k + 2].line + n, " " + piece) for n, piece in enumerate((m.group(2) if m else toks[k + 2].text).split("\n"))]
    return out


@dataclass
class DocUnit:
    """A paragraph, or a bullet with its continuation lines, of one doc comment."""
    rel: str
    lines: tuple
    text: str
    bullet: bool
    item: str
    family: bool = False
    header: bool = False
    keyword: bool = False


def split_units(rel: str, item: str, doc: list[tuple[int, str]]) -> list[DocUnit]:
    units, cur, prev = [], None, None

    def close() -> None:
        nonlocal cur
        if cur is not None:
            units.append(DocUnit(rel, tuple(cur["lines"]), " ".join(x.strip() for x in cur["texts"]).strip(), cur["bullet"], item))
        cur = None

    for line, body in doc:
        if prev is not None and line != prev + 1:
            close()
        prev = line
        if not body.strip():
            close()
            continue
        indent = len(body) - len(body.lstrip(" \t"))
        if cur is not None and (cur["bullet"] and indent > cur["indent"] or not cur["bullet"] and not re.match(r"^\s*[*+-]\s", body)):
            cur["lines"].append(line)
            cur["texts"].append(body)
            continue
        close()
        bullet = re.match(r"^\s*[*+-]\s", body) is not None
        cur = {"lines": [line], "texts": [re.sub(r"^\s*[*+-]\s", "", body) if bullet else body], "bullet": bullet, "indent": indent}
    close()
    return units


def effect_phases(effect: str) -> frozenset | None:
    """The MIR phases an effect admits."""
    m = re.fullmatch(r"(disallowed_from|allowed_from|until):(.+)", effect)
    if m and m.group(2) in MIR_PHASES:
        k = MIR_PHASES.index(m.group(2))
        return frozenset({"disallowed_from": MIR_PHASES[:k], "allowed_from": MIR_PHASES[k:], "until": MIR_PHASES[:k + 1]}[m.group(1)])
    m = re.fullmatch(r"(only_in|not_in):(Analysis|Runtime)", effect)
    return frozenset(p for p in MIR_PHASES if p.startswith(m.group(2)) == (m.group(1) == "only_in")) if m else None


# ============================================================================
# the checker
# ============================================================================


class Checker:
    def __init__(self, options: Options) -> None:
        self.o = options
        self.f = C.Findings()
        self.counts: dict = {}
        self.parsed: dict[str, tuple] = {}
        self.cited = 0

    def add(self, kind: str, message: str) -> None:
        self.f.add(kind, message)

    # ---- inputs
    def load(self) -> bool:
        o = self.o
        self.pins = C.load_pins(o.pins or o.repo / C.PINS_REL)
        trees = {"worktree": C.GitTree(o.repo, "HEAD")}
        missing = [name for name, source in READS.items() if source not in o.trees]
        clones = C.locate_clones(self.pins, missing, o.clones) if missing else {}
        for name, path in clones.items():
            trees[READS[name]] = C.GitTree(path, self.pins.sources[name].revision)
        # The aligned upstream text a `Trust:`-edited file is compared against. The superproject
        # does not hold the alignment commit's objects, so it is read from the rust clone that
        # scripts/trust_core/fetch_sources.py checks those files out in (RUST_UPSTREAM_FILES).
        rust = C.Source("rust", RUST_URL, self.pins.alignment, self.pins.alignment_date, "objects")
        if "upstream" not in o.trees:
            path = Path(o.clones.get("rust") or C.sources_root() / "rust")
            if not (path / ".git").exists():
                raise C.MissingClone(f"the rust clone is missing at {path}; create it with {C.FETCH_COMMAND}")
            clones["rust"] = path
            trees["upstream"] = C.GitTree(path, rust.revision)
        trees.update(o.trees)
        self.trees, self.rustc, self.upstream = trees, trees["worktree"], trees["upstream"]
        self.resolver = C.Resolver(o.repo, {k: v for k, v in trees.items() if k != "upstream"})
        if o.check_pin_state:
            for name, path in clones.items():
                C.verify_clone(self.f, path, rust if name == "rust" else self.pins.sources[name], self.pins)
            C.verify_objects(self.f, f"repository {o.repo}", o.repo)
            C.verify_alignment(self.f, self.rustc, self.pins)
        try:
            self.table_text = (o.table or o.repo / TABLE_REL).read_text(encoding="utf-8")
            self.data = tomllib.loads(self.table_text)
            vocab = tomllib.loads((o.repo / VOCAB_TABLE_REL).read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError) as error:
            self.add("TABLE", str(error))
            return False
        self.vocab = {e["name"]: e.get("phases", list(S_PHASES)) for e in vocab.get("entry", [])}
        self.vocab_ops: dict[str, dict] = {}
        for row in vocab.get("mir_operator", []):
            slot = self.vocab_ops.setdefault(row["mir"], {"maps_to": set(), "refusals": set()})
            slot["maps_to"].update(row.get("maps_to", []))
            slot["refusals"].update([row["refusal"]] if "refusal" in row else [])
        if o.check_vocabulary:
            import core_vocabulary as CV
            vocabulary = CV.collect(CV.Options(repo=o.repo, check_history=o.check_history, check_pin_state=o.check_pin_state))
            if vocabulary.violations:
                self.add("VOCABULARY", f"scripts/trust_core/core_vocabulary.py reports {len(vocabulary.violations)} violation(s), the first: {vocabulary.violations[0]}")
        return True

    def items_of(self, rel: str) -> tuple[list[Item], list[Tok]]:
        if rel not in self.parsed:
            text = self.rustc.text(rel)
            try:
                self.parsed[rel] = read_items(text, rel) if text is not None else ([], [])
            except LexError as error:
                self.add("SCOPE", f"{rel}: {error}")
                self.parsed[rel] = ([], [])
            if text is None:
                self.add("SCOPE", f"{rel} does not exist at HEAD")
        return self.parsed[rel]

    def region(self, item: Item) -> None:
        self.resolver.upstream_region(self.f, item.rel, item.first, item.last, f"{item.kind} {item.name}")

    def constant_evidence_region(self) -> None:
        """Admit only the complete, unchanged upstream conversion function's citations."""
        rel = "compiler/rustc_const_eval/src/const_eval/eval_queries.rs"
        name = "op_to_const"
        current = self.rustc.text(rel)
        original = self.upstream.text(rel)
        try:
            if current is None or original is None:
                raise LexError("current or aligned upstream source is unavailable")
            first, last = read_function_region(current, name)
            old_first, old_last = read_function_region(original, name)
            if current.split("\n")[first - 1:last] != original.split("\n")[old_first - 1:old_last]:
                raise LexError("complete function text differs from the aligned upstream source")
        except LexError as error:
            self.add("PIN", f"{rel}: function {name}: {error}")
            return
        self.resolver.upstream_region(self.f, rel, first, last, f"function {name}")

    def cite(self, kind: str, where: str, c: object, key: str = "quote") -> dict | None:
        """The parts of a verified {ref, quote} (or {ref, arm}) citation, or None."""
        if not isinstance(c, dict) or set(c) != {"ref", key}:
            self.add("TABLE", f"{where}: a citation is {{ref, {key}}}, not {c!r}")
            return None
        self.cited += 1
        return C.parse_ref(c["ref"]) if self.resolver.resolve(self.f, kind, where, c["ref"], c[key]) else None

    def cites(self, kind: str, where: str, row: dict) -> None:
        for name in sorted(CITE_LISTS & set(row)):
            for c in row[name]:
                self.cite(kind, f"{where} {name}", c)
        for name in sorted(CITE_ONE & set(row)):
            self.cite(kind, f"{where} {name}", row[name])
        for name in sorted(ARM_LISTS & set(row)):
            for c in row[name] if isinstance(row[name], list) else []:
                self.cite(kind, f"{where} {name}", c, "arm")

    # ---- TABLE
    def rows(self) -> None:
        d = self.data
        for key in sorted(set(d) - TOP_KEYS):
            self.add("TABLE", f"top-level key {key!r} is not part of the schema")
        if (d.get("schema"), d.get("design"), d.get("vocabulary")) != (SCHEMA, C.DESIGN_REL, VOCAB_TABLE_REL):
            self.add("TABLE", f"schema, design and vocabulary must be {SCHEMA}, {C.DESIGN_REL} and {VOCAB_TABLE_REL}")
        scope = d.get("scope")
        if not isinstance(scope, dict) or set(scope) != SCOPE_KEYS or not isinstance(scope.get("phase_words"), str) or not all(
                isinstance(scope[k], list) and scope[k] and all(isinstance(x, (str, dict)) for x in scope[k]) for k in SCOPE_KEYS - {"phase_words"}):
            self.add("TABLE", f"[scope] holds exactly {sorted(SCOPE_KEYS)}: phase_words a regular expression, the rest non-empty lists")
            scope = {k: [] for k in SCOPE_KEYS} | {"phase_words": r"(?!)"}
        C.repeated_elements(self.f, "TABLE", "[scope]", scope)
        self.scope_row = scope
        try:
            self.phase_words = re.compile(scope["phase_words"])
        except re.error as error:
            self.add("TABLE", f"[scope] phase_words: {error}")
            self.phase_words = re.compile(r"(?!)")
        self.t: dict[str, dict] = {}
        for kind, (allowed, required, key) in ROWS.items():
            valid = []
            for index, row in enumerate(d.get(kind, [])):
                where = f"{kind}[{index}] {key(row) if isinstance(row, dict) else ''}"
                if not isinstance(row, dict) or set(row) - allowed or required - set(row):
                    self.add("TABLE", f"{where}: unknown keys {sorted(set(row) - allowed) if isinstance(row, dict) else row}, missing {sorted(required - set(row)) if isinstance(row, dict) else ''}")
                    continue
                wrong = sorted(k for k, v in row.items() if not (k == "minimize" and v == "no arm") and (
                    not isinstance(v, TYPES.get(k, (str, None))[0]) or isinstance(v, bool) != (TYPES.get(k, (str, None))[0] is bool)
                    or (TYPES.get(k, (str, None))[1] is not None and not all(isinstance(x, TYPES[k][1]) for x in v))))
                if wrong:
                    self.add("TABLE", f"{where}: fields {wrong} have the wrong type")
                    continue
                C.repeated_elements(self.f, "TABLE", where, row)
                for name, value in row.items():
                    if isinstance(value, (list, dict)) and not value and (kind, name) not in ALLOWED_EMPTY:
                        self.add("TABLE", f"{where}: {name} is empty; a list names something, and an optional one is omitted")
                    if name in FREE_TEXT_KEYS and (not isinstance(value, str) or not value.strip() or C.FREE_TEXT_CITATION.search(value)):
                        self.add("TABLE", f"{where}: {name} must be non-empty text without an unchecked line citation")
                valid.append(row)
            self.t[kind] = C.unique_rows(self.f, "TABLE", kind, valid, key)

    # ---- SCOPE
    def scope(self) -> None:
        design = (self.trees.get("design") or self.rustc).lines(C.DESIGN_REL) or []
        roots, refs, self.d03_commit = [], [], None
        for anchor, stop in DESIGN_LIST_ANCHORS:
            hits = [k for k, line in enumerate(design) if anchor in line]
            if len(hits) != 1:
                self.add("SCOPE", f"the design holds the D0.3 list anchor {anchor!r} {len(hits)} times, not once")
                continue
            text, k = design[hits[0]][design[hits[0]].index(anchor):], hits[0]
            while stop not in text and k < hits[0] + 6 and k + 1 < len(design):
                k += 1
                text += " " + design[k].strip()
            refs.append(f"design:{hits[0] + 1}")
            roots += [n for n in re.findall(r"`([A-Z][A-Za-z0-9]*)`", text.split(stop)[0]) if n not in roots]
            commit = re.search(r"at `([0-9a-f]{7,40})`", design[hits[0]])
            self.d03_commit = commit.group(1) if commit else self.d03_commit
        s = self.scope_row
        if sorted(c.get("ref") for c in s["design_lists"] if isinstance(c, dict)) != sorted(refs) or s["design_enums"] != roots:
            self.add("SCOPE", f"[scope] design_lists and design_enums must be the design's D0.3 lists at {refs}: {roots}")
        for c in s["design_lists"]:
            self.cite("SCOPE", "[scope] design_lists", c)
        files = self.rustc.files(MIR_MODULE_DIR, (".rs",))
        scope_files = [SYNTAX_REL] + [f for f in files if f != SYNTAX_REL]
        defined = {i.name for rel in scope_files for i in self.items_of(rel)[0] if i.kind == "enum"}
        elsewhere = [f for f in self.rustc.files(ABSENT_SEARCH_ROOT, (".rs",)) if not f.startswith(MIR_MODULE_DIR)]
        self.rustc.prefetch(elsewhere)
        self.enum_files: dict[str, list[str]] = {}
        for rel in elsewhere:
            text = self.rustc.text(rel) or ""
            for name in set(roots) | set(s["task_named"]):
                if re.search(r"\benum\s+" + re.escape(name) + r"\b", text) and any(i.kind == "enum" and i.name == name for i in self.items_of(rel)[0]):
                    self.enum_files.setdefault(name, []).append(rel)
        for name in s["task_named"]:
            if name not in defined:
                if len(self.enum_files.get(name, [])) > 1:
                    self.add("SCOPE", f"task-named enum {name} is defined in several files: {self.enum_files[name]}")
                scope_files += [f for f in self.enum_files.get(name, []) if f not in scope_files]
        if s["scope_files"] != scope_files:
            self.add("SCOPE", f"[scope] scope_files must be the derived scope files (every .rs file of {MIR_MODULE_DIR}, then the files defining task-named enums outside it): {scope_files}")
        self.defs: dict[str, list[Item]] = {}
        self.uses: dict[str, dict] = {}
        self.toks: dict[str, list[Tok]] = {}
        for rel in scope_files:
            items, toks = self.items_of(rel)
            self.toks[rel], self.uses[rel] = toks, read_uses(toks)
            for item in items:
                self.defs.setdefault(item.name, []).append(item)
        self.in_scope: dict[str, Item] = {}
        self.structs: dict[str, Item] = {}
        self.boundary: dict[str, set] = {}
        self.holders: dict[str, set] = {}  # item -> origins: "E::V", "S.f", "type A" or "<root>"
        self.scope_files = scope_files
        self.absent = sorted(n for n in set(roots) | set(s["task_named"]) if n not in self.defs)
        seen: set = set()
        # the closure of the roots; then each task-named enum it does not reach is a root of its own
        for extra in (False, True):
            work = [(n, "<root>") for n in (s["task_named"] if extra else roots) if n in self.defs and n not in seen]
            while work:
                name, origin = work.pop(0)
                self.holders.setdefault(name, set()).add(origin)
                if name in seen:
                    continue
                seen.add(name)
                if len(self.defs[name]) > 1:
                    self.add("SCOPE", f"{name} is defined {len(self.defs[name])} times in the scope files; resolution is ambiguous")
                item = self.defs[name][0]
                (self.in_scope if item.kind == "enum" else self.structs)[name] = item
                for m in item.members:
                    held = f"{name}::{m.name}" if item.kind == "enum" else f"type {name}" if item.kind == "type" else f"{name}.{m.name}"
                    for path in m.paths:
                        self.payload(item, held, path, work)
        for item in list(self.in_scope.values()) + list(self.structs.values()):
            self.region(item)
        self.variants = {f"{e}::{m.name}": (item, m) for e, item in self.in_scope.items() for m in item.members}
        self.aliases = {n: i.members[0].paths[0].name for n, i in self.structs.items() if i.kind == "type" and i.members and i.members[0].paths}
        self.containers: dict[str, Item] = {}
        for name in s["containers"]:
            item = next((i for rel in scope_files for i in self.items_of(rel)[0] if i.kind == "struct" and i.name == name), None)
            if item is None:
                self.add("SCOPE", f"[scope] container {name} is not a struct of the scope files")
            else:
                self.containers[name] = item
                self.region(item)
        self.fields = {f"{c}.{m.name}": (item, m) for c, item in self.containers.items() for m in item.members}
        self.family = []
        for name in MIR_PHASE_FAMILY:
            item = next((i for i in self.defs.get(name, []) if i.kind == "enum" and i.rel == SYNTAX_REL), None)
            if item is None:
                self.add("PHASE", f"{SYNTAX_REL} defines no enum {name}")
            else:
                self.family.append(item)
                self.region(item)
        self.case_enums = {}
        for name, rel in CASE_ENUM_FILES.items():
            item = next((i for i in self.items_of(rel)[0] if i.kind == "enum" and i.name == name), None)
            if item is None:
                self.add("UNIVERSE", f"{rel} defines no enum {name}")
            else:
                self.case_enums[name] = [m.name for m in item.members]
                self.region(item)
        rows = self.t["absent"]
        for name in sorted(set(self.absent) | set(rows)):
            if name not in rows:
                self.add("SCOPE", f"{name} is named by the design or [scope] task_named, is defined in no scope file, and has no [[absent]] row")
            elif name not in self.absent:
                self.add("SCOPE", f"[[absent]] {name} is stale: it is defined in the scope files")
            elif self.enum_files.get(name):
                self.add("SCOPE", f"[[absent]] {name}: an `enum {name}` exists at {self.enum_files[name]}")
        for name in sorted(set(self.boundary) | set(self.t["boundary"])):
            row = self.t["boundary"].get(name)
            if row is None:
                self.add("SCOPE", f"payload type {name} (reached from {sorted(self.boundary[name])[:3]}) is outside the scope files and has no [[boundary]] row")
            elif name not in self.boundary:
                self.add("SCOPE", f"[[boundary]] {name} is stale: no in-scope payload reaches it")
            elif row["class"] not in BOUNDARY_CLASSES or (row["class"] == "enum") != ("owner" in row):
                self.add("TABLE", f"[[boundary]] {name}: class is one of {BOUNDARY_CLASSES}, and an `enum` names its owner")

    def payload(self, owner: Item, origin: str, path: TypePath, work: list) -> None:
        name = path.name
        if name in PRIMITIVES or name in WRAPPERS or name in owner.generics or name == "Self":
            return
        if len(path.segments) > 1 and not (path.segments[0] in ("crate", "self", "super") and name in self.defs):
            self.boundary.setdefault("::".join(path.segments), set()).add(origin)
            return
        imported = self.uses.get(owner.rel, {}).get(name)
        if name not in self.defs:
            self.boundary.setdefault(name, set()).add(origin)
        elif imported and not (imported[0] in ("super", "self") or imported[:2] == ("crate", "mir") or (imported[0] == "crate" and any(
                f"{ABSENT_SEARCH_ROOT}{'/'.join(imported[1:-1])}{suffix}" in self.scope_files for suffix in (".rs", "/mod.rs")))):
            self.add("SCOPE", f"{origin}: {name} is imported from {'::'.join(imported)} in {owner.rel} and also defined in the scope files; resolution is ambiguous")
        else:
            work.append((name, origin))

    def rooted_holders(self, name: str, seen: frozenset = frozenset()) -> tuple[set, bool]:
        """The in-scope variants whose payload reaches item `name` (through structs and aliases), and whether a root does."""
        variants, rooted = set(), False
        for origin in self.holders.get(name, ()):
            if origin == "<root>":
                rooted = True
            elif "::" in origin:
                variants.add(origin)
            else:
                holder = origin.split(".")[0].replace("type ", "")
                if holder not in seen:
                    v, r = self.rooted_holders(holder, seen | {name})
                    variants, rooted = variants | v, rooted or r
        return variants, rooted

    # ---- INTRINSIC universe
    def intrinsics(self) -> None:
        self.items: dict[str, dict] = {}
        files = self.rustc.files(INTRINSIC_ROOT, (".rs",))
        self.rustc.prefetch(files)
        for rel in files:
            text = self.rustc.text(rel) or ""
            if "rustc_intrinsic" not in text:
                continue
            try:
                code = [t for t in lex(text) if t.kind not in ("doc", "comment")]
            except LexError as error:
                self.add("INTRINSIC", f"{rel}: {error}")
                continue
            parts = rel.split("/")
            module = [parts[1]] + parts[3:-1] + ([] if parts[-1] in ("mod.rs", "lib.rs") else [parts[-1][:-3]])
            mods = [(k, match_close(code, k + 2), code[k + 1].text) for k in range(len(code) - 2)
                    if code[k].text == "mod" and code[k + 1].kind == "ident" and code[k + 2].text == "{"]
            k = 0
            while k < len(code):
                if not (code[k].text == "#" and k + 1 < len(code) and code[k + 1].text in ("[", "!")):
                    k += 1
                    continue
                end = skip_attribute(code, k)
                inner = [t.text for t in code[k:end]]
                if "rustc_intrinsic" in inner and inner != ["#", "[", "rustc_intrinsic", "]"]:
                    self.add("INTRINSIC", f"{rel}:{code[k].line}: attribute {' '.join(inner)} names rustc_intrinsic in a form this checker does not read")
                elif "rustc_intrinsic" in inner:
                    self.intrinsic_item(rel, code, k, end, module, mods)
                k = end

    def intrinsic_item(self, rel: str, code: list[Tok], attr: int, end: int, module: list, mods: list) -> None:
        attrs, b = [], attr
        while b >= 2 and code[b - 1].text == "]":
            m, depth = b - 1, 0
            while m >= 0:
                depth += {"]": 1, "[": -1}.get(code[m].text, 0)
                if depth == 0:
                    break
                m -= 1
            if m < 1 or code[m - 1].text != "#":
                break
            attrs.append("".join(t.text for t in code[m - 1:b]))
            b = m - 1
        k = end
        while k < len(code) and code[k].text == "#":
            e = skip_attribute(code, k)
            attrs.append("".join(t.text for t in code[k:e]))
            k = e
        while k < len(code) and (code[k].text in ("pub", "const", "unsafe", "async", "extern", "default") or code[k].kind == "str"):
            k = match_close(code, k + 1) + 1 if code[k].text == "pub" and code[k + 1].text == "(" else k + 1
        if k + 1 >= len(code) or code[k].text != "fn" or code[k + 1].kind != "ident":
            self.add("INTRINSIC", f"{rel}:{code[attr].line}: #[rustc_intrinsic] is not on a fn item")
            return
        j, depth = k + 2, 0
        while j < len(code):
            if code[j].text in ("(", "["):
                j = match_close(code, j) + 1
                continue
            depth += {"<": 1, ">": -1}.get(code[j].text, 0)
            if code[j].text in (";", "{") and depth <= 0:
                break
            j += 1
        body = j < len(code) and code[j].text == "{"
        last = code[match_close(code, j)].line if body else code[min(j, len(code) - 1)].line
        name = code[k + 1]
        path = "::".join(module + [x[2] for x in mods if x[0] < attr < x[1]] + [name.text])
        if path in self.items:
            self.add("INTRINSIC", f"two #[rustc_intrinsic] items have the path {path}")
        self.items[path] = {"name": name.text, "at": f"{rel}:{name.line}", "body": body, "spec": "#[miri::intrinsic_fallback_is_spec]" in attrs}
        self.resolver.upstream_region(self.f, rel, code[b - 1].end_line if b else 1, last, f"intrinsic {path}")

    # ---- PHASE
    def phases(self) -> None:
        units: dict[tuple, DocUnit] = {}
        seen_items = set()
        for item, family in [(i, True) for i in self.family] + [(i, False) for i in list(self.in_scope.values()) + list(self.structs.values()) + list(self.containers.values())]:
            if (item.rel, item.first, item.name) in seen_items or item.rel not in self.toks:
                continue
            seen_items.add((item.rel, item.first, item.name))
            toks = self.toks[item.rel]
            for k, t in enumerate(toks):
                if t.text == "#" and k + 1 < len(toks) and toks[k + 1].text in ("[", "!") and item.first <= t.line <= item.last:
                    try:
                        inner = [x for x in toks[k:skip_attribute(toks, k)] if x.kind != "comment"]
                    except LexError:
                        continue
                    plain = [x.text for x in inner if x.kind != "str"] in (["#", "[", "doc", "=", "]"], ["#", "!", "[", "doc", "=", "]"]) and sum(x.kind == "str" for x in inner) == 1
                    if any(x.text == "doc" for x in inner) and not plain:
                        self.add("PHASE", f"{item.rel}:{t.line} carries a doc attribute in a form the doc reader does not read, inside {item.name}")
            doc = [(n, text) for n, text in doc_lines_of(toks) if item.first <= n <= item.last]
            for u in split_units(item.rel, item.name, doc):
                u.family = family
                u.header = not u.bullet and HEADER_UNIT.fullmatch(re.sub(r"\s+", " ", u.text)) is not None
                u.keyword = self.phase_words.search(u.text) is not None
                units.setdefault((u.rel, u.lines[0]), u)
        line_unit = {(u.rel, n): u for u in units.values() for n in u.lines}
        unit_rule, self.restrictions, self.semantic = {}, {}, {}
        for rid, row in self.t["phase_rule"].items():
            where = f"phase_rule {rid}"
            cited = set()
            for c in row.get("owner_refs", []):
                self.cite("PHASE", f"{where} owner_refs", c)
            for c in row["refs"]:
                parts = self.cite("PHASE", where, c)
                if parts:
                    cited.update((parts["path"], n) for n in range(parts["start"], parts["end"] + 1))
            for u in {id(line_unit[k]): line_unit[k] for k in cited if k in line_unit}.values():
                if not {(u.rel, n) for n in u.lines} <= cited or u.header:
                    self.add("PHASE", f"{where} cites part of the doc unit {u.rel}:{u.lines[0]}-{u.lines[-1]}, or a header, which is read, not a rule")
                if unit_rule.setdefault((u.rel, u.lines[0]), rid) != rid:
                    self.add("PHASE", f"{where} and {unit_rule[(u.rel, u.lines[0])]} both cite the doc unit {u.rel}:{u.lines[0]}")
            for k in sorted(k for k in cited if k not in line_unit):
                self.add("PHASE", f"{where} cites {k[0]}:{k[1]}, which is no doc line of the MirPhase docs or of an item read")
            kind, effect = row["kind"], row["effect"]
            applies = set(row.get("applies_to", []))
            if "applies_to_enum" in row:
                e = row["applies_to_enum"]
                applies = {f"{e}::{m.name}" for m in self.in_scope[e].members if m.name not in row.get("except", [])} if e in self.in_scope else set()
                if e not in self.in_scope or "applies_to" in row:
                    self.add("PHASE", f"{where}: applies_to_enum {e!r} is an in-scope enum, and replaces applies_to")
            for name in sorted(applies - set(self.variants)):
                self.add("PHASE", f"{where}: applies_to names no in-scope variant {name}")
            if kind not in PHASE_RULE_KINDS:
                self.add("PHASE", f"{where}: kind must be one of {PHASE_RULE_KINDS}")
            elif kind in EFFECTLESS_KINDS:
                extra = {"applies_to_enum", "except"} | ({"applies_to", "s_phases", "owner_refs", "same_as"} if kind == "descriptive" else set())
                if effect != "none" or extra & set(row):
                    self.add("PHASE", f"{where}: a {kind} rule has effect \"none\" and no {sorted(extra & set(row))}")
                elif kind == "semantic" and "same_as" in row:
                    if {"applies_to", "s_phases", "owner_refs"} & set(row):
                        self.add("PHASE", f"{where}: a semantic rule with same_as states nothing else")
                    self.semantic[rid] = {"same_as": row["same_as"]}
                elif kind == "semantic":
                    sp = row.get("s_phases") or []
                    if not sp or sp != [x for x in S_PHASES if x in sp] or not row.get("owner_refs") or not (applies or row.get("note")) or any(
                            not str(c.get("ref")).startswith("design:") for c in row.get("owner_refs", [])):
                        self.add("PHASE", f"{where}: a semantic rule names ordered s_phases, cites the design line that owns it (owner_refs), and applies to variants or says why not")
                    self.semantic[rid] = {"s_phases": set(sp), "applies_to": applies}
            else:
                admitted = effect_phases(effect)
                if admitted is None or {"same_as", "s_phases", "owner_refs"} & set(row):
                    self.add("PHASE", f"{where}: effect {effect!r} is unreadable, or the rule carries a semantic rule's field")
                elif kind == "out-of-scope" and applies:
                    self.add("PHASE", f"{where}: an out-of-scope rule names in-scope variants")
                elif kind != "out-of-scope" and not applies:
                    self.add("PHASE", f"{where}: a {kind} rule applies to no variant")
                elif kind == "variant":
                    for name in applies:
                        self.restrictions.setdefault(name, []).append(admitted)
        for rid, sem in self.semantic.items():
            if "same_as" in sem and "s_phases" not in self.semantic.get(sem["same_as"], {}):
                self.add("PHASE", f"phase_rule {rid}: same_as {sem['same_as']!r} is not a semantic rule stating s_phases")
        for key, u in sorted(units.items()):
            if ((u.family and not u.header) or (not u.family and u.keyword)) and key not in unit_rule:
                self.add("PHASE", f"{u.rel}:{u.lines[0]}-{u.lines[-1]} is {'a MirPhase doc unit' if u.family else 'a doc unit of ' + u.item + ' matching phase_words'} ({u.text[:90]!r}) that no [[phase_rule]] cites")
        ordered = [(u.rel, u.item, u.text) for _, u in sorted(units.items())]
        pin = "sha256:" + hashlib.sha256(json.dumps(ordered, ensure_ascii=False).encode("utf-8")).hexdigest()
        if list(self.t["doc_pin"]) != ["in-scope-docs"] or (self.t["doc_pin"]["in-scope-docs"]["sha256"], self.t["doc_pin"]["in-scope-docs"]["units"]) != (pin, len(ordered)):
            self.add("PHASE", f"exactly one [[doc_pin]] in-scope-docs pins the doc text read: {len(ordered)} units, {pin}; review the changed docs, then re-pin")
        self.counts.update(doc_units=len(units), doc_units_ruled=len(unit_rule))
        # the S phases each read one MIR phase
        s_rows = self.t["s_phase"]
        if sorted(s_rows) != sorted(S_PHASES) or any(r["mir_phase"] not in MIR_PHASES for r in s_rows.values()):
            self.add("PHASE", f"[[s_phase]] rows are exactly {S_PHASES}, each reading a MIR phase")
        self.s_read = {s: r["mir_phase"] for s, r in s_rows.items()}
        # admitted MIR phases: the holders' phases narrowed by the variant rules, or a conflict row's phases
        self.conflicts = {}
        for cid, row in self.t["phase_conflict"].items():
            if row["follows"] not in CONFLICT_FOLLOWS or not set(row["phases"]) <= set(MIR_PHASES):
                self.add("PHASE", f"phase_conflict {cid}: follows is one of {CONFLICT_FOLLOWS} and phases are MIR phases")
            for name in row["applies_to"]:
                if name not in self.variants or self.conflicts.setdefault(name, cid) != cid:
                    self.add("PHASE", f"phase_conflict {cid}: {name} is no in-scope variant, or is in two conflict rows")
        self.admitted, computing = {}, set()
        for name in self.variants:
            self.variant_phases(name, computing)
        self.admitted.update({name: frozenset(MIR_PHASES) for name in self.fields})

    def variant_phases(self, name: str, computing: set) -> frozenset:
        if name in self.admitted or name in computing:
            return self.admitted.get(name, frozenset())
        computing.add(name)
        holders, rooted = self.rooted_holders(name.split("::")[0])
        base = frozenset(MIR_PHASES) if rooted else frozenset().union(*[self.variant_phases(h, computing) for h in holders])
        docs = base.intersection(*self.restrictions.get(name, [base]))
        out = docs
        if name in self.conflicts:
            row = self.t["phase_conflict"][self.conflicts[name]]
            out = frozenset(row["phases"]) & base
            if out == docs or not set(row["phases"]) <= base:
                self.add("PHASE", f"phase_conflict {row['id']}: for {name} its phases {row['phases']} equal the docs' derivation or exceed its holders' phases (stale)")
        computing.discard(name)
        self.admitted[name] = out
        return out

    # ---- UNIVERSE, DISPOSITION, MINIMIZE
    def constructs(self) -> None:
        refusals, self.used_refusals = self.t["refusal"], set()
        self.by_construct: dict[str, list[dict]] = {}
        self.spec_refs: dict[str, set] = {}
        ps_refs: dict[str, list] = {}
        hits = self.hits
        self.seed = {"construct": {"follows": 0, "diverges": 0, "no arm": 0}, "intrinsic": {"follows": 0, "diverges": 0, "no arm": 0}}
        universe = {**self.variants, **self.fields}
        for key, row in self.t["construct"].items():
            name, where = row["mir"], f"construct {key}"
            if name not in universe:
                self.add("UNIVERSE", f"{where}: names no variant of an in-scope enum and no field of a container at the pin (stale or invented)")
                continue
            self.by_construct.setdefault(name, []).append(row)
            item, member = universe[name]
            if row["at"] != f"{item.rel}:{member.line}" or row["mir_phases"] != [p for p in MIR_PHASES if p in self.admitted[name]]:
                self.add("UNIVERSE", f"{where}: at and mir_phases must be {item.rel}:{member.line} and {[p for p in MIR_PHASES if p in self.admitted[name]]}")
            self.cites("CITATION", where, row)
            sp = row["s_phases"]
            if not isinstance(sp, list) or sp != [s for s in S_PHASES if s in sp]:
                self.add("TABLE", f"{where}: s_phases must be an ordered subset of {S_PHASES}")
            self.disposition(where, row, name, member, sp, refusals)
            for sd in row.get("spec_divergence", []):
                self.spec_refs.setdefault(sd, set()).add(name)
            for ps in row.get("phase_semantics", []):
                ps_refs.setdefault(ps, []).append((name, set(sp), row["disposition"], where))
            self.minimize(where, "construct", row, [f"rs::{name}"] if "::" in name else [], hits)
        for name, (item, member) in universe.items():
            rows = self.by_construct.get(name, [])
            if not rows:
                self.add("UNIVERSE", f"{name} ({item.rel}:{member.line}) has no [[construct]] row")
                continue
            groups: dict[tuple, list] = {}
            for r in rows:
                groups.setdefault(tuple(r["s_phases"]), []).append(r)
            covered: set = set()
            for sp, rs in groups.items():
                if set(sp) & covered:
                    self.add("UNIVERSE", f"{name}: rows overlap in S phases {sorted(set(sp) & covered)} without sharing them as cases")
                covered |= set(sp)
                cases, case_enums = [r.get("case") for r in rs], {r.get("case_enum") for r in rs}
                if case_enums != {None}:
                    ce = next(iter(case_enums))
                    if len(case_enums) != 1 or ce not in self.case_enums or sorted(map(str, cases)) != sorted(f"{ce}::{v}" for v in self.case_enums[ce]):
                        self.add("UNIVERSE", f"{name} {list(sp)}: rows with case_enum share one enum of {sorted(CASE_ENUM_FILES)} and have one case per variant")
                elif len(rs) > 1 and (None in cases or len(set(cases)) != len(cases) or cases.count("otherwise") != 1):
                    self.add("UNIVERSE", f"{name} {list(sp)}: rows sharing S phases are distinct cases with exactly one `otherwise` ({cases})")
                elif len(rs) == 1 and cases[0] is not None:
                    self.add("UNIVERSE", f"{name} {list(sp)}: a single row carries a case")
            admitted = [s for s in S_PHASES if self.s_read.get(s) in self.admitted[name]]
            if [s for s in S_PHASES if s in covered] != admitted:
                self.add("PHASE", f"{name}: its rows cover S phases {sorted(covered)}, but it is admitted in {admitted}")
        for enum, item in self.in_scope.items():  # nesting: a child of refused or no_op holders
            holders, rooted = self.rooted_holders(enum)
            kinds = {r["disposition"] for h in holders for r in self.by_construct.get(h, [])}
            for m in item.members if not rooted and kinds in ({"refusal"}, {"no_op"}) else []:
                for r in self.by_construct.get(f"{enum}::{m.name}", []):
                    if r["disposition"] not in ({"refusal"} if kinds == {"refusal"} else {"no_op", "refusal"}):
                        self.add("DISPOSITION", f"{enum}::{m.name}: every row holding {enum} is {kinds.pop() if len(kinds) == 1 else kinds}, so it is too (or refused)")
        for rid, sem in self.semantic.items():
            target = sem if "same_as" not in sem else None
            for name in sorted(target["applies_to"]) if target else []:
                for r in self.by_construct.get(name, []):
                    if set(r["s_phases"]) & sem["s_phases"] and r["disposition"] != "refusal" and rid not in r.get("phase_semantics", []):
                        self.add("PHASE", f"construct {name} {r['s_phases']}: the semantic rule {rid} applies to it in {sorted(sem['s_phases'])}; list it in phase_semantics (or split the row by phase)")
        for rid, uses in ps_refs.items():
            sem = self.semantic.get(rid)
            for name, sp, disposition, where in uses:
                if sem is None or "same_as" in sem or name not in sem["applies_to"] or not sp <= sem["s_phases"] or disposition == "refusal":
                    self.add("PHASE", f"{where}: lists {rid}, which is no semantic rule stating s_phases, does not apply to {name} in {sorted(sp)}, or the row is refused")

    def minimize_coverage(self) -> None:
        """Every hit of the declared minimize search is cited by a row or is a [[stale_arm]] naming nothing at the pin."""
        universe = set(self.variants) | set(self.fields)
        names = {i["name"] for i in self.items.values()}
        for key, row in self.t["stale_arm"].items():
            parts = self.cite("MINIMIZE", f"stale_arm {key}", {"ref": row["ref"], "arm": row["arm"]}, "arm")
            token, at = row["token"], (parts["path"], parts["start"]) if parts else None
            if at is None or token not in self.hits.get(at, set()):
                self.add("MINIMIZE", f"stale_arm {key}: {token!r} is no hit of the minimize search on that line")
                continue
            self.cited_hits.add(at)
            ns, _, rest = token.partition("::")
            if ns == "rs" and (rest in universe or rest.removeprefix("sym::") in names):
                self.add("MINIMIZE", f"stale_arm {key}: {rest} exists at the pin, so the arm is not stale")
        for at in sorted(set(self.hits) - self.cited_hits):
            self.add("MINIMIZE", f"{at[0]}:{at[1]} names {sorted(self.hits[at])} in minimize, and no row or [[stale_arm]] cites that line")

    def disposition(self, where: str, row: dict, name: str, member: Member, sp: list, refusals: dict) -> None:
        disposition = row["disposition"]
        own = {"core", "refusal", "no_op", "dispatch"} & set(row)
        if disposition not in DISPOSITIONS or own != {disposition} or ("dispatch_via" in row and disposition != "dispatch"):
            self.add("TABLE", f"{where}: disposition {disposition!r} is one of {DISPOSITIONS}, with exactly its own field (has {sorted(own)})")
        enum = name.split("::")[0]
        if disposition == "core":
            for n in row["core"]:
                if n not in self.vocab or not set(sp) <= set(self.vocab[n]):
                    self.add("DISPOSITION", f"{where}: {n!r} is not a Core vocabulary entry admitting {sp}")
            if enum in VOCAB_OPERATOR_ENUMS and "::" in name:
                op = self.vocab_ops.get(name, {"maps_to": set(), "refusals": set()})
                if set(row["core"]) != op["maps_to"] or set(row.get("case_refusals", [])) != op["refusals"]:
                    self.add("DISPOSITION", f"{where}: core and case_refusals must be the vocabulary's maps_to {sorted(op['maps_to'])} and refusals {sorted(op['refusals'])} for {name}")
            elif "case_refusals" in row:
                self.add("DISPOSITION", f"{where}: case_refusals are read from the vocabulary's MIR operator rows only")
        elif enum in VOCAB_OPERATOR_ENUMS and name in self.vocab_ops:
            op = self.vocab_ops[name]
            # A vocabulary operator can deliberately have no Core encoding.
            # Preserve its exact refusal instead of demanding an invented
            # Core mapping. Mixed supported/refused cases still use core rows.
            if not (disposition == "refusal" and not op["maps_to"]
                    and op["refusals"] == {row.get("refusal")}):
                self.add("DISPOSITION", f"{where}: the vocabulary maps {name}; its row is core with the vocabulary's names, or its exact refusal when maps_to is empty")
        for r in row.get("case_refusals", []) + ([row["refusal"]] if disposition == "refusal" else []):
            self.used_refusals.add(r)
            if r not in refusals:
                self.add("DISPOSITION", f"{where}: refusal {r!r} is not a declared [[refusal]]")
        if disposition == "dispatch" and row["dispatch"] == "intrinsic":
            if name != "TerminatorKind::Call" or "case" not in row:
                self.add("DISPOSITION", f"{where}: dispatch to the [[intrinsic]] rows is a case of TerminatorKind::Call only")
        elif disposition == "dispatch":
            target = row["dispatch"]
            named = {p.name for p in member.paths} | {self.aliases.get(p.name) for p in member.paths}
            if target not in self.in_scope and target not in self.containers:
                self.add("DISPOSITION", f"{where}: dispatch {target!r} is no in-scope enum or container")
            elif (target in named) == ("dispatch_via" in row):
                self.add("DISPOSITION", f"{where}: dispatch_via cites the conversion into {target} exactly when {target} is not a payload type of {name}")

    def minimize_hits(self) -> dict:
        """(file, line) -> the tokens of the declared minimize search on that line."""
        tree, out = self.trees["minirust"], {}
        rs_enums = set(self.in_scope) | set(self.absent)
        smir = set(self.scope_row["smir_enums"])
        files = tree.files(MINIMIZE_DIR, (".rs",))
        tree.prefetch(files)
        for rel in files:
            try:
                code = [t for t in lex(tree.text(rel) or "") if t.kind not in ("doc", "comment")]
            except LexError as error:
                self.add("MINIMIZE", f"{rel}: {error}")
                continue
            for k in range(len(code) - 4):
                if code[k].text in ("rs", "smir") and code[k + 1].text == code[k + 3].text == "::" and code[k + 2].kind == code[k + 4].kind == "ident" \
                        and (k == 0 or code[k - 1].text != "::"):
                    ns, enum = code[k].text, code[k + 2].text
                    if (ns == "rs" and (enum in rs_enums or enum == "sym")) or (ns == "smir" and enum in smir):
                        out.setdefault((rel, code[k].line), set()).add(f"{ns}::{enum}::{code[k + 4].text}")
        # A declared smir enum is an enum minimize writes as `smir::Enum::Variant` at the pin: a misspelled or stale
        # element would silently narrow the declared search.
        written = {token.split("::")[1] for tokens in out.values() for token in tokens if token.startswith("smir::")}
        for enum in sorted(smir - written):
            self.add("SCOPE", f"[scope] smir_enums {enum!r}: minimize writes no `smir::{enum}::Variant` at the pin (stale or misspelled)")
        self.counts["minimize_hits"] = sum(map(len, out.values()))
        self.hits, self.cited_hits = out, set()
        return out

    def minimize(self, where: str, kind: str, row: dict, own: list, hits: dict) -> None:
        arms, disposition = row["minimize"], row["disposition"]
        mine = sorted(at for at, tokens in hits.items() if set(own) & tokens)
        if arms == "no arm":
            if mine or "arm_class" in row:
                self.add("MINIMIZE", f"{where}: says no arm, but minimize names it at {mine}, or it states an arm_class")
            self.seed[kind]["no arm"] += 1
        elif isinstance(arms, list) and arms:
            cited = set()
            for c in arms:
                parts = C.parse_ref(c.get("ref")) if isinstance(c, dict) else None
                if parts and parts["source"] == "minirust" and str(parts["path"]).startswith(MINIMIZE_DIR):
                    cited.add((parts["path"], parts["start"]))
                else:
                    self.add("MINIMIZE", f"{where}: {c!r} is not a minimize line")
            self.cited_hits |= cited
            if set(mine) - cited:
                self.add("MINIMIZE", f"{where}: minimize names it at {sorted(set(mine) - cited)}, which the row does not cite")
            if row.get("arm_class") not in ARM_CLASSES:
                self.add("MINIMIZE", f"{where}: arm_class is one of {ARM_CLASSES}")
            follows = (row.get("arm_class") == "refuses") == (disposition == "refusal")
            self.seed[kind]["follows" if follows else "diverges"] += 1
            if not follows and not (row.get("divergence") and row.get("divergence_refs")):
                self.add("MINIMIZE", f"{where}: its minimize arms {row.get('arm_class')} and it is {disposition}, so it states `divergence` with design `divergence_refs`")
        else:
            self.add("TABLE", f"{where}: minimize is \"no arm\" or a non-empty list of {{ref, arm}}")
        if any(not str(c.get("ref")).startswith("design:") for c in row.get("divergence_refs", []) if isinstance(c, dict)):
            self.add("MINIMIZE", f"{where}: a divergence cites the design")

    # ---- INTRINSIC rows
    def intrinsic_rows(self) -> None:
        rows: dict[str, list] = {}
        self.i_disp = {d: 0 for d in INTRINSIC_DISPOSITIONS} | {"split": 0}
        hits = self.hits
        for key, row in self.t["intrinsic"].items():
            where, item = f"intrinsic {key}", self.items.get(row["path"])
            if item is None:
                self.add("INTRINSIC", f"{where}: no #[rustc_intrinsic] fn has this path at the pin (stale or invented)")
                continue
            rows.setdefault(row["path"], []).append(row)
            if (row["name"], row["at"], row["fallback_is_spec"]) != (item["name"], item["at"], item["spec"]):
                self.add("INTRINSIC", f"{where}: name, at and fallback_is_spec must be {item['name']!r}, {item['at']}, {item['spec']}")
            self.cites("CITATION", where, row)
            disposition = row["disposition"]
            own = {"core", "refusal", "no_op"} & set(row)
            if own != ({disposition} if disposition != "fallback" else set()) or disposition not in INTRINSIC_DISPOSITIONS:
                self.add("TABLE", f"{where}: disposition {disposition!r} is one of {INTRINSIC_DISPOSITIONS}, with exactly its own field")
            if disposition == "fallback" and not (item["body"] and item["spec"]):
                self.add("INTRINSIC", f"{where}: fallback requires a body marked #[miri::intrinsic_fallback_is_spec]")
            if disposition == "refusal":
                self.used_refusals.add(row["refusal"])
                if row["refusal"] not in self.t["refusal"]:
                    self.add("DISPOSITION", f"{where}: refusal {row['refusal']!r} is not a declared [[refusal]]")
            names = set(row.get("core", []))
            needed = LOWERINGS.get(row.get("lowering"), S_PHASES)
            for n in sorted(names):
                if n not in self.vocab or not set(needed) <= set(self.vocab[n]):
                    self.add("DISPOSITION", f"{where}: {n!r} is not a Core vocabulary entry admitting {list(needed)}, where the intrinsic call is still a call")
            if "Stmt.Assign" in names and "Stmt.Validate" not in names:
                self.add("DISPOSITION", f"{where}: it assigns a call's return value (Stmt.Assign), which rustc retags ([[retag_site]]); core names Stmt.Validate")
            for sd in row.get("spec_divergence", []):
                self.spec_refs.setdefault(sd, set()).add(row["path"])
            if ("lowering" in row) != ("lowered_to" in row) or ("core_extra_reason" in row and "lowering" not in row) or row.get("lowering", "LowerIntrinsics") not in LOWERINGS:
                self.add("TABLE", f"{where}: lowering (one of {sorted(LOWERINGS)}) and lowered_to go together, and core_extra_reason needs them")
            derived = set()
            for c in row.get("lowered_to", []):
                for r in self.by_construct.get(c, []) if c in self.variants else [None]:
                    if r is None:
                        self.add("INTRINSIC", f"{where}: lowered_to {c} is not an in-scope variant")
                    elif r["disposition"] == "core":
                        derived.update(r["core"])
                    elif r["disposition"] == "refusal" and disposition != "refusal":
                        self.add("INTRINSIC", f"{where}: it lowers to {c}, which is refused, so it is refused")
            if disposition == "core" and "lowering" in row and (derived - names or (names - derived and "core_extra_reason" not in row)):
                self.add("INTRINSIC", f"{where}: core must hold its lowered_to rows' names {sorted(derived)}, and adds others only with a core_extra_reason")
            self.minimize(where, "intrinsic", row, [f"rs::sym::{row['name']}"], hits)
        for path, item in self.items.items():
            found = rows.get(path, [])
            cases = [r.get("case") for r in found]
            if not found:
                self.add("INTRINSIC", f"#[rustc_intrinsic] {path} ({item['at']}) has no [[intrinsic]] row")
            elif len(found) > 1 and (None in cases or len(set(cases)) != len(cases) or cases.count("otherwise") != 1):
                self.add("INTRINSIC", f"{path}: its rows are distinct cases with exactly one `otherwise` ({cases})")
            elif len(found) == 1 and cases[0] is not None:
                self.add("INTRINSIC", f"{path}: a single row carries a case")
            else:
                self.i_disp["split" if len(found) > 1 else found[0]["disposition"]] += 1

    # ---- retags, producers, conflicts, refusals, divergences, deferred checks
    def judgments_rest(self) -> None:
        for kind in ("s_phase", "absent", "boundary", "refusal", "phase_conflict", "producer", "retag_site", "body_entry", "spec_divergence", "deferred_check"):
            for key, row in self.t[kind].items():
                self.cites("CITATION", f"{kind} {key}", row)
        body = self.t["body_entry"]
        if list(body) != [BODY_ENTRY] or any(n not in self.vocab for n in body.get(BODY_ENTRY, {}).get("core", [])):
            self.add("RETAG", f"exactly one [[body_entry]] row, {BODY_ENTRY!r}, names Core vocabulary entries")
        for key, row in self.t["retag_site"].items():
            where = f"retag_site {key}"
            for target in row["realized_by"]:
                carried = [body[BODY_ENTRY]["core"]] if target == BODY_ENTRY and BODY_ENTRY in body else \
                    [r["core"] for r in self.by_construct.get(target, []) if r["disposition"] == "core"]
                if not carried and not (row["core"] == [] and any(r["disposition"] == "no_op" for r in self.by_construct.get(target, []))):
                    self.add("RETAG", f"{where}: realized_by {target!r} is neither {BODY_ENTRY!r} nor a construct with a core row")
                if carried and not any(set(row["core"]) <= set(names) for names in carried) or any(set(row.get("forbids", [])) & set(names) for names in carried):
                    self.add("RETAG", f"{where}: no core row of {target} names {row['core']}, or one names a name it forbids {row.get('forbids', [])}")
            for n in row["core"] + row.get("forbids", []):
                if n not in self.vocab:
                    self.add("RETAG", f"{where}: {n!r} is not a Core vocabulary entry")
        for name, row in self.t["producer"].items():
            if name not in self.s_read.values():
                self.add("PHASE", f"producer {name}: is no MIR phase an S phase reads")
            # Every path and exclusion names a file or directory of rustc at HEAD, so a rename cannot leave one pointing
            # at nothing.
            for path in row["paths"] + row.get("exclude", []):
                if not isinstance(path, str) or path != path.strip("/") or (self.rustc.text(path) is None and not self.rustc.files(path + "/")):
                    self.add("PHASE", f"producer {name}: {path!r} is no file or directory at HEAD")
        for name, row in self.t["refusal"].items():
            if not re.fullmatch(r"[A-Z][A-Za-z0-9]*", name) or name not in self.used_refusals:
                self.add("TABLE", f"refusal {name}: an UpperCamel name some row uses (else stale)")
        for sid, row in self.t["spec_divergence"].items():
            if any(not str(c.get("ref")).startswith("minirust:spec/") for c in row["minirust"]) or any(
                    not str(c.get("ref")).startswith("rustc:") for c in row["rust"]) or set(row["applies_to"]) != self.spec_refs.get(sid, set()):
                self.add("DIVERGENCE", f"spec_divergence {sid}: cites MiniRust's spec/ and rustc or the library, and applies_to {sorted(row['applies_to'])} equals the rows listing it {sorted(self.spec_refs.get(sid, set()))}")
        for sid in sorted(set(self.spec_refs) - set(self.t["spec_divergence"])):
            self.add("DIVERGENCE", f"spec_divergence {sid!r} is listed by {sorted(self.spec_refs[sid])} but has no row")
        for key, row in self.t["deferred_check"].items():
            for name in row["fields"]:
                kind, _, name_field = str(name).partition(".")
                if kind not in ROWS or name_field not in ROWS[kind][0]:
                    self.add("DEFERRED", f"deferred_check {key}: {name!r} is not a <row kind>.<field> of the table")
            for exit_id in row["checked_by"]:
                if not EXIT_ID.match(str(exit_id)) or not any(f"**{exit_id}**" in c.get("quote", "") for c in row["cites"] if isinstance(c, dict)):
                    self.add("DEFERRED", f"deferred_check {key}: checked_by {exit_id!r} is an exit id quoted by one of its design citations")

    def design_commit(self) -> None:
        """The scope files and library/ (but for PIN_UNCOMPARED) at the commit the design's D0.3
        item names equal HEAD's."""
        commit = self.d03_commit
        full = (C.git(self.o.repo, "rev-parse", "--verify", "--quiet", f"{commit}^{{commit}}") or "").strip() if commit else ""
        uncompared = [f":(exclude,top,literal){rel}" for rel in PIN_UNCOMPARED]
        changed = C.git(self.o.repo, "diff", "--name-only", full, "HEAD", "--", *self.scope_files, INTRINSIC_ROOT, *uncompared) if full else None
        self.counts["design_commit"] = commit
        if changed is None or changed.strip():
            self.add("PIN", f"the design's D0.3 commit {commit} is not in the repository, or the scope files or library/ differ from HEAD there: {(changed or '').split()[:3]}")

    # ---- counts, document
    def render(self) -> str:
        c = self.counts
        rows = ["| In-scope enum or container | Constructs | core | refusal | no_op | dispatch | split by phase or case | unmapped |", "|---|---:|---:|---:|---:|---:|---:|---:|"]
        total = [0] * 7
        for group, members in sorted([(e, [f"{e}::{m.name}" for m in i.members]) for e, i in self.in_scope.items()]) + \
                [(f"{n} (fields)", [f"{n}.{m.name}" for m in i.members]) for n, i in sorted(self.containers.items())]:
            counts = [len(members), 0, 0, 0, 0, 0, 0]
            for name in members:
                kinds = {r["disposition"] for r in self.by_construct.get(name, [])}
                counts[1 + (DISPOSITIONS.index(kinds.pop()) if len(kinds) == 1 else 4 if kinds else 5)] += 1
            rows.append(f"| `{group.split(' ')[0]}`{group[len(group.split(' ')[0]):]} | {' | '.join(map(str, counts))} |")
            total = [a + b for a, b in zip(total, counts)]
        rows.append(f"| **Total** | {' | '.join(map(str, total))} |")
        by_file: dict[str, int] = {}
        for item in self.items.values():
            by_file[item["at"].rsplit(":", 1)[0]] = by_file.get(item["at"].rsplit(":", 1)[0], 0) + 1
        d = self.i_disp
        mapped = sum(1 for p in self.items if any(r["path"] == p for r in self.t["intrinsic"].values()))
        rows += ["", "| `#[rustc_intrinsic]` items | Count |", "|---|---:|"] + [f"| in `{f}` | {n} |" for f, n in sorted(by_file.items())] + [
            f"| **Total** | {len(self.items)} |", f"| mapped / unmapped | {mapped} / {len(self.items) - mapped} |",
            f"| core / refusal / no_op / fallback / split by case | {d['core']} / {d['refusal']} / {d['no_op']} / {d['fallback']} / {d['split']} |",
            f"| rows with a rustc lowering (LowerIntrinsics or MIR building) | {sum(1 for r in self.t['intrinsic'].values() if 'lowering' in r)} |",
            f"| with a body / of which marked `#[miri::intrinsic_fallback_is_spec]` | {sum(i['body'] for i in self.items.values())} / {sum(i['spec'] for i in self.items.values())} |"]
        s, si = self.seed["construct"], self.seed["intrinsic"]
        refusal_use = {n: [0, 0, 0] for n in self.t["refusal"]}
        for r in self.t["construct"].values():
            for n, slot in ([(r["refusal"], 0)] if r["disposition"] == "refusal" else []) + [(x, 1) for x in r.get("case_refusals", [])]:
                refusal_use.get(n, [0, 0, 0])[slot] += 1
        for r in self.t["intrinsic"].values():
            if r["disposition"] == "refusal":
                refusal_use.get(r["refusal"], [0, 0, 0])[2] += 1
        c.update(variants=len(self.variants), fields=len(self.fields), in_scope=len(self.in_scope), boundary=len(self.boundary), intrinsics=len(self.items),
                 construct_rows=len(self.t["construct"]), intrinsic_rows=len(self.t["intrinsic"]), totals=tuple(total), intrinsic_dispositions=dict(d),
                 seed=(s["follows"], s["diverges"], s["no arm"]), intrinsic_seed=(si["follows"], si["diverges"], si["no arm"]))
        rows += ["", "| Measured | Count |", "|---|---:|",
                 f"| design D0.3 list names (roots) / absent at the pin (with task-named enums) | {len(self.scope_row['design_enums'])} / {', '.join(self.absent) or 'none'} |",
                 f"| scope files (the module rustc_middle::mir, plus files defining task-named enums) | {len(self.scope_files)} |",
                 f"| in-scope enums / their variants; containers / their fields | {len(self.in_scope)} / {len(self.variants)}; {len(self.containers)} / {len(self.fields)} |",
                 f"| payload types outside the scope files ([[boundary]]) / of which enums | {len(self.boundary)} / {sum(1 for r in self.t['boundary'].values() if r['class'] == 'enum')} |",
                 f"| [[construct]] rows / [[intrinsic]] rows | {len(self.t['construct'])} / {len(self.t['intrinsic'])} |",
                 f"| construct rows in the same refuse/translate class as their minimize arms / in the other class / with no minimize arm | {s['follows']} / {s['diverges']} / {s['no arm']} |",
                 f"| intrinsic rows in the same refuse/translate class as their minimize arms / in the other class / with no minimize arm | {si['follows']} / {si['diverges']} / {si['no arm']} |",
                 f"| hits of the declared minimize search / stale minimize arms | {c.get('minimize_hits', 0)} / {len(self.t['stale_arm'])} |",
                 f"| doc units read / cited by a [[phase_rule]] | {c.get('doc_units', 0)} / {c.get('doc_units_ruled', 0)} |",
                 f"| phase rules / of which semantic obligations / phase conflicts | {len(self.t['phase_rule'])} / {sum(1 for x in self.semantic.values() if 'same_as' not in x)} / {len(self.t['phase_conflict'])} |",
                 f"| retag sites (reviewed) / producer rows (reviewed) / deferred checks | {len(self.t['retag_site'])} / {len(self.t['producer'])} / {len(self.t['deferred_check'])} |",
                 f"| MiniRust specification divergences / named refusals | {len(self.t['spec_divergence'])} / {len(self.t['refusal'])} |",
                 "", "| Named refusal | [[construct]] rows | vocabulary case refusals | [[intrinsic]] rows |", "|---|---:|---:|---:|"]
        rows += [f"| `{n}` | {a} | {b} | {i} |" for n, (a, b, i) in sorted(refusal_use.items())]
        return "\n".join(rows)

    def document(self, table_text: str) -> dict:
        path = self.o.doc or self.o.repo / DOC_REL
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            self.add("DOC", f"{path}: {error}")
            return {}
        C.check_block(self.f, "DOC", text, COUNTS_BLOCK, table_text)
        sections = C.document_judgments(self.f, "DOC", text, generated=(COUNTS_BLOCK,))
        self.counts["doc_citations"] = sum(C.check_prose(self.f, "DOC", jid, body if isinstance(body, str) else "\n".join(body), self.resolver)
                                           for jid, body in sections.items())
        for revision in [self.pins.alignment] + [self.pins.sources[n].revision for n in READS]:
            if f"`{revision}`" not in text:
                self.add("DOC", f"the document does not record the pin `{revision}`")
        return sections


def judgments(findings: C.Findings, table_text: str, document: dict) -> dict:
    """Every reviewed judgment, keyed `kind:key`: each row, each [scope] judgment, the table's
    comments, and the document's prose sections and outline."""
    data = tomllib.loads(table_text)
    rows = [(f"{kind}:{key(row)}", row) for kind, (_, _, key) in ROWS.items() for row in data.get(kind, []) if isinstance(row, dict)]
    scope = [(f"scope:{name}", (data.get("scope") or {}).get(name)) for name in SCOPE_JUDGMENTS]
    return C.merge_judgments(findings, rows + scope + [("comments:table", C.toml_comments(table_text))] + list(document.items()))


def collect(options: Options | None = None) -> Result:
    options = options or Options()
    checker = Checker(options)
    result = Result(violations=checker.f.violations, counts=checker.counts)
    if not checker.load():
        return result
    checker.rows()
    checker.scope()
    checker.intrinsics()
    checker.constant_evidence_region()
    checker.phases()
    checker.minimize_hits()
    checker.constructs()
    checker.intrinsic_rows()
    checker.minimize_coverage()
    checker.judgments_rest()
    if options.check_pin_state:
        checker.design_commit()
    result.table_text = checker.render()
    sections = checker.document(result.table_text)
    checker.counts["citations"] = checker.cited
    checker.counts["reviews"] = C.check_reviews(
        checker.f, options.registry or options.repo / REGISTRY_REL, DELIVERABLE, judgments(checker.f, checker.table_text, sections),
        JUDGMENT_KINDS, options.repo if options.check_history else None, REGISTRY_REL)
    return result


def main(argv: list[str] | None = None) -> int:
    if tomllib is None:
        print("mir_constructor_table: Python 3.11+ (tomllib) is required", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--minirust", type=Path)
    parser.add_argument("--repo", type=Path, default=REPO_ROOT)
    for name in ("table", "doc", "registry"):
        parser.add_argument(f"--{name}", type=Path)
    parser.add_argument("--print-counts-table", action="store_true")
    parser.add_argument("--write-counts", action="store_true", help="rewrite the document's counts block")
    args = parser.parse_args(argv)
    options = Options(repo=args.repo, table=args.table, doc=args.doc, registry=args.registry, clones={"minirust": args.minirust})
    try:
        result = collect(options)
    except (C.MissingClone, C.PinsError) as error:
        print(f"mir_constructor_table: {error}", file=sys.stderr)
        return 2
    if args.write_counts:
        doc = args.doc or args.repo / DOC_REL
        doc.write_text(C.replace_block(doc.read_text(encoding="utf-8"), COUNTS_BLOCK, result.table_text), encoding="utf-8")
    else:
        print(result.table_text)
    if result.violations:
        print(f"\nmir_constructor_table: {len(result.violations)} violation(s)", file=sys.stderr)
        for violation in result.violations:
            print(f"  {violation}", file=sys.stderr)
        return 1
    print(f"\nmir_constructor_table: OK ({result.counts['citations']} row citations, {result.counts.get('doc_citations', 0)} document citations, {result.counts['reviews']['judgments']} reviewed judgments)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
