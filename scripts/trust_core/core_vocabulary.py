#!/usr/bin/env python3
"""Core vocabulary checker: the names D0.2, D0.3 and D0.6 map into.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §3.1 D-1 ("(C) Core:
the dynamic semantics", its *Syntax* list and its `UB reason` effect) and §5.2 Stage 0.2.
Table: docs/trust-core/core-vocabulary.toml. Document: docs/trust-core/CORE_VOCABULARY.md.
Review registry: docs/trust-core/reviews/core_vocabulary.toml.

The shared layers (pins, citations, uniqueness, the counts block, reviewed judgments)
are scripts/trust_core/common.py's. This file holds the vocabulary's own rules; each
EXITS NON-ZERO when it fails. CORE_VOCABULARY.md's Predicates section states them:

  PIN, TABLE    common: the MiniRust and Reference clones at EXTERNAL_PINS.toml's pins,
                this repository's alignment, no `Trust:` edit in the region of an
                enumerated rustc enum (from the end of the item before it to its closing
                brace), no citation of a rustc file carrying a `Trust:` marker outside
                such a verified region; row keys, values, no repeated element, no
                duplicate row, no line citation in free text, no empty list or table
                outside MAY_BE_EMPTY.
  NAME          `<Inductive>.<Leaf>`, unique, the inductive declared; a variant (every UB
                reason is one) is an UpperCamel leaf of an enum inductive, a field a
                lower_snake leaf of a record inductive.
  ORIGIN        minirust rows cite a scanned MiniRust definition; trust-extension rows
                cite the design or rustc and are upstream proposals.
  RENAME        a minirust name other than its MiniRust token is whole words of a design
                citation of its row; a split inductive carries a design citation.
  EXT-NAME      a trust-extension name is a cited token or design phrase, is named by
                the class-prefix rule, or has an extension_alias row (none stale).
  REQUIRED      every trust-extension name has a consumer or an extension_justification.
  COMPLETENESS  every variant and named field of MiniRust's syntax.md, `Type` and
                `PtrType` is claimed exactly once by an entry or a not_in_core row.
  LAYOUT        not_in_core rows are exactly the scanned parts whose payload type names a
                layout type; each dropped part maps by what its type carries.
  UB-MECHANISM  every `Ub`, `throw_ub` and `ensure_else_ub` token of spec/** is a declared
                mechanism or a literal-message call; each role is one row's.
  UB-SITE       every UB site is claimed once with its exact message; a reason has one
                message and one file; TreeBorrowsUb exactly under spec/mem/tree_borrows/.
  OPERATOR      every Core operator has one typed, cited row; Float stands alone; a
                class-prefix family admits only its class.
  MIR-OPERATOR  every variant of the MIR enums has rows; no (variant, class) pair twice;
                `op` is the family's same-named leaf or the mir_implementation's entry;
                conversions; a row's classes are its operator's.
  FAMILY        mir_family inductives are declared and used (none stale); MiniRust
                families have only MiniRust leaves; class-prefix families are listed.
  COMPOSITION   holders are derived (MiniRust payload, class-prefix rule, rustc MIR
                payload); wrapped_by is the holder; maps_to is the closure.
  MIRRORED      mirrored_enum rows have exactly rustc's variants, each cited.
  ITEMS         item_kind rows classify exactly the Reference's item kinds.
  DESIGN-SYNTAX every word of the design's Syntax list is in a design_item, a phase
                restriction, or a function word; construct words derive their names;
                lowercase phrases are design_phrase rows; flavour and UB phrases fit;
                no keyword, flavour or UB phrase row or function word is unused.
  PHASE         entries a phase restriction follows are [Built, Promoted]; others all three.
  DEFERRED      deferred_check rows name real fields and cite the exits that check them.
  DOC           the counts block regenerates; every line is in a `prose:` section, the
                counts block or the outline (headings, block markers and the reviewed
                sections' opening markers, in order); every «quoted» citation resolves;
                every `Inductive.Leaf` named exists.
  REVIEW        common.check_reviews over every table row, the table's comments (each with
                the line it heads), every prose section and the outline; a committed record
                reviews nothing new.

Usage:
    scripts/trust_core/core_vocabulary.py [--minirust DIR] [--reference DIR] [--repo DIR]
        [--table FILE] [--doc FILE] [--registry FILE] [--print-counts-table]
        [--write-counts]

Exit codes: 0 every predicate holds; 1 a violation; 2 a clone is missing or unreadable pins.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import argparse
import bisect
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

tomllib = C.tomllib
REPO_ROOT = C.REPO_ROOT
DESIGN_REL = C.DESIGN_REL
TABLE_REL = "docs/trust-core/core-vocabulary.toml"
DOC_REL = "docs/trust-core/CORE_VOCABULARY.md"
REGISTRY_REL = f"{C.REVIEWS_DIR}/core_vocabulary.toml"
DELIVERABLE = "core_vocabulary"
SCHEMA = "trust.core.vocabulary.v1"
READS = {"minirust": "minirust", "rust-reference": "reference"}  # EXTERNAL_PINS source -> citation source
COUNTS_BLOCK = "core-vocabulary-counts"

PHASES = ("Built", "Promoted", "Runtime")
RESTRICTED_PHASES = ["Built", "Promoted"]
ORIGINS = ("minirust", "trust-extension")
SYNTAX_GROUPS = ("Program", "Body", "Place", "Operand", "Rvalue", "Stmt", "Terminator", "Ty")
INSTENV_GROUP, UB_GROUP = "InstEnv", "UB"
GROUPS = SYNTAX_GROUPS + (INSTENV_GROUP, UB_GROUP)
# COMPLETENESS: the MiniRust definitions whose every variant and named field is claimed.
SCAN = {"spec/lang/syntax.md": None, "spec/lang/types.md": ("Type", "IntType"), "spec/mem/pointer.md": ("PtrType",)}
SHAPES = ("enum", "record", "wrapper")
# WRAPPER (decision 19): a one-field tuple struct of libspecr's `Name`, or a type alias of `Int`.
WRAPPER_DEFINITION = re.compile(r"\bstruct\s+([A-Z]\w*)\s*\(\s*(?:pub\s+)?(?:libspecr::)?Name\s*\)\s*;|\btype\s+([A-Z]\w*)\s*=\s*(?:libspecr::)?Int\s*;")
LAYOUT_TYPES = ("Size", "Align", "Offset", "TupleHeadLayout", "Discriminator")
CONTAINER_TYPES = ("List", "Map", "Option", "Set")
UB_INDUCTIVE_BY_SITE_DIR = (("spec/mem/tree_borrows/", "TreeBorrowsUb"),)
UB_DEFAULT_INDUCTIVE = "UbReason"
MECHANISM_ROLES = ("variant", "macro", "yeet", "helper", "passthrough")
SYNTAX_BLOCK_START, SYNTAX_BLOCK_END = "*Syntax*, as first-order Clean inductives:", "*Semantic domain.*"
SYNTAX_BULLET = re.compile(r"^\* `([A-Za-z]+)`:")
DESIGN_SET_SCOPE = re.compile(r"([A-Z][A-Za-z0-9]*)\s*∈\s*\{([^}]*)\}")
DESIGN_WORD = r"[A-Za-z][A-Za-z0-9_']*"
EVIDENCE_TAG = re.compile(r"\[[A-Z]†?(?::[^\]]*)?\]")
PHASE_RESTRICTION = re.compile(r"\(phases\s+Built\s+and\s+Promoted\s+only\)")
REFERENCE_ITEMS, ITEM_KIND_PRODUCTIONS = "src/items.md", ("VisItem", "MacroItem")
RUSTC_MIR_SYNTAX = "compiler/rustc_middle/src/mir/syntax.rs"
MIR_ENUMS = (("BinOp", RUSTC_MIR_SYNTAX), ("UnOp", RUSTC_MIR_SYNTAX), ("CastKind", RUSTC_MIR_SYNTAX),
             ("PointerCoercion", "compiler/rustc_middle/src/ty/adjustment.rs"), ("Operand", RUSTC_MIR_SYNTAX),
             ("RuntimeChecks", RUSTC_MIR_SYNTAX))
MIR_EXPANDED = {"CastKind::PointerCoercion"}
OPERATOR_GROUP, OPERATOR_CATEGORY_INDUCTIVES = "Rvalue", ("BinOp", "UnOp")
CLASSES = ("Int", "Uint", "Float", "Bool", "Char", "RawPtr", "Ref", "FnPtr", "FnDef", "Closure", "VTablePtr", "Metadata", "*")
CLASS_WORDS = tuple(c for c in CLASSES if c[0].isupper())
NUMERIC_CLASSES = ("Int", "Uint", "Float", "Bool", "Char")
OVERFLOW_VALUES = ("ub", "reports-flag", "not-ub")
UB_KINDS = ("zero-divisor", "shift-amount", "inexact", "size-mismatch", "negative-distance")
# A flavour or operator UB phrase's requirements: each a non-empty list of its values, or ub_any = true.
REQUIREMENT_VALUES = {"overflow": OVERFLOW_VALUES, "classes_within": CLASSES, "ub_has": UB_KINDS, "ub_lacks": UB_KINDS}
# OQ-3: the call-shape message form MiniRust uses for ill-shaped intrinsic calls.
CALL_SHAPE_MESSAGE = re.compile(
    r"^(?:invalid (?:number of arguments|return type|(?:first |second |third )?arguments?(?: type)?) "
    r"(?:for|to) |unsized pointee requested for )"
)
EXIT_ID = re.compile(r"^E\d+(?:\.\d+)+[a-z]?$")
UPPER_CAMEL = re.compile(r"^[A-Z][A-Za-z0-9]*$")
LOWER_SNAKE = re.compile(r"^[a-z][a-z0-9_]*$")
FREE_TEXT_KEYS = ("note", "reason", "ignored", "why", "claim", "replaces")

CITE = ({"ref", "quote"}, {"ref", "quote"})
# kind -> (allowed keys, required keys, key of a row). Every row of every kind is a judgment.
ROWS = {
    "inductive": ({"name", "group", "shape", "origin", "minirust_ref", "minirust_token", "minirust_split_from", "wrapped_by",
                   "design_refs", "rustc_refs", "libspecr_refs", "upstream_proposal", "note"}, {"name", "group", "shape", "origin"}, lambda r: r.get("name")),
    "entry": ({"name", "kind", "origin", "phases", "minirust_ref", "minirust_token", "design_refs", "rustc_refs",
               "upstream_proposal", "note"}, {"name", "kind", "origin", "phases"}, lambda r: r.get("name")),
    "not_in_core": ({"minirust_ref", "minirust_token", "reason", "design_refs", "replaced_by", "payload"},
                    {"minirust_ref", "minirust_token", "reason", "design_refs", "replaced_by"},
                    lambda r: f"{r.get('minirust_ref')} {r.get('minirust_token')}"),
    "ub_mechanism": ({"ref", "text", "role"}, {"ref", "text", "role"}, lambda r: r.get("ref")),
    "ub_reason": ({"name", "origin", "sites", "design_refs", "rustc_refs", "raised_by", "upstream_proposal", "note"},
                  {"name", "origin"}, lambda r: r.get("name")),
    "design_item": ({"line", "token", "covered_by", "ignored"}, {"line", "token"}, lambda r: f"{r.get('line')} {r.get('token')}"),
    "operator": ({"name", "classes", "classes_from", "overflow", "ub", "flavour_from", "note"},
                 {"name", "classes", "classes_from", "overflow", "ub", "flavour_from"}, lambda r: r.get("name")),
    "mir_operator": ({"mir", "operand", "op", "maps_to", "convert", "refusal", "note"}, {"mir", "maps_to"},
                     lambda r: f"{r.get('mir')} {','.join(map(str, r.get('operand') or ['-']))}"),
    "design_phrase": ({"line", "phrase", "names", "cites", "why"}, {"line", "phrase", "names", "cites", "why"},
                      lambda r: f"{r.get('line')} {r.get('phrase')}"),
    "design_keyword": ({"word", "leaf", "cite"}, {"word", "leaf", "cite"}, lambda r: r.get("word")),
    "design_flavour": ({"phrase", "requires"}, {"phrase", "requires"}, lambda r: r.get("phrase")),
    "design_ub_phrase": ({"phrase", "follows", "requires"}, {"phrase", "follows", "requires"}, lambda r: r.get("phrase")),
    "item_kind": ({"kind", "word", "names", "why"}, {"kind", "word", "names", "why"}, lambda r: r.get("kind")),
    "mir_family": ({"enum", "operands", "inductives"}, {"enum", "operands", "inductives"}, lambda r: f"{r.get('enum')} {r.get('operands')}"),
    "mir_implementation": ({"mir", "operand", "op", "requires", "refusal", "cites", "why"}, {"mir", "cites", "why"},
                           lambda r: f"{r.get('mir')} {r.get('operand', '-')}"),
    "mirrored_enum": ({"inductive", "enum", "file"}, {"inductive", "enum", "file"}, lambda r: r.get("inductive")),
    "conversion": ({"source", "target", "arm", "why"}, {"source", "target", "arm", "why"}, lambda r: f"{r.get('source')}->{r.get('target')}"),
    "extension_alias": ({"name", "cites", "why"}, {"name", "cites", "why"}, lambda r: r.get("name")),
    "extension_justification": ({"name", "cites", "why"}, {"name", "cites", "why"}, lambda r: r.get("name")),
    "payload_home": ({"name", "homes", "cites", "why"}, {"name", "homes", "cites", "why"}, lambda r: r.get("name")),
    "layout_home": ({"definition", "home", "cites", "why"}, {"definition", "home", "cites", "why"}, lambda r: r.get("definition")),
    "not_layout": ({"minirust_ref", "minirust_token", "cites", "why"}, {"minirust_ref", "minirust_token", "cites", "why"},
                   lambda r: f"{r.get('minirust_ref')} {r.get('minirust_token')}"),
    "deferred_check": ({"id", "claim", "fields", "replaces", "checked_by", "cites"}, {"id", "claim", "fields", "replaces", "checked_by", "cites"},
                       lambda r: r.get("id")),
}
DESIGN_SYNTAX_KEYS = {"function_words", "prose_words"}
# TABLE: the type of every field (a list's elements after the colon); kind-specific overrides.
STRS = ("name group shape origin minirust_ref minirust_token minirust_split_from wrapped_by note kind reason ref text role "
        "token ignored overflow mir op refusal phrase why word leaf follows enum operands file source target definition "
        "home id claim replaces inductive").split()
STR_LISTS = "phases replaced_by raised_by covered_by classes ub operand maps_to names inductives requires homes fields checked_by".split()
DICT_LISTS = "design_refs rustc_refs libspecr_refs sites classes_from flavour_from cites".split()
TYPES = {**{k: (str, None) for k in STRS}, **{k: (list, str) for k in STR_LISTS}, **{k: (list, dict) for k in DICT_LISTS},
         "line": (int, None), "upstream_proposal": (bool, None), "payload": (dict, None), "convert": (dict, None),
         "cite": (dict, None), "arm": (dict, None)}
TYPE_OVERRIDES = {"design_flavour": {"requires": (dict, None)}, "design_ub_phrase": {"requires": (dict, None)},
                  "mir_implementation": {"operand": (str, None)}}
# TABLE: a list or table value is non-empty (an optional one is omitted instead), except where
# the kind's rule gives the empty value its meaning: an erased or open item kind, a refusal's
# maps_to, an operator without UB or flavour, a type none of whose parts has a home
# (LAYOUT), and a UB phrase after a mirrored construct (DESIGN-SYNTAX).
MAY_BE_EMPTY = {("item_kind", "names"), ("mir_operator", "maps_to"), ("operator", "ub"), ("operator", "flavour_from"),
                ("payload_home", "homes"), ("design_ub_phrase", "requires")}
TOP_KEYS = {"schema", "design", "design_syntax", "adopted"} | set(ROWS)
# Every table row, the [design_syntax] lists, the table's comments, the document's prose
# sections and its outline.
JUDGMENT_KINDS = set(ROWS) | {"design_syntax", "adopted", "comments", "prose", "outline"}


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


# --------------------------------------------------------------------------
# words and a small reader of specr and Rust enum/struct syntax
# --------------------------------------------------------------------------


def words_of(identifier: str) -> list[str]:
    out = []
    for part in re.split(r"[^A-Za-z0-9]+", identifier):
        out.extend(w.lower() for w in re.findall(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z0-9]+|[A-Z]+", part))
    return out


def phrase_has_words(phrase: str, words: list[str]) -> bool:
    tokens = [t.lower() for t in re.findall(r"[A-Za-z0-9]+", phrase)]
    n = len(words)
    return n > 0 and (any(tokens[i:i + n] == words for i in range(len(tokens) - n + 1)) or "".join(words) in tokens)


def normalize(text: str) -> str:
    return re.sub(r"[^a-z0-9]", "", text.lower())


def code_blocks(text: str) -> list[tuple[int, list[str]]]:
    """(first line number of the body, body lines) for each ``` fence."""
    blocks, lines, i = [], text.split("\n"), 0
    while i < len(lines):
        if lines[i].lstrip().startswith("```"):
            j = i + 1
            while j < len(lines) and not lines[j].lstrip().startswith("```"):
                j += 1
            blocks.append((i + 2, lines[i + 1:j]))
            i = j + 1
        else:
            i += 1
    return blocks


class Source:
    """Text plus a mask in which strings, char literals, comments and attributes are blank."""

    OPENERS = {"(": ")", "[": "]", "{": "}"}

    def __init__(self, text: str, first_line: int = 1) -> None:
        self.text, self.first_line = text, first_line
        mask, i, n = list(text), 0, len(text)

        def blank(a: int, b: int) -> None:
            for k in range(a, min(b, n)):
                if mask[k] != "\n":
                    mask[k] = " "

        while i < n:
            if text[i] == '"':
                j = i + 1
                while j < n and text[j] != '"':
                    j += 2 if text[j] == "\\" else 1
                blank(i + 1, j)
                i = j + 1
            elif text.startswith("//", i):
                j = text.find("\n", i)
                j = n if j < 0 else j
                blank(i, j)
                i = j
            elif text.startswith("/*", i):
                j = text.find("*/", i + 2)
                j = n if j < 0 else j + 2
                blank(i, j)
                i = j
            elif text[i] == "'" and re.match(r"'(?:\\.|[^\\'\n])'", text[i:i + 4]):
                m = re.match(r"'(?:\\.|[^\\'\n])'", text[i:i + 4])
                blank(i + 1, i + m.end() - 1)
                i += m.end()
            else:
                i += 1
        self.mask = re.sub(r"#\s*\[[^\]]*\]", lambda x: " " * len(x.group(0)), "".join(mask))
        self._starts = [0] + [k + 1 for k, c in enumerate(text) if c == "\n"]

    def line_of(self, pos: int) -> int:
        return self.first_line + bisect.bisect_right(self._starts, pos) - 1

    def close(self, open_pos: int) -> int | None:
        stack = []
        for k in range(open_pos, len(self.mask)):
            ch = self.mask[k]
            if ch in self.OPENERS:
                stack.append(self.OPENERS[ch])
            elif ch in ")]}":
                if not stack or stack[-1] != ch:
                    return None
                stack.pop()
                if not stack:
                    return k
        return None

    def split_top(self, a: int, b: int, sep: str = ",", angle: bool = False) -> list[tuple[int, int]]:
        out, depth, start = [], 0, a
        for k in range(a, b):
            ch = self.mask[k]
            if ch in self.OPENERS or (angle and ch == "<"):
                depth += 1
            elif ch in ")]}" or (angle and ch == ">" and self.mask[k - 1] not in "-="):
                depth -= 1
            elif ch == sep and depth == 0:
                out.append((start, k))
                start = k + 1
        out.append((start, b))
        return out

    def enum_variants(self, name: str) -> tuple[dict[str, int], tuple[int, int] | None]:
        """Variant name -> line for `enum <name>` (any visibility), and the enum's region as
        (first line, last line), or None when the enum is not found. The region runs from the
        line on which the item before the enum ends (its `}` or `;`, or the first line) to the
        enum's closing brace, so it holds the enum's visibility, attributes, doc comments and
        every comment written above it."""
        m = re.search(r"\benum\s+" + re.escape(name) + r"\b[^{;]*\{", self.mask)
        close = self.close(m.end() - 1) if m else None
        if close is None:
            return {}, None
        variants = {}
        for a, b in self.split_top(m.end(), close):
            ident = re.match(r"\s*([A-Za-z_]\w*)", self.mask[a:b])
            if ident:
                variants[ident.group(1)] = self.line_of(a + ident.start(1))
        return variants, (self.enclosing_first_line(m.start()), self.line_of(close))

    def enclosing_first_line(self, pos: int) -> int:
        """`item_first_line`, widened over every brace level that encloses `pos`: an enum
        declared inside a macro invocation (`crate::target_spec_enum! { .. }`) or a `mod`
        block starts, for the marker guard, where the statement opening that level starts, so
        a `Trust:` edit written above the macro or the module is inside the region."""
        first = self.item_first_line(pos)
        mask, k, depth = self.mask, pos - 1, 0
        while k >= 0:
            ch = mask[k]
            if ch == "}":
                depth += 1
            elif ch == "{":
                if depth == 0:
                    j = k - 1
                    while j >= 0 and mask[j] not in ";{}":
                        j -= 1
                    first = min(first, self.line_of(j) if j >= 0 else self.first_line)
                else:
                    depth -= 1
            k -= 1
        return first

    def item_first_line(self, pos: int) -> int:
        """The line on which the item before the keyword at `pos` ends: the scan goes back over
        whitespace, masked comments and attributes, `pub` and `pub(..)`, and stops at any other
        character (the preceding item's `}` or `;`)."""
        mask, k = self.mask, pos - 1
        while k >= 0:
            if mask[k].isspace():
                k -= 1
                continue
            end = k
            if mask[k] == ")":
                depth = 0
                while k >= 0:
                    depth += {")": 1, "(": -1}.get(mask[k], 0)
                    if depth == 0:
                        break
                    k -= 1
                k -= 1
                while k >= 0 and mask[k].isspace():
                    k -= 1
            if k >= 2 and mask[k - 2:k + 1] == "pub" and (k < 3 or not (mask[k - 3].isalnum() or mask[k - 3] == "_")):
                k -= 3
                continue
            k = end
            break
        return self.line_of(k) if k >= 0 else self.first_line


def scan_definitions(text: str, rel: str, wanted) -> tuple[dict, list[str]]:
    """(line, token) -> (parent, "variant" | "field", payload) for every variant and named field."""
    found, problems, seen = {}, [], set()
    for first_line, body in code_blocks(text):
        src = Source("\n".join(body), first_line)
        for match in re.finditer(r"\b(enum|struct)\s+([A-Za-z_]\w*)\s*(?:<[^>{;(]*>)?[^{;(]*\{", src.mask):
            kind_word, name = match.group(1), match.group(2)
            if wanted is not None and name not in wanted:
                continue
            seen.add(name)
            close = src.close(match.end() - 1)
            if close is None:
                problems.append(f"{rel}: unterminated definition of {name}")
                continue
            for a, b in src.split_top(match.end(), close, angle=True):
                segment = src.mask[a:b]
                if not segment.strip():
                    continue
                pattern = r"\s*([A-Za-z_]\w*)" if kind_word == "enum" else r"\s*(?:pub(?:\s*\([^)]*\))?\s+)?([A-Za-z_]\w*)\s*:"
                ident = re.match(pattern, segment)
                kind = "variant" if kind_word == "enum" else "field"
                if not ident:
                    problems.append(f"{rel}: unparsable {kind} in {name}: {segment.strip()[:40]!r}")
                    continue
                key = (src.line_of(a + ident.start(1)), ident.group(1))
                if key in found:
                    problems.append(f"{rel}:{key[0]}: {key[1]} defined twice")
                found[key] = (name, kind, segment[ident.end(1):])
    problems += [f"{rel}: definition `{name}` not found" for name in wanted or () if name not in seen]
    return found, problems


def extract_ub_sites(tree, mechanisms: list) -> tuple[dict[str, str], list[str]]:
    """"path:line of the message literal" -> message for every UB site in spec/** code blocks."""
    sites, problems = {}, []
    declared = {m["ref"]: m.get("role") for m in mechanisms if isinstance(m, dict) and "ref" in m}
    files = tree.files("spec/", (".md",))
    tree.prefetch(files)
    for rel in files:
        for first_line, body in code_blocks(tree.text(rel) or ""):
            src = Source("\n".join(body), first_line)

            def at(pos: int) -> str:
                return f"{rel}:{src.line_of(pos)}"

            def add(literal_pos: int, message: str) -> None:
                if at(literal_pos) in sites:
                    problems.append(f"{at(literal_pos)}: two UB messages on one line")
                sites[at(literal_pos)] = message

            for m in re.finditer(r"\bUb\b", src.mask):
                if declared.get(at(m.start())) not in ("variant", "yeet"):
                    problems.append(f"{at(m.start())}: the `Ub` termination is named outside the declared variant and throw_ub! body")
            for m in re.finditer(r"\bthrow_ub\b", src.mask):
                bang = re.match(r"\s*!\s*(\S)", src.mask[m.end():])
                role = declared.get(at(m.start()))
                if bang is None or role == "macro":
                    if role != "macro":
                        problems.append(f"{at(m.start())}: `throw_ub` named other than as the declared macro or an invocation")
                    continue
                open_pos = m.end() + bang.end() - 1
                close = src.close(open_pos) if bang.group(1) == "(" else None
                lit = re.match(r'\s*"((?:[^"\\]|\\.)*)"', src.text[open_pos + 1:close]) if close else None
                if lit is None:
                    problems.append(f"{at(m.start())}: throw_ub! is not a parenthesized literal message")
                elif lit.group(1) == "{}":
                    if role != "passthrough":
                        problems.append(f"{at(m.start())}: throw_ub!(\"{{}}\", ..) outside the declared ensure_else_ub helper")
                else:
                    add(open_pos + 1 + lit.start(1), lit.group(1))
            for m in re.finditer(r"\bensure_else_ub\b", src.mask):
                if declared.get(at(m.start())) == "helper":
                    continue
                call = re.match(r"\s*\(", src.mask[m.end():])
                close = src.close(m.end() + call.end() - 1) if call else None
                if close is None:
                    problems.append(f"{at(m.start())}: `ensure_else_ub` used other than as a direct call")
                    continue
                args = [x for x in src.split_top(m.end() + call.end(), close) if src.text[x[0]:x[1]].strip()]
                lit = re.fullmatch(r'\s*"((?:[^"\\]|\\.)*)"\s*', src.text[args[-1][0]:args[-1][1]]) if args else None
                if lit is None:
                    problems.append(f"{at(m.start())}: ensure_else_ub without a trailing literal message")
                else:
                    add(args[-1][0] + lit.start(1), lit.group(1))
    return sites, problems


def split_types(text: str) -> list[str]:
    parts, depth, current = [], 0, ""
    for ch in text:
        depth += ch in "([{<"
        depth -= ch in ")]}>"
        if ch == "," and depth == 0:
            parts.append(current)
            current = ""
        else:
            current += ch
    return [" ".join(p.split()) for p in parts + [current] if p.strip()]


def payload_parts(payload: str):
    """("fields", [(name, type)]) for `{ name: T, .. }`, else ("type", T)."""
    text = payload.strip()
    if text.startswith("{"):
        inner = text[1:text.rfind("}")] if "}" in text else text[1:]
        fields = []
        for part in split_types(inner):
            m = re.match(r"(?:pub\s+)?([a-z_]\w*)\s*:\s*(.+)$", part, re.S)
            fields.append((m.group(1), " ".join(m.group(2).split())) if m else ("?", part))
        return "fields", fields
    if text.startswith(":"):
        return "type", " ".join(text[1:].split())
    if text.startswith("("):
        return "type", " ".join(text[1:-1].split())
    return "type", ""


def expand_aliases(text: str, aliases: dict[str, str]) -> str:
    for _ in range(len(aliases) + 1):
        expanded = re.sub(r"\b([A-Z]\w*)\b", lambda m: "(" + aliases[m.group(1)] + ")" if m.group(1) in aliases else m.group(0), text)
        if expanded == text:
            break
        text = expanded
    return text


def meets_requirements(requirements: dict, operator: dict) -> bool:
    kinds = operator.get("ub") if isinstance(operator.get("ub"), list) else []
    classes = operator.get("classes") if isinstance(operator.get("classes"), list) else []
    return not (
        ("overflow" in requirements and operator.get("overflow") not in requirements["overflow"])
        or ("classes_within" in requirements and not set(classes) <= set(requirements["classes_within"]))
        or any(k not in kinds for k in requirements.get("ub_has", ()))
        or any(k in kinds for k in requirements.get("ub_lacks", ()))
        or (requirements.get("ub_any") and not (operator.get("overflow") == "ub" or kinds))
    )


def legacy_ref(ref: object) -> str | None:
    """A row citation's `path:line` as a common reference, its source read from the path."""
    m = re.fullmatch(r"(.+):([1-9][0-9]*)", ref) if isinstance(ref, str) else None
    if m is None:
        return None
    path, line = m.groups()
    if path == DESIGN_REL:
        return f"design:{line}"
    if path.startswith(C.UPSTREAM_PREFIXES):
        return f"rustc:{path}:{line}"
    if path.startswith(("spec/", "tooling/")):
        return f"minirust:{path}:{line}"
    return None


# --------------------------------------------------------------------------
# the checker
# --------------------------------------------------------------------------


class Checker:
    def __init__(self, options: Options) -> None:
        self.o = options
        self.f = C.Findings()
        self.counts: dict = {}
        self.rustc: dict[str, Source | None] = {}
        self.enums: dict[tuple[str, str], dict[str, int]] = {}
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
        trees.update(o.trees)
        self.trees = trees
        self.resolver = C.Resolver(o.repo, trees)
        if o.check_pin_state:
            for name, path in clones.items():
                C.verify_clone(self.f, path, self.pins.sources[name], self.pins)
            C.verify_objects(self.f, f"repository {o.repo}", o.repo)
            C.verify_alignment(self.f, trees["worktree"], self.pins)
        try:
            self.table_text = (o.table or o.repo / TABLE_REL).read_text(encoding="utf-8")
            self.data = tomllib.loads(self.table_text)
        except (OSError, tomllib.TOMLDecodeError) as error:
            self.add("TABLE", f"{o.table or TABLE_REL}: {error}")
            return False
        self.enumerated_enums()
        return True

    def cite(self, kind: str, where: str, ref: str | None, quote: object, word: bool = False, raw: object = None) -> bool:
        self.cited += 1
        if ref:
            return self.resolver.resolve(self.f, kind, where, ref, quote, word)
        self.add(kind, f"{where}: {raw!r} is not a citation of the design, rustc or MiniRust")
        return False

    def rustc_source(self, rel: str) -> Source | None:
        if rel not in self.rustc:
            text = self.trees["worktree"].text(rel)
            self.rustc[rel] = None if text is None else Source(text)
            if text is None:
                self.add("MIR-OPERATOR", f"{rel} does not exist at HEAD")
        return self.rustc[rel]

    def rustc_enum(self, enum: str, rel: str) -> dict[str, int]:
        """The variants of a rustc enum read at HEAD. Its region is registered with the resolver
        (common.Resolver.upstream_region), which refuses a `Trust:` edit in it and exempts a
        citation inside it from the whole-file guard."""
        if (enum, rel) not in self.enums:
            src = self.rustc_source(rel)
            variants, span = src.enum_variants(enum) if src else ({}, None)
            if span is not None:
                self.resolver.upstream_region(self.f, rel, span[0], span[1], f"enum {enum}")
            self.enums[(enum, rel)] = variants
        return self.enums[(enum, rel)]

    def enumerated_enums(self) -> None:
        """Parse every rustc enum the checker enumerates (the MIR enums and the mirrored_enum
        rows) before any citation is resolved, so a citation into an enum's file is checked
        against the enum's verified region."""
        rows = self.data.get("mirrored_enum")
        mirrored = [(r["enum"], r["file"]) for r in rows if isinstance(r, dict) and isinstance(r.get("enum"), str)
                    and isinstance(r.get("file"), str)] if isinstance(rows, list) else []
        for enum, rel in list(MIR_ENUMS) + mirrored:
            self.rustc_enum(enum, rel)

    # ---- TABLE
    def rows(self) -> None:
        d = self.data
        for key in sorted(set(d) - TOP_KEYS):
            self.add("TABLE", f"top-level key {key!r} is not part of the schema")
        if d.get("schema") != SCHEMA:
            self.add("TABLE", f"schema is not {SCHEMA}")
        if d.get("design") != DESIGN_REL:
            self.add("TABLE", f"design is not {DESIGN_REL}")
        self.t: dict[str, dict] = {}
        for kind, (allowed, required, key) in ROWS.items():
            valid = []
            for index, row in enumerate(d.get(kind, [])):
                where = f"{kind}[{index}] {key(row) if isinstance(row, dict) else ''}"
                if not isinstance(row, dict):
                    self.add("TABLE", f"{where}: not a table")
                    continue
                if set(row) - allowed or required - set(row):
                    self.add("TABLE", f"{where}: unknown keys {sorted(set(row) - allowed)}, missing keys {sorted(required - set(row))}")
                    continue
                types = {k: TYPE_OVERRIDES.get(kind, {}).get(k, TYPES[k]) for k in row}
                wrong = sorted(k for k, (outer, inner) in types.items() if not isinstance(row[k], outer) or isinstance(row[k], bool) != (outer is bool)
                               or (inner is not None and not all(isinstance(x, inner) for x in row[k])))
                if wrong:
                    self.add("TABLE", f"{where}: fields {wrong} have the wrong type")
                    continue
                C.repeated_elements(self.f, "TABLE", where, row)
                for name in sorted(k for k, v in row.items() if isinstance(v, (list, dict)) and not v and (kind, k) not in MAY_BE_EMPTY):
                    self.add("TABLE", f"{where}: {name} is empty; a list names something, and an optional one is omitted")
                for text_key in FREE_TEXT_KEYS:
                    value = row.get(text_key)
                    if text_key in row and (not isinstance(value, str) or not value.strip()):
                        self.add("TABLE", f"{where}: {text_key} must be non-empty text")
                    elif isinstance(value, str) and C.FREE_TEXT_CITATION.search(value):
                        self.add("TABLE", f"{where}: {text_key} carries an unchecked line citation: {value!r}")
                valid.append(row)
            self.t[kind] = C.unique_rows(self.f, "TABLE", kind, valid, key)
        words = d.get("design_syntax")
        if not isinstance(words, dict) or set(words) != DESIGN_SYNTAX_KEYS or not all(
                isinstance(v, list) and v == sorted(set(v)) and all(isinstance(w, str) and w == w.lower() for w in v) for v in words.values()):
            self.add("TABLE", "[design_syntax] holds exactly function_words and prose_words, each a sorted list of distinct lowercase words")
            words = {k: [] for k in DESIGN_SYNTAX_KEYS}
        self.function_words, self.prose_words = frozenset(words["function_words"]), frozenset(words["prose_words"])
        adopted = d.get("adopted")
        if not isinstance(adopted, dict) or set(adopted) != {"prefix", "design_refs", "note"} or not all(
                isinstance(adopted[k], str) and adopted[k].strip() for k in ("prefix", "note")) or not self.refs("[adopted]", adopted)[0]:
            self.add("TABLE", "[adopted] holds exactly a prefix, a note and design_refs that hold their phrases (decision 18)")
        for kind in ("design_phrase", "mir_implementation", "extension_alias", "extension_justification", "payload_home", "layout_home", "not_layout", "deferred_check"):
            for k, row in self.t[kind].items():
                for c in row["cites"] if isinstance(row["cites"], list) else [None]:
                    if not isinstance(c, dict) or set(c) != {"ref", "quote"}:
                        self.add("TABLE", f"{kind} {k}: a citation is {{ref, quote}}, not {c!r}")
                    else:
                        self.cite(kind.upper().replace("_", "-"), f"{kind} {k}", c["ref"], c["quote"])
                if not row["cites"]:
                    self.add("TABLE", f"{kind} {k}: cites its sources")
        for kind, attr in (("conversion", "arm"), ("design_keyword", "cite")):
            for k, row in self.t[kind].items():
                c = row[attr]
                if not isinstance(c, dict) or set(c) != {"ref", "quote"}:
                    self.add("TABLE", f"{kind} {k}: {attr} is {{ref, quote}}")
                else:
                    self.cite("TABLE", f"{kind} {k}", c["ref"], c["quote"])

    def refs(self, where: str, row: dict) -> tuple[list[str], list[str]]:
        """The phrases of a row's verified design citations, and the tokens of its rustc citations."""
        design, rustc = [], []
        for c in row.get("design_refs") or []:
            ref = legacy_ref(c.get("ref")) if isinstance(c, dict) else None
            if not isinstance(c, dict) or set(c) != {"ref", "phrase"} or not (ref or "").startswith("design:"):
                self.add("DESIGN-REF", f"{where}: a design_ref is {{ref = \"{DESIGN_REL}:<line>\", phrase}}, not {c!r}")
            elif self.cite("DESIGN-REF", where, ref, c["phrase"]):
                design.append(c["phrase"])
        for c in row.get("rustc_refs") or []:
            ref = legacy_ref(c.get("ref")) if isinstance(c, dict) else None
            if not isinstance(c, dict) or set(c) != {"ref", "token"} or not (ref or "").startswith("rustc:"):
                self.add("RUSTC-REF", f"{where}: a rustc_ref is {{ref = \"compiler/<path>:<line>\", token}}, not {c!r}")
            elif self.cite("RUSTC-REF", where, ref, c["token"], word=True):
                rustc.append(c["token"])
        return design, rustc

    # ---- NAME, ORIGIN, RENAME, COMPLETENESS
    def names(self) -> None:
        t, self.scanned, self.claims, self.wrapper_claims, wrappers = self.t, {}, {}, {}, set()
        mr = self.trees["minirust"]
        mr.prefetch(list(SCAN))
        for rel, wanted in SCAN.items():
            text = mr.text(rel)
            if text is None:
                self.add("COMPLETENESS", f"{rel} does not exist at the MiniRust pin")
                text = ""
            self.scanned[rel], problems = scan_definitions(text, rel, wanted)
            for first_line, body in code_blocks(text):
                src = Source("\n".join(body), first_line)
                wrappers.update((rel, src.line_of(m.start()), m.group(1) or m.group(2)) for m in WRAPPER_DEFINITION.finditer(src.mask))
            for problem in problems:
                self.add("COMPLETENESS", problem)
        self.inductives, self.entries, self.ub = t["inductive"], t["entry"], t["ub_reason"]
        self.extension_names = []
        minirust_tokens = {r.get("minirust_token") for r in self.inductives.values() if r.get("origin") == "minirust"}
        for name, row in self.inductives.items():
            where = f"inductive {name}"
            if not isinstance(name, str) or not UPPER_CAMEL.match(name):
                self.add("NAME", f"{where}: an inductive name is UpperCamel")
            if row["group"] not in GROUPS or row["shape"] not in SHAPES:
                self.add("TABLE", f"{where}: group must be one of {GROUPS} and shape one of {SHAPES}")
            if (row["shape"] == "wrapper" or "libspecr_refs" in row) and (row["origin"] != "minirust" or row["group"] not in SYNTAX_GROUPS):
                self.add("NAME", f"{where}: a wrapper or libspecr-defined inductive is a minirust syntax inductive")
            if "libspecr_refs" in row and row["shape"] != "enum":
                self.add("NAME", f"{where}: a libspecr-defined inductive is an enum")
            for c in row.get("libspecr_refs") or []:
                self.cite("MINIRUST-REF", f"{where} libspecr_refs", C.parse_ref(c.get("ref")) and c.get("ref"), c.get("quote"), raw=c)
            if row["group"] == UB_GROUP and row["shape"] != "enum":
                self.add("NAME", f"{where}: a UB inductive's reasons are UpperCamel variants, so it is an enum, not a {row['shape']}")
            design, rustc = self.refs(where, row)
            self.origin(where, row, design, rustc)
            if row.get("origin") == "minirust":
                self.minirust_ref(where, row, "inductive", None)
                self.rename(where, name, row.get("minirust_token"), design)
            elif row.get("origin") == "trust-extension":
                self.extension_names.append((where, name, name, design, rustc))
            split = row.get("minirust_split_from")
            if split is not None and (not design or split not in minirust_tokens):
                self.add("RENAME", f"{where}: split from MiniRust `{split}` needs a design citation and a minirust inductive whose token is `{split}`")
        for name, row in list(self.entries.items()) + [(n, dict(r, kind="variant")) for n, r in self.ub.items()]:
            is_ub = name in self.ub
            where = f"{'ub_reason' if is_ub else 'entry'} {name}"
            parts = name.split(".") if isinstance(name, str) else []
            inductive = self.inductives.get(parts[0]) if len(parts) == 2 else None
            if inductive is None:
                self.add("NAME", f"{where}: a name is <Inductive>.<Leaf> of a declared inductive")
                continue
            if name in self.entries and name in self.ub:
                self.add("NAME", f"{where}: the name is both an entry and a UB reason")
            if (inductive["group"] == UB_GROUP) != is_ub:
                self.add("NAME", f"{where}: UB reasons, and only they, are leaves of a UB inductive")
            if row["kind"] == "variant" and (inductive["shape"] != "enum" or not UPPER_CAMEL.match(parts[1])):
                self.add("NAME", f"{where}: a variant is an UpperCamel leaf of an enum inductive")
            elif row["kind"] == "field" and (inductive["shape"] != "record" or not LOWER_SNAKE.match(parts[1])):
                self.add("NAME", f"{where}: a field is a lower_snake leaf of a record inductive")
            elif row["kind"] not in ("variant", "field"):
                self.add("TABLE", f"{where}: kind must be variant or field")
            if is_ub:
                continue
            if not isinstance(row["phases"], list) or not row["phases"] or row["phases"] != [p for p in PHASES if p in row["phases"]]:
                self.add("PHASE", f"{where}: phases {row['phases']!r} is not an ordered non-empty subset of {PHASES}")
            design, rustc = self.refs(where, row)
            self.origin(where, row, design, rustc)
            if row["origin"] == "minirust":
                parents = {inductive.get("minirust_token"), inductive.get("minirust_split_from")} - {None}
                key = self.minirust_ref(where, row, row["kind"], parents, inductive.get("minirust_token") if "libspecr_refs" in inductive else None)
                if key is not None:
                    self.claims.setdefault(key, []).append(name)
                self.rename(where, parts[1], row.get("minirust_token"), design)
            elif row["origin"] == "trust-extension":
                self.extension_names.append((where, name, parts[1], design, rustc))
        for rel, number, token in sorted(wrappers | set(self.wrapper_claims)):
            owners = self.wrapper_claims.get((rel, number, token), [])
            if len(owners) != 1 or (rel, number, token) not in wrappers:
                self.add("COMPLETENESS", f"MiniRust wrapper `{token}` ({rel}:{number}) is claimed by {owners}, not by exactly one wrapper inductive, or is no wrapper definition")
        self.counts["wrappers"] = len(wrappers)
        for name, row in self.inductives.items():
            if row["group"] != UB_GROUP and row["shape"] != "wrapper" and not any(e.split(".")[0] == name for e in self.entries):
                self.add("TABLE", f"inductive {name} has no entries")
            if row["group"] == UB_GROUP and not any(e.split(".")[0] == name for e in self.ub):
                self.add("TABLE", f"UB inductive {name} has no reasons")

    def origin(self, where: str, row: dict, design: list, rustc: list) -> None:
        origin, proposal = row.get("origin"), row.get("upstream_proposal")
        if origin not in ORIGINS:
            self.add("ORIGIN", f"{where}: origin {origin!r} is not one of {ORIGINS}")
        elif origin == "minirust" and proposal not in (None, False):
            self.add("ORIGIN", f"{where}: a minirust row cannot be an upstream proposal")
        elif origin == "trust-extension":
            if "minirust_ref" in row or "minirust_token" in row or row.get("sites"):
                self.add("ORIGIN", f"{where}: a trust-extension row cites MiniRust")
            if proposal is not True:
                self.add("ORIGIN", f"{where}: a trust-extension row sets upstream_proposal = true")
            if not design and not rustc:
                self.add("ORIGIN", f"{where}: a trust-extension row that nothing cites")

    def minirust_ref(self, where: str, row: dict, kind: str, parents, libspecr_enum: str | None = None) -> tuple | None:
        m = re.fullmatch(r"(.+):([1-9][0-9]*)", str(row.get("minirust_ref")))
        token = row.get("minirust_token")
        if m is None or not isinstance(token, str):
            self.add("MINIRUST-REF", f"{where}: malformed minirust_ref/minirust_token")
            return None
        rel, number = m.group(1), int(m.group(2))
        if not self.cite("MINIRUST-REF", where, f"minirust:{rel}:{number}", token, word=True):
            return None
        line = self.trees["minirust"].lines(rel)[number - 1]
        if libspecr_enum is not None:
            # A variant of an enum libspecr defines: MiniRust writes it as a path on the cited line.
            if kind != "variant" or f"{libspecr_enum}::{token}" not in line:
                self.add("MINIRUST-REF", f"{where}: a variant of the libspecr enum {libspecr_enum} cites a line writing `{libspecr_enum}::{token}`")
            return None
        if kind in ("variant", "field"):
            definition = self.scanned.get(rel, {}).get((number, token))
            if definition is None:
                self.add("ORIGIN", f"{where}: a minirust {kind} cites a scanned MiniRust {kind}; {rel}:{number} {token!r} is not one")
                return None
            if definition[1] != kind:
                self.add("MINIRUST-REF", f"{where}: {rel}:{number} {token!r} is a {definition[1]}, the entry a {kind}")
            if parents and definition[0] not in parents:
                self.add("MINIRUST-REF", f"{where}: {token!r} belongs to MiniRust `{definition[0]}`, not to {sorted(parents)}")
            return (rel, number, token)
        if "libspecr_refs" in row:
            if not re.search(r"\b[a-z_]\w*\s*:\s*" + re.escape(token) + r"\s*,", line):
                self.add("MINIRUST-REF", f"{where}: {rel}:{number} does not name `{token}` as a field's type")
        elif row.get("shape") == "wrapper":
            match = WRAPPER_DEFINITION.search(line)
            if match is None or token not in match.groups():
                self.add("MINIRUST-REF", f"{where}: {rel}:{number} does not define `{token}` as a one-field tuple struct of Name or an alias of Int")
            self.wrapper_claims.setdefault((rel, number, token), []).append(row.get("name"))
        elif not re.search(r"\b(?:pub\s+)?(enum|struct)\s+" + re.escape(token) + r"\b", line):
            self.add("MINIRUST-REF", f"{where}: {rel}:{number} does not define the enum or struct `{token}`")
        return None

    def rename(self, where: str, name: str, token: object, design: list) -> None:
        if isinstance(token, str) and name != token and not any(phrase_has_words(p, words_of(name)) for p in design):
            self.add("RENAME", f"{where}: renames MiniRust `{token}` to `{name}` without a design phrase naming `{name}` as whole words")

    # ---- LAYOUT and the not_in_core homes
    def layout(self) -> None:
        aliases = {}
        for rel in SCAN:
            for first_line, body in code_blocks(self.trees["minirust"].text(rel) or ""):
                for m in re.finditer(r"\btype\s+([A-Z]\w*)\s*=\s*([^;]*);", Source("\n".join(body), first_line).mask):
                    aliases[m.group(1)] = " ".join(m.group(2).split())
        self.homes_required: set[str] = set()
        known = set(self.entries) | set(self.inductives)
        in_instenv = lambda n: self.inductives.get(str(n).split(".")[0], {}).get("group") == INSTENV_GROUP  # noqa: E731
        payload_homes, layout_homes = self.t["payload_home"], self.t["layout_home"]
        used_payload, used_layout = set(), set()

        def carries(type_text: str) -> tuple[bool, bool]:
            idents = re.findall(r"\b[A-Za-z_]\w*\b", expand_aliases(type_text, aliases))
            return any(i in LAYOUT_TYPES for i in idents), any(i not in LAYOUT_TYPES and i not in CONTAINER_TYPES for i in idents)

        def part_names(where, part, type_text, names, parent, data_homes, basis) -> None:
            if not isinstance(names, list) or not names or any(n not in known for n in names):
                self.add("LAYOUT", f"{where}: {part} maps to a non-empty list of vocabulary names, not {names!r}")
                return
            has_layout, has_data = carries(type_text)
            inst, syntax = [n for n in names if in_instenv(n)], [n for n in names if not in_instenv(n)]
            if has_layout and not inst:
                self.add("LAYOUT", f"{where}: {part} (`{type_text}`) carries layout, so it names its {INSTENV_GROUP} home")
            if has_data != bool(syntax):
                self.add("LAYOUT", f"{where}: {part} (`{type_text}`) {'carries more than layout, so it names' if has_data else 'carries only layout, so it names no'} Core syntax ({syntax})")
            if has_layout or inst:
                home = layout_homes.get(parent)
                if home is None:
                    self.add("LAYOUT", f"{where}: {part} maps layout of MiniRust `{parent}`, which no layout_home places")
                else:
                    used_layout.add(parent)
                    if (set(inst) != {home["home"]}) if has_layout else not set(inst) <= {home["home"]}:
                        self.add("LAYOUT", f"{where}: {part} names {sorted(inst)}, but the layout of MiniRust `{parent}` goes to ['{home['home']}']")
            if has_data and data_homes is not None and set(syntax) != data_homes:
                self.add("LAYOUT", f"{where}: {part} names the Core syntax {sorted(syntax)}, but its data goes to exactly {sorted(data_homes)} ({basis})")
            self.homes_required.update(names)

        out_keys = set()
        self.payload_count = 0
        for key, row in self.t["not_in_core"].items():
            where = f"not_in_core {key}"
            if not self.refs(where, row)[0]:
                self.add("COMPLETENESS", f"{where}: a not_in_core row cites the design")
            m = re.fullmatch(r"(.+):([1-9][0-9]*)", str(row["minirust_ref"]))
            definition = self.scanned.get(m.group(1), {}).get((int(m.group(2)), row["minirust_token"])) if m else None
            if definition is None:
                self.add("COMPLETENESS", f"{where}: is not a scanned MiniRust variant or field")
                continue
            claim = (m.group(1), int(m.group(2)), row["minirust_token"])
            out_keys.add(claim)
            self.claims.setdefault(claim, []).append(f"not_in_core:{row['minirust_token']}")
            shape, parts = payload_parts(definition[2])
            replaced = row["replaced_by"]
            if shape == "fields":
                payload = row.get("payload") if isinstance(row.get("payload"), dict) else {}
                if sorted(payload) != sorted(n for n, _ in parts):
                    self.add("COMPLETENESS", f"{where}: payload maps {sorted(payload)}, but MiniRust's payload fields are {sorted(n for n, _ in parts)}")
                homes = set()
                for name in replaced if isinstance(replaced, list) else []:
                    if name not in payload_homes:
                        self.add("LAYOUT", f"{where}: replaced_by names {name!r}, which no payload_home places")
                        homes = None
                    elif homes is not None:
                        used_payload.add(name)
                        homes |= set(payload_homes[name]["homes"])
                for part, type_text in parts:
                    self.payload_count += 1
                    if part in payload:
                        part_names(where, f"payload field `{part}`", type_text, payload[part], definition[0], homes, f"the payload_home rows of {replaced}")
                if not isinstance(replaced, list) or not replaced or any(n not in known or in_instenv(n) for n in replaced):
                    self.add("COMPLETENESS", f"{where}: replaced_by lists the Core syntax names that replace the construct")
                else:
                    self.homes_required.update(replaced)
            else:
                if "payload" in row:
                    self.add("COMPLETENESS", f"{where}: MiniRust {definition[0]}::{row['minirust_token']} has no payload fields, so the row carries no payload")
                holders = set()
                for ident in dict.fromkeys(i for i in re.findall(r"\b[A-Za-z_]\w*\b", expand_aliases(parts, aliases)) if i not in LAYOUT_TYPES + CONTAINER_TYPES):
                    found = {o for rel, defs in self.scanned.items() for (n, tok), (_, kind, pl) in defs.items()
                             if kind == "variant" and payload_parts(pl)[0] == "type" and ident in split_types(payload_parts(pl)[1])
                             for o in self.claims.get((rel, n, tok), []) if not o.startswith("not_in_core:")}
                    if len(found) != 1:
                        self.add("LAYOUT", f"{where}: the data type `{ident}` is the payload of {sorted(found)} MiniRust variants' Core entries, not exactly one")
                        holders = None
                        break
                    holders |= found
                part_names(where, "replaced_by", parts, replaced, definition[0], holders, "the Core entry of the MiniRust variant whose payload is that type")
        for name, row in payload_homes.items():
            if name not in used_payload:
                self.add("LAYOUT", f"payload_home {name}: no not_in_core row is replaced by it (stale)")
            if any(h not in known for h in [name] + list(row["homes"])):
                self.add("LAYOUT", f"payload_home {name}: names a name that is not in the vocabulary")
        for parent, row in layout_homes.items():
            if parent not in used_layout:
                self.add("LAYOUT", f"layout_home {parent}: no not_in_core part carries its layout (stale)")
            if row["home"] not in self.entries or not in_instenv(row["home"]):
                self.add("LAYOUT", f"layout_home {parent}: {row['home']!r} is not an {INSTENV_GROUP} entry")
        self.entry_of, self.layout_carrying = {}, 0
        exempt, used_exempt = set(self.t["not_layout"]), set()
        for rel, found in self.scanned.items():
            for (number, token), (parent, kind, payload) in sorted(found.items()):
                owners = self.claims.get((rel, number, token), [])
                if len(owners) != 1:
                    self.add("COMPLETENESS", f"MiniRust {parent}::{token} ({kind}, {rel}:{number}) is claimed {len(owners)} times {owners}, not once by an entry or a not_in_core row")
                elif not owners[0].startswith("not_in_core:"):
                    self.entry_of[(parent, token)] = owners[0]
                expanded = expand_aliases(payload, aliases)
                has_layout = any(re.search(r"\b" + t + r"\b", expanded) for t in LAYOUT_TYPES)
                self.layout_carrying += has_layout
                if has_layout and f"{rel}:{number} {token}" in exempt:
                    has_layout = False
                    used_exempt.add(f"{rel}:{number} {token}")
                if has_layout != ((rel, number, token) in out_keys):
                    self.add("LAYOUT", f"MiniRust {parent}::{token} ({rel}:{number}) {'carries layout but is a Core entry' if has_layout else 'carries no layout but is not_in_core'}")
        for key in sorted(exempt - used_exempt):
            self.add("LAYOUT", f"not_layout {key}: is no scanned MiniRust part whose payload names a layout type (stale)")

    # ---- UB-MECHANISM, UB-SITE
    def ub_reasons(self) -> None:
        mechanisms = list(self.t["ub_mechanism"].values())
        for ref, row in self.t["ub_mechanism"].items():
            self.cite("UB-MECHANISM", f"ub_mechanism {ref}", f"minirust:{ref}", row["text"])
        for role in MECHANISM_ROLES:
            if sum(1 for m in mechanisms if m["role"] == role) != 1:
                self.add("UB-MECHANISM", f"exactly one ub_mechanism has role {role!r}")
        for ref, row in self.t["ub_mechanism"].items():
            if row["role"] not in MECHANISM_ROLES:
                self.add("UB-MECHANISM", f"ub_mechanism {ref}: role {row['role']!r} is not one of {MECHANISM_ROLES}")
        self.sites, problems = extract_ub_sites(self.trees["minirust"], mechanisms)
        for problem in problems:
            self.add("UB-MECHANISM", problem)
        claimed, self.ub_by_file = {}, {}
        known = set(self.entries) | set(self.inductives)
        for name, row in self.ub.items():
            where = f"ub_reason {name}"
            design, rustc = self.refs(where, row)
            self.origin(where, row, design, rustc)
            sites = row.get("sites") or []
            messages, files = set(), set()
            for site in sites:
                if not isinstance(site, dict) or set(site) != {"ref", "message"} or not all(isinstance(v, str) for v in site.values()):
                    self.add("TABLE", f"{where}: a site is {{ref, message}} of strings")
                    continue
                claimed.setdefault(site["ref"], []).append(name)
                if site["ref"] not in self.sites:
                    self.add("UB-SITE", f"{where}: {site['ref']} is not a UB message literal at the pin")
                elif self.sites[site["ref"]] != site["message"]:
                    self.add("UB-SITE", f"{where}: {site['ref']} raises {self.sites[site['ref']]!r}, the table says {site['message']!r}")
                messages.add(site["message"])
                files.add(site["ref"].rsplit(":", 1)[0])
            inductive = name.split(".")[0]
            if row["origin"] == "minirust":
                if not sites or len(messages) > 1 or len(files) > 1:
                    self.add("UB-SITE", f"{where}: a minirust reason lists its sites, with one message ({sorted(messages)}) in one file ({sorted(files)})")
                for f in files:
                    self.ub_by_file[f] = self.ub_by_file.get(f, 0) + 1
                expected = next((ind for prefix, ind in UB_INDUCTIVE_BY_SITE_DIR if files and all(f.startswith(prefix) for f in files)), UB_DEFAULT_INDUCTIVE)
            else:
                expected = UB_DEFAULT_INDUCTIVE
            if inductive != expected:
                self.add("UB-SITE", f"{where}: its sites ({sorted(files)}) make it a {expected} reason, not a {inductive} reason")
            raised = row.get("raised_by", [])
            if not isinstance(raised, list) or any(n not in known for n in raised):
                self.add("UB-SITE", f"{where}: raised_by names vocabulary entries, not {raised!r}")
        for ref, message in sorted(self.sites.items()):
            if len(claimed.get(ref, [])) != 1:
                self.add("UB-SITE", f"MiniRust UB at {ref} ({message!r}) is claimed by {claimed.get(ref, [])}, not exactly one reason")

    # ---- COMPOSITION, OPERATOR, FAMILY
    def containers(self) -> None:
        inductives, entries = self.inductives, self.entries
        group_of = lambda n: inductives.get(n.split(".")[0], {}).get("group")  # noqa: E731
        self.family = {n for n, r in inductives.items() if r["group"] == OPERATOR_GROUP and n != "Rvalue"}
        self.holder, self.basis, self.extension_class = {}, {}, {}
        nested = {n: r for n, r in inductives.items() if n not in SYNTAX_GROUPS and r["group"] in SYNTAX_GROUPS}
        for name, row in sorted(nested.items()):
            if row["origin"] != "minirust" or row["shape"] == "wrapper":
                continue
            holders = {self.entry_of[(parent, variant)]
                       for found in self.scanned.values() for (_, variant), (parent, kind, payload) in found.items()
                       if kind == "variant" and (parent, variant) in self.entry_of and group_of(self.entry_of[(parent, variant)]) == row["group"]
                       and row.get("minirust_token") in ([t for _, t in payload_parts(payload)[1]] if payload_parts(payload)[0] == "fields" else split_types(payload_parts(payload)[1]))}
            if len(holders) > 1:
                self.add("COMPOSITION", f"inductive {name}: MiniRust holds it in {sorted(holders)} of its group, so its constructor is ambiguous")
            elif holders:
                self.holder[name], self.basis[name] = holders.pop(), "minirust"
        shapes = []
        for name in sorted(self.family - set(OPERATOR_CATEGORY_INDUCTIVES)):
            if inductives[name]["origin"] == "minirust" and name in self.holder:
                category, leaf = self.holder[name].split(".")
                prefix = next((w for w in CLASS_WORDS if name.startswith(w) and leaf.startswith(w)), "")
                shapes.append((name[len(prefix):], category, leaf[len(prefix):], name))
        for name in sorted(self.family - set(OPERATOR_CATEGORY_INDUCTIVES)):
            if inductives[name]["origin"] != "trust-extension":
                continue
            matches = [(w, category, rest, source) for base, category, rest, source in shapes for w in CLASS_WORDS if name == w + base]
            holder = f"{matches[0][1]}.{matches[0][0]}{matches[0][2]}" if len(matches) == 1 else None
            if holder is None or holder not in entries:
                self.add("COMPOSITION", f"inductive {name}: a trust-extension operator inductive is named <operand class><base> after exactly one MiniRust operator inductive, and held by that inductive's holder renamed for the class ({[m[3] for m in matches]}, {holder})")
                continue
            self.holder[name], self.basis[name], self.extension_class[name] = holder, "class_prefix", matches[0][0]
        families = {(r["enum"], r["operands"]): r["inductives"] for r in self.t["mir_family"].values()}
        self.family_used: set[tuple[str, str, str]] = set()  # (enum, operands, inductive) a rule consulted
        for name, row in sorted(nested.items()):
            if name in self.holder or name in self.family or row["origin"] != "trust-extension":
                continue
            tokens = [r.get("token") for r in row.get("rustc_refs") or [] if isinstance(r, dict)]
            holders = set()
            for enum, rel in MIR_ENUMS:
                for variant, number in (self.rustc_enum(enum, rel) if tokens else {}).items():
                    if any(re.fullmatch(r"\s*" + re.escape(variant) + r"\(\s*" + re.escape(str(t)) + r"\s*\),?\s*", self.rustc[rel].text.split("\n")[number - 1]) for t in tokens):
                        found = {i for i in families.get((enum, "other"), ()) if f"{i}.{variant}" in entries}
                        self.family_used.update((enum, "other", i) for i in found)
                        holders.update(f"{i}.{variant}" for i in found)
            if len(holders) > 1:
                self.add("COMPOSITION", f"inductive {name}: rustc's MIR payloads hold it in {sorted(holders)}, so its constructor is ambiguous")
            elif holders:
                self.holder[name], self.basis[name] = holders.pop(), "rustc"
        self.wrapper_of = {}
        for name in sorted(self.family - set(OPERATOR_CATEGORY_INDUCTIVES)):
            derived = self.holder.get(name)
            if derived is None or derived.split(".")[0] not in OPERATOR_CATEGORY_INDUCTIVES:
                self.add("OPERATOR", f"inductive {name}: no BinOp or UnOp constructor holds it")
                continue
            if inductives[name].get("wrapped_by") != derived:
                self.add("COMPOSITION", f"inductive {name}: wrapped_by {inductives[name].get('wrapped_by')!r}, but its derived holder ({self.basis[name]}) is {derived}")
            self.wrapper_of[name] = derived
        for name, row in inductives.items():
            if "wrapped_by" in row and name not in self.wrapper_of and name not in self.family - set(OPERATOR_CATEGORY_INDUCTIVES):
                self.add("TABLE", f"inductive {name}: only a nested operator inductive carries wrapped_by")
        if len(set(self.wrapper_of.values())) != len(self.wrapper_of):
            self.add("OPERATOR", f"two operator inductives name one wrapper: {self.wrapper_of}")
        # FAMILY
        for (enum, operands), inds in families.items():
            if operands not in ("float", "other") or enum not in dict(MIR_ENUMS):
                self.add("FAMILY", f"mir_family {enum} {operands}: operands is float or other, over a MIR enum")
            for ind in inds:
                if ind not in inductives:
                    self.add("FAMILY", f"mir_family {enum} {operands}: {ind} is not declared")
                elif enum not in OPERATOR_CATEGORY_INDUCTIVES:
                    continue
                elif inductives[ind]["origin"] == "minirust":
                    for leaf in (e for e, r in entries.items() if e.split(".")[0] == ind and r["origin"] != "minirust"):
                        self.add("FAMILY", f"{leaf}: MiniRust's {ind} implements MIR operators by name, so its leaves are MiniRust's")
                elif ind not in self.extension_class and ind in self.family:
                    self.add("FAMILY", f"mir_family {enum} {operands}: the trust-extension inductive {ind} is not named by the class-prefix rule")
        for ind, cls in self.extension_class.items():
            category, operands = self.holder[ind].split(".")[0], "float" if cls == "Float" else "other"
            if ind not in families.get((category, operands), ()):
                self.add("FAMILY", f"inductive {ind}: no mir_family lists it for MIR {category} over {cls}")
            self.family_used.add((category, operands, ind))

    def operators(self) -> None:
        self.operator_names = {e for e in self.entries if e.split(".")[0] in self.family and e not in set(self.wrapper_of.values())}
        self.ops = self.t["operator"]
        for name, row in self.ops.items():
            where = f"operator {name}"
            if name not in self.operator_names:
                self.add("OPERATOR", f"{where}: is not a Core operator (a leaf of an operator inductive that wraps no other)")
                continue
            classes, overflow, kinds = row["classes"], row["overflow"], row["ub"]
            if not isinstance(classes, list) or not classes or any(c not in CLASSES for c in classes) or classes != sorted(set(classes)):
                self.add("OPERATOR", f"{where}: classes {classes!r} is not a sorted non-empty subset of {CLASSES}")
            if overflow not in OVERFLOW_VALUES or not isinstance(kinds, list) or any(k not in UB_KINDS for k in kinds) or kinds != sorted(set(kinds)):
                self.add("OPERATOR", f"{where}: overflow is one of {OVERFLOW_VALUES} and ub a sorted subset of {UB_KINDS}")
            if isinstance(classes, list) and "Float" in classes and len(classes) > 1:
                self.add("OPERATOR", f"{where}: admits Float together with other classes; a float operation has its own operator")
            ind = name.split(".")[0]
            if ind in self.extension_class and classes != [self.extension_class[ind]]:
                self.add("OPERATOR", f"{where}: {ind} is named for the class {self.extension_class[ind]}, but its classes are {classes}")
            if not row["classes_from"]:
                self.add("OPERATOR", f"{where}: cites the source of its classes")
            for key in ("classes_from", "flavour_from"):
                for c in row[key]:
                    if not isinstance(c, dict) or set(c) != {"ref", "phrase"}:
                        self.add("OPERATOR", f"{where}: a {key} citation is {{ref, phrase}}")
                    else:
                        self.cite("OPERATOR", f"{where} {key}", legacy_ref(c["ref"]), c["phrase"], raw=c["ref"])
        for name in sorted(self.operator_names - set(self.ops)):
            self.add("OPERATOR", f"Core operator {name} has no operator row")

    # ---- MIR-OPERATOR, MIRRORED
    def mir(self) -> None:
        expected, self.mir_variants = {}, 0
        for enum, rel in MIR_ENUMS:
            variants = self.rustc_enum(enum, rel)
            if not variants:
                self.add("MIR-OPERATOR", f"{rel}: enum {enum} was not found")
            self.mir_variants += len(variants)
            expected.update((f"{enum}::{v}", enum) for v in variants if f"{enum}::{v}" not in MIR_EXPANDED)
        entries, known = self.entries, set(self.entries) | set(self.inductives)
        impls = {}
        for key, row in self.t["mir_implementation"].items():
            impls[(row["mir"], row.get("operand"))] = row
            names = ([row["op"]] if "op" in row else []) + row.get("requires", [])
            if ("op" in row) == ("refusal" in row) or any(n not in known for n in names) or ("refusal" in row and not UPPER_CAMEL.match(str(row["refusal"]))):
                self.add("MIR-OPERATOR", f"mir_implementation {key}: exactly one of op and an UpperCamel refusal, naming vocabulary")
        conversions = {(r["source"], r["target"]) for r in self.t["conversion"].values()}
        sources = [s for s, _ in conversions]
        for s, t in conversions:
            if s not in CLASSES or t not in CLASSES or s == t or sources.count(s) > 1:
                self.add("MIR-OPERATOR", f"conversion {s}->{t}: converts one operand class to another, at most one conversion per class")
        families = {(r["enum"], r["operands"]): r["inductives"] for r in self.t["mir_family"].values()}
        pairs, used_impls, used_conversions = {}, set(), set()
        self.mir_counts = {"renamed": 0, "refusals": 0, "composition": 0}
        self.mir_required: set[str] = set()
        for key, row in self.t["mir_operator"].items():
            where = f"mir_operator {key}"
            mir, operand, maps_to = row["mir"], row.get("operand"), row["maps_to"]
            if mir not in expected:
                self.add("MIR-OPERATOR", f"{where}: {mir!r} is not a MIR operator variant at the pin (or is expanded)")
                continue
            enum = expected[mir]
            if enum in ("Operand", "RuntimeChecks") and operand is not None or enum not in ("Operand", "RuntimeChecks") and not operand:
                self.add("MIR-OPERATOR", f"{where}: an Operand or RuntimeChecks row has no operand list, every other row a non-empty one")
            classes = operand if isinstance(operand, list) and operand else [None]
            for cls in classes:
                pairs.setdefault((mir, cls), []).append(key)
            chosen = {cls: impls.get((mir, cls)) for cls in classes}
            used_impls.update((mir, cls) for cls, impl in chosen.items() if impl is not None)
            if "refusal" in row:
                self.mir_counts["refusals"] += 1
                if maps_to != [] or "op" in row or "convert" in row or "note" not in row or any(i is None or i.get("refusal") != row["refusal"] for i in chosen.values()):
                    self.add("MIR-OPERATOR", f"{where}: a refusal has an empty maps_to, no op or convert, a note, and the refusal its mir_implementation names")
                continue
            op = row.get("op")
            if not maps_to or any(n not in known for n in maps_to) or op not in entries or op not in maps_to:
                self.add("MIR-OPERATOR", f"{where}: maps_to names vocabulary and holds op {op!r}, a vocabulary entry")
                continue
            self.mir_required.update(maps_to)
            requires = set()
            for cls, impl in chosen.items():
                if impl is not None:
                    requires.update(impl.get("requires", []))
                    if impl.get("op") != op:
                        self.add("MIR-OPERATOR", f"{where}: {mir} over {cls} is implemented by {impl.get('op') or 'the refusal ' + str(impl.get('refusal'))} ({impl['why']}), not {op}")
                else:
                    operands = "float" if cls == "Float" else "other"
                    if op.split(".")[1] != mir.split("::")[1] or op.split(".")[0] not in families.get((enum, operands), ()):
                        self.add("MIR-OPERATOR", f"{where}: {mir} over {cls} is the leaf named {mir.split('::')[1]} of {list(families.get((enum, operands), ()))} or a mir_implementation's entry; {op} is neither")
                    else:
                        self.family_used.add((enum, operands, op.split(".")[0]))
            self.mir_counts["renamed"] += any(chosen.values())
            convert = row.get("convert", {})
            for source, target in convert.items() if isinstance(convert, dict) else [("?", "?")]:
                if source not in (operand or []) or (source, target) not in conversions:
                    self.add("MIR-OPERATOR", f"{where}: converts {source!r} to {target!r}, which is not one of its classes and a conversion row")
                used_conversions.add((source, target))
            closure, unheld = {op} | requires | ({"CastOp.Transmute"} if convert else set()), set()
            stack = list(closure)
            while stack:
                inductive = stack.pop().split(".")[0]
                if inductive in SYNTAX_GROUPS:
                    continue
                if inductive not in self.holder:
                    unheld.add(inductive)
                elif self.holder[inductive] not in closure:
                    closure.add(self.holder[inductive])
                    stack.append(self.holder[inductive])
            if unheld or set(maps_to) != closure:
                self.add("COMPOSITION", f"{where}: maps_to must be exactly {sorted(closure)} (op, its required compositions and a conversion's transmute, with their holders); it lacks {sorted(closure - set(maps_to))}, adds {sorted(set(maps_to) - closure)}, and {sorted(unheld)} have no holder")
            else:
                self.mir_counts["composition"] += 1
            op_ind = op.split(".")[0]
            if op_ind in self.family - set(OPERATOR_CATEGORY_INDUCTIVES) and any(n != op and n.split(".")[0] == op_ind and n != "CastOp.Transmute" for n in maps_to):
                self.add("MIR-OPERATOR", f"{where}: maps_to names a second leaf of op's operator inductive {op_ind}")
            if op in self.ops:
                for cls in operand or []:
                    if "->" in cls:
                        continue
                    target = convert.get(cls, cls) if isinstance(convert, dict) else cls
                    if cls not in CLASSES or not ("*" in self.ops[op]["classes"] or target in self.ops[op]["classes"]):
                        self.add("MIR-OPERATOR", f"{where}: {mir} over {cls}{' as ' + target if target != cls else ''} maps to {op}, whose operands are {self.ops[op]['classes']}")
            elif enum in ("BinOp", "UnOp") or (enum in ("CastKind", "PointerCoercion") and mir != "PointerCoercion::Unsize" and set(operand or []) & set(NUMERIC_CLASSES)):
                self.add("MIR-OPERATOR", f"{where}: op {op} of a MIR operator or numeric cast is a Core operator with typed attributes")
        for (mir, cls), keys in sorted(pairs.items(), key=str):
            if len(keys) > 1:
                self.add("MIR-OPERATOR", f"{mir} over {cls}: covered by {len(keys)} rows {keys}, exactly one is required")
        for mir in sorted(set(expected) - {m for m, _ in pairs}):
            self.add("MIR-OPERATOR", f"{mir} has no mir_operator row: D0.3 would have no Core name to map it to")
        for key in sorted(set(impls) - used_impls, key=str):
            self.add("MIR-OPERATOR", f"mir_implementation {key[0]} {key[1]}: no mir_operator row covers it (stale)")
        for pair in sorted(conversions - used_conversions):
            self.add("MIR-OPERATOR", f"conversion {pair[0]}->{pair[1]}: no mir_operator row uses it (stale)")
        for (enum, operands), inds in sorted(families.items()):
            for ind in (i for i in inds if (enum, operands, i) not in self.family_used):
                self.add("FAMILY", f"mir_family {enum} {operands}: {ind} implements no MIR row by name, holds no rustc payload and is named by no class-prefix rule (stale)")
        used_ops = {r.get("op") for r in self.t["mir_operator"].values()}
        for name in sorted(self.ops):
            if self.entries.get(name, {}).get("origin") == "trust-extension" and name not in used_ops:
                self.add("OPERATOR", f"operator {name}: a trust-extension operator is the op of no mir_operator row")
        self.mir_pairs = len(pairs)
        # MIRRORED
        self.mirrored_variants, self.mirrored_lines = 0, {}
        for inductive, row in self.t["mirrored_enum"].items():
            variants = self.rustc_enum(row["enum"], row["file"])
            if inductive not in self.inductives or not variants:
                self.add("MIRRORED", f"mirrored_enum {inductive}: the Core inductive is declared and rustc {row['enum']} exists in {row['file']}")
                continue
            self.mirrored_variants += len(variants)
            leaves = {n.split(".")[1]: r for n, r in self.entries.items() if n.split(".")[0] == inductive}
            for variant, number in variants.items():
                self.mirrored_lines[(f"{row['file']}:{number}", variant)] = inductive
                if variant not in leaves or not any(isinstance(r, dict) and (r.get("ref"), r.get("token")) == (f"{row['file']}:{number}", variant) for r in leaves[variant].get("rustc_refs") or []):
                    self.add("MIRRORED", f"rustc {row['enum']}::{variant} ({row['file']}:{number}) has no {inductive} leaf citing it")
            for leaf in sorted(set(leaves) - set(variants)):
                self.add("MIRRORED", f"{inductive}.{leaf} is no variant of rustc {row['enum']} at the pin")

    # ---- ITEMS, DESIGN-SYNTAX, PHASE
    def item_kinds(self) -> dict[str, int]:
        lines = self.trees["reference"].lines(REFERENCE_ITEMS)
        kinds, productions = {}, set()
        for first_line, body in code_blocks("\n".join(lines or [])):
            if not lines[first_line - 2].strip().startswith("```grammar"):
                continue
            text = "\n".join(body)
            heads = list(re.finditer(r"^([A-Z]\w*)\s*->", text, re.M))
            for index, head in enumerate(heads):
                if head.group(1) not in ITEM_KIND_PRODUCTIONS:
                    continue
                productions.add(head.group(1))
                start, end = head.end(), heads[index + 1].start() if index + 1 < len(heads) else len(text)
                group = text.find("(", start, end)
                if group >= 0:
                    depth, k = 0, group
                    while k < end:
                        depth += (text[k] == "(") - (text[k] == ")")
                        if depth == 0:
                            break
                        k += 1
                    start, end = group + 1, k
                for m in re.finditer(r"\b[A-Z][A-Za-z]*\b", text[start:end]):
                    kinds[m.group(0)] = first_line + text[:start + m.start()].count("\n")
        for production in set(ITEM_KIND_PRODUCTIONS) - productions:
            self.add("ITEMS", f"{REFERENCE_ITEMS}: the `{production}` production was not found at the Reference pin")
        classified = self.t["item_kind"]
        for kind in sorted(set(kinds) ^ set(classified)):
            self.add("ITEMS", f"item kind {kind}: {'the Reference has it and no item_kind classifies it' if kind in kinds else 'no Reference item kind at the pin'}")
        for kind, row in classified.items():
            if row["word"] in ("erased", "open") and row["names"] or any(n not in set(self.entries) | set(self.inductives) for n in row["names"]):
                self.add("ITEMS", f"item_kind {kind}: an erased or open kind names nothing, any other names vocabulary")
        return kinds

    def design_syntax(self) -> None:
        lines = self.trees.get("design", self.trees["worktree"]).lines(DESIGN_REL) or []
        start = next((i for i, text in enumerate(lines) if SYNTAX_BLOCK_START in text), None)
        end = next((i for i, text in enumerate(lines) if start is not None and i > start and text.startswith(SYNTAX_BLOCK_END)), None)
        inductives, entries, ops = self.inductives, self.entries, self.ops
        known_syntax = set(entries) | set(inductives)
        group_of = lambda n: inductives.get(n.split(".")[0], {}).get("group")  # noqa: E731
        self.dc = {k: 0 for k in ("words", "function", "outside", "restriction", "covered", "ignored", "phrase", "derived", "flavour", "ub", "ambiguous", "item_kind", "restrictions")}
        self.design_covered, restricted = set(), set()
        if start is None or end is None:
            self.add("DESIGN-SYNTAX", "the (C) *Syntax* block was not found in the design")
            return
        block = (start + 2, end)
        offsets, bullet_of, joined, current = {}, {}, "", None
        for number in range(block[0], block[1] + 1):
            text = EVIDENCE_TAG.sub(lambda m: " " * len(m.group(0)), lines[number - 1])
            bullet = SYNTAX_BULLET.match(text)
            if bullet:
                current = bullet.group(1)
                if current not in SYNTAX_GROUPS:
                    self.add("DESIGN-SYNTAX", f"design line {number}: a bullet for `{current}`, which is not one of {SYNTAX_GROUPS}")
            if current is not None:
                bullet_of[number] = current
            offsets[number] = len(joined)
            joined += text + "\n"
        backticked = {(m.start() + 1, m.end() - 1) for m in re.finditer(r"`([A-Za-z_][A-Za-z0-9_]*)`", joined)}
        restriction_spans = [(m.start(), m.end()) for m in PHASE_RESTRICTION.finditer(joined)]
        set_scopes = [(m.start(2), m.end(2), m.group(1)) for m in DESIGN_SET_SCOPE.finditer(joined)]
        keyword_leaf, used_keywords, used_flavours, used_ub_phrases, seen_words = {}, set(), set(), set(), set()
        for word, row in self.t["design_keyword"].items():
            parsed = C.parse_ref(row["cite"]["ref"])
            if parsed and parsed["source"] == "minirust" and (parsed["start"] + 1, row["leaf"]) in self.scanned.get(parsed["path"], {}):
                keyword_leaf[word] = row["leaf"]
            else:
                self.add("DESIGN-SYNTAX", f"design_keyword {word}: the line after its MiniRust citation defines `{row['leaf']}`")
        flavours = {p: r["requires"] for p, r in self.t["design_flavour"].items()}
        ub_phrases = {p: (r["follows"], r["requires"]) for p, r in self.t["design_ub_phrase"].items()}
        for p, req, follows in [(p, r, "operator") for p, r in flavours.items()] + [(p, v[1], v[0]) for p, v in ub_phrases.items()]:
            typed = isinstance(req, dict) and all((k == "ub_any" and v is True) or (k in REQUIREMENT_VALUES and isinstance(v, list) and v and all(x in REQUIREMENT_VALUES[k] for x in v)) for k, v in req.items())
            if follows not in ("operator", "mirrored") or not typed or bool(req) != (follows == "operator"):
                self.add("DESIGN-SYNTAX", f"design phrase {p!r}: follows an operator with requirements (non-empty lists of {sorted(REQUIREMENT_VALUES)} values, or ub_any = true), or a mirrored construct with none")
        phrases = {(r["line"], r["phrase"]): r for r in self.t["design_phrase"].values()}

        def names_word(word: str, name: str) -> bool:
            parts = [name.split(".")[-1]] if name not in inductives else [name]
            if any(word == p or ((word.islower() or LOWER_SNAKE.match(p)) and normalize(word) == normalize(p)) for p in parts):
                return True
            if name not in inductives and word in keyword_leaf and name.split(".")[-1] == keyword_leaf[word]:
                used_keywords.add(word)
                return True
            return False

        spans_of = lambda token, text: [(m.start(), m.end()) for m in re.finditer(r"(?<![A-Za-z0-9_])" + re.escape(token) + r"(?![A-Za-z0-9_])", text)]  # noqa: E731
        rows = [r for r in self.t["design_item"].values()]
        valid = []
        for row in rows:
            where = f"design_item {row['line']} {row['token']!r}"
            text = lines[row["line"] - 1] if isinstance(row["line"], int) and 0 < row["line"] <= len(lines) else ""
            if not isinstance(row["token"], str) or not spans_of(row["token"], text) or row["line"] not in bullet_of:
                self.add("DESIGN-SYNTAX", f"{where}: is not whole words of a bullet line of the (C) *Syntax* block")
            elif ("covered_by" in row) == ("ignored" in row):
                self.add("DESIGN-SYNTAX", f"{where}: carries exactly one of covered_by and ignored")
            else:
                valid.append((row, where))
        items = []
        for row, where in valid:
            line_spans = [(offsets[row["line"]] + a, offsets[row["line"]] + b) for a, b in spans_of(row["token"], lines[row["line"] - 1])]
            longer = [(offsets[row["line"]] + a, offsets[row["line"]] + b) for other, _ in valid if other["line"] == row["line"] and len(other["token"]) > len(row["token"])
                      for a, b in spans_of(other["token"], lines[row["line"] - 1])]
            free = [s for s in line_spans if not any(a <= s[0] and s[1] <= b for a, b in longer)]
            if len(free) != 1:
                self.add("DESIGN-SYNTAX", f"{where}: occurs {len(free)} times on its line outside longer design items, so its position is ambiguous")
                continue
            a, b = free[0]
            if any(x < b and a < y for x, y in restriction_spans):
                self.add("DESIGN-SYNTAX", f"{where}: overlaps a phase restriction, which PHASE reads")
            words = []
            for m in re.finditer(DESIGN_WORD, row["token"]):
                word = m.group(0)[:-2] if m.group(0).endswith("'s") else m.group(0).split("'")[0]
                pos = a + m.start()
                if len(word) >= 2 and word.lower() not in self.function_words:
                    words.append((m.group(0), word, word[0].isupper() or "_" in word or (pos, pos + len(word)) in backticked, pos))
            item = {"row": row, "where": where, "start": a, "end": b, "bullet": bullet_of[row["line"]], "words": words, "covered": None, "attached": None}
            if "ignored" in row:
                self.dc["ignored"] += 1
                for raw, _, _, _ in words:
                    if raw.lower() not in self.prose_words:
                        self.add("DESIGN-SYNTAX", f"{where}: ignores {raw!r}, which is not a prose word; cover it instead")
            elif not isinstance(row["covered_by"], list) or not row["covered_by"] or any(n not in known_syntax | set(self.ub) for n in row["covered_by"]):
                self.add("DESIGN-SYNTAX", f"{where}: covered_by is a non-empty list of vocabulary names")
            else:
                self.dc["covered"] += 1
                item["covered"] = row["covered_by"]
                self.design_covered.update(row["covered_by"])
            items.append(item)
        used_prose = {raw.lower() for it in items if "ignored" in it["row"] for raw, _, _, _ in it["words"]}
        for word in sorted(self.prose_words - used_prose):
            self.add("DESIGN-SYNTAX", f"prose word {word!r} is in no ignored design_item (stale)")
        items.sort(key=lambda it: it["start"])
        for i, item in enumerate(items):
            if i and items[i - 1]["bullet"] == item["bullet"] and items[i - 1]["end"] <= item["start"]:
                between = joined[items[i - 1]["end"]:item["start"]].replace("`", " ").replace("*", " ")
                if all(t.lower() in self.function_words for t in between.split()):
                    item["attached"] = items[i - 1]
        requirements_on = {}
        for item in items:
            target, token = item["attached"], item["row"]["token"]
            if target is not None and target["covered"] is not None:
                if token in flavours:
                    requirements_on.setdefault(id(target), []).append(flavours[token])
                elif token in ub_phrases and ub_phrases[token][0] == "operator":
                    requirements_on.setdefault(id(target), []).append(ub_phrases[token][1])
        item_words = {}
        for kind, row in self.t["item_kind"].items():
            if row["word"] not in ("erased", "open"):
                item_words.setdefault(row["word"], set()).update(row["names"])
        seen_item_words, used_phrases = set(), set()
        for item in items:
            row, where, token, covered, target = item["row"], item["where"], item["row"]["token"], item["covered"], item["attached"]
            if token in ub_phrases:
                self.dc["ub"] += 1
                used_ub_phrases.add(token)
                follows, requirements = ub_phrases[token]
                if covered is None or target is None or target["covered"] is None or any(group_of(n) != UB_GROUP for n in covered):
                    self.add("DESIGN-SYNTAX", f"{where}: a UB phrase covers UB reasons and follows a covered construct")
                    continue
                if follows == "operator":
                    named = [n for n in target["covered"] if n in ops]
                    expected = {r for r, u in self.ub.items() if set(u.get("raised_by", [])) & set(named)}
                    for op in named:
                        if not meets_requirements(requirements, ops[op]):
                            self.add("DESIGN-SYNTAX", f"{where}: the design says `{target['row']['token']}` {token}, but {op} has overflow {ops[op]['overflow']!r} and UB {ops[op]['ub']}")
                    basis = f"the UB reasons raised_by {named}"
                else:
                    mirrored = set(target["covered"]) & set(self.t["mirrored_enum"])
                    expected = {r for r, u in self.ub.items() if any(isinstance(x, dict) and self.mirrored_lines.get((x.get("ref"), x.get("token"))) in mirrored for x in u.get("rustc_refs") or [])}
                    basis = f"the UB reasons citing a variant of the mirrored {sorted(mirrored)}"
                if not expected or set(covered) != expected:
                    self.add("DESIGN-SYNTAX", f"{where}: covers {sorted(covered)}, but {basis} are {sorted(expected)}")
                continue
            if covered is not None and any(group_of(n) == UB_GROUP for n in covered):
                self.add("DESIGN-SYNTAX", f"{where}: names UB reasons, which only a UB phrase covers")
            if token in flavours:
                self.dc["flavour"] += 1
                used_flavours.add(token)
                named = [n for n in target["covered"] if n in ops] if target is not None and target["covered"] is not None else []
                if covered is not None or not named:
                    self.add("DESIGN-SYNTAX", f"{where}: a flavour phrase is ignored prose that follows a covered Core operator")
                for op in named:
                    if not meets_requirements(flavours[token], ops[op]):
                        self.add("DESIGN-SYNTAX", f"{where}: the design says `{target['row']['token']}` {token}, but {op} has classes {ops[op]['classes']}, overflow {ops[op]['overflow']!r} and UB {ops[op]['ub']}")
                continue
            if covered is None:
                if target is not None and target["covered"] is not None and any(n in ops for n in target["covered"]):
                    self.add("DESIGN-SYNTAX", f"{where}: ignored phrase {token!r} follows an operator word and is no flavour phrase")
                continue
            if item["bullet"] == "Program" and token in item_words:
                self.dc["item_kind"] += 1
                seen_item_words.add(token)
                if set(covered) != item_words[token]:
                    self.add("ITEMS", f"{where}: covers {sorted(covered)}, but the item kinds classified under {token!r} are held by {sorted(item_words[token])}")
                continue
            for name in covered:
                if group_of(name) != item["bullet"]:
                    self.add("DESIGN-SYNTAX", f"{where}: covered_by {name!r} is in group {group_of(name)!r}, not the `{item['bullet']}` bullet's")
            named_by_words, rules = set(), []
            for raw, word, strict, pos in item["words"]:
                if not strict:
                    continue
                named = {n for n in known_syntax if group_of(n) == item["bullet"] and names_word(word, n)}
                if not named:
                    self.add("DESIGN-SYNTAX", f"{where}: {word!r} names no leaf or inductive of the `{item['bullet']}` bullet's group")
                    continue
                variants = sorted(n for n in named if n not in inductives and n.split(".")[-1] == keyword_leaf.get(word, word))
                if len(variants) >= 2:
                    self.dc["ambiguous"] += 1
                    scope = next((s for x, y, s in set_scopes if x <= pos < y), None)
                    requirements = requirements_on.get(id(item), [])
                    if scope is not None:
                        chosen, rule = {n for n in variants if n.split(".")[0] == scope}, f"it lies in the design's `{scope} ∈ {{..}}` set"
                    elif requirements:
                        chosen, rule = {n for n in variants if n in ops and all(meets_requirements(r, ops[n]) for r in requirements)}, "the design's flavour after it fits"
                    else:
                        chosen, rule = {n for n in variants if n.split(".")[0] == item["bullet"]}, f"it is read in the `{item['bullet']}` bullet"
                        displaced = [n for n in variants if n not in chosen and entries[n]["origin"] == "minirust"]
                        if displaced and any(entries[n]["origin"] == "trust-extension" for n in chosen):
                            self.add("DESIGN-SYNTAX", f"{where}: {word!r} names MiniRust {displaced} and trust-extension {sorted(chosen)}; with no design set or flavour to separate them, the extension would duplicate the MiniRust construct")
                    if len(chosen) != 1:
                        self.add("DESIGN-SYNTAX", f"{where}: {word!r} names {variants}, and {rule} picks {sorted(chosen)}, not exactly one")
                    named = (named - set(variants)) | chosen
                    rules.append(f"{word!r} is {sorted(chosen)} because {rule}")
                origins = {(entries.get(n) or inductives.get(n))["origin"] for n in named}
                if origins == set(ORIGINS):
                    self.add("DESIGN-SYNTAX", f"{where}: {word!r} names MiniRust and trust-extension names {sorted(named)} together, so the extension duplicates the MiniRust construct")
                named_by_words |= named
            lowercase = [raw for raw, _, strict, _ in item["words"] if not strict]
            phrase = phrases.get((row["line"], token))
            if phrase is not None:
                self.dc["phrase"] += 1
                used_phrases.add((row["line"], token))
                if not lowercase or set(covered) != set(phrase["names"]) or not named_by_words <= set(phrase["names"]):
                    self.add("DESIGN-SYNTAX", f"{where}: covers {sorted(covered)}; its design_phrase maps it to exactly {sorted(phrase['names'])}, its construct words name {sorted(named_by_words)}, and it has lowercase words {lowercase}")
            elif lowercase or not item["words"]:
                self.add("DESIGN-SYNTAX", f"{where}: {token!r} has lowercase words {lowercase}, which name nothing by themselves, and no design_phrase row")
            else:
                self.dc["derived"] += 1
                if set(covered) != named_by_words:
                    self.add("DESIGN-SYNTAX", f"{where}: its construct words name exactly {sorted(named_by_words)} in the `{item['bullet']}` bullet{' (' + '; '.join(rules) + ')' if rules else ''}, but covered_by is {sorted(covered)}")
        for word in sorted(set(item_words) - seen_item_words):
            self.add("ITEMS", f"no design_item of the `Program` bullet covers the item word {word!r}")
        for key, row in phrases.items():
            if key not in used_phrases or any(n not in known_syntax for n in row["names"]):
                self.add("DESIGN-SYNTAX", f"design_phrase {key}: no covered design_item is that phrase on that line, or it names unknown vocabulary (stale)")
        for number in range(block[0], block[1] + 1):
            for m in re.finditer(DESIGN_WORD, joined[offsets[number]:offsets[number] + len(lines[number - 1])]):
                a, b = offsets[number] + m.start(), offsets[number] + m.end()
                self.dc["words"] += 1
                seen_words.add(m.group(0).lower())
                is_function = m.group(0).lower() in self.function_words
                self.dc["function"] += is_function
                if any(x <= a and b <= y for x, y in restriction_spans):
                    self.dc["restriction"] += 1
                elif any(it["start"] <= a and b <= it["end"] for it in items):
                    pass
                elif is_function:
                    self.dc["outside"] += 1
                else:
                    self.add("DESIGN-SYNTAX", f"design line {number} word {m.group(0)!r} lies in no design_item and is not a function word")
        for kind, stale in (("design_keyword", set(keyword_leaf) - used_keywords), ("design_flavour", set(flavours) - used_flavours),
                            ("design_ub_phrase", set(ub_phrases) - used_ub_phrases), ("function word", self.function_words - seen_words)):
            for key in sorted(stale):
                self.add("DESIGN-SYNTAX", f"{kind} {key!r}: no word or design_item of the Syntax list uses it (stale)")
        for a, _ in restriction_spans:
            self.dc["restrictions"] += 1
            before = len(joined[:a].rstrip(" `*\n"))
            owners = [it for it in items if it["end"] == before and it["covered"] is not None]
            if not owners or any(n not in entries for it in owners for n in it["covered"]):
                self.add("PHASE", f"the phase restriction at offset {a} of the Syntax list follows a covered design_item of entries")
            restricted.update(n for it in owners for n in it["covered"] if n in entries)
        for name, row in entries.items():
            expected = RESTRICTED_PHASES if name in restricted else list(PHASES)
            if isinstance(row["phases"], list) and row["phases"] != expected:
                self.add("PHASE", f"entry {name}: phases {row['phases']} but the design {'restricts it to' if name in restricted else 'states no restriction for it, so it is'} {expected}")
        self.restricted = restricted

    # ---- EXT-NAME, REQUIRED, DEFERRED
    def extensions(self) -> None:
        rule_named = set(self.extension_class) | {self.holder[n] for n in self.extension_class}
        aliases, justified = self.t["extension_alias"], self.t["extension_justification"]
        self.name_grounds = {"cited": 0, "rule": 0, "alias": 0}
        extension = set()
        for where, full, name, design, rustc in self.extension_names:
            extension.add(full)
            grounded = name in rustc or any(phrase_has_words(p, words_of(name)) for p in design)
            by_rule, alias = full in rule_named, full in aliases
            if (grounded or by_rule) and alias:
                self.add("EXT-NAME", f"{where}: `{full}` is {'a cited token or design phrase' if grounded else 'named by the class-prefix rule'}, so its extension_alias is stale")
            elif not (grounded or by_rule or alias):
                self.add("EXT-NAME", f"{where}: `{name}` is no cited rustc token or whole-word design phrase, is not named by the class-prefix rule, and has no extension_alias")
            if grounded or by_rule or alias:
                self.name_grounds["cited" if grounded else "rule" if by_rule else "alias"] += 1
        for name in sorted(set(aliases) - extension):
            self.add("EXT-NAME", f"extension_alias {name}: is no trust-extension inductive or entry (stale)")
        consumers = set(self.design_covered) | self.mir_required | self.homes_required
        for row in self.t["mir_implementation"].values():
            consumers.update(([row["op"]] if "op" in row else []) + row.get("requires", []))
        for row in self.ub.values():
            consumers.update(row.get("raised_by", []))
        for inductive in self.t["mirrored_enum"]:
            consumers.add(inductive)
            consumers.update(n for n in self.entries if n.split(".")[0] == inductive)
        consumers.update([ind for _, ind in UB_INDUCTIVE_BY_SITE_DIR] + [UB_DEFAULT_INDUCTIVE])
        consumers.update(n.split(".")[0] for n, r in list(self.entries.items()) + list(self.ub.items()) if r["origin"] == "minirust")

        def closure(names: set[str]) -> set[str]:
            closed, stack = set(names), list(names)
            while stack:
                name = stack.pop()
                implied = name.split(".")[0] if "." in name else self.holder.get(name)
                if implied and implied not in closed:
                    closed.add(implied)
                    stack.append(implied)
            return closed

        required, with_justifications = closure(consumers), closure(consumers | set(justified))
        rows = [(n, r) for kind in (self.inductives, self.entries, self.ub) for n, r in kind.items() if r["origin"] == "trust-extension"]
        self.required = {"names": len(rows), "by_consumer": 0, "justified": 0}
        for name, _ in rows:
            if name in required:
                self.required["by_consumer"] += 1
                if name in justified:
                    self.add("REQUIRED", f"extension_justification {name}: a consumer already requires it (stale)")
            elif name in with_justifications:
                self.required["justified"] += 1
            else:
                self.add("REQUIRED", f"{name}: a trust-extension name that no design item, MIR composition, not_in_core home, mirrored enum, raised_by or holder requires, and no extension_justification justifies")
        for name in sorted(set(justified) - {n for n, _ in rows}):
            self.add("REQUIRED", f"extension_justification {name}: is no trust-extension name (stale)")

    def deferred(self) -> None:
        kinds = dict(ROWS)
        for key, row in self.t["deferred_check"].items():
            where = f"deferred_check {key}"
            for name in row["fields"]:
                kind, _, field_name = str(name).partition(".")
                if kind not in kinds or field_name not in kinds[kind][0]:
                    self.add("DEFERRED", f"{where}: {name!r} is not a <row kind>.<field> of the table")
            for exit_id in row["checked_by"]:
                if not EXIT_ID.match(str(exit_id)) or not any(f"**{exit_id}**" in c.get("quote", "") for c in row["cites"] if isinstance(c, dict)):
                    self.add("DEFERRED", f"{where}: checked_by {exit_id!r} is an exit id quoted by one of its design citations")

    # ---- counts, document, judgments
    def render(self) -> str:
        groups = {g: {"inductives": 0, **{(k, o): 0 for k in ("variant", "field") for o in ORIGINS}} for g in SYNTAX_GROUPS + (INSTENV_GROUP,)}
        for row in self.inductives.values():
            if row["group"] in groups:
                groups[row["group"]]["inductives"] += 1
        for name, row in self.entries.items():
            group = self.inductives.get(name.split(".")[0], {}).get("group")
            if group in groups and (row["kind"], row["origin"]) in groups[group]:
                groups[group][(row["kind"], row["origin"])] += 1
        out = ["| Category | Inductives | Variants (minirust) | Variants (trust-extension) | Fields (minirust) | Fields (trust-extension) | Entries |",
               "|---|---:|---:|---:|---:|---:|---:|"]
        total = [0] * 5
        for group, row in groups.items():
            values = [row["inductives"], row[("variant", "minirust")], row[("variant", "trust-extension")], row[("field", "minirust")], row[("field", "trust-extension")]]
            if group == INSTENV_GROUP:
                out.append(f"| **Syntax total** | {' | '.join(map(str, total))} | {sum(total[1:])} |")
                out.append(f"| {group} (instantiation environment, not syntax) | {' | '.join(map(str, values))} | {sum(values[1:])} |")
            else:
                out.append(f"| {group} | {' | '.join(map(str, values))} | {sum(values[1:])} |")
                total = [a + b for a, b in zip(total, values)]
        self.counts["groups"] = {g: tuple(v.values()) for g, v in groups.items()}
        extension_ub = sum(1 for r in self.ub.values() if r["origin"] == "trust-extension")
        out += ["", "| UB reasons | Origin | Reasons |", "|---|---|---:|"]
        out += [f"| sites in `{f}` | minirust | {v} |" for f, v in sorted(self.ub_by_file.items())]
        out += [f"| no MiniRust site | trust-extension | {extension_ub} |",
                f"| **Total** | minirust {sum(self.ub_by_file.values())}, trust-extension {extension_ub} | {len(self.ub)} |", ""]
        intrinsic = [r for r in self.ub.values() if r.get("raised_by") and all(n.startswith("Intrinsic") for n in r["raised_by"])]
        c = self.counts
        c.update({
            "ub_reasons": len(self.ub), "ub_extension": extension_ub, "ub_sites": len(self.sites),
            "ub_distinct_messages": len(set(self.sites.values())),
            "ub_raised_by": sum(1 for r in self.ub.values() if r.get("raised_by")),
            "ub_intrinsic": len(intrinsic),
            "ub_call_shape": sum(1 for r in intrinsic if all(CALL_SHAPE_MESSAGE.match(s["message"]) for s in r.get("sites", []))),
            "scanned": sum(len(v) for v in self.scanned.values()), "layout_carrying": self.layout_carrying,
            "not_in_core": len(self.t["not_in_core"]), "payload_parts": self.payload_count,
            "operators": len(self.ops), "operators_extension": sum(1 for n in self.ops if self.entries.get(n, {}).get("origin") == "trust-extension"),
            "operators_flavoured": sum(1 for r in self.ops.values() if r["overflow"] != "not-ub" or r["ub"]),
            "mir_variants": self.mir_variants, "mir_pairs": self.mir_pairs, "mir_rows": len(self.t["mir_operator"]),
            "mirrored_variants": self.mirrored_variants, "design_phrases": len(self.t["design_phrase"]),
            "containers": tuple(sum(1 for b in self.basis.values() if b == k) for k in ("minirust", "class_prefix", "rustc")),
            **{f"design_{k}": v for k, v in self.dc.items()}, **{f"extension_{k}": v for k, v in self.required.items()},
            **{f"grounds_{k}": v for k, v in self.name_grounds.items()}, **{f"mir_{k}": v for k, v in self.mir_counts.items()},
        })
        kinds = {w: sum(1 for r in self.t["item_kind"].values() if r["word"] == w) for w in ("items", "impls", "statics", "erased", "open")}
        rows = [
            ("UB inductives", sum(1 for r in self.inductives.values() if r["group"] == UB_GROUP)),
            ("MiniRust UB sites in spec/** code blocks", c["ub_sites"]),
            ("Distinct MiniRust UB messages", c["ub_distinct_messages"]),
            ("UB reasons with a raised_by (reviewed)", c["ub_raised_by"]),
            ("UB reasons raised only by intrinsic operations", c["ub_intrinsic"]),
            ("of which every message has the call-shape form", c["ub_call_shape"]),
            ("Scanned MiniRust variants and fields", c["scanned"]),
            ("of which carry layout (payload names a layout type)", c["layout_carrying"]),
            ("of which a reviewed not_layout row says are not layout", len(self.t["not_layout"])),
            ("Wrapper inductives (a MiniRust one-field tuple struct of `Name` or alias of `Int` in the scanned files) / libspecr-defined enum inductives",
             f"{self.counts['wrappers']} / {sum(1 for r in self.inductives.values() if 'libspecr_refs' in r)}"),
            ("not_in_core rows", c["not_in_core"]),
            ("Payload fields of not_in_core variants, each mapped by what its type carries", c["payload_parts"]),
            ("Words (`[A-Za-z][A-Za-z0-9_']*` tokens) in the design's (C) Syntax list, evidence tags removed", c["design_words"]),
            ("of which closed function words, anywhere in the list", c["design_function"]),
            ("of which inside the phase restrictions", c["design_restriction"]),
            ("of which outside every design_item phrase and phase restriction (all closed function words)", c["design_outside"]),
            ("design_item rows covered by vocabulary", c["design_covered"]),
            ("of which derived from construct words / a design_phrase row / item words / UB phrases",
             f"{c['design_derived']} / {c['design_phrase']} / {c['design_item_kind']} / {c['design_ub']}"),
            ("design_phrase rows", c["design_phrases"]),
            ("design_item rows ignored with a reason", c["design_ignored"]),
            ("Prose and payload words an ignored row may contain", len(self.prose_words)),
            ("Design flavour phrases checked against operator attributes / UB phrases checked against raised_by or mirrored citations", f"{c['design_flavour']} / {c['design_ub']}"),
            ("Construct words naming more than one leaf of their bullet's group, resolved by set, flavour or bullet", c["design_ambiguous"]),
            ("Rust Reference item kinds (in `items` / `impls` / `statics` / erased / open)", f"{sum(kinds.values())} ({' / '.join(str(kinds[w]) for w in kinds)})"),
            ("Design phase restrictions / entries they restrict", f"{c['design_restrictions']} / {len(self.restricted)}"),
            ("Core operators with typed attributes (minirust / trust-extension)", f"{c['operators']} ({c['operators'] - c['operators_extension']} / {c['operators_extension']})"),
            ("of which state UB or an overflow flag", c["operators_flavoured"]),
            ("Operand-class conversion rows", len(self.t["conversion"])),
            ("rustc MIR variants read (BinOp, UnOp, CastKind, PointerCoercion, Operand, RuntimeChecks)", c["mir_variants"]),
            ("MIR (variant, operand class or unsize case) pairs the rows list", c["mir_pairs"]),
            ("mir_operator rows / implemented as a mir_implementation names / named refusals", f"{c['mir_rows']} / {c['mir_renamed']} / {c['mir_refusals']}"),
            ("mir_implementation rows (variant, class or case)", len(self.t["mir_implementation"])),
            ("mir_operator rows whose maps_to equals the derived composition", c["mir_composition"]),
            ("Nested syntax inductives with a derived holding constructor (MiniRust payload / class-prefix rule / rustc MIR payload)",
             f"{sum(c['containers'])} ({' / '.join(map(str, c['containers']))})"),
            ("rustc enums mirrored leaf for leaf / their variants", f"{len(self.t['mirrored_enum'])} / {c['mirrored_variants']}"),
            ("Class-prefix operator families", len(self.extension_class)),
            ("payload_home / layout_home rows", f"{len(self.t['payload_home'])} / {len(self.t['layout_home'])}"),
            ("Trust-extension names (inductives, entries, UB reasons) / required by a consumer / justified by an extension_justification",
             f"{c['extension_names']} / {c['extension_by_consumer']} / {c['extension_justified']}"),
            ("Trust-extension names grounded by a cited token or design phrase / named by the class-prefix rule / explained by an extension_alias",
             f"{c['grounds_cited']} / {c['grounds_rule']} / {c['grounds_alias']}"),
            ("deferred_check rows (behavioural facts recorded as reviewed judgments, each naming its checking exits)", len(self.t["deferred_check"])),
        ]
        out += ["| Measured at the pins | Count |", "|---|---:|"] + [f"| {label} | {value} |" for label, value in rows]
        return "\n".join(out)

    def document(self, table_text: str) -> dict[str, str]:
        path = self.o.doc or self.o.repo / DOC_REL
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            self.add("DOC", f"{path}: {error}")
            return {}
        C.check_block(self.f, "DOC", text, COUNTS_BLOCK, table_text)
        sections = C.document_judgments(self.f, "DOC", text, generated=(COUNTS_BLOCK,))
        for jid, body in sections.items():
            body = body if isinstance(body, str) else "\n".join(body)
            self.counts["doc_citations"] = self.counts.get("doc_citations", 0) + C.check_prose(self.f, "DOC", jid, body, self.resolver)
        pins = [self.pins.alignment] + [self.pins.sources[n].revision for n in READS]
        for revision in pins:
            if f"`{revision}`" not in text:
                self.add("DOC", f"the document does not record the pin `{revision}`")
        names = set(self.entries) | set(self.ub)
        for m in re.finditer(r"`([A-Z][A-Za-z0-9]*)\.([A-Za-z][A-Za-z0-9_]*)`", text):
            if m.group(1) in self.inductives and f"{m.group(1)}.{m.group(2)}" not in names:
                self.add("DOC", f"the document names `{m.group(1)}.{m.group(2)}`, which is not in the vocabulary")
        return sections


def judgments(findings: C.Findings, table_text: str, document: dict) -> dict:
    """Every reviewed judgment of the vocabulary, keyed `kind:key`: each table row, each
    design_syntax list, the [adopted] rule, the table's comments, and the document's judgments
    (its prose sections and outline). One id from two sources is refused."""
    data = tomllib.loads(table_text)
    rows = [(f"{kind}:{key(row)}", row) for kind, (_, _, key) in ROWS.items() for row in data.get(kind, []) if isinstance(row, dict)]
    lists = [(f"design_syntax:{name}", value) for name, value in (data.get("design_syntax") or {}).items()]
    adopted = [("adopted:rule", data["adopted"])] if "adopted" in data else []
    return C.merge_judgments(findings, rows + lists + adopted + [("comments:table", C.toml_comments(table_text))] + list(document.items()))


def collect(options: Options | None = None) -> Result:
    options = options or Options()
    checker = Checker(options)
    result = Result(violations=checker.f.violations, counts=checker.counts)
    if not checker.load():
        return result
    checker.rows()
    checker.names()
    checker.layout()
    checker.ub_reasons()
    checker.containers()
    checker.operators()
    checker.mir()
    item_kinds = checker.item_kinds()
    checker.design_syntax()
    checker.extensions()
    checker.deferred()
    result.table_text = checker.render()
    checker.counts["item_kinds"] = len(item_kinds)
    sections = checker.document(result.table_text)
    checker.counts["citations"] = checker.cited
    checker.counts["reviews"] = C.check_reviews(
        checker.f, options.registry or options.repo / REGISTRY_REL, DELIVERABLE, judgments(checker.f, checker.table_text, sections),
        JUDGMENT_KINDS, options.repo if options.check_history else None, REGISTRY_REL)
    return result


def main(argv: list[str] | None = None) -> int:
    if tomllib is None:
        print("core_vocabulary: Python 3.11+ (tomllib) is required", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--minirust", type=Path)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--repo", type=Path, default=REPO_ROOT)
    for name in ("table", "doc", "registry"):
        parser.add_argument(f"--{name}", type=Path)
    parser.add_argument("--print-counts-table", action="store_true")
    parser.add_argument("--write-counts", action="store_true", help="rewrite the document's counts block")
    args = parser.parse_args(argv)
    options = Options(repo=args.repo, table=args.table, doc=args.doc, registry=args.registry,
                      clones={"minirust": args.minirust, "rust-reference": args.reference})
    try:
        result = collect(options)
    except (C.MissingClone, C.PinsError) as error:
        print(f"core_vocabulary: {error}", file=sys.stderr)
        return 2
    if args.print_counts_table:
        print(result.table_text)
    elif args.write_counts:
        doc = args.doc or args.repo / DOC_REL
        doc.write_text(C.replace_block(doc.read_text(encoding="utf-8"), COUNTS_BLOCK, result.table_text), encoding="utf-8")
    else:
        print(result.table_text)
    if result.violations:
        print(f"\ncore_vocabulary: {len(result.violations)} violation(s)", file=sys.stderr)
        for violation in result.violations:
            print(f"  {violation}", file=sys.stderr)
        return 1
    print(f"\ncore_vocabulary: OK ({result.counts['citations']} row citations, {result.counts.get('doc_citations', 0)} document citations, "
          f"{result.counts['reviews']['judgments']} reviewed judgments)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
