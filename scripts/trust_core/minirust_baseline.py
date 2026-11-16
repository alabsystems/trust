#!/usr/bin/env python3
"""D0.6 MiniRust baseline checker (design exit E0.8b, "0 unmapped rows").

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.2 Stage 0.2 (D0.6: "the
pinned MiniRust revision, and a table mapping every MiniRust syntax constructor and memory-model
operation to a Core constructor or a divergence entry") and §3.1 D-1 (the divergence ledger).
Table: docs/trust-core/minirust-baseline.toml. Document: docs/trust-core/MINIRUST_BASELINE.md.
Review registry: docs/trust-core/reviews/minirust_baseline.toml.

The shared layers (pins, git trees, citations, uniqueness, generated blocks, reviewed judgments
and their history) are scripts/trust_core/common.py's. This file holds D0.6's own rules; each
EXITS NON-ZERO when it fails. MINIRUST_BASELINE.md's Predicates section states them:

  PIN          common: the MiniRust and Reference clones at EXTERNAL_PINS.toml's pins, this
               repository's alignment, no replace ref or grafts file.
  UNIVERSE     a specr reader (tokenizer and item parser) reads every ```rust fence of every
               Markdown file under MiniRust's spec/ at the pin: every definition, variant, field,
               fn, associated type and const, and macro. SYNTAX is what `Program` reaches through
               variant and field types; every type name so reached that MiniRust does not define is
               exactly one [[external]] row, and an external `enum` row's variants are syntax
               members, each written `Name::Variant` in a fence, every such path declared. argmatch
               case fns and dispatchers are derived from the variant or enum they match.
  UB-MECHANISM every `throw_ub!` literal and trailing `ensure_else_ub` literal is a UB site with its
               enclosing member; any other use of `Ub`, `throw_ub` or `ensure_else_ub` fails.
  VOCABULARY   every MiniRust citation of the Core vocabulary names exactly one universe member of
               its kind; the vocabulary's UB sites are the extracted sites with their messages.
  MAPPING      no member is claimed twice, and a claim carries the ref and token the reader
               derived; a core row's members carry Core names (a vocabulary name, or the member's
               own adopted name if it is not syntax), a syntax member exactly the names the
               vocabulary cites for it; a divergence row's members carry none and its counterpart
               holds the vocabulary's names for them; extension names only in trust-extends rows;
               a UB site only in a divergence row naming its reason; a kept site is a site of the
               row that keeps it; no UB site inside a trust-extends member is claimed as changed;
               kinds, resolutions (an `| LD-n |` row of the design), citations.
  RULING       the ruling states of the Language Decisions ledger (language-decisions.toml's
               [[ratify]] rows): a row rests on LD-n when its divergence resolves to LD-n, or its
               design_ref or a citation quotes the design's `| LD-n |` line. A row that rests on an
               LD-n the ledger ruled `revised` or `rejected` contradicts that ruling, since the line
               it rests on states the recommendation the ruling overturned, unless the row's
               `rulings` re-justifies it: an entry naming LD-n whose quote is text of that ruling's
               ruling_record. A divergence that resolves to an LD-n whose ruling is still `pending`
               rests on no ruling. A `rulings` entry for a decision the row does not rest on, for
               an LD-n with no [[ratify]] row, or quoting text the ruling_record lacks, is stale.
  UNMAPPED     exit E0.8b: every member, UB site and extension that no row maps and no derivation
               maps (a derived member whose source is unmapped, a UB site inside a divergence
               member that no row claims or keeps, a UB site whose derived reason names are not
               all vocabulary names) is one violation; the published Unmapped column counts them.
  DOC          the counts and ledger blocks regenerate; every line is in a reviewed section, a
               generated block or the outline; every «quoted» citation resolves; the pins are
               recorded.
  REVIEW       common.check_reviews over every row, external row, the table's comments, every
               prose section and the outline.

Usage:
    scripts/trust_core/minirust_baseline.py [--minirust DIR] [--reference DIR] [--repo DIR]
        [--table FILE] [--doc FILE] [--vocabulary FILE] [--registry FILE] [--decisions FILE]
        [--write-blocks]

Exit codes: 0 every predicate holds; 1 a violation; 2 a clone is missing or unreadable pins.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

tomllib = C.tomllib
TABLE_REL = "docs/trust-core/minirust-baseline.toml"
DOC_REL = "docs/trust-core/MINIRUST_BASELINE.md"
VOCABULARY_REL = "docs/trust-core/core-vocabulary.toml"
DECISIONS_REL = "docs/trust-core/language-decisions.toml"  # the Language Decisions ledger; its [[ratify]] rows hold the ruling states
RULINGS = ("pending", "ratified", "revised", "rejected")  # language_decisions.py's ruling states
OVERTURNED = ("revised", "rejected")  # a ruling that does not stand behind the design's recommendation
REGISTRY_REL = f"{C.REVIEWS_DIR}/minirust_baseline.toml"
DELIVERABLE = "minirust_baseline"
SCHEMA = "trust.core.minirust-baseline.v2"
READS = {"minirust": "minirust", "rust-reference": "reference"}  # EXTERNAL_PINS source -> citation source
COUNTS_BLOCK, LEDGER_BLOCK = "minirust-baseline-counts", "minirust-baseline-ledger"
SYNTAX_ROOT = "Program"
PATH_PREFIXES = frozenset({"libspecr", "std", "crate", "lang", "mem", "self", "super"})
NON_RUST_ITEM = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:fn|enum|struct|impl|trait|type|const|use|macro_rules!)\b")
EXTERNAL_CLASSES = ("enum", "container", "scalar")
KINDS = ("trust-extends", "trust-restricts", "trust-differs", "not-modeled-yet")
UPSTREAM = "upstream-proposal"
LD = re.compile(r"^LD-([1-9][0-9]*)$")
# The design's list of extensions: the one sentence holding EXTENSION_START, items after LEAD up to END.
EXTENSION_START = "Trust's **extensions** are hand-authored Clean modules layered over the"
EXTENSION_LEAD, EXTENSION_END = "generated core: ", ". Each extension"
ALIAS_REASON, TREE_BORROWS_UB = "UbReason.AliasViolation", "TreeBorrowsUb"
ROW_KEYS, ROW_REQUIRED = {"id", "title", "members", "note", "cites", "divergence", "rulings"}, {"id", "title", "members", "note"}
DIVERGENCE_KEYS = {"kind", "explanation", "design_ref", "resolution", "counterpart", "kept_ub_sites"}
EXTERNAL_KEYS = {"name", "class", "variants", "cites", "why"}
TABLE_KEYS = {"schema", "design", "vocabulary", "external", "row"}
JUDGMENT_KINDS = {"row", "external", "comments", "prose", "outline"}
ROW_ID = re.compile(r"^R-[A-Z0-9][A-Z0-9-]*$")
MEMBER_CLASSES = ("syntax", "domain", "operation", "derived-case", "derived-dispatcher")


@dataclass
class Result:
    violations: list = field(default_factory=list)
    counts: dict = field(default_factory=dict)
    counts_text: str = ""
    ledger_text: str = ""


@dataclass
class Options:
    repo: Path = C.REPO_ROOT
    table: Path | None = None
    doc: Path | None = None
    vocabulary: Path | None = None
    registry: Path | None = None
    decisions: Path | None = None
    pins: Path | None = None
    clones: dict = field(default_factory=dict)
    trees: dict = field(default_factory=dict)  # citation source -> tree; mutation tests only
    check_pin_state: bool = True
    check_history: bool = True


# --------------------------------------------------------------------------
# the specr reader
# --------------------------------------------------------------------------


class SpecrError(Exception):
    pass


@dataclass
class Tok:
    kind: str  # ident, lifetime, str, char, num, punct, doc
    text: str
    line: int
    value: str = ""  # a string literal's contents, escapes kept


PUNCTS = ("<<=", ">>=", "...", "..=", "::", "->", "=>", "..", "==", "!=", "<=", ">=", "&&", "||",
          "+=", "-=", "*=", "/=", "%=", "^=", "&=", "|=", "<<", ">>")
OPEN = {"(": ")", "[": "]", "{": "}"}
CLOSE = {v: k for k, v in OPEN.items()}


def tokenize(text: str, first_line: int, rel: str) -> list:
    """Tokens of a specr code block; `//` and `/* */` comments dropped, `///` kept as doc."""
    toks, i, n, line = [], 0, len(text), first_line
    while i < n:
        c = text[i]
        if c.isspace():
            line += c == "\n"
            i += 1
        elif text.startswith("///", i) and not text.startswith("////", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            toks.append(Tok("doc", text[i + 3:j], line))
            i = j
        elif text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith(("/*", "*/"), j):
                    depth, j = depth + (1 if text[j] == "/" else -1), j + 2
                else:
                    line, j = line + (text[j] == "\n"), j + 1
            if depth:
                raise SpecrError(f"{rel}:{line}: unterminated block comment")
            i = j
        elif c == '"':
            j, start = i + 1, line
            while j < n and text[j] != '"':
                if text[j] == "\\":
                    j += 2
                    continue
                line, j = line + (text[j] == "\n"), j + 1
            if j >= n:
                raise SpecrError(f"{rel}:{start}: unterminated string literal")
            toks.append(Tok("str", text[i:j + 1], start, text[i + 1:j]))
            i = j + 1
        elif c == "'":
            char = re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'", text[i:])
            m = char or re.match(r"'[A-Za-z_][A-Za-z0-9_]*", text[i:])
            if not m:
                raise SpecrError(f"{rel}:{line}: stray quote")
            toks.append(Tok("char" if char else "lifetime", m.group(0), line))
            i += m.end()
        elif c.isalpha() or c == "_":
            m = re.match(r"[A-Za-z_][A-Za-z0-9_]*", text[i:])
            toks.append(Tok("ident", m.group(0), line))
            i += m.end()
        elif c.isdigit():
            m = re.match(r"[0-9][0-9_]*(?:\.[0-9][0-9_]*(?![A-Za-z_.]))?(?:[a-z][a-z0-9]*)?", text[i:])
            toks.append(Tok("num", m.group(0), line))
            i += m.end()
        else:
            p = next((p for p in PUNCTS if text.startswith(p, i)), c)
            toks.append(Tok("punct", p, line))
            i += len(p)
    return toks


def code_fences(text: str, rel: str) -> list:
    """(first body line, body text, info string) for every ``` fence of a file."""
    lines, out, i = text.split("\n"), [], 0
    while i < len(lines):
        if lines[i].startswith("```"):
            j = next((k for k in range(i + 1, len(lines)) if lines[k].startswith("```")), None)
            if j is None:
                raise SpecrError(f"{rel}:{i + 1}: unterminated code fence")
            if lines[j].strip() != "```":
                raise SpecrError(f"{rel}:{j + 1}: a closing fence carries an info string")
            out.append((i + 2, "\n".join(lines[i + 1:j]), lines[i][3:].strip()))
            i = j + 1
        else:
            if lines[i].lstrip().startswith("```"):
                raise SpecrError(f"{rel}:{i + 1}: an indented code fence")
            i += 1
    return out


@dataclass
class Item:
    kind: str  # enum, struct, alias, trait, impl, fn, assoc-type, assoc-const, const, macro
    name: str
    line: int
    rel: str
    parent: object = None
    attrs: list = field(default_factory=list)
    generics: list = field(default_factory=list)
    variants: list = field(default_factory=list)  # (name, line, [(field name | None, line, type tokens)])
    shape: str = ""
    fields: list = field(default_factory=list)  # (name, line, type tokens)
    type_toks: list = field(default_factory=list)
    params: list = field(default_factory=list)  # (pattern tokens, type tokens)
    body: tuple = ()
    self_type: str = ""
    trait: str = ""
    children: list = field(default_factory=list)
    toks: list = field(default_factory=list)
    member_id: str = ""


class Parser:
    def __init__(self, toks: list, rel: str) -> None:
        self.t, self.i, self.rel = toks, 0, rel

    def peek(self, k: int = 0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def at(self, text: str, k: int = 0) -> bool:
        p = self.peek(k)
        return p is not None and p.text == text and p.kind in ("punct", "ident")

    def fail(self, message: str):
        p = self.peek()
        raise SpecrError(f"{self.rel}:{p.line if p else 'end'}: {message}")

    def expect(self, text: str):
        if not self.at(text):
            self.fail(f"expected {text!r}, found {self.peek().text if self.peek() else 'the end of the block'!r}")
        self.i += 1
        return self.t[self.i - 1]

    def ident(self):
        p = self.peek()
        if p is None or p.kind != "ident":
            self.fail(f"expected an identifier, found {p.text if p else 'the end of the block'!r}")
        self.i += 1
        return p

    def close_of(self, i: int) -> int:
        stack = []
        for j in range(i, len(self.t)):
            tk = self.t[j]
            if tk.kind == "punct" and tk.text in OPEN:
                stack.append(OPEN[tk.text])
            elif tk.kind == "punct" and tk.text in CLOSE:
                if not stack or stack[-1] != tk.text:
                    raise SpecrError(f"{self.rel}:{tk.line}: unbalanced {tk.text!r}")
                stack.pop()
                if not stack:
                    return j
        raise SpecrError(f"{self.rel}:{self.t[i].line}: unclosed {self.t[i].text!r}")

    def angles(self) -> list:
        start, depth = self.i, 0
        while self.i < len(self.t):
            tk = self.t[self.i]
            if tk.kind == "punct" and tk.text in OPEN:
                self.i = self.close_of(self.i) + 1
                continue
            if tk.kind == "punct":
                depth += {"<": 1, "<<": 2, ">": -1, ">>": -2}.get(tk.text, 0)
                if depth < 0:
                    self.fail("unbalanced angle brackets")
                if depth == 0:
                    self.i += 1
                    return self.t[start + 1:self.i - 1]
            self.i += 1
        self.fail("unclosed angle bracket")

    def attrs_and_docs(self) -> list:
        attrs = []
        while self.i < len(self.t):
            p = self.t[self.i]
            if p.kind == "doc":
                self.i += 1
            elif p.kind == "punct" and p.text == "#":
                j = self.i + 1 + self.at("!", 1)
                if j >= len(self.t) or self.t[j].text != "[":
                    self.fail("`#` not followed by an attribute")
                close = self.close_of(j)
                attrs.append(self.t[j + 1:close])
                self.i = close + 1
            else:
                return attrs
        return attrs

    def visibility(self) -> None:
        if self.at("pub"):
            self.i += 1
            if self.at("("):
                self.i = self.close_of(self.i) + 1

    def type_until(self, stops: set) -> list:
        start, depth = self.i, 0
        while self.i < len(self.t):
            tk = self.t[self.i]
            if tk.kind == "punct":
                if depth == 0 and (tk.text in stops or tk.text in CLOSE):
                    break
                if tk.text in OPEN:
                    self.i = self.close_of(self.i) + 1
                    continue
                if tk.text == "<":
                    depth += 1
                elif tk.text in (">", ">>") and depth > 0:
                    depth -= 1 if tk.text == ">" else 2
            elif tk.kind == "ident" and depth == 0 and tk.text in stops:
                break
            self.i += 1
        return self.t[start:self.i]

    @staticmethod
    def generic_names(inner: list) -> list:
        names, depth, expect = [], 0, True
        for tk in inner:
            depth += {"<": 1, "(": 1, "[": 1, ">": -1, ")": -1, "]": -1, ">>": -2}.get(tk.text, 0)
            if tk.text == "," and depth == 0:
                expect = True
            elif expect and depth == 0 and tk.kind in ("ident", "lifetime") and tk.text != "const":
                names.append(tk.text)
                expect = False
        return names

    def items(self, end: int, parent=None) -> list:
        out = []
        handlers = {"use": self.use_item, "enum": self.enum_item, "struct": self.struct_item, "type": self.type_item,
                    "const": self.const_item, "trait": self.trait_item, "impl": self.impl_item, "fn": self.fn_item,
                    "macro_rules": self.macro_item}
        while self.i < end:
            attrs = self.attrs_and_docs()
            if self.i >= end:
                break
            self.visibility()
            p = self.peek()
            if p.kind == "punct" and p.text == ";":
                self.i += 1
                continue
            if p.kind != "ident" or p.text not in handlers:
                self.fail(f"unexpected {p.text!r} at item position")
            item = handlers[p.text](attrs, parent)
            if item is not None:
                out.append(item)
        return out

    def use_item(self, attrs, parent):
        while self.i < len(self.t) and not self.at(";"):
            self.i += 1
        self.expect(";")

    def macro_item(self, attrs, parent):
        self.expect("macro_rules")
        self.expect("!")
        name = self.ident()
        if not self.at("{"):
            self.fail("macro_rules! without a brace body")
        close = self.close_of(self.i)
        item = Item("macro", name.text, name.line, self.rel, parent, attrs, body=(self.i, close))
        self.i = close + 1
        return item

    def components(self, close: int, named: bool) -> list:
        comps = []
        while self.i < close:
            self.attrs_and_docs()
            if self.i >= close:
                break
            self.visibility()
            name = None
            if named:
                name = self.ident()
                self.expect(":")
            tt = self.type_until({","})
            if not tt:
                self.fail("an empty component")
            comps.append((name.text if name else None, name.line if name else tt[0].line, tt))
            if self.at(","):
                self.i += 1
            elif self.i != close:
                self.fail(f"expected ',' after {name.text if name else 'a component'}")
        return comps

    def braced_or_tuple(self) -> tuple[str, list]:
        if not (self.at("(") or self.at("{")):
            return "", []
        named, c = self.at("{"), self.close_of(self.i)
        self.i += 1
        comps = self.components(c, named)
        self.i = c + 1
        return ("named" if named else "tuple"), comps

    def enum_item(self, attrs, parent):
        self.expect("enum")
        name = self.ident()
        item = Item("enum", name.text, name.line, self.rel, parent, attrs)
        if self.at("<"):
            item.generics = self.generic_names(self.angles())
        if not self.at("{"):
            self.fail(f"enum {name.text} without a brace body")
        close = self.close_of(self.i)
        self.i += 1
        while self.i < close:
            self.attrs_and_docs()
            if self.i >= close:
                break
            variant = self.ident()
            if self.at("="):
                self.fail("an explicit enum discriminant")
            item.variants.append((variant.text, variant.line, self.braced_or_tuple()[1]))
            if self.at(","):
                self.i += 1
            elif self.i != close:
                self.fail(f"expected ',' after variant {variant.text}")
        self.i = close + 1
        return item

    def struct_item(self, attrs, parent):
        self.expect("struct")
        name = self.ident()
        item = Item("struct", name.text, name.line, self.rel, parent, attrs)
        if self.at("<"):
            item.generics = self.generic_names(self.angles())
        if self.at(";"):
            item.shape = "unit"
        else:
            item.shape, comps = self.braced_or_tuple()
            if not item.shape:
                self.fail(f"struct {name.text}: unexpected {self.peek().text!r}")
            item.fields = comps if item.shape == "named" else [(str(k), line, tt) for k, (_, line, tt) in enumerate(comps)]
        if item.shape != "named":
            self.expect(";")
        return item

    def type_item(self, attrs, parent):
        self.expect("type")
        name = self.ident()
        item = Item("alias" if parent is None else "assoc-type", name.text, name.line, self.rel, parent, attrs)
        if self.at("<"):
            item.generics = self.generic_names(self.angles())
        if self.at(":"):
            self.i += 1
            self.type_until({"=", ";"})
        if self.at("="):
            self.i += 1
            item.type_toks = self.type_until({";"})
        self.expect(";")
        return item

    def const_item(self, attrs, parent):
        self.expect("const")
        name = self.ident()
        item = Item("assoc-const" if parent is not None else "const", name.text, name.line, self.rel, parent, attrs)
        self.expect(":")
        item.type_toks = self.type_until({"=", ";"})
        while self.i < len(self.t) and not self.at(";"):
            self.i = self.close_of(self.i) + 1 if self.peek().kind == "punct" and self.peek().text in OPEN else self.i + 1
        self.expect(";")
        return item

    def trait_item(self, attrs, parent):
        self.expect("trait")
        name = self.ident()
        item = Item("trait", name.text, name.line, self.rel, parent, attrs)
        if self.at("<"):
            item.generics = self.generic_names(self.angles())
        if self.at(":"):
            self.i += 1
            self.type_until({"{", "where"})
        if not self.at("{"):
            self.fail(f"trait {name.text} without a body")
        close = self.close_of(self.i)
        self.i += 1
        item.children = self.items(close, item)
        self.i = close + 1
        return item

    def impl_item(self, attrs, parent):
        keyword = self.expect("impl")
        item = Item("impl", "", keyword.line, self.rel, parent, attrs)
        if self.at("<"):
            item.generics = self.generic_names(self.angles())
        first = self.type_until({"for", "{", "where"})
        if self.at("for"):
            self.i += 1
            item.trait, item.self_type = type_head(first), type_head(self.type_until({"{", "where"}))
        else:
            item.self_type = type_head(first)
        if not item.self_type:
            self.fail("impl without a self type")
        if self.at("where"):
            self.type_until({"{"})
        if not self.at("{"):
            self.fail("impl without a body")
        close = self.close_of(self.i)
        self.i += 1
        item.children = self.items(close, item)
        self.i = close + 1
        return item

    def fn_item(self, attrs, parent):
        self.expect("fn")
        name = self.ident()
        item = Item("fn", name.text, name.line, self.rel, parent, attrs)
        if self.at("<"):
            item.generics = self.generic_names(self.angles())
        if not self.at("("):
            self.fail(f"fn {name.text} without parameters")
        close = self.close_of(self.i)
        self.i += 1
        while self.i < close:
            start, depth, colon = self.i, 0, None
            while self.i < close:
                tk = self.peek()
                if tk.kind == "punct" and tk.text in OPEN:
                    self.i = self.close_of(self.i) + 1
                    continue
                if tk.kind == "punct":
                    if tk.text == "<":
                        depth += 1
                    elif tk.text in (">", ">>") and depth:
                        depth -= 1 if tk.text == ">" else 2
                    elif tk.text == ":" and depth == 0 and colon is None:
                        colon = self.i
                    elif tk.text == "," and depth == 0:
                        break
                self.i += 1
            item.params.append((self.t[start:self.i], []) if colon is None else (self.t[start:colon], self.t[colon + 1:self.i]))
            if self.i < close and self.at(","):
                self.i += 1
        self.i = close + 1
        if self.at("->"):
            self.i += 1
            self.type_until({"{", ";", "where"})
        if self.at("where"):
            self.type_until({"{", ";"})
        if self.at(";"):
            self.i += 1
            return item
        if not self.at("{"):
            self.fail(f"fn {name.text}: expected a body")
        item.body = (self.i, self.close_of(self.i))
        self.i = item.body[1] + 1
        return item


def type_head(tokens: list) -> str:
    """The last top-level identifier of a type path (`&mut`, `dyn`, `crate::` skipped)."""
    idents, depth = [], 0
    for tk in tokens:
        depth += {"<": 1, ">": -1, ">>": -2}.get(tk.text, 0)
        if depth == 0 and tk.kind == "ident" and tk.text not in PATH_PREFIXES | {"mut", "dyn"}:
            idents.append(tk.text)
    return idents[-1] if idents else ""


def type_names(tokens: list, generics: set) -> list:
    """(name, token) for every type name a type mentions, except a generic parameter, a path
    prefix and a projection of a generic parameter (`M::Provenance`)."""
    out = []
    for k, tk in enumerate(tokens):
        if tk.kind != "ident" or tk.text in generics or tk.text in PATH_PREFIXES or tk.text in ("mut", "dyn"):
            continue
        if (k + 1 < len(tokens) and tokens[k + 1].text == "::") or (k >= 2 and tokens[k - 1].text == "::" and tokens[k - 2].text in generics):
            continue
        out.append((tk.text, tk))
    return out


def read_spec(tree) -> tuple[list, list, list, list]:
    """(Markdown files, items, fence info strings, problems) for every file under spec/."""
    files, items, fences, problems = [], [], [], []
    listed = tree.files("spec/")
    tree.prefetch([r for r in listed if r.endswith(".md")])
    for rel in listed:
        if not rel.endswith(".md"):
            problems.append(f"{rel}: a file under spec/ that is not Markdown is not read by the specr reader")
            continue
        files.append(rel)
        text = tree.text(rel)
        if text is None:
            problems.append(f"{rel}: not readable UTF-8 at the pin")
            continue
        try:
            for first, body, info in code_fences(text, rel):
                fences.append(info)
                if info != "rust":
                    problems += [f"{rel}:{first + k}: a fence with info string {info!r} holds a specr item; only ```rust fences are read"
                                 for k, line in enumerate(body.split("\n")) if NON_RUST_ITEM.match(line)]
                    continue
                toks = tokenize(body, first, rel)
                for item in Parser(toks, rel).items(len(toks)):
                    attach(item, toks)
                    items.append(item)
        except SpecrError as error:
            problems.append(str(error))
    return files, items, fences, problems


def attach(item: Item, toks: list) -> None:
    item.toks = toks
    for child in item.children:
        child.parent = item
        attach(child, toks)


# --------------------------------------------------------------------------
# the universe
# --------------------------------------------------------------------------


@dataclass
class Member:
    id: str
    kind: str
    path: str
    rel: str
    line: int
    token: str
    klass: str = ""  # syntax | domain | operation | derived-case | derived-dispatcher
    derived_from: str = ""


def pattern_variant(tokens: list, enums: dict) -> tuple | None:
    """The innermost `Enum::Variant` a case pattern names."""
    if len(tokens) < 3 or tokens[0].kind != "ident" or tokens[1].text != "::" or tokens[2].kind != "ident" or tokens[0].text not in enums:
        return None
    inner = pattern_variant(tokens[4:], enums) if len(tokens) > 3 and tokens[3].text == "(" else None
    return inner or (tokens[0].text, tokens[2].text)


def derive_universe(items: list, externals: dict, f: C.Findings) -> dict:
    members, defs = {}, {}

    def add(m: Member) -> None:
        if m.id in members:
            f.add("UNIVERSE", f"{m.id} is defined twice ({members[m.id].rel}:{members[m.id].line} and {m.rel}:{m.line})")
        else:
            members[m.id] = m

    def walk(its: list) -> None:
        for it in its:
            if it.kind in ("enum", "struct", "alias", "trait") and it.parent is None:
                defs.setdefault(it.name, it)
            walk(it.children)

    walk(items)
    enums = {n: it for n, it in defs.items() if it.kind == "enum"}
    for it in items:
        if it.kind in ("enum", "struct", "alias", "trait"):
            add(Member(f"def:{it.name}", "def", it.name, it.rel, it.line, it.name))
            for vname, vline, _ in it.variants:
                add(Member(f"variant:{it.name}::{vname}", "variant", f"{it.name}::{vname}", it.rel, vline, vname))
            for fname, fline, tt in it.fields:
                add(Member(f"field:{it.name}::{fname}", "field", f"{it.name}::{fname}", it.rel, fline, fname if it.shape == "named" else type_head(tt)))
        elif it.kind == "macro":
            it.member_id = f"macro:{it.name}!"
            add(Member(it.member_id, "macro", f"{it.name}!", it.rel, it.line, it.name))
        elif it.kind == "const":
            add(Member(f"assoc-const:{it.name}", "assoc-const", it.name, it.rel, it.line, it.name))
    fns, dispatchers = [], {}

    def collect(its: list, owner: str | None, self_type: str | None) -> None:
        for it in its:
            if it.kind == "fn":
                fns.append((it, owner, self_type))
            elif it.kind in ("assoc-type", "assoc-const"):
                add(Member(f"{it.kind}:{owner}::{it.name}", it.kind, f"{owner}::{it.name}", it.rel, it.line, it.name))
            elif it.kind == "trait":
                collect(it.children, it.name, None)
            elif it.kind == "impl":
                collect(it.children, f"<{it.self_type} as {it.trait}>" if it.trait else it.self_type, it.self_type)

    collect(items, None, None)
    argmatch = lambda it: [a for a in it.attrs if [t.text for t in a][:3] == ["specr", "::", "argmatch"]]  # noqa: E731
    for it, owner, self_type in fns:
        for attr in argmatch(it):
            texts = [t.text for t in attr]
            well_formed = len(texts) == 6 and texts[3] == "(" and texts[5] == ")"
            index = next((k for k, (pat, _) in enumerate(it.params) if well_formed and [t.text for t in pat][-1:] == [texts[4]]), None)
            ptype = (type_head(it.params[index][1]) if it.params[index][1] else "") if index is not None else ""
            if ptype == "Self" or (index is not None and texts[4] == "self" and not ptype):
                ptype = self_type or ""
            if index is None or ptype not in enums:
                f.add("UNIVERSE", f"{it.rel}:{it.line}: argmatch {' '.join(texts)} names no parameter of fn {it.name} whose type is a MiniRust enum")
                continue
            path = f"{owner}::{it.name}" if owner else it.name
            dispatchers[(owner, it.name)] = (index, ptype)
            it.member_id = f"dispatcher:{path}"
            add(Member(it.member_id, "fn", path, it.rel, it.line, it.name, "derived-dispatcher", f"def:{ptype}"))
    for it, owner, self_type in fns:
        if argmatch(it):
            continue
        path = f"{owner}::{it.name}" if owner else it.name
        if (owner, it.name) in dispatchers:
            index, enum = dispatchers[(owner, it.name)]
            named = pattern_variant(it.params[index][0], enums) if index < len(it.params) else None
            if named is None or named[1] not in [v[0] for v in enums[named[0]].variants] or it.params[index][0][0].text != enum:
                f.add("UNIVERSE", f"{it.rel}:{it.line}: fn {path} shares its name with an argmatch dispatcher over {enum} but its parameter {index} names no variant of it")
                continue
            it.member_id = f"case:{path}[{named[0]}::{named[1]}]"
            add(Member(it.member_id, "fn", f"{path}[{named[0]}::{named[1]}]", it.rel, it.line, it.name, "derived-case", f"variant:{named[0]}::{named[1]}"))
            continue
        if any(pattern_variant(pat, enums) for pat, _ in it.params):
            f.add("UNIVERSE", f"{it.rel}:{it.line}: fn {path} matches a variant in a parameter but no argmatch dispatcher owns it")
        it.member_id = f"fn:{path}"
        add(Member(it.member_id, "fn", path, it.rel, it.line, it.name))
    # SYNTAX: definitions reachable from Program through variant and field types, and the
    # external names so reached (at the first line that names each).
    reach, stack, reached_external = set(), [SYNTAX_ROOT], {}
    if SYNTAX_ROOT not in defs:
        f.add("UNIVERSE", f"MiniRust defines no `{SYNTAX_ROOT}`")
    while stack:
        name = stack.pop()
        if name in reach or name not in defs:
            continue
        reach.add(name)
        it = defs[name]
        for tt in [tt for _, _, comps in it.variants for _, _, tt in comps] + [tt for _, _, tt in it.fields] + ([it.type_toks] if it.kind == "alias" else []):
            for ref, tk in type_names(tt, set(it.generics)):
                if ref in defs:
                    stack.append(ref)
                else:
                    reached_external[ref] = min(reached_external.get(ref, (it.rel, tk.line)), (it.rel, tk.line))
    for name in sorted(set(reached_external) - set(externals)):
        f.add("UNIVERSE", f"syntax reaches `{name}` ({':'.join(map(str, reached_external[name]))}), which MiniRust does not define and no [[external]] row classifies")
    for name in sorted(set(externals) - set(reached_external)):
        f.add("UNIVERSE", f"external {name}: syntax reaches no type of that name (stale)")
    written = {}  # (enum, variant) -> first (rel, line) of `Enum::Variant` in a fence
    for rel, toks in {id(it.toks): (it.rel, it.toks) for it in items}.values():
        for k in range(len(toks) - 2):
            if toks[k].text in externals and toks[k + 1].text == "::" and re.fullmatch(r"[A-Z][A-Za-z0-9]*[a-z][A-Za-z0-9]*", toks[k + 2].text):
                key = (toks[k].text, toks[k + 2].text)
                written[key] = min(written.get(key, (rel, toks[k + 2].line)), (rel, toks[k + 2].line))
    for name, row in externals.items():
        if row.get("class") != "enum":
            continue
        if name in reached_external:
            add(Member(f"def:{name}", "def", name, *reached_external[name], name))
        for variant in row.get("variants") or []:
            if (name, variant) not in written:
                f.add("UNIVERSE", f"external {name}: its variant {variant} is written `{name}::{variant}` in no fence at the pin")
            else:
                add(Member(f"variant:{name}::{variant}", "variant", f"{name}::{variant}", *written[(name, variant)], variant))
        reach.add(name)
    for (name, variant), (rel, line) in sorted(written.items()):
        if externals[name].get("class") != "enum" or variant not in (externals[name].get("variants") or []):
            f.add("UNIVERSE", f"{rel}:{line}: `{name}::{variant}` names no variant the [[external]] row {name} declares")
    for m in members.values():
        m.klass = m.klass or (("syntax" if m.path.split("::")[0] in reach else "domain") if m.kind in ("def", "variant", "field") else "operation")
    return members


def ub_sites(items: list, members: dict, f: C.Findings) -> tuple[dict, dict]:
    """(site "path:line" of the message literal -> message, site -> enclosing member id)."""
    sites, owners, blocks, bodies = {}, {}, {}, []

    def walk(its: list) -> None:
        for it in its:
            blocks.setdefault(id(it.toks), (it.rel, it.toks))
            if it.kind in ("fn", "macro") and it.body:
                bodies.append((it.toks, it.body[0], it.body[1], it))
            walk(it.children)

    walk(items)
    ub_variant = members.get("variant:TerminationInfo::Ub")
    for rel, toks in blocks.values():
        spans = [(a, b, it) for t, a, b, it in bodies if t is toks]
        parser = Parser(toks, rel)
        for k, tk in enumerate(toks):
            if tk.kind != "ident" or tk.text not in ("Ub", "throw_ub", "ensure_else_ub"):
                continue
            where = f"{rel}:{tk.line}"
            inside = [s for s in spans if s[0] < k < s[1]]
            encl = min(inside, key=lambda s: s[1] - s[0])[2] if inside else None
            nxt = [t.text for t in toks[k + 1:k + 3]]
            if tk.text == "Ub":
                if not ((ub_variant is not None and (ub_variant.rel, ub_variant.line) == (rel, tk.line) and encl is None)
                        or (encl is not None and encl.kind == "macro" and encl.name == "throw_ub" and encl.parent is None)):
                    f.add("UB-MECHANISM", f"{where}: `Ub` named outside the TerminationInfo::Ub variant and the throw_ub! body")
                continue
            if tk.text == "throw_ub" and k >= 2 and toks[k - 1].text == "!" and toks[k - 2].text == "macro_rules" and encl is None:
                continue
            if tk.text == "ensure_else_ub" and k >= 1 and toks[k - 1].text == "fn":
                if encl is not None:
                    f.add("UB-MECHANISM", f"{where}: an ensure_else_ub defined inside another item")
                continue
            if (nxt != ["!", "("]) if tk.text == "throw_ub" else (nxt[:1] != ["("]):
                f.add("UB-MECHANISM", f"{where}: `{tk.text}` used other than as its definition or a parenthesized call")
                continue
            open_i = k + 2 if tk.text == "throw_ub" else k + 1
            args = split_args(toks, open_i, parser.close_of(open_i))
            arg = (args[0] if tk.text == "throw_ub" else args[-1]) if args else []
            if len(arg) != 1 or arg[0].kind != "str":
                f.add("UB-MECHANISM", f"{where}: {tk.text} whose {'first' if tk.text == 'throw_ub' else 'last'} argument is not a string literal")
                continue
            if tk.text == "throw_ub" and arg[0].value == "{}":
                if not (encl is not None and encl.kind == "fn" and encl.name == "ensure_else_ub" and encl.parent is None):
                    f.add("UB-MECHANISM", f"{where}: throw_ub!(\"{{}}\", ..) outside the ensure_else_ub helper")
                continue
            site = f"{rel}:{arg[0].line}"
            if site in sites:
                f.add("UB-MECHANISM", f"{site}: two UB messages on one line")
            sites[site] = arg[0].value
            if encl is None or encl.member_id not in members:
                f.add("UB-MECHANISM", f"{site}: a UB site outside every fn and macro member of the universe")
            else:
                owners[site] = encl.member_id
    return sites, owners


def split_args(toks: list, open_i: int, close_i: int) -> list:
    args, current, depth = [], [], 0
    for tk in toks[open_i + 1:close_i]:
        if tk.kind == "punct":
            depth += (tk.text in OPEN) - (tk.text in CLOSE)
            if tk.text == "," and depth == 0:
                args.append(current)
                current = []
                continue
        current.append(tk)
    return args + ([current] if current else [])


# --------------------------------------------------------------------------
# the vocabulary and the design
# --------------------------------------------------------------------------


@dataclass
class Vocabulary:
    names: dict = field(default_factory=dict)  # name -> "inductive" | "entry" | "ub_reason"
    claims: dict = field(default_factory=dict)  # member id -> the names citing it
    not_in_core: dict = field(default_factory=dict)  # member id -> replacement names
    ub_sites: dict = field(default_factory=dict)  # site -> (reason, message)
    extensions: list = field(default_factory=list)
    adopted_prefix: str = ""


def load_vocabulary(f: C.Findings, path: Path, members: dict, sites: dict) -> Vocabulary:
    vocab = Vocabulary()
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        f.add("VOCABULARY", f"{path}: {error}")
        return vocab
    by_ref = {}
    for m in members.values():
        if m.kind in ("def", "variant", "field"):
            by_ref.setdefault((f"{m.rel}:{m.line}", m.token), []).append(m.id)

    def member_at(where: str, ref: object, token: object, kinds: tuple) -> str | None:
        found = [m for m in by_ref.get((ref, token), []) if members[m].kind in kinds]
        if len(found) != 1:
            f.add("VOCABULARY", f"{where}: cites {ref} {token!r}, which is not exactly one MiniRust {'/'.join(kinds)} of the reader's universe ({found})")
        return found[0] if len(found) == 1 else None

    for kind in ("inductive", "entry", "ub_reason"):
        for row in data.get(kind, []):
            name = row.get("name")
            if not isinstance(name, str):
                continue
            vocab.names[name] = kind
            if row.get("origin") == "trust-extension":
                vocab.extensions.append(name)
            elif row.get("origin") == "minirust" and kind != "ub_reason":
                mid = member_at(f"vocabulary {kind} {name}", row.get("minirust_ref"), row.get("minirust_token"), ("def",) if kind == "inductive" else ("variant", "field"))
                if mid:
                    vocab.claims.setdefault(mid, set()).add(name)
                    if row.get("shape") == "wrapper" and f"field:{members[mid].path}::0" in members:
                        vocab.claims.setdefault(f"field:{members[mid].path}::0", set()).add(name)
            if kind == "inductive" and row.get("minirust_split_from"):
                if f"def:{row['minirust_split_from']}" not in members:
                    f.add("VOCABULARY", f"vocabulary inductive {name} is split from {row['minirust_split_from']!r}, which MiniRust does not define")
                else:
                    vocab.claims.setdefault(f"def:{row['minirust_split_from']}", set()).add(name)
            for site in row.get("sites", []) if kind == "ub_reason" else []:
                if site.get("ref") in vocab.ub_sites:
                    f.add("VOCABULARY", f"UB site {site.get('ref')} is listed by two vocabulary reasons")
                vocab.ub_sites[site.get("ref")] = (name, site.get("message"))
    for row in data.get("not_in_core", []):
        mid = member_at("vocabulary not_in_core", row.get("minirust_ref"), row.get("minirust_token"), ("def", "variant", "field"))
        if mid:
            vocab.not_in_core[mid] = set(row.get("replaced_by", [])).union(*[set(v) for v in (row.get("payload") or {}).values()])
    for ref in sorted(set(sites) | set(vocab.ub_sites)):
        if (vocab.ub_sites.get(ref) or (None, None))[1] != sites.get(ref):
            f.add("VOCABULARY", f"UB site {ref}: the pin raises {sites.get(ref)!r}, the vocabulary lists {(vocab.ub_sites.get(ref) or (None, None))[1]!r}")
    vocab.adopted_prefix = (data.get("adopted") or {}).get("prefix") or ""
    if not vocab.adopted_prefix:
        f.add("VOCABULARY", "the vocabulary has no [adopted] naming rule with a prefix")
    return vocab


def design_facts(f: C.Findings, text: str) -> tuple[set, list]:
    """The LD numbers of the design's `| LD-n |` rows, and the extensions its one extension sentence lists."""
    lines = text.split("\n")
    lds = [int(m.group(1)) for m in (re.match(r"^\| LD-([1-9][0-9]*) \|", line) for line in lines) if m]
    if not lds or len(set(lds)) != len(lds):
        f.add("DESIGN", f"the design's LD rows are missing or repeated: {lds}")
    starts = [k for k, line in enumerate(lines) if EXTENSION_START in line]
    body = " ".join(line.strip() for line in lines[starts[0]:starts[0] + 6]) if len(starts) == 1 else ""
    lead, end = body.find(EXTENSION_LEAD), body.find(EXTENSION_END)
    if lead < 0 or end < lead:
        f.add("DESIGN", "the design's extension sentence (`generated core: <items>. Each extension`) is not found once")
        return set(lds), []
    head, _, last = body[lead + len(EXTENSION_LEAD):end].rpartition(" and ")
    items = [i.strip() for i in head.split(", ")] + [last.strip()]
    if not all(items) or len(set(items)) != len(items):
        f.add("DESIGN", f"the design's extension list does not split into distinct items: {items}")
    return set(lds), items


def design_ld_lines(text: str) -> dict:
    """`design:<line>` (1-based) of each `| LD-n |` row of the design -> n."""
    out = {}
    for number, line in enumerate(text.split("\n"), 1):
        m = re.match(r"^\| LD-([1-9][0-9]*) \|", line)
        if m:
            out[f"design:{number}"] = int(m.group(1))
    return out


def load_rulings(f: C.Findings, path: Path) -> dict:
    """LD-n -> (ruling, ruling_record) from the Language Decisions ledger's [[ratify]] rows. An
    unreadable ledger, or a ratify row out of shape, is a RULING violation: nothing then counts as
    ruled, so no row can pass by the ledger being missing."""
    try:
        data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        f.add("RULING", f"{path}: {error}; the ruling states cannot be read")
        return {}
    out = {}
    for row in data.get("ratify", []):
        item = row.get("item") if isinstance(row, dict) else None
        m = LD.match(str(item))
        if m is None:
            continue  # I-PRECEDENCE and other ratified items are not LD rows
        ruling, record = row.get("ruling"), row.get("ruling_record") or ""
        if ruling not in RULINGS or (ruling != "pending") != bool(str(record).strip()):
            f.add("RULING", f"{path}: [[ratify]] {item}: ruling {ruling!r} is not one of {RULINGS} with a ruling_record exactly when ruled")
            continue
        if int(m.group(1)) in out:
            f.add("RULING", f"{path}: [[ratify]] {item} is listed twice")
        out[int(m.group(1))] = (ruling, str(record))
    return out


# --------------------------------------------------------------------------
# the checker
# --------------------------------------------------------------------------


class Checker:
    def __init__(self, options: Options) -> None:
        self.o, self.f, self.counts = options, C.Findings(), {}

    def add(self, kind: str, message: str) -> None:
        self.f.add(kind, message)

    def load(self) -> bool:
        o = self.o
        self.pins = C.load_pins(o.pins or o.repo / C.PINS_REL)
        trees = {"worktree": C.GitTree(o.repo, "HEAD")}
        missing = [name for name, source in READS.items() if source not in o.trees]
        clones = C.locate_clones(self.pins, missing, o.clones) if missing else {}
        trees.update({READS[name]: C.GitTree(path, self.pins.sources[name].revision) for name, path in clones.items()})
        trees.update(o.trees)
        self.trees, self.resolver = trees, C.Resolver(o.repo, trees)
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
        return True

    def cite(self, kind: str, where: str, cites: object) -> None:
        for c in cites if isinstance(cites, list) else [cites]:
            if not isinstance(c, dict) or set(c) != {"ref", "quote"}:
                self.add("TABLE", f"{where}: a citation is {{ref, quote}}, not {c!r}")
            else:
                self.resolver.resolve(self.f, kind, where, c["ref"], c["quote"])

    def shape(self) -> None:
        d = self.data
        for key in sorted(set(d) - TABLE_KEYS):
            self.add("TABLE", f"top-level key {key!r} is not part of the schema")
        for key, value in (("schema", SCHEMA), ("design", C.DESIGN_REL), ("vocabulary", VOCABULARY_REL)):
            if d.get(key) != value:
                self.add("TABLE", f"{key} is not {value}")
        C.repeated_elements(self.f, "TABLE", "the table", {k: v for k, v in d.items() if k in ("external", "row")})
        externals = [r for r in d.get("external", []) if isinstance(r, dict)]
        for row in externals:
            where = f"external {row.get('name')}"
            if set(row) - EXTERNAL_KEYS or {"name", "class", "cites", "why"} - set(row) or row.get("class") not in EXTERNAL_CLASSES \
                        or (row.get("class") == "enum") != isinstance(row.get("variants"), list) or not row.get("cites") or not self.text(row.get("why"), where):
                self.add("TABLE", f"{where}: an external row is {{name, class in {EXTERNAL_CLASSES}, variants (enum only), cites, why}}")
            self.cite("EXTERNAL", where, row.get("cites"))
        self.externals = C.unique_rows(self.f, "TABLE", "external", externals, lambda r: r.get("name"))
        rows = []
        for index, row in enumerate(d.get("row", [])):
            where = f"row[{index}] {row.get('id') if isinstance(row, dict) else ''}"
            if not isinstance(row, dict) or set(row) - ROW_KEYS or ROW_REQUIRED - set(row) or not ROW_ID.match(str(row.get("id"))):
                self.add("TABLE", f"{where}: a row is {{id R-.., title, members, note[, cites][, divergence][, rulings]}}")
                continue
            where = f"row {row['id']}"
            if not self.text(row["title"], where) or not self.text(row["note"], where) or not isinstance(row["members"], list) or not row["members"]:
                self.add("TABLE", f"{where}: title and note are text and members a non-empty list")
                continue
            if "cites" in row:
                self.cite("CITE", where, row["cites"] or [None])
            rows.append(row)
        self.rows = C.unique_rows(self.f, "TABLE", "row", rows, lambda r: r["id"])

    def text(self, value: object, where: str | None = None) -> bool:
        ok = isinstance(value, str) and bool(value.strip())
        if ok and where and C.FREE_TEXT_CITATION.search(value):
            self.add("TABLE", f"{where}: free text carries a line citation no predicate checks; cite it in `cites`")
        return ok

    def universe(self) -> None:
        mr = self.trees["minirust"]
        files, items, fences, problems = read_spec(mr)
        for problem in problems:
            self.add("UNIVERSE", problem)
        self.members = derive_universe(items, self.externals, self.f)
        self.sites, self.owners = ub_sites(items, self.members, self.f)
        c = self.counts
        c.update({"files": len(files), "fences.rust": fences.count("rust"), "fences.other": len(fences) - fences.count("rust"), "ub-sites": len(self.sites)})
        for m in self.members.values():
            c[f"members.{m.kind}.{m.klass}"] = c.get(f"members.{m.kind}.{m.klass}", 0) + 1
        self.vocab = load_vocabulary(self.f, self.o.vocabulary or self.o.repo / VOCABULARY_REL, self.members, self.sites)
        design = self.trees.get("design") or self.trees["worktree"]
        design_text = design.text(C.DESIGN_REL) or ""
        self.lds, self.design_extensions = design_facts(self.f, design_text)
        self.ld_lines = design_ld_lines(design_text)

    def mapping(self) -> None:
        v, c = self.vocab, self.counts
        claims, self.mapping_of, kept = {}, {}, {}
        extension_ids = {f"extension:{n}" for n in v.extensions} | {f"design-extension:{i}" for i in self.design_extensions}
        for rid, row in self.rows.items():
            where, dv = f"row {rid}", row.get("divergence")
            if dv is not None:
                self.divergence(where, dv)
            kind = dv.get("kind") if isinstance(dv, dict) else None
            counterpart = set(dv.get("counterpart") or []) if isinstance(dv, dict) else set()
            c[f"rows.{kind or 'core'}"] = c.get(f"rows.{kind or 'core'}", 0) + 1
            if kind:
                c[f"members.{kind}"] = c.get(f"members.{kind}", 0) + len(row["members"])
            for entry in row["members"]:
                mid = entry.get("member") if isinstance(entry, dict) else None
                ewhere = f"{where} {mid}"
                if not isinstance(mid, str):
                    self.add("TABLE", f"{where}: a member is a table with a `member` id")
                    continue
                claims.setdefault(mid, []).append(rid)
                if mid in extension_ids or mid.startswith(("extension:", "design-extension:")):
                    if set(entry) != {"member"} or mid not in extension_ids:
                        self.add("MAPPING", f"{ewhere}: an extension member carries only `member` and is a vocabulary trust-extension name or an extension the design lists")
                    if kind != "trust-extends":
                        self.add("MAPPING", f"{ewhere}: a trust-extension name is claimed only by a trust-extends divergence")
                    self.mapping_of[mid] = ("divergence", rid)
                    continue
                if set(entry) - {"member", "ref", "token", "core"}:
                    self.add("TABLE", f"{ewhere}: keys {sorted(set(entry) - {'member', 'ref', 'token', 'core'})} are not part of a member")
                if mid.startswith("ub-site:"):
                    ref = mid[len("ub-site:"):]
                    reason = v.ub_sites.get(ref, (None,))[0]
                    if ref not in self.sites or entry.get("ref") != ref or entry.get("token") != self.sites[ref] or "core" in entry:
                        self.add("MAPPING", f"{ewhere}: not a UB site at the pin with ref {ref!r} and its message as token (stale)")
                    elif dv is None or reason not in counterpart or kind == "trust-extends":
                        self.add("MAPPING", f"{ewhere}: a UB site maps by derivation; only a divergence row other than trust-extends claims it as changed, naming its reason {reason}")
                    self.mapping_of[mid] = ("divergence", rid)
                    continue
                m = self.members.get(mid)
                if m is None or m.klass.startswith("derived"):
                    self.add("MAPPING", f"{ewhere}: {'a derived member maps as ' + m.derived_from if m else 'no such MiniRust member at the pin (stale or misspelled)'}")
                    continue
                if (entry.get("ref"), entry.get("token")) != (f"{m.rel}:{m.line}", m.token):
                    self.add("MAPPING", f"{ewhere}: ref/token {entry.get('ref')!r} {entry.get('token')!r} are stale; the pin has {m.rel}:{m.line} {m.token!r}")
                named = v.claims.get(mid, set())
                if dv is None:
                    self.core_member(ewhere, m, entry.get("core"), named)
                else:
                    if "core" in entry:
                        self.add("MAPPING", f"{ewhere}: a divergence row's member carries no core list")
                    for what, names in (("names", named), ("replaces by", v.not_in_core.get(mid, set()))):
                        if not names <= counterpart:
                            self.add("MAPPING", f"{ewhere}: the vocabulary {what} {sorted(names)}; the divergence's counterpart must name them")
                    self.mapping_of[mid] = ("divergence", rid)
            for ref in dv.get("kept_ub_sites", []) if isinstance(dv, dict) else []:
                if ref in kept:
                    self.add("MAPPING", f"{where} kept_ub_sites {ref!r}: listed as kept twice")
                kept[ref] = rid
        for mid, owners in sorted(claims.items()):
            if len(owners) > 1:
                self.add("MAPPING", f"{mid} is claimed by {len(owners)} rows: {owners}")
        self.completeness(claims, kept)

    def core_member(self, where: str, m: Member, core: object, named: set) -> None:
        v, c = self.vocab, self.counts
        if not isinstance(core, list) or not core or not all(isinstance(n, str) for n in core):
            self.add("MAPPING", f"{where}: a core row's member carries a non-empty list of Core names")
            return
        for name in core:
            if v.names.get(name) == "ub_reason":
                self.add("MAPPING", f"{where}: {name} is a UB reason, not a construct")
            elif name not in v.names and (name != v.adopted_prefix + m.path or m.klass == "syntax"):
                self.add("MAPPING", f"{where}: {name!r} is neither a Core vocabulary name nor this non-syntax member's own adopted name {v.adopted_prefix + m.path!r}")
        if m.id in v.not_in_core:
            self.add("MAPPING", f"{where}: the vocabulary has this member not_in_core, so it is a divergence, not a core mapping")
        elif m.klass == "syntax" and not named:
            self.add("MAPPING", f"{where}: a syntax member maps in a core row only to the Core names the vocabulary cites for it, and the vocabulary cites none; name it there or record a divergence")
        elif named and set(core) != named:
            self.add("MAPPING", f"{where}: the vocabulary names this member {sorted(named)}, the row maps it to {sorted(core)}")
        self.mapping_of[m.id] = ("core", tuple(core))
        c["core.members"] = c.get("core.members", 0) + 1
        c["core.adopted"] = c.get("core.adopted", 0) + (not all(n in v.names for n in core))

    def divergence(self, where: str, dv: object) -> None:
        if not isinstance(dv, dict) or set(dv) - DIVERGENCE_KEYS or {"kind", "explanation", "design_ref", "resolution"} - set(dv):
            self.add("MAPPING", f"{where}: a divergence is {{kind, explanation, design_ref, resolution[, counterpart][, kept_ub_sites]}}")
            return
        if dv["kind"] not in KINDS:
            self.add("MAPPING", f"{where}: divergence kind {dv['kind']!r} is not one of {KINDS}")
        if not self.text(dv["explanation"], where):
            self.add("MAPPING", f"{where}: a divergence carries an explanation")
        design = dv["design_ref"]
        if not isinstance(design, dict) or not str(design.get("ref", "")).startswith("design:"):
            self.add("MAPPING", f"{where}: design_ref is {{ref = \"design:<line>\", quote}}")
        self.cite("MAPPING", where, design)
        m = LD.match(str(dv["resolution"]))
        if dv["resolution"] != UPSTREAM and (m is None or int(m.group(1)) not in self.lds):
            self.add("MAPPING", f"{where}: resolution {dv['resolution']!r} is neither {UPSTREAM} nor an LD-n row of the design's LD table")
        for key in ("counterpart", "kept_ub_sites"):
            value = dv.get(key, ["-"])
            if not isinstance(value, list) or not value or not all(isinstance(x, str) for x in value):
                self.add("MAPPING", f"{where}: {key} is a non-empty list of names, or omitted")
        for name in dv.get("counterpart", []) if isinstance(dv.get("counterpart"), list) else []:
            if name not in self.vocab.names:
                self.add("MAPPING", f"{where}: counterpart {name!r} is not a Core vocabulary name")
        if dv["kind"] == "not-modeled-yet" and "counterpart" in dv:
            self.add("MAPPING", f"{where}: a not-modeled-yet divergence names no counterpart")
        c = self.counts
        c[f"rows.{dv['resolution']}"] = c.get(f"rows.{dv['resolution']}", 0) + 1

    def rulings(self) -> None:
        """RULING: no row contradicts a ruled Language Decisions entry (the proven-core plan's RM0)."""
        o, c = self.o, self.counts
        ruled = load_rulings(self.f, o.decisions or o.repo / DECISIONS_REL)
        c.update({"rulings.rows-resting": 0, "rulings.rejustified": 0})
        for rid, row in self.rows.items():
            where, dv = f"row {rid}", row.get("divergence")
            rests: dict = {}  # LD number -> what makes the row rest on it
            if isinstance(dv, dict):
                m = LD.match(str(dv.get("resolution")))
                if m:
                    rests.setdefault(int(m.group(1)), f"its resolution {dv['resolution']}")
                ref = (dv.get("design_ref") or {}).get("ref") if isinstance(dv.get("design_ref"), dict) else None
                if ref in self.ld_lines:
                    rests.setdefault(self.ld_lines[ref], f"its design_ref {ref}")
            for cite in row.get("cites") or [] if isinstance(row.get("cites"), list) else []:
                ref = cite.get("ref") if isinstance(cite, dict) else None
                if ref in self.ld_lines:
                    rests.setdefault(self.ld_lines[ref], f"its citation {ref}")
            justified = set()
            entries = row.get("rulings", [])
            if not isinstance(entries, list) or ("rulings" in row and not entries):
                self.add("RULING", f"{where}: rulings is a non-empty list of {{item = \"LD-n\", quote}}")
                entries = []
            for entry in entries:
                m = LD.match(str(entry.get("item"))) if isinstance(entry, dict) and set(entry) == {"item", "quote"} else None
                if m is None or not isinstance(entry.get("quote"), str) or not entry["quote"].strip():
                    self.add("RULING", f"{where}: a rulings entry is {{item = \"LD-n\", quote}}, not {entry!r}")
                    continue
                n = int(m.group(1))
                if n not in ruled or ruled[n][0] == "pending":
                    self.add("RULING", f"{where}: rulings names LD-{n}, which the ledger has not ruled (stale)")
                elif entry["quote"] not in ruled[n][1]:
                    self.add("RULING", f"{where}: rulings LD-{n}: the quote is not text of the ruling_record (stale)")
                elif n not in rests:
                    self.add("RULING", f"{where}: rulings names LD-{n}, which the row does not rest on (stale)")
                else:
                    justified.add(n)
            c["rulings.rows-resting"] += bool(set(rests) & set(ruled))
            c["rulings.rejustified"] += bool(justified)
            for n, why in sorted(rests.items()):
                if n not in ruled:
                    continue  # a Recorded decision; the ledger rules only the ones it lists
                ruling = ruled[n][0]
                if ruling == "pending" and why.startswith("its resolution"):
                    self.add("RULING", f"{where}: resolves to LD-{n}, whose ruling is pending in {DECISIONS_REL}; a divergence rests on a ruled decision or on {UPSTREAM}")
                elif ruling in OVERTURNED and n not in justified:
                    self.add("RULING", f"{where}: contradicts the ruled LD-{n}: {why} rests on the design's LD-{n} recommendation, which the ledger ruled {ruling!r}; "
                                       f"retire the row, or re-justify it against the ruling with a rulings entry quoting its ruling_record")

    def completeness(self, claims: dict, kept: dict) -> None:
        """Map what derives, then refuse every universe member, UB site and extension that no row and
        no derivation maps, each as one UNMAPPED violation. The published Unmapped column counts
        exactly those violations, so a non-zero column cannot pass."""
        v, c = self.vocab, self.counts
        unmapped = {}  # universe id -> why nothing maps it
        c.update({f"{key}.{group}": 0 for key in ("mapped", "unmapped") for group in MEMBER_CLASSES + ("extensions",)})
        c.update({"ub-sites.claimed": 0, "ub-sites.derived": 0, "ub-sites.kept": 0, "ub-sites.inside-divergence": 0})
        for mid, m in self.members.items():
            if m.klass.startswith("derived"):
                source = self.mapping_of.get(m.derived_from)
                if source is None:
                    unmapped[mid] = f"derived {mid} maps as {m.derived_from}, which no row maps"
                else:
                    self.mapping_of[mid] = source
            elif mid not in self.mapping_of:
                unmapped[mid] = f"MiniRust {m.kind} {m.path} ({m.rel}:{m.line}): " + (f"row {claims[mid][0]} claims it but its mapping is refused" if mid in claims else "no row claims it")
        for ref, rid in sorted(kept.items()):
            owner = self.owners.get(ref)
            if ref not in self.sites or f"ub-site:{ref}" in claims or self.mapping_of.get(owner) != ("divergence", rid):
                self.add("MAPPING", f"row {rid} kept_ub_sites {ref!r}: a kept site is a UB site at the pin, claimed by no row, inside a member of this row ({owner} maps to {self.mapping_of.get(owner)})")
        kinds = {rid: (r.get("divergence") or {}).get("kind") for rid, r in self.rows.items()}
        for ref in sorted(self.sites):
            sid, source = f"ub-site:{ref}", self.mapping_of.get(self.owners.get(ref))
            inside = isinstance(source, tuple) and source[0] == "divergence"
            c["ub-sites.inside-divergence"] += inside
            if sid in self.mapping_of:
                c["ub-sites.claimed"] += 1
                if inside and kinds.get(source[1]) == "trust-extends":
                    self.add("MAPPING", f"UB site {ref} is claimed as changed, but its member {self.owners.get(ref)} is in trust-extends row {source[1]}, which keeps every behaviour of its MiniRust members")
                continue
            if inside and ref not in kept:
                unmapped[sid] = f"UB site {ref} ({self.sites[ref]!r}) is inside {self.owners.get(ref)}, which divergence row {source[1]} changes; a row claims the site as changed or row {source[1]} lists it in kept_ub_sites"
                continue
            reason = v.ub_sites.get(ref, (None,))[0]
            names = (ALIAS_REASON, reason) if str(reason).startswith(TREE_BORROWS_UB + ".") else (reason,)
            missing = [n for n in names if n not in v.names]
            if missing:
                unmapped[sid] = f"UB site {ref} ({self.sites[ref]!r}) " + (f"derives to {list(names)}, and {', '.join(missing)} is no Core vocabulary name" if reason in v.names else "has no vocabulary reason")
                continue
            self.mapping_of[sid] = ("core", names)
            c["ub-sites.derived"] += 1
            c["ub-sites.kept"] += ref in kept
        vocabulary_extensions, design_extensions = (set(f"{prefix}:{n}" for n in names) for prefix, names in (("extension", v.extensions), ("design-extension", self.design_extensions)))
        for mid in sorted(vocabulary_extensions | design_extensions):
            if mid in self.mapping_of:
                c["mapped.extensions"] += 1
            else:
                unmapped[mid] = f"{mid}: no trust-extends row claims it"
                c["unmapped.extensions"] += 1
        c.update({"extensions": len(vocabulary_extensions), "design-extensions": len(design_extensions), "unmapped": len(unmapped)})
        for mid, m in self.members.items():
            c[f"{'mapped' if mid in self.mapping_of else 'unmapped'}.{m.klass}"] += 1
        for uid, why in unmapped.items():
            self.add("UNMAPPED", why)
        c["unmapped.ub"] = sum(uid.startswith("ub-site:") for uid in unmapped)

    # ---- document, blocks, judgments
    def render(self) -> tuple[str, str]:
        g = lambda key: self.counts.get(key, 0)  # noqa: E731
        klass = {k: [g(f"members.{kind}.{k}") for kind in ("def", "variant", "field")] for k in ("syntax", "domain")}
        ops = [g(f"members.{kind}.operation") for kind in ("fn", "assoc-type", "assoc-const", "macro")]
        derived = g("members.fn.derived-case") + g("members.fn.derived-dispatcher")
        ub, ext = g("ub-sites"), g("extensions") + g("design-extensions")
        total = sum(klass["syntax"]) + sum(klass["domain"]) + sum(ops) + derived + ub + ext
        out = ["| Universe at the MiniRust pin | Members | Mapped by a row | Mapped by derivation | Unmapped |", "|---|---:|---:|---:|---:|"]
        for label, k in (("Syntax constructors (definitions / variants / fields reachable from `Program`)", "syntax"),
                         ("Semantic-domain constructors (every other definition / variant / field)", "domain")):
            out.append(f"| {label}: {' / '.join(map(str, klass[k]))} | {sum(klass[k])} | {g('mapped.' + k)} | 0 | {g('unmapped.' + k)} |")
        out += [f"| Operations (fns / associated types / associated consts / macros): {' / '.join(map(str, ops))} | {sum(ops)} | {g('mapped.operation')} | 0 | {g('unmapped.operation')} |",
                f"| argmatch case fns / dispatchers (derived from their variant / enum) | {derived} | 0 | {g('mapped.derived-case') + g('mapped.derived-dispatcher')} | {g('unmapped.derived-case') + g('unmapped.derived-dispatcher')} |",
                f"| UB sites (`throw_ub!` / `ensure_else_ub` literals) | {ub} | {g('ub-sites.claimed')} | {g('ub-sites.derived')} | {g('unmapped.ub')} |",
                f"| Trust extensions: vocabulary trust-extension names / extensions the design lists | {g('extensions')} / {g('design-extensions')} | {g('mapped.extensions')} | 0 | {g('unmapped.extensions')} |",
                f"| **Total** | {total} | | | **{g('unmapped')}** |", "",
                "| Rows and mapped members | Rows | Members |", "|---|---:|---:|",
                f"| core rows (members mapped to vocabulary names only / using adopted names) | {g('rows.core')} | {g('core.members')} ({g('core.members') - g('core.adopted')} / {g('core.adopted')}) |"]
        for kind in KINDS:
            out.append(f"| divergence `{kind}` | {g('rows.' + kind)} | {g('members.' + kind)} |")
        resolutions = sorted({k[5:] for k in self.counts if k.startswith(("rows.LD-", f"rows.{UPSTREAM}"))}, key=lambda r: (r != UPSTREAM, int(r[3:]) if r != UPSTREAM else 0))
        out += [f"| resolution `{r}` | {g('rows.' + r)} | |" for r in resolutions]
        out += [f"| **All rows** | {len(self.rows)} | |", "", "| Measured | Count |", "|---|---:|",
                f"| Markdown files under `spec/` / ```rust fences read / other fences not read | {g('files')} / {g('fences.rust')} / {g('fences.other')} |",
                f"| [[external]] rows (names `Program` reaches that MiniRust does not define) / of class enum | {len(self.externals)} / {sum(1 for r in self.externals.values() if r.get('class') == 'enum')} |",
                f"| UB sites inside members a divergence row changes / claimed as changed by any row / kept by a row's decision | {g('ub-sites.inside-divergence')} / {g('ub-sites.claimed')} / {g('ub-sites.kept')} |"]
        ledger = ["| Row | Kind | Resolution | Members | Design reference |", "|---|---|---|---:|---|"]
        for rid, row in self.rows.items():
            dv = row.get("divergence")
            if isinstance(dv, dict):
                ledger.append(f"| `{rid}` {str(row['title']).replace('|', chr(92) + '|')} | {dv.get('kind')} | {dv.get('resolution')} | {len(row['members'])} | {(dv.get('design_ref') or {}).get('ref')} |")
        return "\n".join(out), "\n".join(ledger)

    def document(self, counts_text: str, ledger_text: str) -> dict:
        path = self.o.doc or self.o.repo / DOC_REL
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            self.add("DOC", f"{path}: {error}")
            return {}
        C.check_block(self.f, "DOC", text, COUNTS_BLOCK, counts_text)
        C.check_block(self.f, "DOC", text, LEDGER_BLOCK, ledger_text)
        sections = C.document_judgments(self.f, "DOC", text, generated=(COUNTS_BLOCK, LEDGER_BLOCK))
        for jid, body in sections.items():
            self.counts["doc-citations"] = self.counts.get("doc-citations", 0) + C.check_prose(self.f, "DOC", jid, body if isinstance(body, str) else "\n".join(body), self.resolver)
        for revision in [self.pins.alignment] + [self.pins.sources[n].revision for n in READS]:
            if f"`{revision}`" not in text:
                self.add("DOC", f"the document does not record the pin `{revision}`")
        return sections


def judgments(f: C.Findings, table_text: str, sections: dict) -> dict:
    """Every reviewed judgment: each row and external row, the table's comments, the document's
    prose sections and outline. One id from two sources is refused."""
    data = tomllib.loads(table_text)
    pairs = [(f"row:{r.get('id')}", r) for r in data.get("row", []) if isinstance(r, dict)]
    pairs += [(f"external:{r.get('name')}", r) for r in data.get("external", []) if isinstance(r, dict)]
    return C.merge_judgments(f, pairs + [("comments:table", C.toml_comments(table_text))] + list(sections.items()))


def collect(options: Options | None = None) -> Result:
    options = options or Options()
    checker = Checker(options)
    result = Result(violations=checker.f.violations, counts=checker.counts)
    if not checker.load():
        return result
    checker.shape()
    checker.universe()
    checker.mapping()
    checker.rulings()
    result.counts_text, result.ledger_text = checker.render()
    sections = checker.document(result.counts_text, result.ledger_text)
    checker.counts["reviews"] = C.check_reviews(
        checker.f, options.registry or options.repo / REGISTRY_REL, DELIVERABLE, judgments(checker.f, checker.table_text, sections),
        JUDGMENT_KINDS, options.repo if options.check_history else None, REGISTRY_REL)
    return result


def main(argv: list[str] | None = None) -> int:
    if tomllib is None:
        print("minirust_baseline: Python 3.11+ (tomllib) is required", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--minirust", type=Path)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--repo", type=Path, default=C.REPO_ROOT)
    for name in ("table", "doc", "vocabulary", "registry", "decisions"):
        parser.add_argument(f"--{name}", type=Path)
    parser.add_argument("--write-blocks", action="store_true", help="rewrite the document's counts and ledger blocks")
    args = parser.parse_args(argv)
    options = Options(repo=args.repo, table=args.table, doc=args.doc, vocabulary=args.vocabulary, registry=args.registry,
                      decisions=args.decisions, clones={"minirust": args.minirust, "rust-reference": args.reference})
    try:
        result = collect(options)
    except (C.MissingClone, C.PinsError) as error:
        print(f"minirust_baseline: {error}", file=sys.stderr)
        return 2
    if args.write_blocks:
        doc = args.doc or args.repo / DOC_REL
        text = C.replace_block(doc.read_text(encoding="utf-8"), COUNTS_BLOCK, result.counts_text)
        doc.write_text(C.replace_block(text, LEDGER_BLOCK, result.ledger_text), encoding="utf-8")
    print(result.counts_text + "\n\n" + result.ledger_text)
    if result.violations:
        print(f"\nminirust_baseline: {len(result.violations)} violation(s)", file=sys.stderr)
        for violation in result.violations:
            print(f"  {violation}", file=sys.stderr)
        return 1
    reviews = result.counts["reviews"]
    print(f"\nminirust_baseline: OK (unmapped {result.counts['unmapped']}; {result.counts.get('doc-citations', 0)} document citations; "
          f"{reviews['judgments']} reviewed judgments, {reviews['records']} review records)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
