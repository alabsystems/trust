"""A small Rust lexer for the landing gate's escape scan: where the string
literals, comments and `#[cfg(test)]` items of one source file are.

Not a parser. It is built to err toward PRODUCTION: a construct it cannot read
(an unbalanced brace, an attribute it does not know) is never marked test-only,
so a mistake here can only make the selector select more, never less.
scripts/tests/land_gate_test.py drives it over the cases it must get right.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import bisect
import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

# A literal's prefix (`r"`, `b"`, ..) is one only after no identifier
# character, Unicode ones included (`ér"` is the identifier `ér`, then a
# string; round 8 of review 4).
TOKEN = re.compile(r'//|/\*|(?<!\w)(?:br|cr|r)#*"|(?<!\w)[bc]"|"|\'')
# A literal's suffix (`"a"r`, `'x'suffix`): part of its token to rustc, so
# never a following literal's prefix (round 8 of review 4: `"a"r"\"` opened a
# raw string at the suffix).
SUFFIX = re.compile(r'\w*')
STRING_BODY = re.compile(r'(?:[^"\\]|\\.)*', re.S)
BLOCK = re.compile(r'/\*|\*/')
RAW_OPEN = re.compile(r'(?:br|cr|r)(#*)"')
# Whitespace to rustc's lexer that Python's `\s` does not take: of
# Pattern_White_Space, LEFT-TO-RIGHT and RIGHT-TO-LEFT MARK (U+0085, U+2028
# and U+2029 it takes). Outside literals and comments each is a space in
# `code` and in `without_comments()`, one character for one, so that every
# regex matching Rust tokens there reads `mod<U+200E>gen;` and
# `include<U+200F>!(..)` as rustc does (review of
# LAND-GATE-EW1-FOLLOWUP-REVIEW-3: they hid a module and an include!).
RUST_SPACES = str.maketrans({c: " " for c in "\u0085\u200e\u200f\u2028\u2029"})
RUST_SPACE_CHARS = re.compile("[\u0085\u200e\u200f\u2028\u2029]")


@dataclass
class Lexed:
    text: str
    code: str = ""                                                      # text with literals/comments blanked
    strings: List[Tuple[int, int, str]] = field(default_factory=list)   # (start, end, value)
    comments: List[Tuple[int, int]] = field(default_factory=list)
    test_spans: List[Tuple[int, int]] = field(default_factory=list)     # #[cfg(test)] items, attribute to end
    test_mod_decls: List[str] = field(default_factory=list)            # `#[cfg(test)] mod x;` names
    mod_decls: List[str] = field(default_factory=list)                 # every `mod x;` name
    _span_starts: List[int] = field(default_factory=list)
    _spans: List[Tuple[int, int]] = field(default_factory=list)
    _legacy: Optional["Lexed"] = field(default=None, repr=False)

    def legacy(self) -> "Lexed":
        """This file as the lexer read it before LAND-GATE-EW1-FOLLOWUP-REVIEW-3
        (commit 6ec42b3f2e): Rust whitespace outside ASCII as written
        (RUST_SPACES), and a #[cfg(test)] item running to its `;` or `{..}`
        (_find_test_items). A #[cfg(test)] declaration is test-only evidence
        only where this reading too takes it for one (land_select's
        _paths_read_before, _declared_only_under_test): the spellings the
        gate first read since then (`mod<U+200E>x;`, `#[cfg(test<U+200E>)]`)
        make no module test-only. Literals and comments are the same."""
        if self._legacy is None:
            code = self.code
            if RUST_SPACE_CHARS.search(self.text):
                chars = list(code)
                for m in RUST_SPACE_CHARS.finditer(self.text):
                    if self.in_code(m.start()):
                        chars[m.start()] = m.group(0)
                code = "".join(chars)
            old = Lexed(self.text, code=code, strings=self.strings, comments=self.comments,
                        _span_starts=self._span_starts, _spans=self._spans)
            _find_test_items(old, legacy=True)
            self._legacy = old
        return self._legacy

    def in_code(self, pos: int) -> bool:
        """True when `pos` is outside every string literal and comment."""
        return 0 <= pos < len(self.text) and not self._inside(pos)

    def _inside(self, pos: int) -> bool:
        # A blanked position whose original char was a space is still blanked:
        # look it up in the sorted spans.
        i = bisect.bisect_right(self._span_starts, pos) - 1
        if i < 0:
            return False
        s, e = self._spans[i]
        return s <= pos < e

    def in_comment(self, pos: int) -> bool:
        """True when `pos` is inside a comment (a string literal is not a comment)."""
        starts = getattr(self, "_comment_starts", None)
        if starts is None:
            self.comments.sort()
            starts = self._comment_starts = [s for s, _ in self.comments]
        i = bisect.bisect_right(starts, pos) - 1
        return i >= 0 and self.comments[i][0] <= pos < self.comments[i][1]

    def doc_comment_starts(self) -> List[int]:
        """The sorted starts of the doc comments, as rustc_lexer types them:
        `///` (not `////`), `//!`, `/**` (not `/***` or `/**/`) and `/*!`.
        rustc makes each a `#[doc = ".."]` attribute: a token, not
        whitespace (round 7 of LAND-GATE-EW1-FOLLOWUP-REVIEW-4)."""
        docs = self.__dict__.get("_doc_starts")
        if docs is None:
            t = self.text
            docs = []
            for s, _e in sorted(self.comments):
                if t.startswith("//", s):
                    if t.startswith("//!", s) or (t.startswith("///", s) and not t.startswith("////", s)):
                        docs.append(s)
                elif t.startswith("/*!", s) or (t.startswith("/**", s) and not t.startswith("/***", s)
                                                and not t.startswith("/**/", s)):
                    docs.append(s)
            self._doc_starts = docs
        return docs

    def in_test(self, pos: int) -> bool:
        return any(s <= pos < e for s, e in self.test_spans)

    def without_comments(self) -> str:
        """Keep literal bytes and offsets; remove comments before regex scans
        (`code` with its literals as written: Rust whitespace outside them a
        space, RUST_SPACES). Built once: every regex reading tokens across
        the text reads it (land_select._scan_file's `view`)."""
        plain = self.__dict__.get("_plain")
        if plain is None:
            chunks = []
            end = 0
            for start, stop, _value in sorted(self.strings):
                chunks.append(self.code[end:start])
                chunks.append(self.text[start:stop])
                end = stop
            chunks.append(self.code[end:])
            plain = self._plain = "".join(chunks)
        return plain


def lex(text: str) -> Lexed:
    out = Lexed(text)
    n = len(text)
    spans: List[Tuple[int, int]] = []
    i = 0
    while True:
        m = TOKEN.search(text, i)
        if m is None:
            break
        tok, s = m.group(0), m.start()
        if tok == "//":
            j = text.find("\n", s)
            j = n if j == -1 else j
            out.comments.append((s, j))
            spans.append((s, j))
            i = j
        elif tok == "/*":
            depth, j = 1, s + 2
            while depth:
                b = BLOCK.search(text, j)
                if b is None:
                    j = n
                    break
                depth += 1 if b.group(0) == "/*" else -1
                j = b.end()
            out.comments.append((s, j))
            spans.append((s, j))
            i = j
        elif tok == "'":
            # A char literal ('x', '\n', '\u{..}', '"') or a lifetime/label ('a).
            if s + 1 < n and text[s + 1] == "\\":
                # s+2 is the escaped character itself (`'\''`, `'\\'`): the
                # closing quote comes after it.
                j = text.find("'", s + 3)
                if j != -1 and j - s <= 12:
                    out.strings.append((s, j + 1, text[s + 1:j]))
                    spans.append((s, j + 1))
                    i = SUFFIX.match(text, j + 1).end()
                    continue
                i = s + 1
            elif s + 2 < n and text[s + 2] == "'":
                out.strings.append((s, s + 3, text[s + 1]))
                spans.append((s, s + 3))
                i = SUFFIX.match(text, s + 3).end()
            else:
                i = s + 1
        elif tok.endswith('"') and tok[0] in "brc" and RAW_OPEN.fullmatch(tok):
            hashes = RAW_OPEN.fullmatch(tok).group(1)
            body = m.end()
            close = '"' + hashes
            j = text.find(close, body)
            j = n if j == -1 else j
            end = min(n, j + len(close))
            out.strings.append((s, end, text[body:j]))
            spans.append((s, end))
            i = SUFFIX.match(text, end).end()
        else:  # "..." , b"...", c"..."
            body = m.end()
            b = STRING_BODY.match(text, body)
            j = b.end()
            end = min(n, j + 1)
            out.strings.append((s, end, text[body:j]))
            spans.append((s, end))
            i = SUFFIX.match(text, end).end()
    spans.sort()
    out._spans = spans
    out._span_starts = [s for s, _ in spans]
    chunks: List[str] = []
    pos = 0
    for s, e in spans:
        if s < pos:
            continue
        chunks.append(text[pos:s])
        chunks.append(re.sub(r"[^\n]", " ", text[s:e]))
        pos = e
    chunks.append(text[pos:])
    out.code = "".join(chunks).translate(RUST_SPACES)
    _find_test_items(out)
    if out.test_spans:
        # Test code is at most what the reading before review 4 took for it
        # (Lexed.legacy): a span stands only where that reading has one at the
        # same attribute. Where both end, this one ends at or before it (the
        # two walks agree until this one stops at a comma or closer); where
        # that reading finds no end (`keep! { #[cfg(test)] include_str!(..) }`
        # last in a file, whose macro drops the attribute) or no test
        # attribute (`#[cfg(test<U+200E>)]`), rustc may compile the item in a
        # non-test build (round 3 of review 4's modules verifier).
        # Where this reading's end falls after that one's (an attribute behind
        # U+200E, which that reading stopped at: `#[cfg(test)]\u200e#[a);]`,
        # which rustc rejects; round 4), the earlier end stands.
        before = dict(out.legacy().test_spans)
        out.test_spans = [(s, min(e, before[s])) for s, e in out.test_spans if s in before]
    return out


def formatting_label_starts(text: str, *, standard_library: bool) -> set[int]:
    """Literal positions used solely as standard DebugStruct field labels.

    This deliberately recognizes a small, bound form, not any method named
    `field`. The caller must establish that `std` is the standard library and
    is not shadowed in the package. Ambiguous imports, bindings and control
    flow retain the literal as a possible input.
    """
    if not standard_library:
        return set()
    lx = lex(text)
    code = lx.code
    imports = list(re.finditer(r"\buse\s+([^;]+);", code))
    binds_fmt = lambda value: bool(re.search(r"(?:\bas\s+(?:r#)?fmt\b|::(?:r#)?fmt\s*$|\{[^}]*\bfmt\b)", value))
    def standard_fmt(value):
        if re.fullmatch(r"std\s*::\s*fmt\s*", value):
            return True
        group = re.fullmatch(r"std\s*::\s*\{([^{}]*)\}\s*", value)
        if group is None:
            return False
        atoms = [atom.strip() for atom in group.group(1).split(",") if atom.strip()]
        bound = [atom for atom in atoms if re.fullmatch(r"fmt(?:\s+as\s+fmt)?", atom)]
        return len(bound) == 1 and not any(re.search(r"\bfmt\b", atom) for atom in atoms if atom not in bound)
    fmt_imports = [m.group(1) for m in imports if binds_fmt(m.group(1))]
    if len(fmt_imports) != 1 or not standard_fmt(fmt_imports[0]):
        return set()
    if re.search(r"\b(?:mod|struct|enum|trait|type)\s+(?:r#)?(?:std|fmt)\b", code):
        return set()
    if any(re.search(r"\bas\s+(?:r#)?std\b|::\s*(?:r#)?std\s*$|\{[^}]*\bstd\b", m.group(1))
           for m in imports):
        return set()
    labels: set[int] = set()
    impl = re.compile(r"\bimpl\s+fmt\s*::\s*Debug\s+for\s+[^{}]+\{")
    for block in impl.finditer(code):
        # Only an ordinary file-level item. Tokens inside a macro invocation,
        # macro definition, nested item or attributed impl need expansion.
        nesting = []
        for char in code[:block.start()]:
            if char in "({[":
                nesting.append(char)
            elif char in ")}]":
                if not nesting or "({["[")}]".index(char)] != nesting.pop():
                    nesting.append("?")
                    break
        before = code[:block.start()].rstrip()
        if nesting or (before and before[-1] not in ";}"):
            continue
        end = _match_brace(code, block.end() - 1)
        if end is None:
            continue
        region = code[block.end():end]
        method = re.search(r"\bfn\s+fmt\s*\(\s*&\s*self\s*,\s*(\w+)\s*:\s*&\s*mut\s+"
                           r"fmt\s*::\s*Formatter\s*(?:<[^>]*>)?\s*\)\s*->\s*fmt\s*::\s*Result\s*\{", region)
        if method is None:
            continue
        if region[:method.start()].strip():
            continue
        start = block.end() + method.end()
        finish = _match_brace(code, start - 1)
        if finish is None or finish > end:
            continue
        body = code[start:finish]
        formatter = method.group(1)
        builders = list(re.finditer(r"\blet\s+mut\s+(\w+)\s*=\s*" + re.escape(formatter) +
                                    r"\s*\.\s*debug_struct\s*\(", body))
        # Binding patterns in loops, closures or nested items need a parser;
        # refusing them is cheaper and safer than guessing their scope.
        if len(builders) != 1 or re.search(r"\b(?:for|match|fn|macro_rules|use|const|static|mod|"
                                          r"struct|enum|type|trait)\b|\||\w+\s*!|#\s*\[", body):
            continue
        builder = builders[0].group(1)
        bindings = re.findall(r"\blet\s+(?:mut\s+)?(\w+)\s*=", body)
        if len(bindings) != len(re.findall(r"\blet\b", body)):
            continue
        if formatter in bindings:
            continue
        if bindings.count(builder) != 1:
            continue
        for call in re.finditer(r"\b" + re.escape(builder) + r"\s*\.\s*field\s*\(\s*", body):
            if call.start() < builders[0].end():
                continue
            if body[:call.start()].rstrip().endswith((".", ":", "#")):
                continue
            pos = start + call.end()
            # code blanks literals with spaces, so find the original argument
            # after the opening parenthesis rather than after regex whitespace.
            opening = code.rfind("(", start + call.start(), pos)
            for literal_start, literal_end, _value in lx.strings:
                if literal_start >= opening + 1 and not text[opening + 1:literal_start].strip():
                    if text[literal_end:finish].lstrip().startswith(","):
                        labels.add(literal_start)
                    break
    return labels


CFG_TEST = re.compile(r"#\s*\[\s*cfg\s*\(\s*(?:test\s*\)|all\s*\(\s*test\s*[,)])")
MOD_DECL = re.compile(r"\bmod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;")
ATTR_OR_WS = re.compile(r"(?:\s+|#\s*!?\s*\[)")
ITEM_STOP = re.compile(r"[()\[\]{};,]")
# What the walk before review 4 (Lexed.legacy) counted: a `;` or `{` ended an
# item, `(` and `[` opened a level and `)` and `]` closed one (_legacy_stops).
LEGACY_TOKEN = re.compile(r"[()\[\]{;]")
# An element of a list that also closes at `>` or `|`: a generic or a closure
# parameter (_list_element).
LIST_STOP = re.compile(r"[()\[\]{};,>|]")
# An item whose header a comma never ends (`fn f<A, B>()`, `impl<A, B>`):
# none of these begins a field, a variant, a parameter or a match arm. No
# `\s*` before the optional ABI: beside the `\s+` after it, a run of `extern  `
# split its spaces every way, time doubling with each (review 4, round 3).
WHOLE_ITEM = re.compile(r"(?:pub\s*(?:\([^)]*\))?\s*)?(?:(?:const|async|unsafe|default|extern(?:\s*\"[^\"]*\")?)\s+)*"
                        r"(?:fn\s+(?:r#)?[A-Za-z_]|(?:struct|enum|trait|type|impl|mod|use|static|macro)\b"
                        r"|union\s+(?:r#)?[A-Za-z_]|macro_rules\s*!|extern\s+crate\b|extern\s*\{)")
BRACE = re.compile(r"[{}]")
# Scanned in place (pattern.finditer(code, k)): a slice copied the rest of the
# file on every call, quadratic in a file's attributes (review of round 4).
BRACKETS = re.compile(r"[\[\]]")
MOD_PREFIX = re.compile(r"(?:pub(?:\s*\([^)]*\))?\s+)?")


def _attr_end(code: str, j: int) -> Optional[int]:
    """`j` at '#': the index after the attribute's closing ']', or None."""
    k = code.find("[", j)
    if k == -1:
        return None
    depth = 0
    for b in BRACKETS.finditer(code, k):
        depth += 1 if b.group(0) == "[" else -1
        if depth == 0:
            return b.end()
    return None


def _legacy_stops(code: str, starts: List[int]) -> Dict[int, Optional[int]]:
    """For each j of `starts`: the position of the first `;` or `{` at or
    after code[j] at a depth at most j's (`(` and `[` open a level, `)` and
    `]` close one, `}` neither), or None: where an item starting at j ended
    before review 4 (Lexed.legacy). That walk went a token at a time from
    each attribute, past the `}` closing a list, so a list of #[cfg(test)]
    elements took time quadratic in its length (an enum of 8000 such
    variants, 19 s; round 4 of review 4's modules verifier). This answers
    every start in one pass from the end: a stop hides each later one at no
    smaller a depth, so the stops left run later and deeper from the top of
    the stack, and the first one at most j's depth is found by bisection."""
    stops: List[int] = []
    stop_depth: List[int] = []
    levels: List[int] = []
    level_after: List[int] = []
    d = 0
    for t in LEGACY_TOKEN.finditer(code):
        ch = t.group(0)
        if ch in ";{":
            stops.append(t.start())
            stop_depth.append(d)
        else:
            d += 1 if ch in "([" else -1
            levels.append(t.start())
            level_after.append(d)
    out: Dict[int, Optional[int]] = {}
    stack: List[int] = []
    stack_depth: List[int] = []  # ascending from the bottom
    k = len(stops)
    for j in sorted(set(starts), reverse=True):
        while k > 0 and stops[k - 1] >= j:
            k -= 1
            while stack_depth and stack_depth[-1] >= stop_depth[k]:
                stack.pop()
                stack_depth.pop()
            stack.append(stops[k])
            stack_depth.append(stop_depth[k])
        before = bisect.bisect_left(levels, j)
        i = bisect.bisect_right(stack_depth, level_after[before - 1] if before else 0)
        out[j] = stack[i - 1] if i else None
    return out


def _find_test_items(lx: Lexed, legacy: bool = False) -> None:
    """`legacy`: as the lexer did before review 4 (Lexed.legacy): an item ran
    to its `;` or `{..}` at a depth at most that of its start, whatever
    comma or closer came first (_legacy_stops)."""
    code, n = lx.code, len(lx.code)
    lx.mod_decls = [m.group(1) for m in MOD_DECL.finditer(code)]
    items: List[Tuple["re.Match", int]] = []
    for m in CFG_TEST.finditer(code):
        k = _attr_end(code, m.start())
        if k is None:
            continue  # unbalanced: leave it production
        # Skip whitespace and further attributes.
        j = k
        while j < n:
            w = ATTR_OR_WS.match(code, j)
            if w is None:
                break
            if w.group(0).lstrip().startswith("#"):
                e = _attr_end(code, j)
                if e is None:
                    j = n
                    break
                j = e
            else:
                j = w.end()
        items.append((m, j))
    stop_at = _legacy_stops(code, [j for _m, j in items]) if legacy else {}
    braces: Dict[int, Optional[int]] = {}
    for m, j in items:
        if legacy:
            p = stop_at[j]
            end = None
            if p is not None and code[p] == ";":
                end = p + 1
                mm = MOD_DECL.match(code, _mod_start(code, j))
                if mm and mm.end() == end:
                    lx.test_mod_decls.append(mm.group(1))
            elif p is not None:
                if p not in braces:
                    braces[p] = _match_brace(code, p)
                end = None if braces[p] is None else braces[p] + 1
            if end is not None:
                lx.test_spans.append((m.start(), end))
            continue
        # The item: up to the first `;` or `{..}` outside parentheses and
        # brackets, or the end of a list element there: a comma (a field, a
        # variant, a parameter, a match arm) or a closer it did not open (the
        # list's last element: `}`, `)`, `]`, and `>` or `|` after `<`, `(`,
        # `,` or `|`). A comma inside an item's header (`fn f<A, B>()`,
        # `impl<A, B>`) does not end it (WHOLE_ITEM). (Review 4 of
        # LAND-GATE-EW1-FOLLOWUP-REVIEW-3: only `;` and `{` ended one, so a
        # #[cfg(test)] field's span ran past its struct's `}` to the next `;`,
        # and a production `mod x;` after it was test code.)
        whole = WHOLE_ITEM.match(code, j) is not None
        stops = LIST_STOP if not whole and _list_element(code, m.start()) else ITEM_STOP
        depth = 0
        end = None
        for t in stops.finditer(code, j):
            ch = t.group(0)
            if ch in "([":
                depth += 1
            elif ch in ")]" and depth > 0:
                depth -= 1
            elif depth > 0 or (ch == "," and whole):
                continue
            elif ch == ";":
                end = t.end()
                mm = MOD_DECL.match(code, _mod_start(code, j))
                if mm and mm.end() == end:
                    lx.test_mod_decls.append(mm.group(1))
                break
            elif ch == "{":
                close = _match_brace(code, t.start())
                end = None if close is None else close + 1
                break
            else:  # `,`, or a closer the item did not open
                end = t.start()
                break
        if end is not None:
            lx.test_spans.append((m.start(), end))


def _list_element(code: str, at: int) -> bool:
    """Whether the attribute at code[at] stands, after any attributes before
    it, behind `<`, `(`, `,` or `|`: on a generic or closure parameter (or
    another list element), which `>` or `|` may close."""
    k = at
    while True:
        k -= 1
        while k >= 0 and code[k].isspace():
            k -= 1
        if k < 0 or code[k] != "]":
            return k >= 0 and code[k] in "<(,|"
        depth, o = 0, k  # an attribute before it: back to its `#`
        while o >= 0:
            depth += {"]": 1, "[": -1}.get(code[o], 0)
            if depth == 0:
                break
            o -= 1
        h = o - 1
        while h >= 0 and (code[h].isspace() or code[h] == "!"):
            h -= 1
        if o < 0 or h < 0 or code[h] != "#":
            return False
        k = h


def _mod_start(code: str, j: int) -> int:
    m = MOD_PREFIX.match(code, j)
    return m.end() if m else j


def _match_brace(code: str, p: int) -> Optional[int]:
    depth = 0
    for b in BRACE.finditer(code, p):
        depth += 1 if b.group(0) == "{" else -1
        if depth == 0:
            return b.start()
    return None
