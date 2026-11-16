#!/usr/bin/env python3
"""D0.4 checker: the retirement plan for Rust's partial semantics, and the freeze that holds them.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, Stage 0.2 D0.4 ("Retirement
plan for the six semantics (RC-6), each with its exit stage") and §6's row "Writing or extending
another partial semantics of Rust ... Existing ones stay only as differential oracles until their
D0.4 exit". Table: docs/trust-core/semantics-retirement.toml. Document:
docs/trust-core/SEMANTICS_RETIREMENT.md. Review registry: docs/trust-core/reviews/semantics_retirement.toml.

The shared layers (pins, citations, uniqueness, the counts block, reviewed judgments) are
scripts/trust_core/common.py's. This file holds D0.4's own rules; each EXITS NON-ZERO when it fails.
Every repository is read from git objects: the superproject at HEAD (and at [pins] base), each
first-party submodule at the gitlink HEAD (and the base) records.

  PIN        common: the source clones the table cites at EXTERNAL_PINS.toml's pins; no replace ref
             or grafts file here; [pins].superproject_base is an ancestor of HEAD and
             gitlinks_at_base is what that commit records; HEAD has exactly the nine gitlinks; no tree read holds a
             path with a newline (`git cat-file --batch` addresses one path per line).
  TABLE      every row kind's keys and types; unique rows (common.unique_rows); no repeated element
             (common.repeated_elements), except in a size_change's items_added and items_removed, which are
             multisets FREEZE compares exactly; a list names something; free text carries citations only in
             the checked `REF «quote»` form, which resolves (common.check_prose).
  CITE       every {ref, quote} in the table resolves at HEAD or its pin (common.Resolver).
  DESIGN     RC-6's six numbered items are each cited by exactly one frozen row, which owns the path
             the item names (§1.4 abbreviations resolved); the §5 exits whose text names one of a
             row's design_names are listed as design exits or excluded by an owner question naming
             them; a design exit's text names the row, a proposed one's does not and its owner
             question names it; every exit citation lies inside that exit's text; the deletion exit
             is a design deletion exit (its text also says `delet…`) unless an owner question names
             the design's; a capability names an exit whose text it cites, or a gap and an owner
             question. Whether a covering exit comes before the deletion is reviewed, not derived.
  FREEZE     own files = the files under own_paths with size_suffixes, plus, for a frozen row, every
             file their module graph reaches: a file is compiled when it is a root, a `mod` target
             (`#[path]` included) or an `include!` target, and the `mod` and `include*!` edges of every
             compiled file are followed however the walk first reached it; an `include_str!` or
             `include_bytes!` target is a member read as data. Digest = sha256 over the sorted
             `repo:path NUL sha256(content)` lines; lines = LF bytes. The baseline is measured at the
             base; HEAD must equal the last size_change's digest_after (or the baseline). Each
             size_change is checked against the state before it (the baseline, or the entry before
             it read at its `at` commit): a retirement only deletes lines; a mechanical-rename is
             exactly its renames; an oracle-bug-fix adds no kernel name and lists its items; growth
             cites a growth_allowed exit; a recorded-extension names an owner question whose text
             names the row, and lists its items and kernel names. No file has two owners.
  HOST       the host crates are enumerated: for each own file of a frozen row at HEAD, the nearest enclosing
             directory whose Cargo.toml has a [package] table, unless it lies under the row's own paths; each
             has one [[host_crate]] row naming exactly its rows, and no row is stale. Each library module tree
             (member files and inline `mod x { }` paths) is pinned by two counts and a digest at the base;
             beside the rows' own files (at the base or at HEAD, which FREEZE pins by content), HEAD equals the
             base plus its recorded changes, none of which adds an own file of a frozen row; a member module
             that is not UTF-8 fails.
  NAMESPACE  names are dotted kernel names (Rust string literals, Lean text) and Lean declarations read with
             their namespace blocks (lean_declared_names; in a Lean file a command starts a line, in a Rust
             file's literals, read as one text, any keyword after whitespace does, and there a declaration
             counts under every namespace opened before it). A prefix namespace: `git grep -F` for the prefix's last segment names
             the files of the search scope that can hold a name; in such a file outside the defining rows'
             own files a dotted name is one those files declare and a declaration is exactly such a name, or
             the file is a recorded outside definer whose name set is pinned (count, digest). A declared
             namespace: every file of the search scope under its paths, outside the rows' own files, is read,
             and every declaration with a name component the pattern matches belongs to a recorded outside
             definer (a path or a glob) whose `path:name` set is pinned. A file either reads that is not
             UTF-8 text fails. A new name is growth, never a consumer.
  SEARCH     a DECLARED search per row ([[search]]: fixed-string terms and ERE patterns, over [search_scope])
             is re-run with `git grep -z -l` (-F, -E; binary files included; names NUL-terminated, so none is
             quoted) in every repository: one grep over every row's terms and patterns names the candidates,
             and each row's hit set is its own grep over exactly those files. Its hit set outside the row's
             own files equals the recorded dispositions exactly: every hit is one consumer (exact path, or a
             directory ending in /) or matches one mention glob, every consumer and glob matches a hit, and a
             beyond_search consumer (reach the removed invocation scanner concluded) exists and is no hit. An
             unconsumed capability's names have no hit outside the row's own files. `checked_by` names exits
             of the row (or, with none, an owner question): the change that makes them runs the gates on
             every consumer and gate unit, which no scanner here derives.
  CRATES     `targo metadata --no-deps --offline` on every declared [[workspace]] (materialized from git
             objects: manifests, target roots and symbolic links): the packages with a path dependency on
             a search's crates equal its recorded dependents, with their dependency kinds.
  GATES      the gate manifest rows ([gate_scope].manifest's heredoc) whose command holds a search's term,
             pattern or crate name, or the path of a consumer it records as a script (read by git grep -F and
             -E, as the searches are), are
             exactly its recorded gates; a gates_beyond_search unit names a gate_source, a harness
             unit that exists and does not match, and resolved evidence.
  SOURCES    every file named like a git hook ([gate_scope].hook_names), every publish/config.sh and
             every .github/workflows file of every repository (outside [search_scope].excluded) has a
             [[gate_source]] entry; each entry's file exists.
  PROBE      every .rs/.lean path of [probe] scope, taken up to its first component named like a
             semantics ([probe].token), is covered by a row's own files or own_paths, a consumer, a
             namespace outside definer, a considered location or a [[probe_negative]]; every
             negative covers a key; only a not-rust negative is a glob.
  DOC        the counts block (the base gitlinks, each row's design and proposed exits and deletion, freeze
             checks, host crates, namespaces, searches, gates) regenerates; it prints only what a table entry
             records or a predicate holds to one, never what moves unreviewed (the gitlinks at HEAD, an unfrozen
             row's files, hit counts, the manifest's other rows, probe keys). Every line is a reviewed
             `prose:` section, the counts block or the outline, which places each section
             (common.document_judgments); every «quoted» citation resolves. A consuming
             test an oracle cites is a recorded consumer of its row.
  REVIEW     common.check_reviews over every table row, the singleton tables, the table's comments,
             every prose section and the outline; a committed record reviews nothing new.

Usage:
    scripts/trust_core/semantics_retirement.py [--repo DIR] [--table FILE] [--doc FILE]
        [--registry FILE] [--print-counts] [--write-counts] [--discover]

`--discover` prints measured values (baselines, host crates, outside definers, search hits
without a disposition, dependents, matched gate rows, uncovered probe keys) to help write the
table; it turns nothing green. Exit codes: 0 every predicate holds; 1 a violation; 2 a clone,
the targo binary or the pins are missing.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import argparse
import fnmatch
import hashlib
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile
import weakref
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

tomllib = C.tomllib
REPO_ROOT = C.REPO_ROOT
TABLE_REL = "docs/trust-core/semantics-retirement.toml"
DOC_REL = "docs/trust-core/SEMANTICS_RETIREMENT.md"
REGISTRY_REL = f"{C.REVIEWS_DIR}/semantics_retirement.toml"
DELIVERABLE = "semantics_retirement"
SCHEMA = "trust.core.semantics-retirement.v4"
COUNTS_BLOCK = "semantics-retirement-counts"
SUPER = "super"
SUBMODULES = ("ay", "clean", "ny", "trust-cg", "trust-ir", "trust-mc", "trust-vc", "trust-wp", "ty")
REPOS = (SUPER,) + SUBMODULES
CLONE_OF = {"minirust": "minirust", "reference": "rust-reference", "fls": "fls", "a-mir-formality": "a-mir-formality"}
SELF_FILES = ("scripts/trust_core/semantics_retirement.py", "scripts/tests/trust_core_semantics_retirement_test.py")
EXIT_ID = r"E\d+(?:\.[0-9A-Za-z]+){1,2}"
OQ_ID = re.compile(r"^OQ-\d+$")

S, L, D, I = str, list, dict, int
CITE_KEYS = {"ref", "quote"}
# kind -> (required fields and types, optional fields and types, key)
ROWS = {
    "semantics": ({"id": S, "rc6_item": I, "name": S, "kind": S, "freeze": S, "host": S, "own_paths": L, "size_suffixes": L,
                   "baseline": D, "design_names": L, "design_refs": L, "owner_questions": L, "role_class": S, "role": S,
                   "exits": L, "deleted_at": D, "replacement_refs": L, "retirement_criteria": L, "deletion_removes": L,
                   "capability": L},
                  {"size_exclude_components": L, "baseline_parts": L, "size_change": L, "growth_allowed": L,
                   "freeze_basis": L, "rc6_claims": L, "evidence": L, "tcb_rows": L, "oracle": D, "exits_excluded": L,
                   "source_refs": L},
                  lambda r: r.get("id")),
    "search": ({"row": S, "terms": L, "consumers": L, "mentions": L, "gates": L, "checked_by": D},
               {"patterns": L, "crates": L, "dependents": L, "beyond_search": L, "gates_beyond_search": L},
               lambda r: r.get("row")),
    "host_crate": ({"repo": S, "dir": S, "rows": L, "files": I, "inline_modules": I, "digest": S, "changes": L}, {},
                   lambda r: f"{r.get('repo')}:{r.get('dir')}"),
    "namespace": ({"prefix": S, "rows": L, "outside_definers": L}, {"pattern": S, "scope": D},
                  lambda r: r.get("prefix")),
    "workspace": ({"repo": S, "manifest": S, "reason": S}, {}, lambda r: f"{r.get('repo')}:{r.get('manifest')}"),
    "gate_source": ({"repo": S, "path": S, "disposition": S, "reason": S}, {"cwd": S, "evidence": L},
                    lambda r: f"{r.get('repo')}:{r.get('path')}"),
    "owner_question": ({"id": S, "question": S, "options": L, "consequence": S}, {}, lambda r: r.get("id")),
    "considered": ({"id": S, "name": S, "locations": L, "evidence": L, "in_plan": S, "reason": S},
                   {"design_refs": L, "row": S, "owner_question": S}, lambda r: r.get("id")),
    "probe_negative": ({"repo": S, "key": S, "disposition": S, "reason": S}, {}, lambda r: f"{r.get('repo')}:{r.get('key')}"),
}
TABLES = {
    "pins": {"superproject_base": S, "gitlinks_at_base": D},
    "search_scope": {"suffixes": L, "basenames": L, "excluded_top_dirs": L, "excluded": L, "reason": S},
    "gate_scope": {"manifest": D, "hook_names": L, "reason": S},
    "probe": {"token": S, "super_top_dirs": L, "reason": S},
    "deliverable": {"exit": S, "gap": S, "owner_question": S, "evidence": L},
}
TOP_KEYS = {"schema", "design", "document"} | set(ROWS) | set(TABLES)
MAY_BE_EMPTY = {"by_exits", "design_names", "outside_definers", "changes", "consumers", "mentions", "gates", "terms", "tcb_rows",
                "covered_by", "dependents", "beyond_search", "gates_beyond_search", "items_added", "items_removed",
                "names_added", "removed"}
MULTISET_KEYS = {"items_added", "items_removed"}  # size_change fields compared as multisets, not sets
FREE_TEXT_KEYS = {"name", "role", "reason", "gap", "question", "options", "consequence", "claim", "correction",
                  "capability", "what", "retirement_criteria", "deletion_removes"}
FREEZES, KINDS = ("design", "design-reading", "none"), ("definitional", "producer")
ROLE_CLASSES = ("differential-oracle", "implementation-checked-against-trustsem", "seed-then-delete", "producer-until-exit")
CHANGE_CLASSES = ("retirement", "mechanical-rename", "oracle-bug-fix", "growth", "recorded-extension")
IN_PLAN, NEGATIVE, ROLES = ("yes", "no", "owner-decision"), ("not-rust", "not-a-semantics"), ("exercises", "links", "names")
JUDGMENT_KINDS = set(ROWS) | set(TABLES) | {"comments", "prose", "outline"}


class ToolMissing(Exception):
    """A tool the checker runs (targo) is not installed; exit 2."""


@dataclass
class Options:
    repo: Path = REPO_ROOT
    table: Path | None = None
    doc: Path | None = None
    registry: Path | None = None
    clones: dict = field(default_factory=dict)
    trees: dict = field(default_factory=dict)       # (repo, "HEAD" | sha) -> tree, shared across runs; overlays in tests
    metadata: dict | None = None                    # workspace key -> packages; mutation tests only
    check_pin_state: bool = True
    check_history: bool = True
    discover: bool = False


@dataclass
class Result:
    violations: list = field(default_factory=list)
    counts: dict = field(default_factory=dict)
    counts_text: str = ""
    discovered: list = field(default_factory=list)


# --------------------------------------------------------------------------
# Rust and Lean reading: comments and literals, module items, declared names
# --------------------------------------------------------------------------

_TOKEN = re.compile(
    r"""(?P<lc>//[^\n]*)
      | (?P<bc>/\*)
      | (?P<raw>(?<![A-Za-z0-9_])[bc]?r(?P<h>\#*)"(?P<rawbody>.*?)"(?P=h))
      | (?P<str>(?<![A-Za-z0-9_])[bc]?"(?P<strbody>(?:\\.|[^"\\])*)")
      | (?P<chr>'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}|.)|[^'\\\n])')""", re.S | re.X)
_MOD = re.compile(r"(?<![A-Za-z0-9_])mod\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)\s*([;{])")
_INCLUDE = re.compile(r"(?<![A-Za-z0-9_])(include|include_str|include_bytes)\s*!\s*\(")
_PATH_ATTR = re.compile(r'(?<![A-Za-z0-9_])path\s*=\s*"((?:\\.|[^"\\])*)"')
_VIS = re.compile(r"pub\s*(?:\([^()]*\))?\s*$")
_RUST_ITEM = re.compile(r"(?<![A-Za-z0-9_])(fn|const|static|struct|enum|union|trait|type|mod|macro_rules!)\s+(?:r#)?([A-Za-z_][A-Za-z0-9_]*)")
_LEAN_ITEM = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
    r"(def|theorem|lemma|abbrev|inductive|structure|class|instance|axiom|opaque)\s+([^\s:({\[]+)", re.M)
_BLANK = re.compile(r"[^\n]")
_CACHE: dict = {}  # parses keyed by content hash, and the crate graph keyed by the gitlinks
_TREE_CACHE = weakref.WeakKeyDictionary()  # tree -> its listing and search results


def _blank(text: str) -> str:
    return _BLANK.sub(" ", text)


def rust_mask(src: str) -> tuple[str, str, list[str]]:
    """(code with comments and literal bodies blanked, code with comments blanked, string literal bodies).
    Offsets and newlines are preserved in both views."""
    key = ("mask", hashlib.sha1(src.encode("utf-8", "surrogatepass")).digest())
    if key in _CACHE:
        return _CACHE[key]
    code, strs, lits, pos = [], [], [], 0
    for m in _TOKEN.finditer(src):
        if m.start() < pos:
            continue
        code.append(src[pos:m.start()])
        strs.append(src[pos:m.start()])
        end = m.end()
        if m.group("bc") is not None:
            depth, end = 1, m.end()
            while end < len(src) and depth:
                if src.startswith("/*", end):
                    depth, end = depth + 1, end + 2
                elif src.startswith("*/", end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
        text = src[m.start():end]
        if m.group("lc") is not None or m.group("bc") is not None:
            code.append(_blank(text))
            strs.append(_blank(text))
        else:
            if m.group("chr") is not None:
                a, b = 1, len(text) - 1
            else:
                a = text.index('"') + 1
                b = len(text) - 1 - (len(m.group("h")) if m.group("raw") is not None else 0)
                lits.append(m.group("rawbody") if m.group("raw") is not None else m.group("strbody"))
            code.append(text[:a] + _blank(text[a:b]) + text[b:])
            strs.append(text)
        pos = end
    code.append(src[pos:])
    strs.append(src[pos:])
    _CACHE[key] = ("".join(code), "".join(strs), lits)
    return _CACHE[key]


def _path_attribute(code: str, strs: str, pos: int) -> str | None:
    """The `#[path = "…"]` among the outer attributes directly before the `mod` at pos."""
    head = code[max(0, pos - 120):pos]
    vis = _VIS.search(head)
    j = pos - (len(head) - vis.start()) if vis else pos
    found = None
    while True:
        k = j
        while k > 0 and code[k - 1].isspace():
            k -= 1
        if k == 0 or code[k - 1] != "]":
            return found
        depth, t = 0, k - 1
        while t >= 0:
            depth += {"]": 1, "[": -1}.get(code[t], 0)
            if depth == 0:
                break
            t -= 1
        s = t - 1
        while s >= 0 and code[s].isspace():
            s -= 1
        if s < 0 or code[s] != "#":
            return found
        attr = _PATH_ATTR.search(strs[s:k])
        found = found or (attr.group(1) if attr else None)
        j = s


def rust_modules(src: str) -> tuple[list, list, list]:
    """(file-module declarations (inline module stack, name, #[path] or None), include macros (kind, literal
    path or None, relative to CARGO_MANIFEST_DIR), inline module paths) of Rust source."""
    key = ("modules", hashlib.sha1(src.encode("utf-8", "surrogatepass")).digest())
    if key in _CACHE:
        return _CACHE[key]
    code, strs, _ = rust_mask(src)
    events = sorted([(m.start(), 0, "mod", m) for m in _MOD.finditer(code)]
                    + [(m.start(), 0, "inc", m) for m in _INCLUDE.finditer(code)]
                    + [(m.start(), 1, m.group(0), None) for m in re.finditer(r"[{}]", code)], key=lambda e: (e[0], e[1]))
    decls, incs, inline, stack, depth, pending = [], [], [], [], 0, None
    for pos, _, kind, m in events:
        if kind == "mod":
            if m.group(2) == ";":
                decls.append((tuple(name for _, name in stack), m.group(1), _path_attribute(code, strs, pos)))
            else:
                pending = (m.end() - 1, m.group(1))
        elif kind == "inc":
            d, t = 1, m.end()
            while t < len(code) and d:
                d += {"(": 1, ")": -1}.get(code[t], 0)
                t += 1
            arg = strs[m.end():t - 1]
            lit = re.fullmatch(r'\s*"((?:\\.|[^"\\])*)"\s*,?\s*', arg)
            env = re.fullmatch(r'\s*concat\s*!\s*\(\s*env\s*!\s*\(\s*"CARGO_MANIFEST_DIR"\s*\)\s*,\s*"((?:\\.|[^"\\])*)"\s*\)\s*,?\s*', arg)
            incs.append((m.group(1), (lit or env).group(1).lstrip("/" if env else "") if (lit or env) else None, env is not None))
        elif kind == "{":
            depth += 1
            if pending and pending[0] == pos:
                stack.append((depth, pending[1]))
                pending = None
        else:
            if stack and stack[-1][0] == depth:
                inline.append(tuple(name for _, name in stack))
                stack.pop()
            depth -= 1
    _CACHE[key] = (decls, incs, inline)
    return _CACHE[key]


def strip_lean_comments(text: str) -> str:
    """Lean text with its comments removed. A comment separates what it stands between (its newlines, or one
    space), so no name is joined across a comment and every name read lies in the source text itself."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("\n" * text.count("\n", i, j) or " ")
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        else:
            cands = [j for j in (text.find("/-", i), text.find("--", i)) if j >= 0]
            j = min(cands) if cands else n
            out.append(text[i:j])
            i = j
    return "".join(out)


_LEAN_DECL = "def|theorem|lemma|abbrev|inductive|structure|class|instance|axiom|opaque"
# Where a Lean command can start: a declaration keyword, a block keyword, a declaration modifier or an attribute. In a
# Lean file a command starts a line, so a keyword inside a string or a name (`"end with a terminator"`,
# `«private.class»`) starts nothing. Lean text carried in a Rust literal is not laid out in lines that way
# (`namespace X inductive T ... end X` on one), so there a command starts at any such token after whitespace.
_LEAN_MODIFIER = "private|protected|noncomputable|partial|unsafe|nonrec"
_LEAN_KEYWORDS = (rf"(?:namespace|section|mutual|end|{_LEAN_DECL}|deriving\s+instance"
                  rf"|{_LEAN_MODIFIER})(?![\w'])|@\[")
# What may stand before a declaration keyword in its command: attributes and modifiers.
_LEAN_PREFIX = rf"(?:@\[[^\]]*\]\s*)*(?:(?:{_LEAN_MODIFIER})\s+)*"
_LEAN_COMMAND = re.compile(rf"(?m)^(?=[ \t]*(?:{_LEAN_KEYWORDS}))")
_LEAN_COMMAND_INLINE = re.compile(rf"(?<![^\s])(?<!deriving )(?=(?:{_LEAN_KEYWORDS}))")
# A command prefix that ends in `in` (`set_option maxHeartbeats 400000 in theorem X`) puts a command after it on its line.
_LEAN_IN = re.compile(rf"\bin[ \t]+(?=(?:{_LEAN_KEYWORDS}))")


def rust_literal_text(text: str) -> str:
    """The Lean text a Rust file carries: its string literal bodies in source order, one after another, with the
    escapes a Lean program needs undone (a newline, a tab, a quote, a backslash, a line continuation). They are read
    as one text, so a `namespace` one literal opens holds the declarations of the literals after it."""
    key = ("literal-text", hashlib.sha1(text.encode("utf-8", "surrogatepass")).digest())
    if key not in _CACHE:
        out = []
        for body in rust_mask(text)[2]:
            body = re.sub(r"\\\n[ \t]*", " ", body)
            out.append(re.sub(r"\\([nt\"\\'])", lambda m: {"n": "\n", "t": "\t"}.get(m.group(1), m.group(1)), body))
        _CACHE[key] = "\n".join(out)
    return _CACHE[key]


def lean_declared_names(text: str, over: bool = False, comments: bool = True, inline: bool = False) -> set[str]:
    """Fully qualified names Lean text declares. The text is split into commands at every token that can start one,
    so several commands on one line are read. `namespace`, `section` and `mutual` blocks are tracked, so a name
    declared inside `namespace X ... end X` is X's, and `_root_.` escapes them. Inductive constructors are names; an
    anonymous instance is read as `NS.instance : TYPE` and a `deriving instance C for T` command as `NS.T.deriving C`,
    since the names Lean generates for them lie in no text.

    A Lean string is not removed: a regular expression cannot tell where one ends (an interpolation or a quote in a
    char literal desynchronises it, and a swallowed region hides the declarations inside it). In a Lean file that
    costs nothing, since a command starts a line; with `inline` (Lean text carried in Rust string literals, where
    several commands stand on one line) a keyword inside a string is read as a command, which can add a name.
    `comments` removes the comments of a Lean file; the text of a Rust literal keeps them, since a `/-` in prose
    would hide what follows.

    With `over`, a declaration is read under its enclosing namespaces AND under every namespace opened before it in
    the text, so nothing that looks like `end` can take a name out of a namespace: that reading can add names, it
    cannot lose one, and it is the reading for every file outside a row's own files. A row's own files are read
    without it, so a name they do not declare cannot exempt a declaration elsewhere."""
    key = ("lean-names", over, comments, inline, hashlib.sha1(text.encode("utf-8", "surrogatepass")).digest())
    if key in _CACHE:
        return _CACHE[key]
    names, stack, opened = set(), [], set()
    source = re.sub(r"\bderiving\s+instance\b", "deriving instance", strip_lean_comments(text) if comments else text)
    source = _LEAN_IN.sub("\n", source)
    for chunk in (_LEAN_COMMAND_INLINE if inline else _LEAN_COMMAND).split(source):
        command = " ".join(chunk.split())
        ns = ".".join(x for x in stack if x)
        spaces = {ns} | opened if over else {ns}

        def qualify(name: str) -> set:
            if name.startswith("_root_."):
                return {name[len("_root_."):]}
            return {f"{n}.{name}" if n else name for n in spaces}
        if m := re.match(r"^namespace\s+([A-Za-z_][\w.']*)", command):
            stack.append(m.group(1))
            opened.add(".".join(x for x in stack if x))
        elif re.match(r"^(?:section|mutual)\b", command):
            stack.append(None)
        elif re.match(r"^end\b", command):
            stack = stack[:-1]
        elif m := re.match(rf"^{_LEAN_PREFIX}deriving\s+instance\s+(.+?)\s+for\s+(.+)$", command):
            for ty in m.group(2).split(","):
                for cls in m.group(1).split(","):
                    names |= qualify(f"{ty.strip()}.deriving {cls.strip()}")
        elif m := re.match(rf"^{_LEAN_PREFIX}instance\s*(?:\(priority[^)]*\)\s*)?:\s*(.+?)\s*(?::=|\bwhere\b|$)", command):
            names |= qualify(f"instance : {m.group(1)}")
        elif m := re.match(rf"^{_LEAN_PREFIX}({_LEAN_DECL})\s+(?:\(priority[^)]*\)\s*)?([^\s:({{\[]+)", command):
            for full in qualify(m.group(2)):
                names.add(full)
                if m.group(1) == "inductive":
                    names.update(f"{full}.{c}" for c in re.findall(r"(?<![|\w])\|\s*([A-Za-z_][\w']*)", command))
    _CACHE[key] = names
    return names


def item_names(path: str, text: str) -> Counter:
    """The multiset of `kind name` items a Rust or Lean file declares."""
    if path.endswith(".rs"):
        return Counter(f"{k} {n}" for k, n in _RUST_ITEM.findall(rust_mask(text)[0]))
    if path.endswith(".lean"):
        return Counter(f"{k} {n}" for k, n in _LEAN_ITEM.findall(strip_lean_comments(text)))
    return Counter()


def kernel_names(path: str, text: str, prefixes) -> set[str]:
    """Kernel names under one of the prefixes: in Rust string literals, or in Lean text."""
    if not prefixes:
        return set()
    if path.endswith(".rs"):
        text = "\n".join(rust_mask(text)[2])
    elif path.endswith(".lean"):
        text = strip_lean_comments(text)
    else:
        return set()
    alt = "|".join(re.escape(p.rstrip(".")) for p in sorted(prefixes, key=len, reverse=True))
    return set(re.findall(rf"(?<![A-Za-z0-9_.'])((?:{alt})(?:\.[A-Za-z_][A-Za-z0-9_']*)+)", text))


def declared_names(path: str, text: str, over: bool = True) -> set[str]:
    """Lean/Clean declarations of a file, fully qualified (lean_declared_names): a Lean file's, those in a Rust file's
    string literals read as one Lean text with its comments kept, and those in any other text file (a generated
    `.defs.txt` a module includes). `over` reads a declaration under every namespace opened before it as well."""
    return lean_declared_names(rust_literal_text(text), over, comments=False, inline=True) if path.endswith(".rs") else lean_declared_names(text, over)


def in_namespace(name: str, prefix: str) -> bool:
    return name == prefix or name.startswith(prefix + ".")


def is_subsequence(small: list, big: list) -> bool:
    it = iter(big)
    return all(any(x == y for y in it) for x in small)


def owns(path: str, own_paths) -> bool:
    for p in own_paths:
        if ("*" in p and fnmatch.fnmatchcase(path, p)) or path == p.rstrip("/") or path.startswith(p if p.endswith("/") else p + "/"):
            return True
    return False


def names_digest(names) -> str:
    return hashlib.sha256("\n".join(sorted(names)).encode()).hexdigest()


def files_digest(files: dict) -> tuple[int, int, str]:
    """(files, lines, digest) of {(repo, path): text}."""
    h, lines = hashlib.sha256(), 0
    for (repo, path), text in sorted(files.items()):
        data = text.encode("utf-8")
        h.update(f"{repo}:{path}\0{hashlib.sha256(data).hexdigest()}\n".encode())
        lines += data.count(b"\n")
    return len(files), lines, h.hexdigest()


def word_in(name: str, text: str) -> bool:
    return re.search(rf"(?<![\w-]){re.escape(name)}(?![\w-])", text) is not None


# --------------------------------------------------------------------------
# the design's §5 exits, RC-6 items and §1.4 abbreviations
# --------------------------------------------------------------------------


class Design:
    def __init__(self, text: str) -> None:
        self.lines = text.split("\n")
        heads = [i + 1 for i, l in enumerate(self.lines) if l.startswith("## ")]
        start5 = next((h for h in heads if self.lines[h - 1].startswith("## 5.")), None)
        end5 = next((h for h in heads if start5 and h > start5), len(self.lines))
        self.exits: dict[str, tuple[int, int]] = {}
        for n in range(start5 or 1, end5 if start5 else 0):
            m = re.match(rf"^(\s*)\*\s+\*\*({EXIT_ID})\*\*", self.lines[n - 1])
            if m and m.group(2) not in self.exits:
                self.exits[m.group(2)] = (n, self.bullet_end(n))
        a = next((i + 1 for i, l in enumerate(self.lines) if l.startswith("**RC-6.")), 0)
        b = next((i + 1 for i, l in enumerate(self.lines) if l.startswith("**RC-7.")), 0)
        self.rc6 = {int(m.group(1)): n for n in range(a, b) if (m := re.match(r"^(\d)\.\s+\*\*", self.lines[n - 1]))}
        abbrev = next((i + 1 for i, l in enumerate(self.lines) if l.startswith("### 1.4")), len(self.lines))
        self.abbrev = {}
        for line in self.lines[abbrev:]:
            if line.startswith(("#", "---")):
                break
            if m := re.match(r"^\|\s*([A-Z][A-Z0-9-]*)\s*\|\s*`([^`]+)`", line):
                self.abbrev[m.group(1)] = m.group(2).rstrip("/")

    def bullet_end(self, n: int) -> int:
        indent, end = len(self.lines[n - 1]) - len(self.lines[n - 1].lstrip(" ")), n
        for k in range(n + 1, len(self.lines) + 1):
            line = self.lines[k - 1]
            if not line.strip() or len(line) - len(line.lstrip(" ")) <= indent or line.startswith("#"):
                break
            end = k
        return end

    def text(self, exit_id: str) -> str:
        a, b = self.exits[exit_id]
        return "\n".join(self.lines[a - 1:b])

    def resolve(self, token: str) -> tuple[str, str] | None:
        """A design path token (abbreviations resolved, `:line` dropped) as (repo, path)."""
        t = re.sub(r":\d+(?:-\d+)?$", "", token.strip())
        head, _, rest = t.partition("/")
        if head in self.abbrev:
            t = self.abbrev[head] + ("/" + rest if rest else "")
        elif "/" not in t:
            return None
        parts = t.split("/", 2)
        if parts[0] == "first-party":
            return (parts[1], parts[2]) if len(parts) == 3 and parts[1] in SUBMODULES else None
        return SUPER, t


# --------------------------------------------------------------------------
# the checker
# --------------------------------------------------------------------------


def cite_line(ref: str) -> int | None:
    parts = C.parse_ref(ref)
    return parts["start"] if parts and parts["source"] == "design" else None


class Checker:
    def __init__(self, options: Options) -> None:
        self.o = options
        self.f = C.Findings()
        self.counts: dict = {}
        self.discovered: list[str] = []
        self.trees: dict = options.trees  # shared, so a caller's repeated runs reuse the trees' caches
        self.own: dict[str, dict] = {}
        self.listed: set[int] = set()

    def add(self, kind: str, message: str) -> None:
        self.f.add(kind, message)

    def discover(self, line: str) -> None:
        if self.o.discover:
            self.discovered.append(line)

    # ---- inputs
    def tree(self, repo: str, rev: str = "HEAD"):
        """A repository at a superproject revision: the superproject itself, or a submodule at its gitlink there."""
        if (repo, rev) not in self.trees:
            self.trees[(repo, rev)] = C.GitTree(self.o.repo, rev) if repo == SUPER else C.first_party_tree(self.o.repo, repo, rev)
            if self.trees[(repo, rev)] is None:
                self.add("PIN", f"{repo} has no readable gitlink at {rev}")
        return self.trees[(repo, rev)]

    def text(self, repo: str, path: str, rev: str = "HEAD") -> str | None:
        tree = self.tree(repo, rev)
        return tree.text(path) if tree is not None else None

    def load(self) -> bool:
        o = self.o
        try:
            self.table_text = (o.table or o.repo / TABLE_REL).read_text(encoding="utf-8")
            self.data = tomllib.loads(self.table_text)
        except (OSError, tomllib.TOMLDecodeError) as error:
            self.add("TABLE", f"{o.table or TABLE_REL}: {error}")
            return False
        self.pins = C.load_pins(o.repo / C.PINS_REL)
        cited = {m.group(1) for m in re.finditer(r'ref = "(minirust|reference|fls|a-mir-formality):', self.table_text)}
        wanted = sorted(CLONE_OF[s] for s in cited)
        missing = [n for n in wanted if n not in o.trees]
        clones = C.locate_clones(self.pins, missing, o.clones) if missing else {}
        trees = {"worktree": self.tree(SUPER)}
        for name, path in clones.items():
            trees[next(k for k, v in CLONE_OF.items() if v == name)] = C.GitTree(path, self.pins.sources[name].revision)
        trees.update({k: v for k, v in o.trees.items() if isinstance(k, str)})
        self.resolver = C.Resolver(o.repo, trees)
        for name in SUBMODULES:
            self.resolver.trees[f"first-party/{name}"] = self.tree(name)
        if o.check_pin_state:
            for name, path in clones.items():
                C.verify_clone(self.f, path, self.pins.sources[name], self.pins)
            C.verify_objects(self.f, f"repository {o.repo}", o.repo)
        self.design = Design(self.resolver.tree_of("design", None)[0].text(C.DESIGN_REL) or "")
        return True

    # ---- TABLE, CITE
    def rows(self) -> None:
        d = self.data
        for key in sorted(set(d) - TOP_KEYS):
            self.add("TABLE", f"top-level key {key!r} is not part of the schema")
        for key, want in (("schema", SCHEMA), ("design", C.DESIGN_REL), ("document", DOC_REL)):
            if d.get(key) != want:
                self.add("TABLE", f"{key} is not {want!r}")
        self.t: dict[str, dict] = {}
        for kind, (required, optional, key) in ROWS.items():
            valid = []
            for index, row in enumerate(d.get(kind, [])):
                where = f"{kind}[{index}] {key(row) if isinstance(row, dict) else ''}"
                if self.shape(where, row, required, optional):
                    valid.append(row)
            self.t[kind] = C.unique_rows(self.f, "TABLE", kind, valid, key)
        self.s = {}
        for name, fields in TABLES.items():
            self.s[name] = d.get(name) if self.shape(name, d.get(name), fields, {}) else {k: t() for k, t in fields.items()}
        self.cite_all("table", {k: v for k, v in d.items()})
        self.oq = self.t["owner_question"]
        self.sem = self.t["semantics"]

    def shape(self, where: str, row, required: dict, optional: dict) -> bool:
        if not isinstance(row, dict):
            self.add("TABLE", f"{where}: not a table")
            return False
        if set(row) - set(required) - set(optional) or set(required) - set(row):
            self.add("TABLE", f"{where}: unknown keys {sorted(set(row) - set(required) - set(optional))}, missing keys {sorted(set(required) - set(row))}")
            return False
        wrong = sorted(k for k, v in row.items() if not isinstance(v, {**required, **optional}[k]) or isinstance(v, bool) != ({**required, **optional}[k] is bool))
        if wrong:
            self.add("TABLE", f"{where}: fields {wrong} have the wrong type")
            return False
        # A size_change's items_added and items_removed are multisets: FREEZE compares them with the change's
        # item Counter, so a repeated item is two items of one name, and a repeat the change lacks fails there.
        # Every other list, those of each size_change entry included, repeats no element.
        C.repeated_elements(self.f, "TABLE", where, {k: ([{f: x for f, x in ch.items() if f not in MULTISET_KEYS} if isinstance(ch, dict) else ch
                                                          for ch in v] if k == "size_change" and isinstance(v, list) else v)
                                                     for k, v in row.items()})
        return True

    def cite_all(self, where: str, value, key: str = "") -> None:
        """Every {ref, quote} resolves; every free-text string carries only checked citations; lists name something."""
        if isinstance(value, dict):
            if "ref" in value or "quote" in value:
                if not CITE_KEYS <= set(value):
                    self.add("TABLE", f"{where}: a citation is {{ref, quote}}, not {value!r}")
                else:
                    self.resolver.resolve(self.f, "CITE", where, value["ref"], value["quote"])
            for k, v in value.items():
                if k not in CITE_KEYS:
                    self.cite_all(f"{where}.{k}", v, k)
        elif isinstance(value, list):
            if not value and key not in MAY_BE_EMPTY:
                self.add("TABLE", f"{where}: is empty; a list names something, and an optional one is omitted")
            for i, v in enumerate(value):
                self.cite_all(f"{where}[{i}]", v, key)
        elif isinstance(value, str) and key in FREE_TEXT_KEYS:
            C.check_prose(self.f, "TABLE", where, value, self.resolver)
            if C.FREE_TEXT_CITATION.search(C.PROSE_CITATION.sub(" ", value)):
                self.add("TABLE", f"{where}: carries a line citation outside the checked `REF «quote»` form: {value[:80]!r}")

    def question(self, where: str, oq: object, names: str | None = None) -> bool:
        """oq is an owner question; with `names`, its text names that word."""
        row = self.oq.get(oq) if isinstance(oq, str) else None
        if row is None:
            self.add("TABLE", f"{where}: {oq!r} is not an owner question")
            return False
        text = " ".join([row["question"], *row["options"], row["consequence"]])
        if names is not None and not word_in(names, text):
            self.add("DESIGN", f"{where}: {oq}'s text does not name {names}")
            return False
        return True

    # ---- PIN
    def pins_state(self) -> None:
        p = self.s["pins"]
        base, links = p.get("superproject_base"), p.get("gitlinks_at_base") or {}
        if not isinstance(base, str) or not C.HEX40.match(base) or C.git(self.o.repo, "merge-base", "--is-ancestor", base, "HEAD") is None:
            self.add("PIN", f"[pins].superproject_base {base!r} is not a commit HEAD descends from")
            self.base = None
            return
        self.base = base
        for name in SUBMODULES:
            listing = (C.git(self.o.repo, "ls-tree", base, f"first-party/{name}") or "").split()
            if len(listing) < 3 or listing[2] != links.get(name):
                self.add("PIN", f"[pins].gitlinks_at_base.{name} is {links.get(name)!r}; the base records {listing[2] if len(listing) > 2 else 'none'}")
        if set(links) != set(SUBMODULES):
            self.add("PIN", f"[pins].gitlinks_at_base names {sorted(links)}, not the nine submodules")
        head = {line.split("\t")[1].split("/", 1)[1] for line in (C.git(self.o.repo, "ls-tree", "HEAD", "first-party/") or "").splitlines() if " commit " in line}
        if head != set(SUBMODULES):
            self.add("PIN", f"HEAD's first-party gitlinks are {sorted(head)}, not {list(SUBMODULES)}")
        self.counts["gitlinks"] = {name: links.get(name, "") for name in SUBMODULES}

    # ---- DESIGN
    def design_rules(self) -> None:
        dsg = self.design
        if len(dsg.rc6) != 6 or not dsg.exits:
            self.add("DESIGN", f"the design parse found {len(dsg.rc6)} RC-6 items and {len(dsg.exits)} §5 exits")
        for item, line in sorted(dsg.rc6.items()):
            rows = [r for r in self.sem.values() if r["rc6_item"] == item]
            citing = [r for r in rows if r["freeze"] != "none" and any(cite_line(c.get("ref")) == line for c in r["design_refs"] if isinstance(c, dict))]
            if len(rows) != 1 or len(citing) != 1:
                self.add("DESIGN", f"RC-6 item {item} (design line {line}) needs exactly one frozen row citing it; rows {[r['id'] for r in rows]}")
                continue
            row = citing[0]
            tokens = [dsg.resolve(t) for t in re.findall(r"`([^`]+)`", dsg.lines[line - 1])]
            target = next((t for t in tokens if t), None)
            if target is None or target[0] != row["host"] or not (owns(target[1], row["own_paths"]) or any(p.rstrip("/") == target[1].rstrip("/") for p in row["own_paths"])):
                self.add("DESIGN", f"{row['id']}: RC-6 item {item} names {target}, which the row's own_paths ({row['host']}) do not cover")
        for rid, row in self.sem.items():
            if row["rc6_item"] not in dsg.rc6 and row["rc6_item"] != 0:
                self.add("DESIGN", f"{rid}: rc6_item {row['rc6_item']} is not an RC-6 item (0 for a row RC-6 does not list)")
            for field_, allowed in (("freeze", FREEZES), ("kind", KINDS), ("role_class", ROLE_CLASSES)):
                if row[field_] not in allowed:
                    self.add("TABLE", f"{rid}: {field_} {row[field_]!r} is not one of {allowed}")
            for oq in row["owner_questions"]:
                self.question(f"{rid} owner_questions", oq)
            self.exits(rid, row)

    def in_exit(self, where: str, exit_id: str, cite: object) -> bool:
        if exit_id not in self.design.exits:
            self.add("DESIGN", f"{where}: {exit_id!r} is not an exit of §5")
            return False
        line = cite_line(cite.get("ref")) if isinstance(cite, dict) else None
        a, b = self.design.exits[exit_id]
        if line is None or not a <= line <= b:
            self.add("DESIGN", f"{where}: exit {exit_id} must cite its own text (design lines {a}-{b})")
            return False
        return True

    def exits(self, rid: str, row: dict) -> None:
        dsg = self.design
        named = {e for e in dsg.exits if any(word_in(n, dsg.text(e)) for n in row["design_names"])}
        deleting = {e for e in named if re.search(r"\bdelet", dsg.text(e))}
        listed = {}
        for e in row["exits"]:
            if not isinstance(e, dict) or not {"id", "basis", "ref", "quote"} <= set(e) or set(e) - {"id", "basis", "ref", "quote", "owner_question"}:
                self.add("DESIGN", f"{rid}: an exit is {{id, basis, ref, quote[, owner_question]}}, not {e!r}")
                continue
            eid = e["id"]
            if not self.in_exit(f"{rid} exit {eid}", eid, e):
                continue
            listed[eid] = e
            if e["basis"] == "design" and eid not in named:
                self.add("DESIGN", f"{rid}: exit {eid} is marked design, but its text names none of {row['design_names']}")
            elif e["basis"] == "proposed":
                self.question(f"{rid} proposed exit {eid}", e.get("owner_question"), eid)
                if eid in named:
                    self.add("DESIGN", f"{rid}: exit {eid}'s text names the row, so it is a design exit, not proposed")
            elif e["basis"] != "design":
                self.add("DESIGN", f"{rid}: exit {eid} basis must be design or proposed")
        excluded = set()
        for x in row.get("exits_excluded", []):
            if isinstance(x, dict) and x.get("id") in named and self.question(f"{rid} exits_excluded", x.get("owner_question"), x.get("id")):
                excluded.add(x["id"])
            else:
                self.add("DESIGN", f"{rid}: exits_excluded {x!r} is not a design-named exit with an owner question naming it")
        for eid in sorted(named - set(listed) - excluded):
            self.add("DESIGN", f"{rid}: §5 exit {eid} names the row but is neither listed nor excluded by an owner question")
        deleted = row["deleted_at"]
        eid = deleted.get("exit")
        if deleting and eid not in deleting and not all(self.question(f"{rid} deleted_at", deleted.get("owner_question"), x) for x in deleting):
            self.add("DESIGN", f"{rid}: the design deletes the row at {sorted(deleting)}, but deleted_at is {eid!r}")
        if eid:
            if eid not in listed:
                self.add("DESIGN", f"{rid}: deleted_at {eid} is not one of the row's exits")
            elif listed[eid]["basis"] == "design" and eid not in deleting:
                self.add("DESIGN", f"{rid}: deleted_at {eid} is marked design, but its text does not delete the row")
        elif not deleted.get("reason") or not (deleted.get("owner_question") or deleted.get("ref")):
            self.add("DESIGN", f"{rid}: deleted_at without an exit needs a reason and an owner question or a design citation")
        elif deleted.get("owner_question"):
            self.question(f"{rid} deleted_at", deleted["owner_question"])
        for g in row.get("growth_allowed", []):
            if not isinstance(g, dict) or g.get("exit") not in named or not self.in_exit(f"{rid} growth_allowed", g.get("exit"), g):
                self.add("DESIGN", f"{rid}: growth_allowed {g!r} must be a design-named exit citing its own text")
        for cap in row["capability"]:
            text = cap.get("capability") if isinstance(cap, dict) else None
            if not isinstance(text, str) or set(cap) - {"capability", "covered_by", "covered_later_by", "retained_elsewhere", "unconsumed", "needed_until", "gap", "owner_question"}:
                self.add("TABLE", f"{rid}: capability {cap!r} has unknown fields or no text")
                continue
            for field_ in ("covered_by", "covered_later_by", "needed_until"):
                for c in cap.get(field_, []):
                    self.in_exit(f"{rid} capability {text[:40]!r} {field_}", c.get("exit") if isinstance(c, dict) else None, c)
            for ret in cap.get("retained_elsewhere", []):
                if not isinstance(ret, dict) or set(ret) != {"what", "file", "design"}:
                    self.add("TABLE", f"{rid}: capability {text[:40]!r} retained_elsewhere is {{what, file, design}}")
            supplied = cap.get("covered_by") or cap.get("retained_elsewhere") or cap.get("unconsumed") or cap.get("needed_until")
            if (not supplied or cap.get("covered_later_by")) and not (cap.get("gap") and self.question(f"{rid} capability gap", cap.get("owner_question"))):
                self.add("DESIGN", f"{rid}: capability {text[:60]!r} has no covering exit, so it states the gap and an owner question")
        oracle = row.get("oracle")
        if row["kind"] == "definitional" and not (isinstance(oracle, dict) and (set(oracle) == {"consumer"} or (set(oracle) == {"gap", "owner_question"} and self.question(f"{rid} oracle", oracle["owner_question"])))):
            self.add("TABLE", f"{rid}: oracle names its consuming test {{consumer}} or {{gap, owner_question}}")

    def oracles(self) -> None:
        """A consuming test an oracle cites is a recorded consumer of its row (after the searches ran)."""
        for rid, row in self.sem.items():
            ref = ((row.get("oracle") or {}).get("consumer") or {}).get("ref")
            parts = C.parse_ref(ref) if ref else None
            if parts is None:
                continue
            key = (SUPER, parts["path"]) if parts["source"] == "worktree" else tuple((parts["path"] or "").split("/", 1))
            if key not in self.consumer_paths.get(rid, {}):
                self.add("SEARCH", f"{rid}: the oracle's consuming test {key[0]}:{key[-1]} is no recorded consumer of the row")

    # ---- FREEZE
    def own_files(self, row: dict, rev: str) -> dict:
        key = (row["id"], rev)
        if key in self.own:
            return self.own[key]
        host, tree = row["host"], self.tree(row["host"], rev)
        files: dict = {}
        if tree is None:
            self.own[key] = files
            return files
        listing = self.listing(tree)
        excluded = set(row.get("size_exclude_components", []))
        seeds = [p for p in listing if p.endswith(tuple(row["size_suffixes"])) and not excluded & set(p.split("/")) and owns(p, row["own_paths"])]
        members = set(seeds)
        tree.prefetch(seeds)
        if row["freeze"] != "none":
            rust = [p for p in seeds if p.endswith(".rs")]
            path_targets = {self.join(posixpath.dirname(p), attr) for p in rust for inl, _, attr in rust_modules(tree.text(p) or "")[0] if attr and not inl}
            roots = [(p, posixpath.basename(p) in ("mod.rs", "lib.rs", "main.rs") or p in path_targets) for p in rust]
            members |= self.module_graph(tree, roots, None)[0]
        tree.prefetch(sorted(members))
        for p in sorted(members):
            text = tree.text(p)
            if text is None:
                self.add("FREEZE", f"{row['id']}: own file {host}:{p} cannot be read as UTF-8 at {rev}")
            else:
                files[(host, p)] = text
        self.own[key] = files
        return files

    @staticmethod
    def join(base: str, rel: str) -> str | None:
        path = posixpath.normpath(posixpath.join(base, rel))
        return None if path.startswith("../") or path == ".." else path

    def listing(self, tree) -> frozenset:
        """Every path of a tree. A path holding a newline is refused: `git cat-file --batch` reads one path per
        line, so such a path would hand every later file of a batch the content of the file before it."""
        cache = _TREE_CACHE.setdefault(tree, {})
        if "listing" not in cache:
            cache["listing"] = frozenset(tree.files())
        if id(tree) not in self.listed:
            self.listed.add(id(tree))
            for path in sorted(p for p in cache["listing"] if "\n" in p):
                self.add("PIN", f"{tree.repo} at {tree.rev} has a path holding a newline, which no batched read can address: {path!r}")
        return cache["listing"]

    def module_graph(self, tree, roots, package_dir) -> tuple[set, set]:
        """(member files, (file, inline module path)) of the module graph from roots [(path, is_mod_rs)]."""
        listing = self.listing(tree)
        nodes, inline, expanded, work = set(), set(), set(), list(roots)
        while work:
            wave = [(p, m) for p, m in dict.fromkeys(work) if (p, m) not in expanded]
            work = []
            nodes.update(p for p, _ in wave)
            tree.prefetch(sorted({p for p, _ in wave if p in listing}))
            for path, mod_rs in wave:
                expanded.add((path, mod_rs))
                text = tree.text(path) if path in listing else None
                if text is None or ("mod" not in text and "include" not in text):
                    continue
                decls, incs, inlines = rust_modules(text)
                d = posixpath.dirname(path)
                base = d if mod_rs else posixpath.join(d, posixpath.basename(path).removesuffix(".rs"))
                inline.update((path, "::".join(mp)) for mp in inlines)
                for inl, name, attr in decls:
                    b = posixpath.join(base, *inl)
                    if attr:
                        work.append((self.join(b if inl else d, attr), True))
                    elif posixpath.join(b, name + ".rs") in listing:
                        work.append((posixpath.join(b, name + ".rs"), False))
                    elif posixpath.join(b, name, "mod.rs") in listing:
                        work.append((posixpath.join(b, name, "mod.rs"), True))
                for kind, lit, manifest in incs:
                    target = self.join(package_dir if manifest and package_dir is not None else d, lit) if lit else None
                    if target in listing:
                        if kind == "include":
                            work.append((target, mod_rs))
                        else:
                            nodes.add(target)
        return {n for n in nodes if n in listing}, inline

    def freeze(self) -> None:
        owners: dict = {}
        for rid, row in self.sem.items():
            base_files = self.own_files(row, self.base) if self.base else {}
            base = files_digest(base_files)
            head_files = self.own_files(row, "HEAD")
            head = files_digest(head_files)
            recorded = row["baseline"]
            if (recorded.get("files"), recorded.get("lines"), recorded.get("digest")) != base:
                self.add("FREEZE", f"{rid}: recorded baseline {recorded.get('files')} files / {recorded.get('lines')} lines / {str(recorded.get('digest'))[:12]}, measured {base[0]} / {base[1]} / {base[2][:12]} at the base")
                self.discover(f"{rid} baseline = {{ files = {base[0]}, lines = {base[1]}, digest = \"{base[2]}\" }}")
            if not head_files:
                self.add("FREEZE", f"{rid}: the row owns no file at HEAD; a row owns the semantics it names")
            for k in head_files:
                if owners.setdefault(k, rid) != rid:
                    self.add("FREEZE", f"{rid}: own file {k[0]}:{k[1]} is also owned by {owners[k]}")
            parts = []
            for part in row.get("baseline_parts", []):
                got = files_digest({k: v for k, v in base_files.items() if owns(k[1], [part.get("path", "")])})[:2]
                parts.append(got[1])
                if (part.get("files"), part.get("lines")) != got:
                    self.add("FREEZE", f"{rid}: baseline part {part.get('path')} records {part.get('files')} / {part.get('lines')}, measured {got[0]} / {got[1]}")
            changes = row.get("size_change", [])
            status = "not frozen"
            if row["freeze"] != "none":
                expect = changes[-1].get("digest_after") if changes and isinstance(changes[-1], dict) else recorded.get("digest")
                status = ("unchanged" if not changes else f"follows {len(changes)} recorded change(s)") if head[2] == expect else "VIOLATION"
                if head[2] != expect:
                    changed = sorted(f"{k[0]}:{k[1]}" for k in set(base_files) | set(head_files) if base_files.get(k) != head_files.get(k))
                    self.add("FREEZE", f"{rid}: own files at HEAD are {head[0]} files / {head[1]} lines / {head[2][:12]}, not the recorded {str(expect)[:12]} (changed since the base: {changed[:5]}); an edit to a frozen semantics needs a dated size_change entry (§6)")
                    self.discover(f"{rid} HEAD = {{ files = {head[0]}, lines = {head[1]}, digest = \"{head[2]}\" }} changed {changed}")
                self.change_classes(row, base_files, head_files)
            elif changes:
                self.add("FREEZE", f"{rid}: a row with freeze = none records no size_change")
            self.claims(row, base[1], parts)
            self.counts.setdefault("rows", {})[rid] = (base, head, status)

    def change_classes(self, row: dict, base_files: dict, head_files: dict) -> None:
        rid, prev = row["id"], base_files
        prefixes = [ns["prefix"] for ns in self.t["namespace"].values() if rid in ns["rows"] and "pattern" not in ns]
        allowed = {g.get("exit") for g in row.get("growth_allowed", []) if isinstance(g, dict)}
        changes = row.get("size_change", [])
        for index, ch in enumerate(changes):
            where = f"{rid} size_change[{index}]"
            if not isinstance(ch, dict) or not {"date", "change_class", "files_delta", "lines_delta", "digest_after", "reason"} <= set(ch) or ch["change_class"] not in CHANGE_CLASSES or not C.DATE.match(str(ch["date"])):
                self.add("FREEZE", f"{where}: needs date, a change_class of {CHANGE_CLASSES}, files_delta, lines_delta, digest_after and reason")
                return
            last = index == len(changes) - 1
            if not last and not C.HEX40.match(str(ch.get("at", ""))):
                self.add("FREEZE", f"{where}: an entry a later entry follows names the superproject commit it measures (`at`)")
                return
            state = head_files if last and "at" not in ch else self.own_files(row, ch["at"])
            files, lines, dg = files_digest(state)
            pf, pl, _ = files_digest(prev)
            if (files - pf, lines - pl, dg) != (ch["files_delta"], ch["lines_delta"], ch["digest_after"]):
                self.add("FREEZE", f"{where}: records {ch['files_delta']} files / {ch['lines_delta']} lines / {str(ch['digest_after'])[:12]}, but the change is {files - pf} / {lines - pl} / {dg[:12]}")
            added_items, removed_items, before, after = Counter(), Counter(), set(), set()
            for k in set(prev) | set(state):
                a = item_names(k[1], prev[k]) if k in prev else Counter()
                b = item_names(k[1], state[k]) if k in state else Counter()
                added_items, removed_items = added_items + (b - a), removed_items + (a - b)
                before |= (kernel_names(k[1], prev[k], prefixes) | declared_names(k[1], prev[k], over=False)) if k in prev else set()
                after |= (kernel_names(k[1], state[k], prefixes) | declared_names(k[1], state[k], over=False)) if k in state else set()
            added_names, cls = after - before, ch["change_class"]
            if cls == "retirement":
                if not (ch.get("authority") == row["deleted_at"].get("exit") or ch.get("authority") in row["owner_questions"]):
                    self.add("FREEZE", f"{where}: a retirement's authority is the row's deletion exit or one of its owner questions")
                for k, text in state.items():
                    if k not in prev or not is_subsequence(text.split("\n"), prev[k].split("\n")):
                        self.add("FREEZE", f"{where}: a retirement only deletes lines, but {k[0]}:{k[1]} adds some")
            elif cls == "mechanical-rename":
                renames = [tuple(p) for p in ch.get("renames", []) if isinstance(p, list) and len(p) == 2]
                moved = {p[0]: p[1] for p in ch.get("path_renames", []) if isinstance(p, list) and len(p) == 2}
                expected = {}
                for (repo, path), text in prev.items():
                    for old, new in renames:
                        text = re.sub(rf"(?<![A-Za-z0-9_]){re.escape(old)}(?![A-Za-z0-9_])", new, text)
                    expected[(repo, moved.get(path, path))] = text
                if not renames and not moved or expected != state or not ch.get("forced_by"):
                    self.add("FREEZE", f"{where}: applying the recorded renames does not yield the files, or forced_by is missing (differs: {sorted(f'{k[0]}:{k[1]}' for k in set(expected) | set(state) if expected.get(k) != state.get(k))[:5]})")
            else:
                if (Counter(ch.get("items_added", [])), Counter(ch.get("items_removed", []))) != (added_items, removed_items):
                    self.add("FREEZE", f"{where}: items_added / items_removed must be {sorted(added_items.elements())} / {sorted(removed_items.elements())}")
                if cls == "oracle-bug-fix":
                    if added_names:
                        self.add("FREEZE", f"{where}: an oracle bug fix adds no kernel name, but adds {sorted(added_names)[:5]}")
                    if not isinstance(ch.get("regression_test"), dict):
                        self.add("FREEZE", f"{where}: an oracle bug fix cites its regression test")
                elif set(ch.get("names_added", [])) != added_names:
                    self.add("FREEZE", f"{where}: names_added must be {sorted(added_names)}")
                if cls == "growth" and ch.get("authority") not in allowed:
                    self.add("FREEZE", f"{where}: growth's authority is an exit of growth_allowed ({sorted(allowed)}), whose text names the row")
                if cls == "recorded-extension" and not (self.question(where, ch.get("owner_question"), rid) and ch.get("evidence")):
                    self.add("FREEZE", f"{where}: a recorded extension names an owner question whose text names {rid}, and cites its evidence")
            prev = state

    def claims(self, row: dict, lines: int, parts: list) -> None:
        for claim in row.get("rc6_claims", []):
            if not isinstance(claim, dict) or claim.get("kind") not in ("size", "text", "no-superproject-consumer") or claim.get("status") not in ("holds", "stale"):
                self.add("TABLE", f"{row['id']}: rc6_claim {claim!r} needs kind size|text|no-superproject-consumer and status holds|stale")
                continue
            quote = claim.get("design", {}).get("quote", "")
            if claim["kind"] == "text" and not claim.get("evidence"):
                self.add("TABLE", f"{row['id']}: a text rc6_claim cites its evidence")
            if claim["status"] == "stale" and not claim.get("correction"):
                self.add("TABLE", f"{row['id']}: a stale rc6_claim states its correction")
            if claim["kind"] == "size":
                nums = [int(x.replace(",", "")) for x in re.findall(r"(?<![~\d])(\d{1,3}(?:,\d{3})+|\d+)(?=\s+lines|,\s+\d|\s+of\b|\s+\[)", quote)]
                approx = [int(x) for x in re.findall(r"~(\d+)k\b", quote)]
                holds = bool(nums or approx) and all(n in [lines] + parts for n in nums) and all(round(lines / 1000) == a for a in approx)
                if holds != (claim["status"] == "holds") or (not holds and f"{lines:,}" not in claim.get("correction", "")):
                    self.add("FREEZE", f"{row['id']}: rc6_claim {claim.get('claim')!r} is marked {claim['status']}, but the measurement is {lines:,} lines (parts {parts})")

    # ---- HOST
    def host_universe(self) -> dict:
        """`repo:dir` -> rows: for each own file of a frozen row at HEAD, the nearest enclosing directory whose
        Cargo.toml has a [package] table, unless that directory lies under the row's own paths (then every file
        the package adds with the row's suffixes is an own file, and the freeze holds it)."""
        out: dict = {}
        for rid, row in self.sem.items():
            tree = self.tree(row["host"]) if row["freeze"] != "none" else None
            listing = self.listing(tree) if tree is not None else frozenset()
            for _, path in sorted(self.own_files(row, "HEAD") if tree is not None else ()):
                d = path
                while d:
                    d = posixpath.dirname(d)
                    manifest = posixpath.join(d, "Cargo.toml")
                    if manifest not in listing:
                        continue
                    try:
                        package = "package" in tomllib.loads(tree.text(manifest) or "")
                    except tomllib.TOMLDecodeError:
                        self.add("HOST", f"{row['host']}:{manifest} does not parse, so the package holding {path} is unknown")
                        break
                    if package:
                        if not owns(d, row["own_paths"]):
                            out.setdefault(f"{row['host']}:{d}", set()).add(rid)
                        break
        return out

    def host_crates(self) -> None:
        universe = self.host_universe()
        for key in sorted(set(universe) - set(self.t["host_crate"])):
            self.add("HOST", f"crate {key} holds own files of {sorted(universe[key])} and has no [[host_crate]] row")
        for key, hc in self.t["host_crate"].items():
            if key not in universe:
                self.add("HOST", f"host crate {key}: holds no own file of a frozen row at HEAD (stale)")
            elif set(hc["rows"]) != universe[key]:
                self.add("HOST", f"host crate {key}: rows {hc['rows']}, but it holds own files of {sorted(universe[key])}")
            sets = {}
            for rev in (self.base, "HEAD"):
                tree = self.tree(hc["repo"], rev) if rev else None
                manifest = tomllib.loads(tree.text(f"{hc['dir']}/Cargo.toml") or "") if tree else {}
                lib = posixpath.join(hc["dir"], (manifest.get("lib") or {}).get("path", "src/lib.rs"))
                if not manifest.get("package") or lib not in self.listing(tree):
                    self.add("HOST", f"host crate {key}: no package with a library target at {rev}")
                    return
                nodes, inline = self.module_graph(tree, [(lib, True)], hc["dir"])
                rust = sorted(n for n in nodes if n.endswith(".rs"))
                tree.prefetch(rust)
                for n in rust:
                    if tree.text(n) is None:
                        self.add("HOST", f"host crate {key}: module {n} is not UTF-8 text at {rev}, so the modules it declares are unknown")
                sets[rev] = ({f"{hc['repo']}:{p}" for p in nodes}, {f"{hc['repo']}:{p}::{mp}" for p, mp in inline})
            base_set, head_set = sets[self.base][0] | sets[self.base][1], sets["HEAD"][0] | sets["HEAD"][1]
            measured = (len(sets[self.base][0]), len(sets[self.base][1]), names_digest(base_set))
            if (hc["files"], hc["inline_modules"], hc["digest"]) != measured:
                self.add("HOST", f"host crate {key}: recorded {hc['files']} files / {hc['inline_modules']} inline modules / {hc['digest'][:12]}, measured {measured[0]} / {measured[1]} / {measured[2][:12]} at the base")
            expect = set(base_set)
            own = {f"{k[0]}:{k[1]}" for rid in hc["rows"] if rid in self.sem for k in self.own_files(self.sem[rid], "HEAD")}
            for ch in hc["changes"]:
                if not isinstance(ch, dict) or set(ch) != {"date", "added", "removed", "reason"}:
                    self.add("HOST", f"host crate {key}: a change is {{date, added, removed, reason}}")
                    continue
                expect = (expect | set(ch["added"])) - set(ch["removed"])
                for entry in ch["added"]:
                    if entry.split("::", 1)[0] in own:
                        self.add("HOST", f"host crate {key}: change {ch['date']} adds {entry}, (in) an own file of a frozen row: that is the row's size_change")
            # An own file of the crate's rows, at the base or at HEAD, is the freeze's to account for: FREEZE pins
            # every own file by content and refuses any edit, addition or removal without a size_change. The
            # module-tree comparison is over the modules beside the semantics, which only a change entry records.
            own |= {f"{k[0]}:{k[1]}" for rid in hc["rows"] if rid in self.sem for k in self.own_files(self.sem[rid], self.base)}
            beside_head = {e for e in head_set if e.split("::", 1)[0] not in own}
            beside_expect = {e for e in expect if e.split("::", 1)[0] not in own}
            status = "unchanged" if not hc["changes"] else f"follows {len(hc['changes'])} recorded change(s)"
            if beside_head != beside_expect:
                status = "VIOLATION"
                self.add("HOST", f"host crate {key}: the library module tree changed (added {sorted(beside_head - beside_expect)[:8]}, removed {sorted(beside_expect - beside_head)[:8]}); a new module beside a frozen semantics needs a recorded change")
            self.counts.setdefault("host", {})[key] = (measured[:2], (len(sets["HEAD"][0]), len(sets["HEAD"][1])), status)

    # ---- searches over the declared scope
    def pathspecs(self, repo: str) -> list[str]:
        scope = self.s["search_scope"]
        specs = [f"*{s}" for s in scope["suffixes"]] + [f"*{b}" for b in scope["basenames"]]
        specs += [f":(exclude){d.rstrip('/')}" for d in scope["excluded_top_dirs"]]
        specs += [f":(exclude){e['prefix'].rstrip('/')}" for e in scope["excluded"] if isinstance(e, dict) and e.get("repo") == repo]
        return specs

    def in_scope(self, repo: str, path: str) -> bool:
        scope = self.s["search_scope"]
        base = posixpath.basename(path)
        return (path.endswith(tuple(scope["suffixes"])) or base in scope["basenames"]) \
            and not path.startswith(tuple(d.rstrip("/") + "/" for d in scope["excluded_top_dirs"])) \
            and not any(isinstance(e, dict) and e.get("repo") == repo and path.startswith(e["prefix"]) for e in scope["excluded"]) \
            and not (repo == SUPER and path in SELF_FILES)

    def grep(self, repo: str, patterns, fixed: bool = True, paths=None) -> set[str]:
        """The files of `repo` at HEAD in the search scope holding one of `patterns`: `git grep -z -l`, with -F
        fixed strings or -E extended regular expressions, binary files included; within exactly the files `paths`
        when given. Names are read NUL-terminated, so git never quotes one."""
        patterns, tree = sorted(set(patterns)), self.tree(repo)
        if not patterns or tree is None or (paths is not None and not paths):
            return set()
        specs = [f":(literal){p}" for p in sorted(paths)] if paths is not None else self.pathspecs(repo)
        key = ("grep", tuple(patterns), fixed, tuple(specs), json.dumps(self.s["search_scope"], sort_keys=True))
        cache = _TREE_CACHE.setdefault(tree, {})
        if key not in cache:
            args = ["grep", "-z", "-l", "-F" if fixed else "-E"] + [x for p in patterns for x in ("-e", p)] + [tree.rev, "--", *specs]
            out = C.git(tree.repo, *args, binary=True, git_dir=tree.git_dir, ok_codes=(0, 1))
            found, prefix = set(), f"{tree.rev}:".encode()
            for entry in (out or b"").split(b"\0"):
                if entry and not entry.startswith(prefix):
                    self.add("SEARCH", f"git grep in {repo} named {entry[:80]!r}, which is no path at {tree.rev}")
                elif entry:
                    found.add(entry[len(prefix):].decode("utf-8", "surrogateescape"))
            cache[key] = (out is not None, {p for p in found if self.in_scope(repo, p)})
        if not cache[key][0]:
            self.add("SEARCH", f"git grep failed in {repo} at {tree.rev}")
        return cache[key][1]

    def texts(self, kind: str, repo: str, paths) -> dict:
        """path -> text at HEAD. A file that is not UTF-8 text (or a name that is not UTF-8) is reported under `kind`,
        never read as empty: the names it holds are unknown."""
        tree, out = self.tree(repo), {}
        if tree is None:
            self.add(kind, f"{repo}: repository tree at HEAD is unreadable, so its names are unknown")
            return out
        readable = sorted(p for p in paths if "\n" not in p and p == p.encode("utf-8", "surrogateescape").decode("utf-8", "replace"))
        tree.prefetch(readable)
        for path in sorted(paths):
            text = tree.text(path) if path in readable else None
            if text is None:
                self.add(kind, f"{repo}:{path!r} is not UTF-8 text at HEAD, so the names it holds cannot be read")
            else:
                out[path] = text
        return out

    def own_texts(self, rids) -> dict:
        return {k: v for rid in rids if rid in self.sem for k, v in self.own_files(self.sem[rid], "HEAD").items()}

    # ---- NAMESPACE
    def namespaces(self) -> None:
        prefix_rows = {k: ns for k, ns in self.t["namespace"].items() if "pattern" not in ns}
        # A name under a prefix is written with the prefix's last segment in every form that declares or names it:
        # `A.B.x`, `namespace A.B`, `namespace B` inside `namespace A`, `def B.x` inside `namespace A`. So a fixed-string
        # grep for the last segments names every file of the search scope that can hold one.
        segments = sorted({p.rsplit(".", 1)[-1] for p in prefix_rows})
        texts = {repo: self.texts("NAMESPACE", repo, self.grep(repo, segments)) for repo in REPOS}
        self.definers = set()
        for prefix, ns in self.t["namespace"].items():
            own = self.own_texts(ns["rows"])
            recorded = {}
            for od in ns["outside_definers"]:
                if not isinstance(od, dict) or not {"repo", "count", "digest", "reason"} <= set(od) or ("path" in od) == ("glob" in od):
                    self.add("NAMESPACE", f"namespace {prefix}: an outside definer is {{repo, path | glob, count, digest, reason}}")
                else:
                    recorded[(od["repo"], od.get("path") or od.get("glob"))] = od
            found: dict = {}
            if "pattern" in ns:
                scope = ns.get("scope") or {}
                rx, repo, under = re.compile(ns["pattern"]), scope.get("repo"), scope.get("paths") or []
                tree = self.tree(repo) if repo in REPOS and under else None
                files = [p for p in (self.listing(tree) if tree is not None else ()) if owns(p, under) and self.in_scope(repo, p) and (repo, p) not in own]
                if tree is None:
                    self.add("NAMESPACE", f"namespace {prefix}: scope {scope!r} names no repository and paths")
                for path, text in self.texts("NAMESPACE", repo, files).items() if tree is not None else ():
                    names = {n for n in declared_names(path, text) if any(rx.match(part) for part in n.split("."))}
                    if names:
                        entry = next((k for k in recorded if k[0] == repo and (k[1] == path or ("*" in k[1] and fnmatch.fnmatchcase(path, k[1])))), None)
                        found.setdefault(entry or (repo, path), set()).update(f"{path}:{n}" for n in names)
            else:
                subs = [p for p in prefix_rows if p.startswith(prefix + ".")]
                defined = set()
                for (repo, path), text in own.items():
                    names = kernel_names(path, text, [prefix]) | {n for n in declared_names(path, text, over=False) if in_namespace(n, prefix)}
                    defined |= {n for n in names if not any(in_namespace(n, s) for s in subs)}
                lean = any(p.endswith(".lean") for _, p in own)
                segment = prefix.rsplit(".", 1)[-1]
                for repo in REPOS:
                    for path, text in texts[repo].items():
                        if (repo, path) in own or segment not in text:  # no name under the prefix is written without it
                            continue
                        extra = {n for n in kernel_names(path, text, [prefix]) if not any(in_namespace(n, s) for s in subs)
                                 and n not in defined and n != prefix and not (lean and n.rsplit(".", 1)[0] in defined)}
                        # A declaration under the prefix is exempt only when the rows declare that exact name: a
                        # constructor or field mention of a defined name is not, a new name beside one is.
                        extra |= {n for n in declared_names(path, text) if in_namespace(n, prefix) and n != prefix and n not in defined
                                  and not any(in_namespace(n, s) for s in subs)}
                        if extra:
                            found[(repo, path)] = extra
                self.counts.setdefault("namespace_defined", {})[prefix] = len(defined)
            for key, names in sorted(found.items()):
                od = recorded.get(key)
                if od is None:
                    self.add("NAMESPACE", f"namespace {prefix}: {key[0]}:{key[1]} names {len(names)} kernel name(s) no defining row ({', '.join(ns['rows'])}) declares, e.g. {sorted(names)[:3]}; a new name in a frozen namespace is growth, never a consumer")
                    self.discover(f"namespace {prefix} outside definer {{ repo = \"{key[0]}\", path = \"{key[1]}\", count = {len(names)}, digest = \"{names_digest(names)}\" }} {sorted(names)[:4]}")
                elif (od["count"], od["digest"]) != (len(names), names_digest(names)):
                    self.add("NAMESPACE", f"namespace {prefix}: outside definer {key[0]}:{key[1]} records {od['count']} names / {od['digest'][:12]}, measured {len(names)} / {names_digest(names)[:12]} ({sorted(names)[:3]})")
                    self.discover(f"namespace {prefix} outside definer {key} count = {len(names)}, digest = \"{names_digest(names)}\"")
                if "*" not in key[1]:
                    self.definers.add(key)
            for key in sorted(set(recorded) - set(found)):
                self.add("NAMESPACE", f"namespace {prefix}: recorded outside definer {key[0]}:{key[1]} declares no name outside the rows (stale)")
            self.counts.setdefault("namespace", {})[prefix] = (ns["rows"], len(found), sum(len(v) for v in found.values()))

    # ---- SEARCH, CRATES, GATES
    def searches(self) -> None:
        by_row = self.t["search"]
        for rid in sorted(set(self.sem) - set(by_row)):
            self.add("SEARCH", f"{rid}: every row has a [[search]] entry")
        for rid in sorted(set(by_row) - set(self.sem)):
            self.add("SEARCH", f"search {rid}: no such row")
        # One grep per repository over the union of every search finds the candidate files; each row's hit set is its
        # own grep over exactly those files, which is the file set its grep over the whole scope would name.
        candidates = {repo: self.grep(repo, [t for s in by_row.values() for t in s["terms"]])
                      | self.grep(repo, [p for s in by_row.values() for p in s.get("patterns", [])], fixed=False) for repo in REPOS}
        self.consumer_paths: dict = {}
        for rid, s in sorted(by_row.items()):
            if rid not in self.sem:
                continue
            row = self.sem[rid]
            if not (s["terms"] or s.get("patterns")) and row["kind"] != "producer":
                self.add("SEARCH", f"search {rid}: a definitional row declares its search terms")
            own = set(self.own_texts([rid]))
            hits = {(repo, p) for repo in REPOS for p in self.grep(repo, s["terms"], paths=candidates[repo])
                    | self.grep(repo, s.get("patterns", []), fixed=False, paths=candidates[repo])} - own
            consumers = {}
            for c in s["consumers"] + s.get("beyond_search", []):
                if not isinstance(c, dict) or not {"repo", "path", "kind"} <= set(c):
                    self.add("SEARCH", f"search {rid}: a consumer is {{repo, path, kind[, reason, evidence]}}: {c!r}")
                    continue
                consumers[(c["repo"], c["path"])] = c
            beyond = {(c["repo"], c["path"]) for c in s.get("beyond_search", []) if isinstance(c, dict)}
            globs = [(m.get("repo"), m.get("glob"), m) for m in s["mentions"] if isinstance(m, dict) and set(m) == {"repo", "glob", "reason"}]
            if len(globs) != len(s["mentions"]):
                self.add("SEARCH", f"search {rid}: a mention is {{repo, glob, reason}}")
            used_c, used_g = Counter(), Counter()
            for repo, path in sorted(hits):
                by_c = [k for k in consumers if k[0] == repo and (k[1] == path or (k[1].endswith("/") and path.startswith(k[1])))]
                by_g = [g for g in globs if g[0] == repo and fnmatch.fnmatchcase(path, g[1])]
                used_c.update(by_c)
                used_g.update(g[1] for g in by_g if g)
                if len(by_c) + len(by_g) != 1:
                    self.add("SEARCH", f"search {rid}: hit {repo}:{path!r} is matched by {len(by_c)} consumer(s) and {len(by_g)} mention glob(s); each hit has exactly one disposition")
                    self.discover(f"search {rid} undispositioned hit {repo}:{path!r}")
            for key in sorted(consumers):
                if key in beyond:
                    tree = self.tree(key[0])
                    exists = tree is not None and (key[1] in self.listing(tree) or (key[1].endswith("/") and any(p.startswith(key[1]) for p in self.listing(tree))))
                    if not exists or used_c[key]:
                        self.add("SEARCH", f"search {rid}: beyond_search consumer {key[0]}:{key[1]} {'does not exist at HEAD' if not exists else 'is a hit of the search: record it under consumers'}")
                    if not consumers[key].get("evidence") or not consumers[key].get("reason"):
                        self.add("SEARCH", f"search {rid}: beyond_search consumer {key[0]}:{key[1]} states its reason and evidence")
                elif not used_c[key]:
                    self.add("SEARCH", f"search {rid}: consumer {key[0]}:{key[1]} is no hit of the search (stale)")
            for repo, glob, _ in globs:
                if not used_g[glob]:
                    self.add("SEARCH", f"search {rid}: mention glob {repo}:{glob} matches no hit (stale)")
            self.consumer_paths[rid] = consumers
            checked = s["checked_by"]
            if set(checked) - {"by_exits", "owner_question", "rule"} or not isinstance(checked.get("by_exits"), list) or not isinstance(checked.get("rule"), dict) \
                    or not set(checked["by_exits"]) <= {e.get("id") for e in row["exits"] if isinstance(e, dict)} \
                    or (not checked["by_exits"] and not self.question(f"search {rid} checked_by", checked.get("owner_question"))):
                self.add("SEARCH", f"search {rid}: checked_by names the row's exits whose change runs the gates on every consumer and gate unit, or an owner question, and the rule that makes them run")
            for cap in row["capability"]:
                unconsumed = cap.get("unconsumed") if isinstance(cap, dict) else None
                if isinstance(unconsumed, dict) and isinstance(unconsumed.get("names"), list):
                    # A file dispositioned as a mention (reviewed: names it, uses nothing) consumes nothing.
                    mentioned = {(repo, p) for repo, glob, _ in globs for r, p in hits if r == repo and fnmatch.fnmatchcase(p, glob)}
                    named = {(repo, p) for repo in REPOS for p in self.grep(repo, unconsumed["names"])} - own - mentioned
                    if named:
                        self.add("SEARCH", f"{rid}: capability {cap['capability'][:40]!r} is recorded unconsumed, but {sorted(named)[:3]} name {unconsumed['names']}")
            self.counts.setdefault("search", {})[rid] = {"terms": len(s["terms"]), "hits": len(hits), "consumers": len(consumers) - len(beyond),
                                                          "mentions": (len(globs), sum(used_g.values())), "beyond": len(beyond),
                                                          "super_consumers": sum(1 for k in consumers if k[0] == SUPER)}
        for rid, row in self.sem.items():
            for claim in row.get("rc6_claims", []):
                if isinstance(claim, dict) and claim.get("kind") == "no-superproject-consumer" and rid in self.counts.get("search", {}):
                    holds = self.counts["search"][rid]["super_consumers"] == 0 and not any(d.get("workspace", "").startswith(SUPER + ":") for d in by_row[rid].get("dependents", []) if isinstance(d, dict))
                    if holds != (claim.get("status") == "holds"):
                        self.add("SEARCH", f"{rid}: rc6_claim {claim.get('claim')!r} is marked {claim.get('status')}, but the row records {self.counts['search'][rid]['super_consumers']} superproject consumer(s)")

    def metadata(self) -> dict:
        """workspace key -> packages [{name, manifest (repo:path), dependencies [(name, kind, repo:dir)]}]."""
        if self.o.metadata is not None:
            return self.o.metadata
        key = ("metadata", tuple(sorted(self.t["workspace"])), tuple(getattr(self.tree(r), "rev", "") for r in REPOS))
        if key not in _CACHE:
            _CACHE[key] = self.read_metadata()
        for problem in _CACHE[key][1]:
            self.add("CRATES", problem)
        return _CACHE[key][0]

    def read_metadata(self) -> tuple[dict, list]:
        """(the packages, the problems met reading them), cached together so every run reports the problems."""
        targo = shutil.which("targo") or (os.environ.get("ATPKG_BIN") and shutil.which("targo", path=os.environ["ATPKG_BIN"]))
        if not targo:
            raise ToolMissing("targo is not on PATH or in $ATPKG_BIN; the crate graph is read with `targo metadata --no-deps --offline`")
        out: dict = {}
        problems: list[str] = []
        made: list[Path] = []
        with tempfile.TemporaryDirectory(prefix="d04-metadata-") as tmp:
            root = Path(tmp).resolve()
            target = re.compile(r"(^|/)(build\.rs|src/(lib|main)\.rs|(src/bin|tests|examples|benches)/[^/]+\.rs|(src/bin|tests|examples|benches)/[^/]+/main\.rs)$")
            for repo in REPOS:
                tree, prefix = self.tree(repo), (root if repo == SUPER else root / "first-party" / repo)
                listing = [p for p in sorted(self.listing(tree)) if not p.startswith("src/llvm-project/")]
                manifests = [p for p in listing if posixpath.basename(p) == "Cargo.toml"]
                tree.prefetch(manifests)
                explicit = set()
                for m in manifests:
                    try:
                        doc = tomllib.loads(tree.text(m) or "")
                    except tomllib.TOMLDecodeError:
                        continue
                    d = posixpath.dirname(m)
                    specs = [doc.get("lib") or {}] + [t for k in ("bin", "test", "example", "bench") for t in doc.get(k, []) if isinstance(t, dict)]
                    explicit |= {posixpath.normpath(posixpath.join(d, t["path"])) for t in specs if isinstance(t.get("path"), str)}
                    if isinstance((doc.get("package") or {}).get("build"), str):
                        explicit.add(posixpath.normpath(posixpath.join(d, doc["package"]["build"])))
                # A symbolic link (first-party/trust -> ..) is part of the tree a path dependency resolves through. A link
                # that resolves outside the materialized tree is removed once every link exists, so cargo never reads
                # outside it; cargo fails on a path dependency it cannot load, so one through such a link fails, never passes.
                entries = C.git(tree.repo, "ls-tree", "-r", "-z", tree.rev, binary=True, git_dir=tree.git_dir)
                if entries is None:
                    problems.append(f"{repo}: the tree at {tree.rev} cannot be listed with its modes")
                links = sorted(name.decode("utf-8", "surrogateescape") for meta, _, name in (e.partition(b"\t") for e in (entries or b"").split(b"\0"))
                               if meta.startswith(b"120000 "))
                links = [p for p in links if p in listing]
                tree.prefetch(links)
                for p in links:
                    link = tree.text(p)
                    if link is None or "\0" in link:
                        problems.append(f"{repo}:{p!r} is a symbolic link whose target cannot be read")
                        continue
                    (prefix / p).parent.mkdir(parents=True, exist_ok=True)
                    os.symlink(link, prefix / p)
                    made.append(prefix / p)
                wanted = sorted((set(manifests) | {p for p in listing if target.search(p)} | (explicit & set(listing))) - set(links))
                tree.prefetch(wanted)
                for p in wanted:
                    # cargo reads a manifest's text and only the existence of a target root.
                    text = tree.text(p)
                    if text is None and posixpath.basename(p) == "Cargo.toml":
                        problems.append(f"{repo}:{p} is not UTF-8 text at HEAD, so the crate graph cannot read it")
                        continue
                    (prefix / p).parent.mkdir(parents=True, exist_ok=True)
                    (prefix / p).write_text(text or "", encoding="utf-8")
            for link in made:
                if not Path(os.path.realpath(link)).is_relative_to(root):
                    link.unlink()
            for wkey, ws in sorted(self.t["workspace"].items()):
                manifest = (root if ws["repo"] == SUPER else root / "first-party" / ws["repo"]) / ws["manifest"]
                run = subprocess.run([targo, "metadata", "--no-deps", "--offline", "--format-version", "1", "--manifest-path", str(manifest)],
                                     capture_output=True, text=True, cwd=root)
                if run.returncode != 0:
                    problems.append(f"workspace {wkey}: targo metadata failed: {run.stderr.strip()[:300]}")
                    continue

                def rel(path: str) -> str | None:
                    try:
                        r = Path(path).resolve().relative_to(root).as_posix()
                    except ValueError:
                        return None
                    parts = r.split("/", 2)
                    return f"{parts[1]}:{parts[2] if len(parts) > 2 else ''}" if parts[0] == "first-party" and len(parts) > 1 else f"{SUPER}:{r}"
                out[wkey] = [{"name": p["name"], "manifest": rel(p["manifest_path"]),
                              "dependencies": [(dep["name"], dep["kind"] or "normal", rel(dep["path"]) if dep.get("path") else None) for dep in p["dependencies"]]}
                             for p in json.loads(run.stdout)["packages"]]
        return out, problems

    def crates(self) -> None:
        wanted = {rid: s["crates"] for rid, s in self.t["search"].items() if s.get("crates")}
        for rid, s in self.t["search"].items():
            if "dependents" in s and not s.get("crates"):
                self.add("CRATES", f"search {rid}: dependents are recorded only for crates")
        if not wanted:
            return
        packages = self.metadata()
        for rid, crates in sorted(wanted.items()):
            computed = set()
            for c in crates:
                if not isinstance(c, dict) or set(c) != {"repo", "dir", "package"}:
                    self.add("CRATES", f"search {rid}: a crate is {{repo, dir, package}}")
                    continue
                for wkey, pkgs in packages.items():
                    for p in pkgs:
                        kinds = sorted({kind for name, kind, path in p["dependencies"] if name == c["package"] and path == f"{c['repo']}:{c['dir']}"})
                        if kinds:
                            computed.add((wkey, p["name"], c["package"], tuple(kinds)))
            recorded = {(d.get("workspace"), d.get("package"), d.get("crate"), tuple(d.get("kinds", []))) for d in self.t["search"][rid].get("dependents", []) if isinstance(d, dict)}
            for extra in sorted(computed - recorded):
                self.add("CRATES", f"search {rid}: {extra[1]} ({extra[0]}) depends on {extra[2]} ({', '.join(extra[3])}), and is not a recorded dependent")
                self.discover(f'search {rid} dependent {{ workspace = "{extra[0]}", package = "{extra[1]}", crate = "{extra[2]}", kinds = {json.dumps(list(extra[3]))} }}')
            for stale in sorted(recorded - computed):
                self.add("CRATES", f"search {rid}: recorded dependent {stale} is not in the crate graph (stale)")
            self.counts.setdefault("dependents", {})[rid] = len(computed)

    def manifest_units(self) -> dict:
        m = self.s["gate_scope"].get("manifest") or {}
        text = self.text(m.get("repo", SUPER), m.get("path", "")) or ""
        lines = text.split("\n")
        start = next((i for i, l in enumerate(lines) if re.match(rf"^{re.escape(m.get('function', ''))}\(\)\s*\{{", l)), None)
        begin = next((i for i in range(start or 0, len(lines)) if "<<'EOF'" in lines[i]), None) if start is not None else None
        units = {}
        for line in lines[begin + 1:] if begin is not None else []:
            if line == "EOF":
                break
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = line.split("|")
            if len(parts) < 6 or parts[0] in units:
                self.add("GATES", f"gate manifest row {line[:60]!r} does not parse as id|profiles|category|required|date|command, or repeats an id")
                continue
            units[parts[0]] = "|".join(parts[5:])
        if not units:
            self.add("GATES", f"the gate manifest {m.get('repo')}:{m.get('path')} has no rows in {m.get('function')}")
        return units

    def matching_lines(self, lines: list, terms, patterns) -> set[int]:
        """Indexes of `lines` that hold one of the fixed strings `terms` or match one of the extended regular
        expressions `patterns`, read by git grep (-F, -E) as the searches are, so a pattern means one thing."""
        found: set[int] = set()
        with tempfile.TemporaryDirectory(prefix="d04-rows-") as tmp:
            (Path(tmp) / "rows").write_text("".join(f"{line}\n" for line in lines), encoding="utf-8")
            for fixed, wanted in ((True, terms), (False, patterns)):
                wanted = sorted({w for w in wanted if w})
                if not wanted:
                    continue
                out = C.git(tmp, "grep", "--no-index", "-h", "-n", "-F" if fixed else "-E", *[x for w in wanted for x in ("-e", w)], "--", "rows", ok_codes=(0, 1))
                if out is None:
                    self.add("GATES", f"git grep failed over the gate manifest rows for {wanted[:3]}")
                found |= {int(line.split(":", 1)[0]) - 1 for line in (out or "").splitlines()}
        return found

    def gates(self) -> None:
        units = self.manifest_units()
        manifest = f"{(self.s['gate_scope'].get('manifest') or {}).get('repo')}:{(self.s['gate_scope'].get('manifest') or {}).get('path')}"
        ids = sorted(units)
        for rid, s in sorted(self.t["search"].items()):
            terms = list(s["terms"]) + [c.get("package") for c in s.get("crates", []) if isinstance(c, dict)]
            terms += [k[1] for k, c in self.consumer_paths.get(rid, {}).items() if k[0] == SUPER and c.get("kind") == "script"]
            matched = {ids[i] for i in self.matching_lines([units[u] for u in ids], terms, s.get("patterns", []))}
            recorded = {}
            for g in s["gates"]:
                if not isinstance(g, dict) or set(g) != {"unit", "role", "reason"} or g["role"] not in ROLES:
                    self.add("GATES", f"search {rid}: a gate is {{unit, role ({'|'.join(ROLES)}), reason}}: {g!r}")
                else:
                    recorded[g["unit"]] = g
            for u in sorted(matched - set(recorded)):
                self.add("GATES", f"search {rid}: gate manifest row {u} matches the search and has no recorded disposition")
                self.discover(f"search {rid} gate {u}: {units[u][:120]}")
            for u in sorted(set(recorded) - matched):
                self.add("GATES", f"search {rid}: recorded gate {u} is {'no row of the manifest' if u not in units else 'a row the search does not match: record it under gates_beyond_search'}")
            beyond = 0
            for g in s.get("gates_beyond_search", []):
                if not isinstance(g, dict) or set(g) != {"source", "unit", "role", "reason", "evidence"} or g["role"] not in ROLES or not g["evidence"]:
                    self.add("GATES", f"search {rid}: a gate beyond the search is {{source, unit, role, reason, evidence}}: {g!r}")
                    continue
                beyond += 1
                if g["source"] not in self.t["gate_source"] and g["source"] != manifest:
                    self.add("GATES", f"search {rid}: gate {g['unit']} names source {g['source']}, which is no gate_source")
                elif g["source"] == manifest and (g["unit"] not in units or g["unit"] in matched):
                    self.add("GATES", f"search {rid}: gate {g['unit']} beyond the search is {'no manifest row' if g['unit'] not in units else 'matched by the search: record it under gates'}")
            self.counts.setdefault("gates", {})[rid] = (len(matched), beyond)
        self.counts["manifest_units"] = len(units)

    def gate_sources(self) -> None:
        names = set(self.s["gate_scope"]["hook_names"])
        required = set()
        for repo in REPOS:
            tree = self.tree(repo)
            for path in (self.listing(tree) if tree is not None else ()):
                if not self.in_scope_listing(repo, path):
                    continue
                if posixpath.basename(path) in names or path == "publish/config.sh" or "/.github/workflows/" in "/" + path:
                    required.add(f"{repo}:{path}")
        entries = self.t["gate_source"]
        for key in sorted(required - set(entries)):
            self.add("SOURCES", f"{key} is a git hook, release check or CI workflow file with no [[gate_source]] entry")
        for key, entry in sorted(entries.items()):
            tree = self.tree(entry["repo"])
            if tree is None or entry["path"] not in self.listing(tree):
                self.add("SOURCES", f"gate_source {key} does not exist at HEAD")
        self.counts["gate_sources"] = (len(required), len(entries))

    def in_scope_listing(self, repo: str, path: str) -> bool:
        return not (repo == SUPER and any(path.startswith(e["prefix"]) for e in self.s["search_scope"]["excluded"] if isinstance(e, dict) and e.get("repo") == repo))

    # ---- PROBE
    def probe(self) -> None:
        token = re.compile(self.s["probe"]["token"], re.I)
        negatives = self.t["probe_negative"]
        used = Counter()
        for key, neg in negatives.items():
            if neg["disposition"] not in NEGATIVE or ("*" in neg["key"] and neg["disposition"] != "not-rust"):
                self.add("PROBE", f"probe_negative {key}: disposition is not-rust or not-a-semantics, and only not-rust may be a glob")
        considered = [(loc.get("repo", SUPER), loc["path"]) for c in self.t["considered"].values() for loc in c["locations"] if isinstance(loc, dict) and loc.get("path")]
        counts = Counter()
        for repo in REPOS:
            tree = self.tree(repo)
            keys = set()
            for path in (self.listing(tree) if tree is not None else ()):
                if not path.endswith((".rs", ".lean")) or (repo == SUPER and not (path.split("/")[0] in self.s["probe"]["super_top_dirs"] or (path.startswith("compiler/") and "trust" in path.split("/")[1]))):
                    continue
                parts = path.split("/")
                for i, comp in enumerate(parts):
                    last = i == len(parts) - 1
                    stem = re.sub(r"\.(rs|lean)$", "", comp) if last else comp
                    if any(token.fullmatch(t) for t in re.split(r"[-_.]", stem) if t):
                        keys.add("/".join(parts[:i + 1]) + ("" if last else "/"))
                        break
            own = {k[1] for rid, row in self.sem.items() for k in self.own_files(row, "HEAD") if k[0] == repo}
            own_paths = [p for r in self.sem.values() if r["host"] == repo for p in r["own_paths"]]
            consumers = [k[1] for c in self.consumer_paths.values() for k in c if k[0] == repo]
            for key in sorted(keys):
                probe_file = key + "_.rs" if key.endswith("/") else key
                if key in own or (key.endswith("/") and any(p.startswith(key) for p in own)) or owns(key, own_paths) or owns(probe_file, own_paths):
                    cover = "row"
                elif any(p == key or (key.endswith("/") and p.startswith(key)) or (p.endswith("/") and key.startswith(p)) for p in consumers):
                    cover = "consumer"
                elif (repo, key) in self.definers:
                    cover = "definer"
                elif any(r == repo and (owns(key, [p]) or owns(probe_file, [p]) or key.rstrip("/") == p.rstrip("/")) for r, p in considered):
                    cover = "considered"
                else:
                    neg = next((k for k, n in negatives.items() if n["repo"] == repo and (n["key"] == key or ("*" in n["key"] and fnmatch.fnmatchcase(key, n["key"])))), None)
                    cover = "negative" if neg else None
                    used[neg] += 1
                if cover is None:
                    self.add("PROBE", f"probe key {repo}:{key} is covered by no row, consumer, outside definer, considered location or probe_negative; adjudicate it")
                    self.discover(f"probe uncovered {repo}:{key}")
                counts[cover or "uncovered"] += 1
        for key in sorted(set(negatives) - set(used)):
            self.add("PROBE", f"probe_negative {key} covers no probe key (stale)")
        self.counts["probe"] = dict(counts)

    # ---- other rows
    def others(self) -> None:
        for cid, c in self.t["considered"].items():
            if c["in_plan"] not in IN_PLAN:
                self.add("TABLE", f"considered {cid}: in_plan is one of {IN_PLAN}")
            if c["in_plan"] == "yes" and c.get("row") not in self.sem:
                self.add("TABLE", f"considered {cid}: in_plan yes names its row")
            if c["in_plan"] == "owner-decision":
                self.question(f"considered {cid}", c.get("owner_question"))
            for loc in c["locations"]:
                tree = self.tree(loc.get("repo", SUPER)) if isinstance(loc, dict) else None
                if tree is None or not any(owns(p, [loc["path"]]) for p in tree.files(loc["path"].split("*")[0].rsplit("/", 1)[0] if "*" in loc["path"] else loc["path"])):
                    self.add("TABLE", f"considered {cid}: location {loc!r} names no file at HEAD")
        referenced = set(re.findall(r'"(OQ-\d+)"', json.dumps([r for kind, rows in self.t.items() if kind != "owner_question" for r in rows.values()] + [self.s])))
        for oq in sorted(set(self.oq) - referenced):
            self.add("TABLE", f"owner question {oq} is referenced by no row (stale)")
        self.question("deliverable", self.s["deliverable"].get("owner_question"))
        for oq in self.oq:
            if not OQ_ID.match(oq):
                self.add("TABLE", f"owner question id {oq!r} is not OQ-<n>")
        for key, gs in self.t["gate_source"].items():
            if gs["disposition"] not in ("gate", "not-a-gate", "delegates"):
                self.add("TABLE", f"gate_source {key}: disposition is gate, not-a-gate or delegates")
        for key, hc in self.t["host_crate"].items():
            if not set(hc["rows"]) <= set(self.sem):
                self.add("TABLE", f"host_crate {key}: rows {hc['rows']} are not all rows")

    # ---- counts, document, judgments
    def render(self) -> str:
        """The counts block: only what a table entry records, or a measurement a predicate holds to one, so it
        changes only with a reviewed record. What moves unreviewed (the gitlinks at HEAD, an unfrozen row's files,
        hits a mention glob absorbs, the manifest's other rows, the probe keys) is checked, not published."""
        c, out = self.counts, []
        frozen = {rid for rid, row in self.sem.items() if row["freeze"] != "none"}
        out += ["| Repository | Gitlink at the base |", "|---|---|"]
        out += [f"| {n} | `{b[:12]}` |" for n, b in c.get("gitlinks", {}).items()]
        out += ["", "| Row | Freeze | Baseline files / lines / digest | HEAD files / lines / digest | Freeze check |", "|---|---|---|---|---|"]
        for rid, (base, head, status) in c.get("rows", {}).items():
            at_head = f"{head[0]} / {head[1]} / `{head[2][:12]}`" if rid in frozen else "-"
            out.append(f"| {rid} | {self.sem[rid]['freeze']} | {base[0]} / {base[1]} / `{base[2][:12]}` | {at_head} | {status} |")
        out += ["", "| Row | Design exits | Proposed exits (owner question) | Deleted at |", "|---|---|---|---|"]
        for rid, row in self.sem.items():
            exits = [e for e in row["exits"] if isinstance(e, dict)]
            design = ", ".join(e["id"] for e in exits if e.get("basis") == "design") or "-"
            proposed = ", ".join(f"{e['id']} ({e.get('owner_question')})" for e in exits if e.get("basis") == "proposed") or "-"
            deleted = row["deleted_at"].get("exit") or f"not named ({row['deleted_at'].get('owner_question') or 'design citation'})"
            out.append(f"| {rid} | {design} | {proposed} | {deleted} |")
        out += ["", "| Host crate | Rows | Files / inline modules at the base | At HEAD | Check |", "|---|---|---|---|---|"]
        for key, (base, head, status) in c.get("host", {}).items():
            out.append(f"| `{key}` | {', '.join(self.t['host_crate'][key]['rows'])} | {base[0]} / {base[1]} | {head[0]} / {head[1]} | {status} |")
        out += ["", "| Namespace | Rows | Names own files define | Outside definers | Their names |", "|---|---|---|---|---|"]
        for prefix, (rows, definers, names) in c.get("namespace", {}).items():
            defined = c.get("namespace_defined", {}).get(prefix, "-") if set(rows) <= frozen else "-"
            out.append(f"| `{prefix}` | {', '.join(rows)} | {defined} | {definers} | {names} |")
        out += ["", "| Row | Terms | Consumers (hits) | Mention globs | Consumers beyond the search | Dependents | Manifest rows matched | Gate units beyond the search |",
                "|---|---|---|---|---|---|---|---|"]
        for rid, s in sorted(c.get("search", {}).items(), key=lambda kv: list(self.sem).index(kv[0]) if kv[0] in self.sem else 99):
            gates = c.get("gates", {}).get(rid, (0, 0))
            out.append(f"| {rid} | {s['terms']} | {s['consumers']} | {s['mentions'][0]} | {s['beyond']} | {c.get('dependents', {}).get(rid, '-')} | {gates[0]} | {gates[1]} |")
        out += ["", "| Recorded and held at HEAD | Count |", "|---|---:|",
                f"| Hook, release-check and workflow files / gate_source entries | {c.get('gate_sources', (0, 0))[0]} / {c.get('gate_sources', (0, 0))[1]} |",
                f"| Considered entries / owner questions | {len(self.t['considered'])} / {len(self.oq)} |"]
        return "\n".join(out)

    def document(self) -> dict:
        path = self.o.doc or self.o.repo / DOC_REL
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            self.add("DOC", f"{path}: {error}")
            return {}
        C.check_block(self.f, "DOC", text, COUNTS_BLOCK, self.counts_text)
        sections = document_sections(self.f, text)
        for jid, body in sections.items():
            self.counts["doc_citations"] = self.counts.get("doc_citations", 0) + C.check_prose(self.f, "DOC", jid, body if isinstance(body, str) else "\n".join(body), self.resolver)
        return sections


def document_sections(findings: C.Findings, text: str) -> dict:
    """The document's reviewed sections and its outline, which places every section
    (common.document_judgments): a section moved between headings changes the outline judgment."""
    return C.document_judgments(findings, "DOC", text, generated=(COUNTS_BLOCK,))


def judgments(findings: C.Findings, table_text: str, document: dict) -> dict:
    """Every reviewed judgment, keyed `kind:key`: each row, each singleton table, the table's comments and the
    document's sections and outline. One id from two sources is refused."""
    data = tomllib.loads(table_text)
    rows = [(f"{kind}:{key(row)}", row) for kind, (_, _, key) in ROWS.items() for row in data.get(kind, []) if isinstance(row, dict)]
    tables = [(f"{name}:table", data.get(name)) for name in TABLES]
    return C.merge_judgments(findings, rows + tables + [("comments:table", C.toml_comments(table_text))] + list(document.items()))


def collect(options: Options | None = None) -> Result:
    options = options or Options()
    checker = Checker(options)
    result = Result(violations=checker.f.violations, counts=checker.counts, discovered=checker.discovered)
    if not checker.load():
        return result
    checker.rows()
    checker.pins_state()
    checker.design_rules()
    if checker.base:
        checker.freeze()
        checker.host_crates()
    checker.namespaces()
    checker.searches()
    checker.crates()
    checker.oracles()
    checker.gates()
    checker.gate_sources()
    checker.probe()
    checker.others()
    checker.counts_text = result.counts_text = checker.render()
    sections = checker.document()
    checker.counts["reviews"] = C.check_reviews(
        checker.f, options.registry or options.repo / REGISTRY_REL, DELIVERABLE, judgments(checker.f, checker.table_text, sections),
        JUDGMENT_KINDS, options.repo if options.check_history else None, REGISTRY_REL)
    return result


def main(argv: list[str] | None = None) -> int:
    if tomllib is None:
        print("semantics_retirement: Python 3.11+ (tomllib) is required", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", type=Path, default=REPO_ROOT)
    for name in ("table", "doc", "registry"):
        parser.add_argument(f"--{name}", type=Path)
    parser.add_argument("--minirust", type=Path)
    parser.add_argument("--print-counts", action="store_true")
    parser.add_argument("--write-counts", action="store_true", help="rewrite the document's counts block")
    parser.add_argument("--discover", action="store_true", help="print measured values that help write the table")
    args = parser.parse_args(argv)
    options = Options(repo=args.repo, table=args.table, doc=args.doc, registry=args.registry,
                      clones={"minirust": args.minirust}, discover=args.discover)
    try:
        result = collect(options)
    except (C.MissingClone, C.PinsError, ToolMissing) as error:
        print(f"semantics_retirement: {error}", file=sys.stderr)
        return 2
    for line in result.discovered:
        print(f"# {line}")
    if args.write_counts:
        doc = args.doc or args.repo / DOC_REL
        doc.write_text(C.replace_block(doc.read_text(encoding="utf-8"), COUNTS_BLOCK, result.counts_text), encoding="utf-8")
    elif args.print_counts:
        print(result.counts_text)
    if result.violations:
        print(f"\nsemantics_retirement: {len(result.violations)} violation(s)", file=sys.stderr)
        for violation in result.violations:
            print(f"  {violation}", file=sys.stderr)
        return 1
    print(f"semantics_retirement: OK ({len(result.counts.get('rows', {}))} rows, {result.counts.get('doc_citations', 0)} document citations, "
          f"{result.counts['reviews']['judgments']} reviewed judgments)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
