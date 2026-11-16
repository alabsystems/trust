#!/usr/bin/env python3
"""D0.2 UB coverage matrix checker: the Rust Reference's UB statements and Miri's tests/fail corpus,
each mapped onto a TrustSem Core UB reason or a Trust Language Decision (LD) entry.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.2 Stage 0.2 (deliverable
D0.2, exit E0.7). Table: docs/trust-core/ub-coverage-matrix.toml. Document:
docs/trust-core/UB_COVERAGE_MATRIX.md. Review registry: docs/trust-core/reviews/ub_coverage_matrix.toml.

The shared layers (pins, citations, uniqueness, generated blocks, reviewed judgments) are
scripts/trust_core/common.py's. This file holds the matrix's own rules; each EXITS NON-ZERO when
it fails. The document's Predicates section states them:

  PIN, TABLE   common: the MiniRust and Reference clones at EXTERNAL_PINS.toml's pins and this
               repository's alignment; HEAD:src/tools/miri/tests/fail is the tree [miri_pin]
               records; row keys and types, no duplicate row, no repeated list element, no line
               citation in free text; every `cites` citation resolves (common.Resolver).
  REFERENCE    the universe is derived from the Reference at its pin by [reference_search]:
               every rule and list item of the UB chapter, and in every other src/ file each rule
               whose body matches the declared words, links into the chapter or has a validity
               id, and each such line outside a rule. Each unit has exactly one row; a row naming
               no unit is stale; kind, line and body digest are derived and compared. A row names
               its unit by rule, item and text, and by its line where units share those.
  MIRI         the universe is every tests/fail/**/*.rs at HEAD; revisions (one list, none
               repeated), compile flags, the stderr of each revision (none missing, none orphaned,
               no other file) and its first error line are derived; the class is derived by the
               [[class_form]] rows (exactly one base form, at most one refinement, no default) and
               the Tree Borrows detail form by the [[tb_form]] rows (exactly one).
  MAPPING      every reason is a vocabulary UB reason and every LD id an entry of the design's LD
               table (LD-1..LD-13, one consecutive block); no row names a [[settled_ld]] entry; the
               effect and disposition rules; the declared [[inclusion]], [[miri_coverage]] and
               [[name_rule]] scopes, re-run against the vocabulary and the rows.
  COUNT        [design_count] equals the number of Miri files, and each of its design quotes
               states that number; each [[deferred_check]] exit is quoted by one of its citations;
               [added_reasons] are trust-extension vocabulary reasons with a justification.
  DOC          the three generated blocks regenerate; every line is in a `prose:` section, a block
               or the outline, which lists the headings, block markers and section markers in order;
               every «quoted» citation resolves; every UB reason named exists; the pins are recorded.
  REVIEW       common.check_reviews over every table row and singleton table, the table's
               comments (each with the line it heads), every prose section and the outline. A row
               that names an LD entry, mentions
               one in its note or cites its design row carries that row's text in its judgment, so
               an amended LD row needs a new review of every row relying on it.

Usage:
    scripts/trust_core/ub_coverage_matrix.py [--minirust DIR] [--reference DIR] [--repo DIR]
        [--table FILE] [--doc FILE] [--registry FILE] [--vocabulary FILE] [--write-blocks]

Exit codes: 0 every predicate holds; 1 a violation; 2 a clone is missing or the pins are unreadable.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import argparse
import collections
import hashlib
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

tomllib = C.tomllib
REPO_ROOT = C.REPO_ROOT
DESIGN_REL = C.DESIGN_REL
TABLE_REL = "docs/trust-core/ub-coverage-matrix.toml"
DOC_REL = "docs/trust-core/UB_COVERAGE_MATRIX.md"
VOCAB_REL = "docs/trust-core/core-vocabulary.toml"
REGISTRY_REL = f"{C.REVIEWS_DIR}/ub_coverage_matrix.toml"
DELIVERABLE = "ub_coverage_matrix"
SCHEMA = "trust.core.ub-coverage-matrix.v2"
READS = {"minirust": "minirust", "rust-reference": "reference"}  # EXTERNAL_PINS source -> citation source
MIRI = "src/tools/miri/"
FAIL = "tests/fail/"
CHAPTER = "src/behavior-considered-undefined.md"
COUNTS, LISTS, ADDED = "ub-coverage-matrix-counts", "ub-coverage-matrix-lists", "ub-coverage-matrix-added-reasons"

EFFECTS = ("ub", "definition", "not-ub", "scope", "library-invariant")
UB_CLASSES = ("ub", "ub-stacked-borrows", "ub-tree-borrows", "ub-data-race")
NON_UB_CLASSES = ("abort", "unsupported", "resource-exhaustion", "memory-leak", "deadlock",
                  "post-monomorphization-error", "link-error", "compile-error", "no-entry-point")
CLASSES = UB_CLASSES + ("const-eval-error",) + NON_UB_CLASSES
DISPOSITIONS = ("reason", "ld", "no-core-ub", "non-ub")
BASES = ("miri-internal", "miri-analysis-mode", "minirust-divergence")
TB_FORMS = ("child", "foreign", "dealloc", "no-exposed")
SWITCHES = ("-Zmiri-disable-validation", "-Zmiri-disable-alignment-check", "-Zmiri-disable-stacked-borrows",
            "-Zmiri-symbolic-alignment-check", "-Zmiri-permissive-provenance", "-Zmiri-strict-provenance",
            "-Zmiri-recursive-validation", "-Zmiri-tree-borrows-implicit-writes")
LD_IDS = tuple(f"LD-{n}" for n in range(1, 14))
LD_ROW = re.compile(r"^\| (LD-\d+) \| ")
LD_MENTION = re.compile(r"\bLD-\d+\b")
EXIT_ID = re.compile(r"^E\d+(?:\.\d+)+[a-z]?$")
REASON_NAME = re.compile(r"`((?:UbReason|TreeBorrowsUb)\.[A-Za-z0-9]+)`")

RULE_RE = re.compile(r"^r\[([A-Za-z0-9_.\-]+)\]\s*$")
HEADING_RE = re.compile(r"^#{1,6} ")
FENCE_RE = re.compile(r"^\s*(```|~~~)")
ITEM_RE = re.compile(r"^( *)\* (.*)$")
LINKDEF_RE = re.compile(r"^\[([^\]]+)\]:\s*(\S+)")

S, I, L, B, D = str, int, list, bool, dict
# kind -> ({field: (type, element type)}, required fields, key). Every row of every kind is a judgment.
ROWS = {
    "reference": ({"file": (S, None), "rule": (S, None), "item": (S, None), "text": (S, None), "kind": (S, None),
                   "line": (I, None), "body_sha256": (S, None), "effect": (S, None), "reasons": (L, S), "ld": (L, S),
                   "note": (S, None), "cites": (L, D)},
                  {"file", "kind", "line", "body_sha256", "effect", "reasons", "ld", "note"},
                  lambda r: f"{r.get('file')}:{r.get('line')}"),
    "miri": ({"path": (S, None), "outcomes": (L, D), "note": (S, None), "cites": (L, D)},
             {"path", "outcomes", "note"}, lambda r: r.get("path")),
    "class_form": ({"id": (S, None), "class": (S, None), "refines": (S, None), "error": (S, None), "text": (S, None),
                    "cites": (L, D), "why": (S, None)}, {"id", "class"}, lambda r: r.get("id")),
    "tb_form": ({"form": (S, None), "pattern": (S, None), "cites": (L, D)}, {"form", "pattern", "cites"}, lambda r: r.get("form")),
    "inclusion": ({"id": (S, None), "rule": (S, None), "kind": (S, None), "site_files": (L, S), "raised_by": (L, S),
                   "inductive": (S, None), "reasons": (L, S), "ld": (L, S), "why": (S, None)},
                  {"id", "rule", "why"}, lambda r: r.get("id")),
    "miri_coverage": ({"directory": (S, None), "rules": (L, S), "why": (S, None)}, {"directory", "rules", "why"},
                      lambda r: r.get("directory")),
    "name_rule": ({"inductive": (S, None), "reasons": (L, S), "ld": (L, S), "classes": (L, S), "why": (S, None)},
                  {"inductive", "reasons", "ld", "classes", "why"}, lambda r: r.get("inductive")),
    "settled_ld": ({"id": (S, None), "cite": (D, None), "why": (S, None)}, {"id", "cite", "why"}, lambda r: r.get("id")),
    "deferred_check": ({"id": (S, None), "claim": (S, None), "replaces": (S, None), "checked_by": (L, S), "cites": (L, D)},
                       {"id", "claim", "replaces", "checked_by", "cites"}, lambda r: r.get("id")),
}
OUTCOME = ({"revision": (S, None), "stderr": (S, None), "error": (S, None), "class": (S, None), "disposition": (S, None),
            "reasons": (L, S), "ld": (L, S), "tb_protected": (B, None), "basis": (S, None)},
           {"revision", "stderr", "error", "class", "disposition", "reasons", "ld"})
# Singleton tables, each one judgment `<name>:table`.
SINGLETONS = {
    "miri_pin": ({"tests_fail_tree": (S, None), "why": (S, None)}, {"tests_fail_tree", "why"}),
    "reference_search": ({"words": (S, None), "validity_id": (S, None), "excluded": (L, S), "why": (S, None)},
                         {"words", "validity_id", "excluded", "why"}),
    "tracker": ({"default": (S, None), "flags": (L, L), "implicit_writes": (S, None), "cites": (L, D)},
                {"default", "flags", "implicit_writes", "cites"}),
    "specific": ({"stacked": (D, None), "tree": (D, None), "retag_access": (S, None), "why": (S, None)},
                 {"stacked", "tree", "retag_access", "why"}),
    "design_count": ({"count": (I, None), "cites": (L, D), "why": (S, None)}, {"count", "cites", "why"}),
    "added_reasons": ({"names": (L, S), "why": (S, None)}, {"names", "why"}),
}
TOP_KEYS = {"schema", "design", "vocabulary"} | set(ROWS) | set(SINGLETONS)
FREE_TEXT = ("note", "why", "claim", "replaces")
MAY_BE_EMPTY = {"reasons", "ld"}
JUDGMENT_KINDS = set(ROWS) | set(SINGLETONS) | {"comments", "prose", "outline"}


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


@dataclass
class Options:
    repo: Path = REPO_ROOT
    table: Path | None = None
    doc: Path | None = None
    registry: Path | None = None
    vocabulary: Path | None = None
    pins: Path | None = None
    clones: dict = field(default_factory=dict)
    trees: dict = field(default_factory=dict)  # citation source -> tree; mutation tests only
    check_pin_state: bool = True
    check_history: bool = True


@dataclass
class Result:
    violations: list = field(default_factory=list)
    counts: dict = field(default_factory=dict)
    blocks: dict = field(default_factory=dict)
    judgments: dict = field(default_factory=dict)


@dataclass(frozen=True)
class Unit:
    file: str
    rule: str | None
    item: str | None
    text: str | None
    kind: str
    line: int
    section: str
    body_sha256: str

    @property
    def key(self) -> tuple:
        return (self.file, self.rule or "", self.item or "", self.text or "")


@dataclass
class Outcome:
    revision: str
    stderr: str
    error: str | None
    klass: str | None
    flags: list
    tracker: str
    form: str | None
    text: str


@dataclass
class MiriFile:
    path: str
    revisioned: bool
    outcomes: list
    source: str


# --------------------------------------------------------------------------
# the Reference universe
# --------------------------------------------------------------------------


def reference_blocks(lines: list[str]) -> list[dict]:
    """The file split at rule ids; a heading after text inside a rule starts an unruled block."""
    out, fence, seen_text = [{"rule": None, "start": 1, "body": []}], False, False
    for number, text in enumerate(lines, 1):
        is_fence = bool(FENCE_RE.match(text))
        if not fence and not is_fence:
            m = RULE_RE.match(text)
            if m:
                out.append({"rule": m.group(1), "start": number, "body": []})
                seen_text = False
                continue
            if HEADING_RE.match(text) and out[-1]["rule"] is not None and seen_text:
                out.append({"rule": None, "start": number, "body": []})
                seen_text = False
        out[-1]["body"].append((number, text, fence or is_fence))
        seen_text = seen_text or bool(text.strip())
        fence = fence != is_fence
    return out


def body_digest(body: list) -> str:
    return sha256_text("\n".join(text for _, text, _ in body).strip("\n"))


def chapter_units(lines: list[str]) -> list[Unit]:
    h2 = [(n, t) for n, t in enumerate(lines, 1) if t.startswith("## ")]
    units = []
    for block in reference_blocks(lines):
        content = [(n, t) for n, t, _ in block["body"] if t.strip() and not LINKDEF_RE.match(t)]
        if block["rule"] is None:
            units += [Unit(CHAPTER, None, None, t.strip(), "text", n, "none", sha256_text(t.strip())) for n, t in content]
            continue
        first = content[0][0] if content else block["start"]
        heading = [t for n, t in h2 if n <= first]
        section = "list" if not heading else ("validity" if heading[-1] == "## Invalid values" else "definitions")
        items = [(n, len(m.group(1)), m.group(2).rstrip()) for n, t, code in block["body"]
                 if not code and not t.lstrip().startswith(">") for m in [ITEM_RE.match(t)] if m]
        digest = body_digest(block["body"])
        if items:
            units += [Unit(CHAPTER, block["rule"], t, None, "nested-list-item" if indent else "list-item", n, section, digest)
                      for n, indent, t in items]
        else:
            kind = "paragraph" if any(not HEADING_RE.match(t) for _, t in content) else "heading"
            units.append(Unit(CHAPTER, block["rule"], None, None, kind, block["start"], section, digest))
    return units


def other_units(tree, search: dict) -> list[Unit]:
    words = re.compile(search["words"], re.IGNORECASE)
    validity = re.compile(search["validity_id"])
    units = []
    files = [f for f in tree.files("src/", (".md",)) if f != CHAPTER and f not in search["excluded"]]
    tree.prefetch(files)
    for rel in files:
        lines = tree.lines(rel) or []
        labels = {m.group(1).lower() for t in lines for m in [LINKDEF_RE.match(t)]
                  if m and (CHAPTER.rsplit("/", 1)[1] in m.group(2) or m.group(2).startswith("undefined."))}

        def mentions(t: str) -> bool:
            if LINKDEF_RE.match(t):
                return False
            if words.search(t) or CHAPTER.rsplit("/", 1)[1] in t or "](undefined." in t:
                return True
            return any(label.lower() in labels for label in re.findall(r"\[([^\]]+)\](?!\()", t))

        for block in reference_blocks(lines):
            hits = [(n, t) for n, t, _ in block["body"] if mentions(t)]
            if block["rule"] is None:
                units += [Unit(rel, None, None, t.strip(), "text", n, "other", sha256_text(t.strip())) for n, t in hits]
            elif hits or validity.search(block["rule"]):
                content = [t for _, t, _ in block["body"] if t.strip() and not LINKDEF_RE.match(t)]
                kind = "rule" if any(not HEADING_RE.match(t) for t in content) else "heading"
                units.append(Unit(rel, block["rule"], None, None, kind, block["start"], "other", body_digest(block["body"])))
    return units


# --------------------------------------------------------------------------
# the Miri universe
# --------------------------------------------------------------------------


def annotations(source: str) -> tuple[list, dict]:
    """(every `//@revisions:` list, compile flags by revision); "" holds the flags of every revision."""
    revisions, flags = [], collections.defaultdict(list)
    for text in source.split("\n"):
        m = re.match(r"^\s*//@\s*revisions:\s*(.*)$", text)
        if m:
            revisions.append(m.group(1).split())
        m = re.match(r"^\s*//@\s*(?:\[([A-Za-z0-9_,]+)\])?\s*compile-flags:\s*(.*)$", text)
        if m:
            for rev in (m.group(1).split(",") if m.group(1) else [""]):
                flags[rev].extend(m.group(2).split())
    return revisions, flags


# --------------------------------------------------------------------------
# the checker
# --------------------------------------------------------------------------


class Checker:
    def __init__(self, options: Options) -> None:
        self.o = options
        self.f = C.Findings()
        self.counts: dict = {}
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
            vocabulary = tomllib.loads((o.vocabulary or o.repo / VOCAB_REL).read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError) as error:
            self.add("TABLE", f"the table or the vocabulary does not load: {error}")
            return False
        self.vocab = {r["name"]: r for r in vocabulary.get("ub_reason", []) if isinstance(r, dict) and isinstance(r.get("name"), str)}
        self.justified = {r.get("name"): r for r in vocabulary.get("extension_justification", []) if isinstance(r, dict)}
        design = self.resolver.tree_of("design", None)
        self.design_lines = design[0].lines(design[1]) or []
        return True

    def cite(self, where: str, cites: object) -> list:
        """Resolve a `cites` list of {ref, quote}; returns the citations that resolved."""
        good = []
        for c in cites if isinstance(cites, list) else []:
            self.cited += 1
            if not isinstance(c, dict) or set(c) != {"ref", "quote"}:
                self.add("TABLE", f"{where}: a citation is {{ref, quote}}, not {c!r}")
            elif self.resolver.resolve(self.f, "CITE", where, c["ref"], c["quote"]):
                good.append(c)
        return good

    def typed(self, where: str, row: object, spec: tuple) -> bool:
        fields, required = spec
        if not isinstance(row, dict):
            self.add("TABLE", f"{where}: not a table")
            return False
        if set(row) - set(fields) or required - set(row):
            self.add("TABLE", f"{where}: unknown keys {sorted(set(row) - set(fields))}, missing keys {sorted(required - set(row))}")
            return False
        wrong = sorted(k for k, v in row.items() if not isinstance(v, fields[k][0]) or (isinstance(v, bool) != (fields[k][0] is bool))
                       or (fields[k][1] is not None and not all(isinstance(x, fields[k][1]) for x in v)))
        if wrong:
            self.add("TABLE", f"{where}: fields {wrong} have the wrong type")
            return False
        C.repeated_elements(self.f, "TABLE", where, row)
        for name in sorted(k for k, v in row.items() if isinstance(v, (list, dict)) and not v and k not in MAY_BE_EMPTY):
            self.add("TABLE", f"{where}: {name} is empty; an optional list is omitted")
        for name in FREE_TEXT:
            if isinstance(row.get(name), str) and (not row[name].strip() or C.FREE_TEXT_CITATION.search(row[name])):
                self.add("TABLE", f"{where}: {name} is empty or carries an unchecked line citation")
        return True

    # ---- TABLE
    def rows(self) -> None:
        d = self.data
        for key in sorted(set(d) - TOP_KEYS):
            self.add("TABLE", f"top-level key {key!r} is not part of the schema")
        if d.get("schema") != SCHEMA or d.get("design") != DESIGN_REL or d.get("vocabulary") != VOCAB_REL:
            self.add("TABLE", f"schema, design and vocabulary are {SCHEMA}, {DESIGN_REL} and {VOCAB_REL}")
        self.t = {}
        for kind, (fields, required, key) in ROWS.items():
            valid = []
            for index, row in enumerate(d.get(kind, [])):
                where = f"{kind}[{index}] {key(row) if isinstance(row, dict) else ''}"
                if self.typed(where, row, (fields, required)):
                    self.cite(where, row.get("cites"))
                    valid.append(row)
            self.t[kind] = C.unique_rows(self.f, "TABLE", kind, valid, key)
        for key, row in self.t["class_form"].items():
            if not {"error", "text"} & set(row) or not {"cites", "why"} & set(row):
                self.add("TABLE", f"class_form {key}: a form matches an error line or a stderr text, and cites its source or says why")
        self.s = {}
        for name, spec in SINGLETONS.items():
            ok = self.typed(f"[{name}]", d.get(name), spec)
            self.s[name] = d[name] if ok else None
            if ok:
                self.cite(f"[{name}]", d[name].get("cites"))
        spec, tracker = self.s["specific"], self.s["tracker"]
        if spec is not None and not all(isinstance(spec[w], dict) and set(spec[w]) == {"label", "class", "directory", "tracker"}
                                        and all(isinstance(v, str) for v in spec[w].values()) for w in ("stacked", "tree")):
            self.add("TABLE", "[specific]: stacked and tree are {label, class, directory, tracker} strings")
            self.s["specific"] = None
        if tracker is not None and not all(len(pair) == 2 and all(isinstance(v, str) for v in pair) for pair in tracker["flags"]):
            self.add("TABLE", "[tracker]: flags are [flag, tracker] pairs of strings")
            self.s["tracker"] = None
        if any(v is None for v in self.s.values()):
            self.add("TABLE", "a singleton table is missing or malformed, so the universes cannot be derived")

    # ---- design: the LD table, settled entries, deferred checks, the design's Miri count
    def design(self) -> None:
        self.ld_text, self.ld_line = {}, {}
        for number, text in enumerate(self.design_lines, 1):
            m = LD_ROW.match(text)
            if m:
                if m.group(1) in self.ld_text:
                    self.add("MAPPING", f"the design's LD table names {m.group(1)} twice")
                self.ld_text.setdefault(m.group(1), text)
                self.ld_line.setdefault(m.group(1), number)
        lines = [self.ld_line.get(i) for i in LD_IDS]
        if sorted(self.ld_text, key=lambda s: int(s[3:])) != list(LD_IDS) or lines != list(range(lines[0] or 0, (lines[0] or 0) + len(LD_IDS))):
            self.add("MAPPING", f"the design's LD table is not exactly LD-1..LD-13 in one consecutive block: {sorted(self.ld_text)}")
        for key, row in self.t["settled_ld"].items():
            c = row["cite"]
            if key not in LD_IDS or set(c) != {"ref", "quote"} or c["ref"] != f"design:{self.ld_line.get(key)}":
                self.add("MAPPING", f"settled_ld {key}: cites {c.get('ref')!r}, not its LD row design:{self.ld_line.get(key)}")
            else:
                self.cite(f"settled_ld {key}", [c])
        for key, row in self.t["deferred_check"].items():
            quotes = [c.get("quote", "") for c in row["cites"] if isinstance(c, dict) and str(c.get("ref")).startswith("design:")]
            for exit_id in row["checked_by"]:
                if not EXIT_ID.match(exit_id) or not any(f"**{exit_id}**" in q for q in quotes):
                    self.add("COUNT", f"deferred_check {key}: checked_by {exit_id!r} is an exit id quoted by one of its design citations")

    def relied_ld(self, row: dict) -> list:
        """The LD entries a row relies on: named in it or its outcomes, mentioned in its note, or cited by design row."""
        names = set(row.get("ld") or []) | set(LD_MENTION.findall(row.get("note") or ""))
        names |= {e for o in row.get("outcomes") or [] if isinstance(o, dict) for e in o.get("ld") or []}
        by_line = {f"design:{n}": i for i, n in self.ld_line.items()}
        names |= {by_line[c.get("ref")] for c in row.get("cites") or [] if isinstance(c, dict) and c.get("ref") in by_line}
        return sorted(names, key=lambda s: (len(s), s))

    def names(self, where: str, reasons: list, ld: list) -> None:
        for name in reasons:
            if name not in self.vocab:
                self.add("MAPPING", f"{where}: {name} is no UB reason of the Core vocabulary")
        for entry in ld:
            if entry not in self.ld_text:
                self.add("MAPPING", f"{where}: {entry} is no entry of the design's LD table")
            elif entry in self.t["settled_ld"]:
                self.add("MAPPING", f"{where}: {entry} is settled by rank 1 ([[settled_ld]]); the matrix names an LD entry only for an open decision")
        for rule in self.t["name_rule"].values():
            if any(r.startswith(rule["inductive"] + ".") for r in reasons) and not (set(rule["reasons"]) <= set(reasons) and set(rule["ld"]) <= set(ld)):
                self.add("MAPPING", f"{where}: a {rule['inductive']} reason is named only with {rule['reasons']} and {rule['ld']}")

    # ---- REFERENCE
    def reference(self) -> None:
        tree = self.trees["reference"]
        lines = tree.lines(CHAPTER)
        if lines is None or self.s["reference_search"] is None:
            self.add("REFERENCE", f"{CHAPTER} is not readable at the Reference pin, or [reference_search] is malformed")
            self.units, self.ref_rows = [], {}
            return
        self.units = chapter_units(lines) + other_units(tree, self.s["reference_search"])
        by_key = collections.defaultdict(list)
        for unit in self.units:
            by_key[unit.key].append(unit)
        self.ref_rows = {}  # unit -> its row; units are distinct by file and line, so none collapses into another
        for row in self.t["reference"].values():
            key = (row["file"], row.get("rule") or "", row.get("item") or "", row.get("text") or "")
            where = f"reference {row['file']}:{row['line']} {key[1] or '(no rule)'}"
            candidates = by_key.get(key, [])
            if len(candidates) > 1:  # units that share a rule, item and text are told apart by their line
                candidates = [u for u in candidates if u.line == row["line"]]
                if not candidates:
                    self.add("REFERENCE", f"{where}: the units at lines {[u.line for u in by_key[key]]} share its rule, item and text, and its line is none of them")
                    continue
            if not candidates:
                self.add("REFERENCE", f"{where}: names no unit of the Reference at the pin (stale row)")
                continue
            unit = candidates[0]
            if unit in self.ref_rows:
                self.add("TABLE", f"{where}: a second row for one unit")
                continue
            for name, value in (("kind", unit.kind), ("line", unit.line), ("body_sha256", unit.body_sha256)):
                if row[name] != value:
                    self.add("REFERENCE", f"{where}: {name} is {row[name]!r}; derived {value!r}")
            self.ref_rows[unit] = row
            effect, reasons, ld = row["effect"], row["reasons"], row["ld"]
            self.names(where, reasons, ld)
            bullet = unit.file == CHAPTER and unit.kind.endswith("list-item") and unit.section in ("list", "validity")
            for bad, message in (
                (effect not in EFFECTS, f"effect {effect!r} is not one of {EFFECTS}"),
                (unit.kind == "heading" and effect != "scope", "a heading states no condition, so its effect is scope"),
                (effect in ("ub", "definition") and not (reasons or ld), f"effect {effect} maps to no reason and no LD entry"),
                (effect == "not-ub" and not reasons, "a not-ub row names the reasons whose scope it bounds"),
                (effect in ("scope", "library-invariant") and bool(reasons or ld), f"effect {effect} maps to nothing"),
                (effect == "library-invariant" and unit.file == CHAPTER, "the UB chapter states language UB, not a library invariant"),
                (bullet and effect not in ("ub", "definition"), f"a bullet of the {unit.section} list maps to a reason or an LD entry (effect ub or definition)"),
            ):
                if bad:
                    self.add("MAPPING", f"{where}: {message}")
        for unit in self.units:
            if unit not in self.ref_rows:
                self.add("REFERENCE", f"unmapped Reference unit: {unit.file}:{unit.line} {unit.rule or '(no rule)'} {(unit.item or unit.text or unit.kind)[:80]!r}")
        self.inclusions()

    def inclusions(self) -> None:
        for key, inc in self.t["inclusion"].items():
            rows = [row for unit, row in self.ref_rows.items()
                    if unit.file == CHAPTER and unit.rule == inc["rule"] and inc.get("kind") in (None, unit.kind)]
            if not rows:
                self.add("MAPPING", f"inclusion {key}: names no row of rule {inc['rule']} (stale)")
            required = set(inc.get("reasons", []))
            for name, r in self.vocab.items():
                files = {s["ref"].rsplit(":", 1)[0] for s in r.get("sites") or [] if isinstance(s, dict) and "ref" in s}
                if ("site_files" in inc and files and files <= set(inc["site_files"])) \
                        or ("raised_by" in inc and r.get("raised_by") and set(r["raised_by"]) <= set(inc["raised_by"])) \
                        or ("inductive" in inc and name.startswith(inc["inductive"] + ".")):
                    required.add(name)
            for scope in ("site_files", "raised_by", "inductive"):
                if scope in inc and not required - set(inc.get("reasons", [])):
                    self.add("MAPPING", f"inclusion {key}: its {scope} scope selects no vocabulary reason (stale)")
            for row in rows:
                missing = sorted(required - set(row["reasons"]))
                if missing or not set(inc.get("ld", [])) <= set(row["ld"]):
                    self.add("MAPPING", f"inclusion {key}: reference {row['file']}:{row['line']} must include {missing} and LD {inc.get('ld', [])}")

    # ---- MIRI
    def miri_universe(self) -> list[MiriFile]:
        tree = self.trees["worktree"]
        forms = list(self.t["class_form"].values())
        tb_forms = list(self.t["tb_form"].values())
        tracker, specific = self.s["tracker"], self.s["specific"]
        if tracker is None or specific is None:
            return []
        paths = tree.files(MIRI + FAIL)
        tree.prefetch(paths)
        rels = {p[len(MIRI):] for p in paths}
        out, used = [], set()
        for rel in sorted(r for r in rels if r.endswith(".rs")):
            source = tree.text(MIRI + rel) or ""
            declared, flags = annotations(source)
            if len(declared) > 1 or any(len(set(r)) != len(r) for r in declared):
                self.add("MIRI", f"{rel}: its //@revisions lines {declared} are not one list of distinct revisions, so outcomes would share a stderr and a row")
            revisions = declared[-1] if declared else None
            for rev in flags:
                if rev and rev not in (revisions or []):
                    self.add("MIRI", f"{rel}: compile-flags for revision {rev!r}, which //@revisions does not name")
            outcomes = []
            for rev in revisions or [""]:
                name = f"{rel.rsplit('/', 1)[1][:-3]}{'.' + rev if rev else ''}.stderr"
                stderr_rel = f"{rel.rsplit('/', 1)[0]}/{name}"
                used.add(stderr_rel)
                where = f"{rel}{'[' + rev + ']' if rev else ''}"
                text = tree.text(MIRI + stderr_rel)
                all_flags = flags.get("", []) + (flags.get(rev, []) if rev else [])
                trk = next((t for flag, t in tracker["flags"] if flag in all_flags), tracker["default"])
                if text is None:
                    self.add("MIRI", f"{where}: its stderr {name} does not exist")
                    outcomes.append(Outcome(rev, name, None, None, all_flags, trk, None, ""))
                    continue
                error = next((t for t in text.split("\n") if re.match(r"^error(?:\[E\d+\])?: ", t)), None)
                klass = self.classify(where, text, error, forms)
                form = self.tb_form(where, text, tb_forms) if klass == "ub-tree-borrows" else None
                outcomes.append(Outcome(rev, name, error, klass, all_flags, trk, form, text))
            out.append(MiriFile(rel, revisions is not None, outcomes, source))
        for rel in sorted(rels - used - {r for r in rels if r.endswith(".rs")}):
            self.add("MIRI", f"{rel} is {'the stderr of no test revision' if rel.endswith('.stderr') else 'neither a test nor a stderr file'}")
        return out

    def classify(self, where: str, text: str, error: str | None, forms: list) -> str | None:
        def matches(form: dict) -> bool:
            return (error is not None and ("error" not in form or re.search(form["error"], error) is not None)
                    and ("text" not in form or form["text"] in text))
        base = [f["class"] for f in forms if "refines" not in f and matches(f)]
        if len(base) != 1:
            self.add("MIRI", f"{where}: the error line {error!r} matches the class forms {base}, not exactly one (there is no default class)")
            return None
        refined = [f["class"] for f in forms if f.get("refines") == base[0] and matches(f)]
        if len(refined) > 1:
            self.add("MIRI", f"{where}: the stderr matches several refinements {refined}")
            return None
        return refined[0] if refined else base[0]

    def tb_form(self, where: str, text: str, forms: list) -> str | None:
        found = [f["form"] for f in forms for line in text.split("\n") if re.match(f["pattern"], line)]
        if len(found) != 1:
            self.add("MIRI", f"{where}: the Tree Borrows stderr carries the detail forms {found}, not exactly one")
            return None
        return found[0]

    def specific(self, file: MiriFile, which: str) -> tuple[list, list]:
        """(revisions, why) of a file's outcomes that are Stacked- or Tree-Borrows-specific ([specific])."""
        rule, retag = self.s["specific"][which], re.compile(self.s["specific"]["retag_access"])
        reported = [o.klass == rule["class"] for o in file.outcomes]
        race = [o.klass == "ub-data-race" and bool(retag.search(o.error or "")) and o.tracker == rule["tracker"] for o in file.outcomes]
        directory = file.path.startswith(rule["directory"])
        revs = [o.revision for o, a, b in zip(file.outcomes, reported, race) if a or b or directory]
        why = [w for w, hit in ((f"{rule['label']} violation reported", any(reported)), (f"race with a {rule['label']} retag", any(race)),
                                (f"{rule['directory'][len(FAIL):]} directory", directory)) if hit]
        return revs, why

    def miri(self) -> None:
        self.files = self.miri_universe()
        by_path = {f.path: f for f in self.files}
        self.miri_rows = {}
        for path, row in self.t["miri"].items():
            where = f"miri {path}"
            file = by_path.get(path)
            if file is None:
                self.add("MIRI", f"{where}: names no tests/fail file at HEAD (stale row)")
                continue
            derived = {o.revision: o for o in file.outcomes}
            judged = {}
            for index, outcome in enumerate(row["outcomes"]):
                if self.typed(f"{where} outcome[{index}]", outcome, OUTCOME):
                    if outcome["revision"] in judged:
                        self.add("TABLE", f"{where}: repeats outcome {outcome['revision']!r}")
                    judged[outcome["revision"]] = outcome
            if sorted(judged) != sorted(derived):
                self.add("MIRI", f"{where}: outcomes for revisions {sorted(judged)}; derived {sorted(derived)}")
            for rev, outcome in judged.items():
                d = derived.get(rev)
                if d is None:
                    continue
                ow = f"{where}{'[' + rev + ']' if rev else ''}"
                for name, value in (("stderr", d.stderr), ("error", d.error), ("class", d.klass)):
                    if outcome[name] != value:
                        self.add("MIRI", f"{ow}: {name} is {outcome[name]!r}; derived {value!r}")
                self.outcome(ow, outcome, d, file, row, judged)
            self.miri_rows[path] = (row, file)
        for path in by_path:
            if path not in self.t["miri"]:
                self.add("MIRI", f"unmapped Miri tests/fail file: {path}")
        for key, cov in self.t["miri_coverage"].items():
            allowed = {r for unit, row in self.ref_rows.items() if unit.file == CHAPTER and unit.rule in cov["rules"] for r in row["reasons"]}
            if not any(p.startswith(key) for p in by_path) or not all(any(u.rule == r for u in self.units) for r in cov["rules"]):
                self.add("MAPPING", f"miri_coverage {key}: names no Miri directory or no chapter rule (stale)")
            for path, (row, _) in self.miri_rows.items():
                for o in row["outcomes"] if path.startswith(key) else []:
                    missing = sorted(set(o.get("reasons", [])) - allowed) if o.get("disposition") == "reason" else []
                    if missing:
                        self.add("MAPPING", f"miri_coverage {key}: {path}[{o['revision']}] names {missing}, which no row of {cov['rules']} names")

    def outcome(self, ow: str, o: dict, d: Outcome, file: MiriFile, row: dict, judged: dict) -> None:
        disposition, reasons, ld, klass = o["disposition"], o["reasons"], o["ld"], d.klass
        self.names(ow, reasons, ld)
        iw = self.s["tracker"]["implicit_writes"]
        error = d.error or ""
        rules = (
            (disposition not in DISPOSITIONS, f"disposition {disposition!r} is not one of {DISPOSITIONS}"),
            (klass in NON_UB_CLASSES and disposition != "non-ub", f"class {klass} is not UB, so its disposition is non-ub"),
            (klass in UB_CLASSES and disposition == "non-ub", f"class {klass} reports UB; its disposition is reason, ld or no-core-ub"),
            (disposition == "reason" and not reasons, "disposition reason names a reason"),
            (disposition == "ld" and (not ld or bool(reasons)), "disposition ld names LD entries and no reason"),
            (disposition in ("no-core-ub", "non-ub") and bool(reasons), f"disposition {disposition} names no reason"),
            ((disposition == "no-core-ub") != ("basis" in o) or o.get("basis", BASES[0]) not in BASES, f"exactly a no-core-ub outcome states a basis, one of {BASES}"),
            (o.get("basis") == "miri-analysis-mode" and "-Zmiri-symbolic-alignment-check" not in d.flags, "basis miri-analysis-mode needs -Zmiri-symbolic-alignment-check"),
            (o.get("basis") == "miri-internal" and not re.search(r"\bmiri_\w+", file.source), "basis miri-internal needs the test to call a `miri_*` interface"),
            (o.get("basis") == "minirust-divergence" and not any(str(c.get("ref")).startswith("minirust:") for c in row.get("cites", [])), "basis minirust-divergence cites the MiniRust text that raises no UB"),
            (klass == "ub-stacked-borrows" and (disposition != "ld" or "LD-1" not in ld), "a Stacked Borrows verdict is decided by LD-1 (disposition ld with LD-1)"),
            (klass == "ub-tree-borrows" and (disposition not in ("reason", "ld") or "LD-1" not in ld), "a Tree Borrows verdict is a reason or ld, with LD-1"),
            ("tb_protected" in o and not (klass == "ub-tree-borrows" and disposition == "reason" and d.form == "child"), "tb_protected is judged only for a Tree Borrows child access of disposition reason"),
            (klass == "ub-tree-borrows" and disposition == "reason" and d.form == "child" and "tb_protected" not in o, "a Tree Borrows child access of disposition reason needs the tb_protected judgment"),
            (klass == "ub-data-race" and (disposition not in ("reason", "ld") or "LD-4" not in ld), "a race verdict is a reason or ld, with LD-4"),
            (klass == "ub-data-race" and bool(re.search(self.s["specific"]["retag_access"], error)) and "LD-1" not in ld, "a race with a retag carries LD-1"),
            (klass == "ub-data-race" and disposition == "reason" and "Data race detected" in error and "UbReason.DataRace" not in reasons, "Miri's data race maps to UbReason.DataRace"),
            ("Race condition detected" in error and "UbReason.DataRace" in reasons, "Miri's race condition involves only atomic accesses, which is no data race"),
            ("<wildcard>" in error and "LD-3" not in ld, "an access through a wildcard provenance carries LD-3"),
            (klass not in UB_CLASSES + ("const-eval-error",) and bool(ld) and disposition != "non-ub", "LD entries on a non-UB class belong to a non-ub outcome"),
        )
        for bad, message in rules:
            if bad:
                self.add("MAPPING", f"{ow}: {message}")
        for rule in self.t["name_rule"].values():
            if any(r.startswith(rule["inductive"] + ".") for r in reasons) and klass not in rule["classes"]:
                self.add("MAPPING", f"{ow}: a {rule['inductive']} reason is named only for classes {rule['classes']}")
        if klass == "ub-tree-borrows" and iw in d.flags:
            twins = [x for x in file.outcomes if x is not d and x.klass == klass and iw not in x.flags and x.text == d.text]
            twin = judged.get(twins[0].revision) if twins else None
            keys = ("disposition", "reasons", "ld", "tb_protected")
            if twin is not None and any(twin.get(k) != o.get(k) for k in keys):
                self.add("MAPPING", f"{ow}: revision {twins[0].revision!r} prints the byte-identical report without {iw}, so this outcome is judged exactly as that revision")
            elif not twins and disposition != "ld":
                self.add("MAPPING", f"{ow}: a verdict under {iw} depends on LD-1's open parameter (disposition ld)")

    # ---- COUNT
    def count(self) -> None:
        dc = self.s["design_count"]
        if dc is not None:
            n = sum(1 for f in self.files)
            if dc["count"] != n:
                self.add("COUNT", f"[design_count] records {dc['count']}; {n} tests/fail files are read at HEAD")
            for c in dc["cites"]:
                if not isinstance(c, dict) or not re.search(rf"(?<!\d){dc['count']}(?!\d)", str(c.get("quote"))):
                    self.add("COUNT", f"[design_count]: the design quote {c!r} does not state the count {dc['count']}")
        added = self.s["added_reasons"]
        for name in added["names"] if added else []:
            if self.vocab.get(name, {}).get("origin") != "trust-extension" or name not in self.justified:
                self.add("COUNT", f"[added_reasons] {name} is no trust-extension vocabulary reason with an extension_justification")
        pin = self.s["miri_pin"]
        if pin is not None and self.o.check_pin_state:
            tree = (C.git(self.o.repo, "rev-parse", f"HEAD:{MIRI}{FAIL}".rstrip("/")) or "").strip()
            if tree != pin["tests_fail_tree"]:
                self.add("PIN", f"HEAD:{MIRI}{FAIL.rstrip('/')} is tree {tree or 'unknown'}, not the recorded {pin['tests_fail_tree']}")

    # ---- counts, lists, document
    def render(self) -> dict:
        c = self.counts

        def bucket(select) -> dict:
            chosen = [(u, self.ref_rows.get(u)) for u in self.units if select(u)]
            kinds = collections.Counter("unmapped" if r is None else {(True, True): "both", (True, False): "reason", (False, True): "ld",
                                        (False, False): "none"}[(bool(r["reasons"]), bool(r["ld"]))] for _, r in chosen)
            effects = collections.Counter(r["effect"] for _, r in chosen if r is not None)
            return {"total": len(chosen), **{k: kinds[k] for k in ("reason", "ld", "both", "none", "unmapped")},
                    "effects": " / ".join(str(effects[e]) for e in EFFECTS)}

        chapter_bullet = lambda u, s: u.file == CHAPTER and u.section == s and u.kind.endswith("list-item")  # noqa: E731
        c["ub_list"] = bucket(lambda u: chapter_bullet(u, "list"))
        c["ub_list_top"] = sum(1 for u in self.units if chapter_bullet(u, "list") and u.kind == "list-item")
        c["validity_list"] = bucket(lambda u: chapter_bullet(u, "validity"))
        c["validity_top"] = sum(1 for u in self.units if chapter_bullet(u, "validity") and u.kind == "list-item")
        c["chapter_other"] = bucket(lambda u: u.file == CHAPTER and not u.kind.endswith("list-item"))
        c["other_reference"] = bucket(lambda u: u.file != CHAPTER)
        c["chapter_rules"] = len({u.rule for u in self.units if u.file == CHAPTER and u.rule})
        outcomes = [(o, d) for row, file in self.miri_rows.values() for o in row["outcomes"] if isinstance(o, dict)
                    for d in [next((x for x in file.outcomes if x.revision == o.get("revision")), None)] if d]
        all_outcomes = [o for f in self.files for o in f.outcomes]
        c["miri_files"], c["miri_revisioned"], c["miri_outcomes"] = len(self.files), sum(f.revisioned for f in self.files), len(all_outcomes)
        c["by_class"] = {k: (sum(o.klass == k for o in all_outcomes), sum(any(o.klass == k for o in f.outcomes) for f in self.files)) for k in CLASSES}
        c["by_disposition"] = {k: sum(o.get("disposition") == k for o, _ in outcomes) for k in DISPOSITIONS}
        c["by_basis"] = {k: sum(o.get("basis") == k for o, _ in outcomes) for k in BASES}
        spec = {w: [(f, *self.specific(f, w)) for f in self.files] for w in ("stacked", "tree")}
        spec = {w: [(f, revs, why) for f, revs, why in v if revs] for w, v in spec.items()}
        for w, v in spec.items():
            c[f"{w}_files"] = (len(v), sum(len(revs) == len(f.outcomes) for f, revs, _ in v))
            c[f"{w}_outcomes"] = sum(len(revs) for _, revs, _ in v)
        c["both_specific"] = len({f.path for f, _, _ in spec["stacked"]} & {f.path for f, _, _ in spec["tree"]})
        c["by_tracker"] = {k: sum(o.tracker == k for o in all_outcomes) for k in ("stacked", "tree", "none")}
        c["by_switch"] = {s: sum(s in o.flags for o in all_outcomes) for s in SWITCHES}
        c["tb_forms"] = {k: sum(o.form == k for o in all_outcomes) for k in TB_FORMS}
        c["tb_protected"] = tuple(sum(o.get("tb_protected") is v for o, _ in outcomes) for v in (True, False))
        c["files_by_dispositions"] = collections.Counter("+".join(sorted({o.get("disposition") for o in row["outcomes"] if isinstance(o, dict)}))
                                                         for row, _ in self.miri_rows.values())
        ref_ld = collections.Counter(e for row in self.ref_rows.values() for e in row["ld"])
        miri_ld = collections.Counter(e for o, _ in outcomes for e in o.get("ld", []))
        c["ld_use"] = {k: (ref_ld[k], miri_ld[k]) for k in LD_IDS}
        ref_reasons = {r for row in self.ref_rows.values() for r in row["reasons"]}
        miri_reasons = {r for o, _ in outcomes for r in o.get("reasons", [])}
        names = set(self.vocab)
        c["reasons"] = (len(names), len((self.s["added_reasons"] or {}).get("names", [])), len(names & ref_reasons),
                        len(names & miri_reasons), len(names - ref_reasons - miri_reasons))

        e = lambda b: f"{b['total']} | {b['reason']} | {b['ld']} | {b['both']} | {b['none']} | {b['unmapped']} | {b['effects']}"  # noqa: E731
        out = ["| Reference universe | Units | Mapped to a reason only | To an LD entry only | To both | Row maps to nothing | Unmapped (no row) | Effect ub / definition / not-ub / scope / library-invariant |",
               "|---|---:|---:|---:|---:|---:|---:|---|",
               f"| UB list bullets in `{CHAPTER}` ({c['ub_list_top']} top-level, {c['ub_list']['total'] - c['ub_list_top']} nested): E0.7 | {e(c['ub_list'])} |",
               f"| Validity-list bullets in `{CHAPTER}` ({c['validity_top']} top-level, {c['validity_list']['total'] - c['validity_top']} nested) | {e(c['validity_list'])} |",
               f"| Other rules of `{CHAPTER}` ({c['chapter_rules']} rule ids in the chapter) | {e(c['chapter_other'])} |",
               f"| Rules and lines in the rest of `src/` selected by `[reference_search]` | {e(c['other_reference'])} |",
               "", "| Miri `tests/fail` | Count |", "|---|---:|",
               f"| `.rs` files / of which with revisions / outcomes (one per revision) | {c['miri_files']} / {c['miri_revisioned']} / {c['miri_outcomes']} |"]
        out += [f"| outcomes (files) of class `{k}` | {n} ({f}) |" for k, (n, f) in c["by_class"].items()]
        out += [f"| outcomes of disposition `{k}` | {n} |" for k, n in c["by_disposition"].items()]
        out += [f"| `no-core-ub` outcomes with basis `{k}` | {n} |" for k, n in c["by_basis"].items()]
        out += [f"| Stacked-Borrows-specific files / of which every outcome / outcomes (the unit E2.2.1 excludes) | {c['stacked_files'][0]} / {c['stacked_files'][1]} / {c['stacked_outcomes']} |",
                f"| Tree-Borrows-specific files / of which every outcome / outcomes | {c['tree_files'][0]} / {c['tree_files'][1]} / {c['tree_outcomes']} |",
                f"| files both Stacked- and Tree-Borrows-specific | {c['both_specific']} |"]
        out += [f"| outcomes run under borrow tracker `{k}` | {n} |" for k, n in c["by_tracker"].items()]
        out += [f"| outcomes run with `{k}` | {n} |" for k, n in c["by_switch"].items()]
        out += [f"| Tree Borrows outcomes with detail form `{k}` | {n} |" for k, n in c["tb_forms"].items()]
        out += [f"| Tree Borrows child-access protector judgments (protected / unprotected) | {c['tb_protected'][0]} / {c['tb_protected'][1]} |",
                "", "| Files by the set of dispositions of their outcomes | Files |", "|---|---:|"]
        out += [f"| {k} | {n} |" for k, n in sorted(c["files_by_dispositions"].items())]
        out += ["", "| LD entry | Design line | Reference rows | Miri outcomes |", "|---|---:|---:|---:|"]
        out += [f"| {k} | {self.ld_line.get(k)} | {r} | {m} |" for k, (r, m) in c["ld_use"].items()]
        out += ["", "| Core UB reasons | Count |", "|---|---:|",
                f"| in the vocabulary | {c['reasons'][0]} |", f"| of which added by D0.2 (`[added_reasons]`) | {c['reasons'][1]} |",
                f"| named by at least one Reference row | {c['reasons'][2]} |", f"| named by at least one Miri outcome | {c['reasons'][3]} |",
                f"| named by neither | {c['reasons'][4]} |"]
        blocks = {COUNTS: "\n".join(out)}

        def revs(rs):
            return ", ".join(r or "-" for r in rs)
        other = {"stacked": "tree", "tree": "stacked"}
        both = {w: {f.path for f, _, _ in spec[w]} for w in spec}
        lists = []
        for w, title in (("stacked", "Stacked"), ("tree", "Tree")):
            lists += [f"#### {title}-Borrows-specific files", "", f"| File | {title}-Borrows-specific revisions | Why (derived) | Also {other[w].capitalize()}-Borrows-specific |", "|---|---|---|---|"]
            lists += [f"| `{f.path}` | {revs(r)} | {'; '.join(why)} | {'yes' if f.path in both[other[w]] else 'no'} |" for f, r, why in spec[w]]
            lists.append("")
        rows = [(p, o) for p, (row, _) in sorted(self.miri_rows.items()) for o in row["outcomes"] if isinstance(o, dict)]
        lists += ["#### Outcomes Miri reports as UB that Core does not", "", "| File | Revision | Basis |", "|---|---|---|"]
        lists += [f"| `{p}` | {o['revision'] or '-'} | {o.get('basis')} |" for p, o in rows if o.get("disposition") == "no-core-ub"]
        lists += ["", "#### Outcomes decided by an LD entry (other than Stacked Borrows verdicts)", "", "| File | Revision | LD |", "|---|---|---|"]
        lists += [f"| `{p}` | {o['revision'] or '-'} | {','.join(o['ld'])} |" for p, o in rows if o.get("disposition") == "ld" and o.get("class") != "ub-stacked-borrows"]
        lists += ["", "#### LD entries named by no row", "", ", ".join(k for k, (r, m) in c["ld_use"].items() if not r and not m) or "(none)"]
        lists += ["", "#### Core UB reasons named by no Reference row", "", ", ".join(f"`{n}`" for n in sorted(names - ref_reasons)) or "(none)"]
        lists += ["", "#### Core UB reasons named by no Reference row and no Miri outcome", "", ", ".join(f"`{n}`" for n in sorted(names - ref_reasons - miri_reasons)) or "(none)"]
        blocks[LISTS] = "\n".join(lists)
        added = ["| Reason | Rank-1 source (the vocabulary's `[[extension_justification]]` citations) |", "|---|---|"]
        for name in (self.s["added_reasons"] or {}).get("names", []):
            cites = [f"{x.get('ref')} «{x.get('quote')}»" for x in (self.justified.get(name) or {}).get("cites", []) if isinstance(x, dict)]
            added.append(f"| `{name}` | {'<br>'.join(cites)} |")
        blocks[ADDED] = "\n".join(added)
        return blocks

    def document(self, blocks: dict) -> dict:
        path = self.o.doc or self.o.repo / DOC_REL
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            self.add("DOC", f"{path}: {error}")
            return {}
        for name, body in blocks.items():
            C.check_block(self.f, "DOC", text, name, body)
        sections = C.document_judgments(self.f, "DOC", text, generated=tuple(blocks))
        self.counts["doc_citations"] = sum(C.check_prose(self.f, "DOC", jid, body, self.resolver)
                                           for jid, body in sections.items() if isinstance(body, str))
        pins = [self.pins.alignment] + [self.pins.sources[n].revision for n in READS]
        pins += [self.s["miri_pin"]["tests_fail_tree"]] if self.s["miri_pin"] else []
        for revision in pins:
            if f"`{revision}`" not in text:
                self.add("DOC", f"the document does not record the pin `{revision}`")
        for name in sorted(set(REASON_NAME.findall(text)) - set(self.vocab)):
            self.add("DOC", f"the document names `{name}`, which is not a vocabulary UB reason")
        return sections

    def judgments(self, sections: dict) -> dict:
        data = self.data
        pairs = []
        for kind, (_, _, key) in ROWS.items():
            for row in data.get(kind, []):
                if isinstance(row, dict):
                    content = row
                    if kind in ("reference", "miri"):
                        relied = self.relied_ld(row)
                        content = dict(row, relies_on_ld_rows={e: self.ld_text.get(e) for e in relied}) if relied else row
                    pairs.append((f"{kind}:{key(row)}", content))
        pairs += [(f"{name}:table", data[name]) for name in SINGLETONS if name in data]
        pairs.append(("comments:table", C.toml_comments(self.table_text)))
        return C.merge_judgments(self.f, pairs + list(sections.items()))


def collect(options: Options | None = None) -> Result:
    options = options or Options()
    checker = Checker(options)
    result = Result(violations=checker.f.violations, counts=checker.counts)
    if not checker.load():
        return result
    checker.rows()
    if any(v is None for v in checker.s.values()):
        return result
    checker.design()
    checker.reference()
    checker.miri()
    checker.count()
    result.blocks = checker.render()
    sections = checker.document(result.blocks)
    checker.counts["citations"] = checker.cited
    result.judgments = checker.judgments(sections)
    checker.counts["reviews"] = C.check_reviews(
        checker.f, options.registry or options.repo / REGISTRY_REL, DELIVERABLE, result.judgments,
        JUDGMENT_KINDS, options.repo if options.check_history else None, REGISTRY_REL)
    return result


def main(argv: list[str] | None = None) -> int:
    if tomllib is None:
        print("ub_coverage_matrix: Python 3.11+ (tomllib) is required", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--minirust", type=Path)
    parser.add_argument("--reference", type=Path)
    parser.add_argument("--repo", type=Path, default=REPO_ROOT)
    for name in ("table", "doc", "registry", "vocabulary"):
        parser.add_argument(f"--{name}", type=Path)
    parser.add_argument("--write-blocks", action="store_true", help="rewrite the document's generated blocks")
    args = parser.parse_args(argv)
    options = Options(repo=args.repo, table=args.table, doc=args.doc, registry=args.registry, vocabulary=args.vocabulary,
                      clones={"minirust": args.minirust, "rust-reference": args.reference})
    try:
        result = collect(options)
    except (C.MissingClone, C.PinsError) as error:
        print(f"ub_coverage_matrix: {error}", file=sys.stderr)
        return 2
    if args.write_blocks and result.blocks:
        doc = args.doc or args.repo / DOC_REL
        text = doc.read_text(encoding="utf-8")
        for name, body in result.blocks.items():
            text = C.replace_block(text, name, body)
        doc.write_text(text, encoding="utf-8")
    print(result.blocks.get(COUNTS, ""))
    if result.violations:
        print(f"\nub_coverage_matrix: {len(result.violations)} violation(s)", file=sys.stderr)
        for violation in result.violations:
            print(f"  {violation}", file=sys.stderr)
        return 1
    print(f"\nub_coverage_matrix: OK ({result.counts['citations']} row citations, {result.counts.get('doc_citations', 0)} document citations, "
          f"{result.counts['reviews']['judgments']} reviewed judgments)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
