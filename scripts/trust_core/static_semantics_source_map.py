#!/usr/bin/env python3
"""D0.7 static-semantics source map checker (design exit E0.8b).

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.2 Stage 0.2 (D0.7:
"the FLS chapter, the Reference section, the a-mir-formality judgment, or the `de-facto`
label"; E0.8b: "D0.6 and D0.7 have 0 unmapped rows") and §3.1 (St). Ledger:
docs/trust-core/static-semantics-source-map.toml. Document:
docs/trust-core/STATIC_SEMANTICS_SOURCE_MAP.md. Review registry:
docs/trust-core/reviews/static_semantics_source_map.toml.

The shared layers (pins, git trees, citations, uniqueness, generated blocks, reviewed
judgments, immutable snapshots) are scripts/trust_core/common.py's. This file holds the
source map's own rules; each EXITS NON-ZERO when it fails. The document's Predicates
section states them:

  PIN        common: the FLS, Reference and a-mir-formality clones at their EXTERNAL_PINS
             pins; rust-lang/rfcs and rust-lang/rust (the standard library, at the
             alignment commit) read from git objects without lazy fetching; the rfcs pin
             is master's first-parent commit at the alignment timestamp; this
             repository's alignment.
  UNIVERSE   (a) FLS paragraphs and sections, (b) Reference rules, (c) design-named
             (St) parts, (d) a-mir-formality judgments, (e) standard-library members,
             (f) standard-library documentation sections, each enumerated from the pinned
             source by the rule its [selection.*] judgment declares; every member is
             owned by exactly one row. The std corpus is a common.RootedTree at the
             declared crates' src/ roots. A declared value that selects nothing (a
             crate, a rubric, an excluded file or include) is stale.
  TABLE      keys and types of every row; no duplicate row, title, conflict or cross-row
             citation; no repeated list element; no line citation in free text; no
             registered RFC whose status no citation reads.
  CITE       every citation resolves at its pin (common.Resolver, plus member quotes,
             a-mir-formality judgment names, decision snapshots); every citation of a
             rustc test (.rs under tests/) declares an expect that compiletest's
             annotations agree with, and no other citation carries one; a trust-test
             citation names a UI test bound to a row.
  LABEL      documented, compat-candidate and de-facto rows carry what their label needs;
             conflicts carry their required sides and outcomes; design parts are graded.
  SEARCH     a recorded search's declared scope and terms are re-run: every scope member
             is silent or addressed, every file holding a term is a mention, none stale.
  DISPOSE    grammar side-condition candidates (declared predicates), members mapped
             outside (St), twins, and a-mir-formality notes (declared predicate) are each
             dispositioned exactly once, and no disposition group is empty; a rule a
             rejecting rustc test cites is not dispositioned descriptive.
  PIN-DELTA  each pin exception equals its committed snapshot; the FLS paragraphs the
             later commits add, remove or change are enumerated by reverse-applying the
             snapshot's patches to the pinned files.
  SNAPSHOT   common.check_immutable on the bytes the checker parses (HEAD equals the
             working tree); kind, retrieval date and URL are the snapshot's own; every
             registered snapshot is used, every file registered; decision snapshots are
             decisions in effect at the alignment.
  DOC        every generated block regenerates; every line is in a `prose:` section, a
             generated block or the outline; every «quoted» citation resolves.
  REVIEW     common.check_reviews over every ledger table, the ledger's comments, the
             rfcs entry of EXTERNAL_PINS.toml, every prose section and the outline.

Usage:
    scripts/trust_core/static_semantics_source_map.py [--repo DIR] [--ledger FILE] [--doc FILE]
        [--registry FILE] [--fls DIR] [--reference DIR] [--formality DIR] [--rfcs DIR] [--rust DIR]
        [--write-blocks]

Exit codes: 0 every predicate holds; 1 a violation; 2 a clone is missing or the pins are unreadable.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import argparse
import collections
import json
import posixpath
import re
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

tomllib = C.tomllib
REPO_ROOT = C.REPO_ROOT
LEDGER_REL = "docs/trust-core/static-semantics-source-map.toml"
DOC_REL = "docs/trust-core/STATIC_SEMANTICS_SOURCE_MAP.md"
DELIVERABLE = "static_semantics_source_map"
REGISTRY_REL = f"{C.REVIEWS_DIR}/{DELIVERABLE}.toml"
SCHEMA = "trust.core.static-semantics-source-map.v4"
SNAPSHOT_DIR = "docs/trust-core/snapshots/static-semantics"
READS = {"fls": "fls", "rust-reference": "reference", "a-mir-formality": "a-mir-formality", "rfcs": "rfcs"}
RUST_URL = "https://github.com/rust-lang/rust"
KINDS = ("rfcs", "std", "trust-test")  # citation kinds beyond common's: two clones and Trust's own UI tests
BLOCKS = ("pins", "universe", "rows", "dispositions", "by-component", "by-area", "design-parts", "labels",
          "side-conditions", "rfcs", "decisions", "searches", "conflicts", "pin-delta")

AREAS = set("""grammar macro-expansion name-resolution visibility typing type-inference coercions subtyping-variance
lifetimes traits coherence impl-selection well-formedness method-probing fallback closure-kind captures patterns
binding-modes borrowing two-phase-borrows drop-check temporaries const-context unsafety-checking attributes items
entry-point elaboration promotion drop-order layout dynamic abi-ffi inline-assembly library lints-diagnostics limits
codegen linkage documentation""".split())
COMPONENTS = ("St.grammar", "St.macro-by-example", "St.expansion-inputs", "St.name-resolution", "St.typing", "St.traits",
              "St.algorithmic", "St.borrowing", "St.acceptance-unassigned", "St.builtin-expansion-unassigned", "T.rust-t",
              "T.elab", "T.promote", "L.layout", "C.core", "C.const-eval", "outside.library", "outside.codegen",
              "outside.linkage", "outside.tooling")
GRAMMAR_COMPONENTS = {"St.grammar", "St.macro-by-example"}
LABELS = ("documented", "compat-candidate", "de-facto")
# kind -> (admitted sides, required sides); side -> admitted citation kinds.
CONFLICT_SIDES = {
    "fls-reference": ({"fls", "reference", "rustc"}, {"fls", "reference"}),
    "fls-std": ({"fls", "std", "rustc"}, {"fls", "std"}),
    "document-rustc": ({"document", "rustc", "decision"}, {"document", "rustc"}),
    "formality-rustc": ({"formality", "rustc", "document", "decision"}, {"formality", "rustc"}),
    "document-gap": ({"document"}, {"document"}),
}
SIDE_KINDS = {"fls": {"fls"}, "reference": {"reference"}, "std": {"std"}, "document": {"fls", "reference", "rfcs", "std"},
              "rustc": {"worktree", "trust-test"}, "formality": {"a-mir-formality"}, "decision": {"decision"}}
OUTCOME_KEYS = {"document-rustc": "document_outcome", "formality-rustc": "formality_outcome"}
OPPOSITE = {"accept": {"error"}, "reject": {"pass", "no-error"}}
EXPECTS = ("pass", "error", "no-error")
RFC_STATUSES = ("stabilized", "partially-stabilized", "not-stabilized")
RANK1_RFC = ("stabilized", "partially-stabilized")
DISMISSAL_KINDS = ("post-parse-restriction", "semantic", "not-a-restriction")
DESCRIPTIVE = ("definition", "dynamic-behavior", "elaboration", "layout", "codegen-effect", "library-api")
ACKNOWLEDGING = ("run-time-requirement", "const-evaluation", "lint-level", "link-time", "external-tool", "no-rejection", "consequence")
DISPOSITION_KINDS = DESCRIPTIVE + ACKNOWLEDGING + ("restated",)
NOTE_KINDS = ("divergence", "model-incomplete", "model-formulation", "not-static-semantics", "test-infrastructure", "unverified")
RANK1_CORPORA = ("fls", "reference", "rfcs", "std")
SEARCH_CORPORA = ("fls", "reference", "rfcs", "std", "a-mir-formality", "decisions")
VERDICTS = ("documents", "contrary", "open", "silent", "unrelated")
DECISION_SNAPSHOT, DECISION_INDEX, PIN_DERIVATION = ("trust.core.static-semantics.decision-snapshot.v1",
                                                     "trust.core.static-semantics.decision-index.v1",
                                                     "trust.core.static-semantics.pin-derivation.v1")
UI_TEST_ROW_MARKER = "D0.7 static-semantics source map, row "
FREE_TEXT = ("title", "note", "reason", "summary", "finding", "behavior", "decision", "status_note", "rule", "label",
             "covers", "excludes")
MIN_QUOTE = 15

# kind -> (key of a row, the keys a row may carry); every row of every table is a reviewed judgment.
TABLES = {kind: (keys.split()[0], set(keys.split())) for kind, keys in {
    "row": "id title area component label note design_parts fls_sections fls reference std std_text formality rfcs decisions "
           "documents rustc_behavior refines conflicts search",
    "rfc": "number file status status_note status_evidence",
    "grammar_side_condition": "id name fls reference",
    "grammar_side_condition_dismissal": "id kind reason reference",
    "outside_st_static_candidate": "id kind reason fls reference std restates",
    "twin": "id note fls reference std",
    "formality_test_note": "ref quote kind reason",
    "pin_exception": "source default_branch default_branch_state state_committer_date successor successor_committer_date "
                     "merged_into_default_branch_by merged_at commits_after_state snapshot decision historical_at",
    "snapshot": "file kind url retrieved sha256",
    "count": "key block label",
}.items()}
SELECTIONS = {name: set(keys.split()) for name, keys in {
    "fls": "rule toctree excluded_rubrics runtime_rubrics evidence",
    "reference": "rule summary rule_regex excluded_files non_summary_files evidence",
    "std": "rule crates evidence",
    "std_docs": "rule covers excludes declared excluded_includes",
    "predicates": "rule side_condition_text side_condition_id side_condition_grammar_marker formality_note",
    "design": "rule",
    "formality": "rule judgment_root",
    "decisions": "rule team_labels disposition_labels rfcbot_logins",
}.items()}
JUDGMENT_KINDS = set(TABLES) | {"selection", "comments", "pins", "prose", "outline"}


@dataclass
class Result:
    violations: list = field(default_factory=list)
    counts: dict = field(default_factory=dict)
    blocks: dict = field(default_factory=dict)


@dataclass
class Options:
    repo: Path = REPO_ROOT
    ledger: Path | None = None
    doc: Path | None = None
    registry: Path | None = None
    pins: Path | None = None
    clones: dict = field(default_factory=dict)  # EXTERNAL_PINS source (or "rust") -> clone directory
    trees: dict = field(default_factory=dict)   # citation kind -> tree; mutation tests only
    check_pin_state: bool = True
    check_history: bool = True


def span(ref: str) -> tuple | None:
    parts = C.parse_ref(ref, C.SOURCE_KINDS + KINDS)
    return None if parts is None or parts["start"] is None else (parts["source"], parts["path"], parts["start"], parts["end"])


# --------------------------------------------------------------------------
# universes
# --------------------------------------------------------------------------

FLS_LABEL = re.compile(r"^\.\. _(fls_[A-Za-z0-9]+):\s*$")
FLS_RUBRIC = re.compile(r"^\.\. rubric:: (.+?)\s*$")
UNDERLINE = re.compile(r"^([=\-~^\"'`#*+<>])\1{2,}\s*$")


@dataclass
class Section:
    sid: str
    chapter: str
    title: str
    line: int
    informational: bool = False
    syntax: bool = False
    paragraphs: list = field(default_factory=list)  # (pid, rubric, line)


def fls_paragraphs(files: dict) -> dict:
    """pid -> text of every :dp: paragraph of `files` (path under src/ -> text), segmented as
    common.Resolver segments the FLS paragraph a citation names."""
    with tempfile.TemporaryDirectory() as empty:
        spans = C.Resolver(REPO_ROOT, {"fls": C.DirTree(empty, files)}).spans("fls")
    return {pid: found[-1][2] for pid, found in spans.items()}


def enumerate_fls(tree, selection: dict, errors: list) -> dict:
    text = tree.text(selection.get("toctree", "")) or ""
    toc = re.search(r"^\.\. toctree::\n((?:[ \t]+.*\n|\s*\n)*)", text, re.M)
    chapters = [e.strip() for e in (toc.group(1).splitlines() if toc else []) if e.strip() and not e.strip().startswith(":")]
    if not chapters:
        errors.append(f"UNIVERSE: {selection.get('toctree')} has no toctree at the FLS pin")
    tree.prefetch([f"src/{c}.rst" for c in chapters])
    u = {"chapters": [], "pages": [], "sections": {}, "paragraphs": {}, "members": {}, "member_sections": {},
         "excluded": collections.Counter(), "excluded_sections": collections.Counter(), "rubrics": collections.Counter()}
    for chapter in chapters:
        lines = tree.lines(f"src/{chapter}.rst")
        if lines is None:
            errors.append(f"UNIVERSE: src/{chapter}.rst, named by the toctree, does not exist at the FLS pin")
            continue
        page = any(line.strip() == ".. informational-page::" for line in lines)
        (u["pages"] if page else u["chapters"]).append(chapter)
        current, rubric = None, None
        for i, line in enumerate(lines):
            label = FLS_LABEL.match(line)
            if label:
                j = i + 1
                while j < len(lines) and not lines[j].strip():
                    j += 1
                if j + 1 < len(lines) and UNDERLINE.match(lines[j + 1]):
                    current, rubric = Section(label.group(1), chapter, lines[j].strip(), j + 1), None
                    if current.sid in u["sections"]:
                        errors.append(f"UNIVERSE: FLS section id {current.sid} is defined twice")
                    u["sections"][current.sid] = current
                continue
            stripped = line.strip()
            if current is not None and stripped == ".. informational-section::":
                current.informational = True
            if current is not None and stripped.startswith(".. syntax::"):
                current.syntax = True
            if FLS_RUBRIC.match(line):
                rubric = FLS_RUBRIC.match(line).group(1)
            for dp in C.FLS_PARAGRAPH.finditer(line):
                if current is None:
                    errors.append(f"UNIVERSE: FLS {chapter}.rst paragraph {dp.group(1)} precedes any section label")
                else:
                    current.paragraphs.append((dp.group(1), rubric, i + 1))
        for section in [s for s in u["sections"].values() if s.chapter == chapter]:
            informational = section.informational or re.match(r"Examples?\b", section.title)
            has_member = False
            for pid, rub, line in section.paragraphs:
                if pid in u["paragraphs"]:
                    errors.append(f"UNIVERSE: FLS paragraph id {pid} is defined twice")
                u["paragraphs"][pid] = (section.sid, rub, line)
                reason = "informational-page" if page else "informational-section" if informational else \
                    f"rubric:{rub}" if rub in selection.get("excluded_rubrics", []) else None
                if reason:
                    u["excluded"][reason] += 1
                else:
                    u["members"][pid] = (section.sid, rub, line)
                    u["rubrics"][rub or "(none)"] += 1
                    has_member = True
            reason = "informational-page" if page else "informational-section" if informational else None
            if reason:
                u["excluded_sections"][reason] += 1
            elif has_member or section.syntax:
                u["member_sections"][section.sid] = section
            else:
                u["excluded_sections"]["only-excluded-rubrics" if section.paragraphs else "heading-only"] += 1
    u["texts"] = fls_paragraphs({f"src/{c}.rst": tree.text(f"src/{c}.rst") for c in u["chapters"]})
    for key, counter, prefix in (("excluded_rubrics", u["excluded"], "rubric:"), ("runtime_rubrics", u["rubrics"], "")):
        for rubric in selection.get(key, []):
            if not counter[prefix + str(rubric)]:
                errors.append(f"UNIVERSE: selection.fls {key} names {rubric!r}, a rubric no universe chapter paragraph is under (stale)")
    return u


FENCE = re.compile(r"^\s*>?\s*(```|~~~)(.*)$")


def enumerate_reference(tree, selection: dict, errors: list) -> dict:
    rule = re.compile(selection.get("rule_regex", "$^"))
    summary = tree.text(selection.get("summary", "")) or ""
    files = re.findall(r"\]\(([^)\s]+\.md)\)", summary)
    excluded = {e.get("file") for e in selection.get("excluded_files", [])}
    tree.prefetch(tree.files("src/", (".md",)))
    u = {"files": [f for f in files if f not in excluded], "excluded_files": [f for f in files if f in excluded],
         "rules": {}, "members": {}, "non_summary": {}}
    for rel in excluded - set(files):
        errors.append(f"UNIVERSE: excluded Reference file {rel} is not a SUMMARY.md chapter (stale)")
    for rel in files:
        lines = tree.lines(f"src/{rel}")
        if lines is None:
            errors.append(f"UNIVERSE: SUMMARY.md names {rel}, which does not exist at the Reference pin")
            continue
        found = [(m.group(1), i) for i, line in enumerate(lines) for m in [rule.match(line)] if m and m.end() == len(line)]
        for n, (rid, i) in enumerate(found):
            end = found[n + 1][1] if n + 1 < len(found) else len(lines)
            if rid in u["rules"]:
                errors.append(f"UNIVERSE: Reference rule {rid} is defined twice ({u['rules'][rid][0]}, {rel})")
            u["rules"][rid] = (rel, i + 1, lines[i + 1:end])
            if rel not in excluded:
                u["members"][rid] = u["rules"][rid]
    named = set(files) | {Path(selection.get("summary", "")).name}
    for path in tree.files("src/", (".md",)):
        ids = [m.group(1) for line in (tree.lines(path) or []) for m in [rule.match(line)] if m and m.end() == len(line)]
        if path[4:] not in named and ids:
            u["non_summary"][path[4:]] = ids
    return u


def rule_text(lines: list, grammar: bool = False) -> str:
    """A Reference rule's text without code blocks (with `grammar`, ```grammar bodies kept)."""
    out, fence, is_grammar = [], False, False
    for line in lines:
        m = FENCE.match(line)
        if m:
            if not fence:
                is_grammar = m.group(2).strip().startswith("grammar")
            fence = not fence
        elif line.strip() and (not fence or (grammar and is_grammar)):
            out.append(line.strip())
    return " ".join(out)


def grammar_lines(lines: list) -> list:
    out, fence, is_grammar = [], False, False
    for line in lines:
        m = FENCE.match(line)
        if m:
            if not fence:
                is_grammar = m.group(2).strip().startswith("grammar")
            fence = not fence
        elif fence and is_grammar:
            out.append(line)
    return out


JUDGMENT_OPEN = re.compile(r"^\s*judgment_fn!\s*\{")
FN_NAME = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?fn\s+([A-Za-z_]\w*)\s*\(")


def enumerate_formality(tree, root: str, note_predicate: str, errors: list) -> tuple[dict, dict]:
    """((file, line) -> judgment name for every judgment_fn! under `root`, (file, line) -> text of every note line)."""
    files = tree.files("", (".rs",))
    tree.prefetch(files)
    judgments, notes, note = {}, {}, re.compile(note_predicate)
    for rel in files:
        lines = tree.lines(rel) or []
        for i, line in enumerate(lines):
            if note.search(line):
                notes[(rel, i + 1)] = line.strip()
            if rel.startswith(root + "/") and JUDGMENT_OPEN.match(line):
                j = next((j for j in range(i + 1, len(lines)) if JUDGMENT_OPEN.match(lines[j]) or FN_NAME.match(lines[j])), None)
                if j is None or not FN_NAME.match(lines[j]):
                    errors.append(f"UNIVERSE: a-mir-formality {rel}: a judgment_fn! with no fn name")
                else:
                    judgments[(rel, j + 1)] = FN_NAME.match(lines[j]).group(1)
    return judgments, notes


STRING = re.compile(r'"(?:[^"\\]|\\.)*"')
ITEM_DOC = re.compile(r"^\s*//[/!]\s?")


def attribute_blocks(lines: list):
    """(item line index, [(line index, text)]) for every line after a run of outer attributes and comments."""
    block, i = [], 0
    while i < len(lines):
        stripped = lines[i].strip()
        if not stripped or stripped.startswith(("#!", "//!")):
            block, i = [], i + 1
        elif stripped.startswith("//"):
            block.append((i, stripped))
            i += 1
        elif stripped.startswith("#["):
            depth, j, text = 0, i, []
            while j < len(lines):
                text.append(lines[j].strip())
                unquoted = STRING.sub('""', lines[j])
                depth += unquoted.count("[") - unquoted.count("]")
                if depth <= 0:
                    break
                j += 1
            block.append((i, " ".join(text)))
            i = j + 1
        else:
            if block:
                yield i, block
            block, i = [], i + 1


INCLUDE = re.compile(r'^#(!?)\[doc\s*=\s*include_str!\("([^"]+)"\)\]$')


def included(rel: str, path: str) -> str:
    return posixpath.normpath(posixpath.join(posixpath.dirname(rel), path))


def include_lines(tree, rel: str, path: str, errors: list) -> list:
    """(negative line, text) of the documentation file `rel` includes; a file outside the corpus is refused."""
    text = tree.text(included(rel, path))
    if text is None:
        errors.append(f"UNIVERSE: std {rel} includes {included(rel, path)} as documentation, which is not a file of the corpus at the alignment commit")
    return [(-(k + 1), line) for k, line in enumerate((text or "").split("\n"))]


def doc_lines(block: list, rel: str, tree, errors: list) -> list:
    """(line, text) of an item's outer docs: its `///` lines, then any `#[doc = include_str!("..")]` file."""
    out = [(i + 1, ITEM_DOC.sub("", text)) for i, text in block if text.startswith("///")]
    for _, text in block:
        m = INCLUDE.match(text)
        if m and not m.group(1):
            out += include_lines(tree, rel, m.group(2), errors)
    return out


def enumerate_std(tree, errors: list) -> dict:
    """member id -> (locations, doc lines) for rule (e), over the std tree (rooted at the declared crates)."""
    files = tree.files("library/", (".rs",))
    tree.prefetch(files)
    members = {}
    for rel in files:
        lines = tree.lines(rel)
        if lines is None:
            errors.append(f"UNIVERSE: std {rel} is not readable at the alignment commit (the rust clone is partial)")
            continue
        crate = rel.split("/")[1]
        for item, block in attribute_blocks(lines):
            attrs = [text for _, text in block if text.startswith("#[")]
            stable, found = any(a.startswith("#[stable(") for a in attrs), []
            if any(re.match(r"#\[rustc_builtin_macro\b", a) for a in attrs):
                name = re.match(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:macro_rules!\s*|macro\s+)([A-Za-z_]\w*)", lines[item])
                if name is None:
                    errors.append(f"UNIVERSE: std {rel}: #[rustc_builtin_macro] on an item whose name does not parse")
                elif stable:
                    found.append(f"macro:{crate}::{name.group(1)}")
            else:
                langs = [m.group(1) for a in attrs if a.startswith(("#[lang", "#[cfg_attr(")) for m in [re.search(r'\blang\s*=\s*"([^"]+)"', a)] if m]
                auto = re.match(r"^\s*(?:pub\s+)?(?:unsafe\s+)?auto\s+trait\s+([A-Za-z_]\w*)", lines[item])
                if langs and stable:
                    found.append(f"lang:{langs[0]}")
                elif auto and stable:
                    found.append(f"auto-trait:{crate}::{auto.group(1)}")
            for a in attrs:
                for kind, pattern in (("primitive", r'#\[rustc_doc_primitive\s*=\s*"([^"]+)"\]'), ("keyword", r'#\[doc\(keyword\s*=\s*"([^"]+)"\)\]'),
                                      ("attribute", r'#\[doc\(attribute\s*=\s*"([^"]+)"\)\]')):
                    m = re.match(pattern, a)
                    if m:
                        found.append(f"{kind}:{m.group(1)}")
            for mid in found:
                if mid in members:
                    members[mid][0].append((rel, item + 1))
                else:
                    members[mid] = ([(rel, item + 1)], doc_lines(block, rel, tree, errors))
    return members


DOC_HEADING = re.compile(r"^(#{1,6})\s+(\S.*?)\s*$")


def doc_sections(base: str, lines: list) -> dict:
    """id -> (first line, text) for the sections of one documentation text, split at its markdown headings
    outside code blocks: `base` for the text before the first heading, `base#Heading` for each heading
    (a repeated heading takes ` (2)`, ` (3)`)."""
    out, fence, title, first, body = {}, False, "", lines[0][0] if lines else 0, []
    seen = collections.Counter()

    def close():
        if title or any(t.strip() for t in body):
            seen[title] += 1
            key = base + (f"#{title}" if title else "") + (f" ({seen[title]})" if seen[title] > 1 else "")
            out[key] = (first, C.collapse(" ".join(body)))
    for number, text in lines:
        if text.lstrip().startswith(("```", "~~~")):
            fence = not fence
        heading = None if fence else DOC_HEADING.match(text)
        if heading:
            close()
            title, first, body = heading.group(2), number, []
        else:
            body.append(text)
    close()
    return out


def enumerate_std_docs(tree, std: dict, selection: dict, errors: list) -> dict:
    """member id -> (file, first line, text) for rule (f): the module documentation of every file that
    defines a rule-(e) member, and the declared module and item documentation."""
    module_files = {f for locations, _ in std.values() for f, _ in locations}
    declared = selection.get("declared", [])
    excluded = {(e.get("file"), e.get("include")): e for e in selection.get("excluded_includes", []) if isinstance(e, dict)}
    seen, members = set(), {}

    def module_doc(rel: str, lines: list) -> list:
        """A file's module documentation: its `//!` lines, then each file a `#![doc = include_str!(..)]` includes,
        except an include selection.std_docs excludes."""
        out = [(i + 1, ITEM_DOC.sub("", line)) for i, line in enumerate(lines) if line.lstrip().startswith("//!")]
        for line in lines:
            m = INCLUDE.match(line.strip())
            if m and m.group(1):
                seen.add((rel, included(rel, m.group(2))))
                if (rel, included(rel, m.group(2))) not in excluded:
                    out += include_lines(tree, rel, m.group(2), errors)
        return out
    for rel in sorted(module_files):
        for key, (line, text) in doc_sections(f"doc:{rel}", module_doc(rel, tree.lines(rel) or [])).items():
            members[key] = (rel, line, text)
    for entry in declared:
        rel, item = entry.get("file"), entry.get("item")
        lines = tree.lines(rel) if isinstance(rel, str) else None
        if lines is None:
            errors.append(f"UNIVERSE: selection.std_docs declares {rel!r}, which is not a file at the alignment commit")
            continue
        if item is None:
            if rel in module_files:
                errors.append(f"UNIVERSE: selection.std_docs declares the module docs of {rel}, which rule (f) already enumerates (stale)")
            doc, base = module_doc(rel, lines), f"doc:{rel}"
        else:
            declaration = re.compile(r"^\s*pub(?:\([^)]*\))?\s+(?:const\s+)?(?:unsafe\s+)?(?:auto\s+)?" + re.escape(str(entry.get("kind")))
                                     + r"\s+" + re.escape(str(item)) + r"\b")
            blocks = [doc_lines(block, rel, tree, errors) for i, block in attribute_blocks(lines) if declaration.match(lines[i])]
            if len(blocks) != 1 or entry.get("kind") not in ("trait", "struct", "enum", "union", "fn", "macro", "type"):
                errors.append(f"UNIVERSE: selection.std_docs declares the {entry.get('kind')} {rel}::{item}, which is declared {len(blocks)} times there")
                continue
            doc, base = blocks[0], f"doc:{rel}::{item}"
        if not doc:
            errors.append(f"UNIVERSE: selection.std_docs declares {base[4:]}, which has no documentation")
        for key, (line, text) in doc_sections(base, doc).items():
            members[key] = (rel, line, text)
    for rel, include in sorted(set(excluded) - seen, key=str):
        errors.append(f"UNIVERSE: selection.std_docs excludes the include {include!r} of {rel!r}, which no enumerated module documentation includes (stale)")
    return members


def enumerate_design_parts(text: str, errors: list) -> list:
    """(kind, phrase) of every part the §3.1 (St) bullets name."""
    lines = text.split("\n")
    start = next((i for i, line in enumerate(lines) if line.startswith("**(St) Static: Rust's static semantics.**")), None)
    end = next((i for i, line in enumerate(lines) if line.startswith("**(T) Rust-T and its formal elaboration.**")), None)
    if start is None or end is None or end <= start:
        errors.append("UNIVERSE: the design's §3.1 (St) block is not found")
        return []

    def bullet(prefix):
        for i in range(start, end):
            if lines[i].startswith(prefix):
                j = i + 1
                while j < end and lines[j].startswith("  "):
                    j += 1
                return " ".join(s.strip() for s in lines[i:j])
        return ""

    parts = []
    for kind, prefix, pattern in (("algorithmic", "* **The algorithmic parts that decide meaning.**", r"decide meaning\.\*\* (.+?) decide which code runs"),
                                  ("borrowing", "* **Borrowing.**", r"over Promoted-phase Core, including (.+?)\."),
                                  ("traits", "* **Types and traits.**", r"plus (.+?) as relations")):
        m = re.search(pattern, bullet(prefix))
        if not m:
            errors.append(f"UNIVERSE: the design's (St) {kind} sentence no longer parses")
            continue
        items = [s.strip() for s in m.group(1).split(", ")]
        last = items.pop()
        items += [s.strip() for s in last.split(" and ", 1)] if " and " in last else [last]
        parts += [(kind, p) for p in items if p]
    return parts


ANNOTATION = re.compile(r"//(?:\[([A-Za-z0-9_,\- ]+)\])?~(\^+|v+|\||\?)?\s*(ERROR|WARN|WARNING|NOTE|HELP|SUGGESTION)?")
PASS_HEADER = re.compile(r"^\s*//@\s*(?:\[([A-Za-z0-9_,\- ]+)\])?\s*(run|check|build)-pass\b")


def annotations(lines: list) -> list:
    """(target line, kind, revisions or None) for every compiletest `//~` annotation."""
    out, previous = [], None
    for number, line in enumerate(lines, 1):
        for m in ANNOTATION.finditer(line):
            mark = m.group(2) or ""
            target = number - len(mark) if mark.startswith("^") else number + len(mark) if mark.startswith("v") else \
                previous if mark == "|" else None if mark == "?" else number
            previous = target
            out.append((target, (m.group(3) or "").upper(), {r.strip() for r in m.group(1).split(",")} if m.group(1) else None))
    return out


def expectation_problem(lines: list, expect: str, first: int, last: int, revision: str | None) -> str | None:
    """Why the test's compiletest annotations do not declare `expect` for the quoted lines."""
    def applies(revs):
        return revs is None or revision is None or revision in revs
    errors = [t for t, kind, revs in annotations(lines) if kind == "ERROR" and applies(revs)]
    in_window = [t for t in errors if t is not None and first <= t <= last]
    if expect == "error":
        return None if in_window else "no ERROR annotation targets the quoted lines"
    if expect == "no-error":
        return "an ERROR annotation targets the quoted lines" if in_window else None
    if expect is None:
        return f"a rustc test citation declares expect ({', '.join(EXPECTS)})"
    if expect == "pass":
        passing = [m for m in map(PASS_HEADER.match, lines) if m and (m.group(1) is None or revision is None or revision in m.group(1).split(","))]
        return "the test has no run-, check- or build-pass header" if not passing else \
            "the test declares pass but carries ERROR annotations" if errors else None
    return f"expect {expect!r} is not one of {EXPECTS}"


# --------------------------------------------------------------------------
# snapshots
# --------------------------------------------------------------------------

def reverse_patch(new_text: str, patch: str) -> str | None:
    """The file before a unified-diff patch, from the file after it; None when a hunk does not apply."""
    lines, out, pos = new_text.split("\n"), [], 0
    hunks = list(re.finditer(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*$", patch, re.M))
    for n, hunk in enumerate(hunks):
        start = int(hunk.group(3)) - (1 if int(hunk.group(4) or 1) else 0)
        body = patch[hunk.end() + 1: hunks[n + 1].start() if n + 1 < len(hunks) else len(patch)].split("\n")
        if body and body[-1] == "":
            body.pop()
        if start < pos or sum(1 for line in body if line[:1] in (" ", "-")) != int(hunk.group(2) or 1):
            return None
        out += lines[pos:start]
        pos = start
        for line in body:
            tag, text = line[:1], line[1:]
            if tag in (" ", "+"):
                if pos >= len(lines) or lines[pos] != text:
                    return None
                pos += 1
            if tag in (" ", "-"):
                out.append(text)
            elif tag not in ("+", "\\"):
                return None
    return "\n".join(out + lines[pos:])


SNAPSHOT_KINDS = {DECISION_SNAPSHOT: "decision", DECISION_INDEX: "decision-index", PIN_DERIVATION: "pin-derivation"}


def snapshot_url(snapshot: dict) -> str:
    """The URL a snapshot was retrieved from: a decision's own url, the search API an index's queries ran on,
    or the compare of a pin derivation's base and head."""
    compare = snapshot.get("compare") if isinstance(snapshot.get("compare"), dict) else {}
    return snapshot.get("url") if snapshot.get("schema") == DECISION_SNAPSHOT else "https://api.github.com/search/issues" \
        if snapshot.get("schema") == DECISION_INDEX else \
        f"https://api.github.com/repos/{snapshot.get('repo')}/compare/{compare.get('base')}...{compare.get('head')}"


def historical_exception_pins(repo: Path, exception: dict, descriptor: dict, current: C.Pins) -> C.Pins:
    """Bind archival evidence to its exact former inputs, without granting current authority.

    An ancestor with different pins is insufficient: that commit must already hold this exact
    exception, snapshot descriptor and payload. The snapshot still goes through the normal
    immutable-history and pin-exception checks. Only its contribution to today's delta is omitted.
    """
    revision = exception.get("historical_at")
    if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None or \
            C.git(repo, "merge-base", "--is-ancestor", revision, "HEAD") is None:
        raise ValueError("historical_at must name a full ancestor commit")
    tree = C.GitTree(repo, revision)
    try:
        ledger = tomllib.loads(tree.text(LEDGER_REL) or "")
        exceptions = ledger.get("pin_exception", [])
        registered = ledger.get("snapshot", [])
        if not isinstance(exceptions, list) or not all(isinstance(row, dict) for row in exceptions) or \
                not isinstance(registered, list) or not all(isinstance(row, dict) for row in registered):
            raise ValueError("historical ledger rows are malformed")
        original = [row for row in exceptions if row.get("source") == exception.get("source")]
        archived = {key: value for key, value in exception.items() if key != "historical_at"}
        if ledger.get("schema") != SCHEMA or original != [archived]:
            raise ValueError("historical exception differs from its committed original")
        snapshots = [row for row in registered if row.get("file") == exception.get("snapshot")]
        if snapshots != [descriptor]:
            raise ValueError("historical snapshot descriptor differs from its committed original")
        path = exception["snapshot"]
        payload = tree.text(path)
        if payload is None or payload.encode("utf-8") != (Path(repo) / path).read_bytes():
            raise ValueError("historical snapshot payload differs from its committed original")
        pins_text = tree.text(C.PINS_REL)
        if pins_text is None:
            raise ValueError("historical external pins are unavailable")
        with tempfile.TemporaryDirectory() as directory:
            pin_path = Path(directory) / "pins.toml"
            pin_path.write_text(pins_text, encoding="utf-8")
            pins = C.load_pins(pin_path)
        source, now = pins.sources.get(exception.get("source")), current.sources.get(exception.get("source"))
        if source is None or now is None or source.url != now.url or source.revision == now.revision or \
                C.parse_date(pins.alignment_date) >= C.parse_date(current.alignment_date):
            raise ValueError("historical exception must bind an older alignment and a different pin of the same source")
        return pins
    except (OSError, KeyError, TypeError, tomllib.TOMLDecodeError, C.PinsError) as error:
        raise ValueError(f"historical exception inputs are invalid: {error}") from error


def decision_problems(snapshot: dict, selection: dict, alignment: str) -> list:
    labels = set(snapshot.get("labels", []))
    complete = [c for c in snapshot.get("comments", []) if c.get("author") in selection.get("rfcbot_logins", [])
                and "is now **complete**" in str(c.get("body", ""))]
    landed = snapshot.get("merged_at") or snapshot.get("closed_at")
    return [problem for problem, fails in (
        (f"carries none of the team labels {selection.get('team_labels')}", not labels & set(selection.get("team_labels", []))),
        (f"carries none of {selection.get('disposition_labels')}", not labels & set(selection.get("disposition_labels", []))),
        ("is not labelled finished-final-comment-period", "finished-final-comment-period" not in labels),
        ("has no rfcbot comment completing its final comment period at or before the alignment",
         not any(str(c.get("created_at")) <= alignment for c in complete)),
        (f"was merged or closed at {landed!r}, not at or before the alignment", not (isinstance(landed, str) and landed <= alignment)),
    ) if fails]


# --------------------------------------------------------------------------
# the checker
# --------------------------------------------------------------------------


class Checker:
    def __init__(self, options: Options) -> None:
        self.o, self.f = options, C.Findings()
        self.counts: dict = {}
        self.rfc_uses: set = set()  # RFC files cited where their registered status decides a check

    def add(self, kind: str, message: str) -> None:
        self.f.add(kind, message)

    # ---- inputs
    def load(self) -> bool:
        o = self.o
        self.pins = C.load_pins(o.pins or o.repo / C.PINS_REL)
        try:
            self.ledger_text = (o.ledger or o.repo / LEDGER_REL).read_text(encoding="utf-8")
            self.data = tomllib.loads(self.ledger_text)
        except (OSError, tomllib.TOMLDecodeError) as error:
            self.add("TABLE", f"{o.ledger or LEDGER_REL}: {error}")
            self.data = None
        crates = (self.data or {}).get("selection")
        for key in ("std", "crates"):
            crates = crates.get(key) if isinstance(crates, dict) else None
        rust = C.Source("rust", RUST_URL, self.pins.alignment, self.pins.alignment_date, "objects")
        wanted = [name for name, kind in READS.items() if kind not in o.trees]
        clones = C.locate_clones(self.pins, wanted, o.clones) if wanted else {}
        trees = {"worktree": C.GitTree(o.repo, "HEAD"), "trust-test": C.GitTree(o.repo, "HEAD")}
        for name, path in clones.items():
            source = self.pins.sources[name]
            trees[READS[name]] = C.GitTree(path, source.revision)
        if "std" not in o.trees:
            path = Path(o.clones.get("rust") or C.sources_root() / "rust")
            if not (path / ".git").exists():
                raise C.MissingClone(
                    f"the rust clone is missing at {path}; create it (the standard library at the alignment commit):\n"
                    f"  git init {path} && git -C {path} remote add origin {RUST_URL} && git -C {path} fetch --depth 1 "
                    f"--filter=blob:none origin {rust.revision} && git -C {path} sparse-checkout set --no-cone "
                    f"'/library/core/src' '/library/alloc/src' '/library/std/src' '/library/proc_macro/src' && "
                    f"git -C {path} checkout FETCH_HEAD")
            clones["rust"] = path
            trees["std"] = C.GitTree(path, rust.revision)
        trees.update(o.trees)
        # The standard-library corpus is exactly the declared crates' src/ roots: no citation, search or
        # enumeration reads past them, whichever objects the partial clone holds.
        trees["std"] = C.RootedTree(trees["std"], [f"library/{c}/src/" for c in crates if isinstance(c, str)] if isinstance(crates, list) else [])
        self.trees = trees
        self.resolver = C.Resolver(o.repo, trees, kinds=KINDS, comment_kinds=("std",))
        if o.check_pin_state:
            for name, path in clones.items():
                C.verify_clone(self.f, path, rust if name == "rust" else self.pins.sources[name], self.pins)
            C.verify_objects(self.f, f"repository {o.repo}", o.repo)
            C.verify_alignment(self.f, trees["worktree"], self.pins)
        return self.data is not None

    def repository_file(self, tree: object) -> bool:
        """Whether a citation's resolved tree is this repository at HEAD (the `worktree` and `trust-test` trees)."""
        return tree is not None and any(tree is self.resolver.trees.get(k) for k in ("worktree", "trust-test"))

    def cite(self, kind: str, where: str, item: object, word_key: str | None = None, kinds: set | None = None) -> tuple | None:
        """Resolve a {ref, quote} citation; returns its span (source, path, first, last)."""
        if not isinstance(item, dict) or not isinstance(item.get("ref"), str):
            self.add(kind, f"{where}: a citation is {{ref, quote}}, not {item!r}")
            return None
        ref, quote = item["ref"], item.get(word_key or "quote")
        at = span(ref)
        if at is None or (kinds is not None and at[0] not in kinds):
            self.add(kind, f"{where}: {ref!r} is not a line citation of {sorted(kinds or ['a source'])}")
            return None
        if at[0] == "trust-test" and at[1] not in self.bound_tests:
            self.add(kind, f"{where}: {ref} is not a UI test whose header binds it to a row ({UI_TEST_ROW_MARKER}ID)")
        if word_key is None and isinstance(quote, str) and len(C.collapse(quote)) < MIN_QUOTE:
            self.add(kind, f"{where}: the quote {quote!r} is shorter than {MIN_QUOTE} characters, too weak to pin a line")
        if not self.resolver.resolve(self.f, kind, where, ref, quote, word=word_key is not None):
            return None
        # A citation is of a rustc test by the file it resolves to, whatever its prefix: a .rs file under tests/ of
        # this repository at HEAD (`worktree:`, `rustc:` and `trust-test:` all read it).
        tree, rel = self.resolver.tree_of(at[0], at[1])
        if self.repository_file(tree) and rel.startswith("tests/") and rel.endswith(".rs"):
            problem = expectation_problem(tree.lines(rel) or [], item.get("expect"), at[2], at[3], item.get("revision"))
            if problem:
                self.add("CITE", f"{where}: {ref} expect {item.get('expect')!r}: {problem}")
        elif "expect" in item or "revision" in item:
            self.add("CITE", f"{where}: {ref}: expect and revision belong to a citation of a rustc test (a .rs file under tests/)")
        return at

    # ---- universes
    def universes(self) -> None:
        d, errors = self.data, []
        sel = d.get("selection", {})
        self.sel = {k: sel.get(k) if isinstance(sel.get(k), dict) else {} for k in SELECTIONS}
        for key in sorted(set(sel) | set(SELECTIONS)):
            if not isinstance(sel.get(key), dict) or set(sel[key]) != SELECTIONS.get(key):
                self.add("TABLE", f"[selection.{key}] holds exactly the keys {sorted(SELECTIONS.get(key, []))}")
            else:
                C.repeated_elements(self.f, "TABLE", f"selection.{key}", sel[key])
        self.fls = enumerate_fls(self.trees["fls"], self.sel["fls"], errors)
        self.ref = enumerate_reference(self.trees["reference"], self.sel["reference"], errors)
        listed = {e.get("file"): e for e in self.sel["reference"].get("non_summary_files", [])}
        for key, keys in (("excluded_files", {"file", "reason"}), ("non_summary_files", {"file", "rules", "reason", "evidence"})):
            for e in self.sel["reference"].get(key, []):
                if not isinstance(e, dict) or set(e) != keys or not e.get("reason"):
                    self.add("TABLE", f"selection.reference {key}: an entry holds exactly {sorted(keys)}, with a reason: {e!r:.80}")
        for rel in sorted(set(listed) | set(self.ref["non_summary"])):
            if sorted(listed.get(rel, {}).get("rules", [])) != sorted(self.ref["non_summary"].get(rel, [])):
                errors.append(f"UNIVERSE: Reference file src/{rel} holds rule ids {self.ref['non_summary'].get(rel, [])}, "
                              f"non_summary_files lists {listed.get(rel, {}).get('rules')}")
        predicates = self.sel["predicates"]
        self.judgments, self.notes = enumerate_formality(self.trees["a-mir-formality"], self.sel["formality"].get("judgment_root", ""),
                                                         predicates.get("formality_note", "$^"), errors)
        if not self.judgments:
            errors.append(f"UNIVERSE: selection.formality judgment_root {self.sel['formality'].get('judgment_root')!r} holds no judgment_fn! (stale)")
        for crate in self.sel["std"].get("crates", []):
            if not self.trees["std"].files(f"library/{crate}/src/", (".rs",)):
                errors.append(f"UNIVERSE: selection.std crates names {crate!r}, which has no library/{crate}/src/ source at the alignment commit (stale)")
        self.std = enumerate_std(self.trees["std"], errors)
        self.std_docs = enumerate_std_docs(self.trees["std"], self.std, self.sel["std_docs"], errors)
        design = self.trees.get("design") or self.trees["worktree"]
        self.parts = enumerate_design_parts(design.text(C.DESIGN_REL) or "", errors)
        for problem in errors:
            kind, _, message = problem.partition(": ")
            self.add(kind, message)
        self.bound_tests = {}
        grep = C.git(self.o.repo, "grep", "-n", "-F", UI_TEST_ROW_MARKER, "HEAD", "--", "tests") or ""
        for line in grep.splitlines():
            m = re.match(r"^HEAD:([^:]+):\d+:.*" + re.escape(UI_TEST_ROW_MARKER) + r"([A-Z0-9-]+)", line)
            if m:
                self.bound_tests[m.group(1)] = m.group(2)

    def member_text(self, source: str, mid: object) -> str | None:
        if source == "fls":
            return self.fls["texts"].get(mid) if mid in self.fls["members"] else None
        if source == "reference":
            return C.collapse(" ".join(self.ref["members"][mid][2])) if mid in self.ref["members"] else None
        if source == "std":
            if mid in self.std:
                return C.collapse(" ".join(text for _, text in self.std[mid][1]))
            return self.std_docs[mid][2] if mid in self.std_docs else None
        return None

    # ---- TABLE
    def tables(self) -> None:
        d = self.data
        known = {"schema", "design", "selection"} | set(TABLES)
        for key in sorted(set(d) - known):
            self.add("TABLE", f"top-level key {key!r} is not part of the schema")
        if d.get("schema") != SCHEMA or d.get("design") != C.DESIGN_REL:
            self.add("TABLE", f"schema must be {SCHEMA} and design {C.DESIGN_REL}")
        self.t = {}
        for kind, (key, allowed) in TABLES.items():
            rows = [r for r in d.get(kind, []) if isinstance(r, dict)]
            if len(rows) != len(d.get(kind, [])):
                self.add("TABLE", f"[[{kind}]] holds a value that is not a table")
            for row in rows:
                C.repeated_elements(self.f, "TABLE", f"{kind} {row.get(key)}", row)
                if set(row) - allowed or not isinstance(row.get(key), str):
                    self.add("TABLE", f"{kind} {row.get(key)!r}: unknown keys {sorted(set(row) - allowed)}, or no {key}")
            self.t[kind] = C.unique_rows(self.f, "TABLE", kind, [r for r in rows if isinstance(r.get(key), str)], lambda r, k=key: r[k])
        for where, value in self.free_text(d):
            if not isinstance(value, str) or not value.strip():
                self.add("TABLE", f"{where}: must be non-empty text")
            elif C.FREE_TEXT_CITATION.search(value):
                self.add("TABLE", f"{where}: carries a line citation no predicate checks: {C.FREE_TEXT_CITATION.search(value).group(0)!r}")

    def free_text(self, value, where=""):
        if isinstance(value, dict):
            for k, v in value.items():
                if k in FREE_TEXT and not isinstance(v, (dict, list)):
                    yield f"{where}.{k}", v
                else:
                    yield from self.free_text(v, f"{where}.{k}")
        elif isinstance(value, list):
            for i, v in enumerate(value):
                yield from self.free_text(v, f"{where}[{i}]")

    def registered(self) -> None:
        """The [[rfc]] registry and the evidence of the [selection.*] judgments."""
        evidence = [(f"selection.{k}", e) for k in ("fls", "reference", "std") for e in self.sel[k].get("evidence", [])]
        evidence += [(f"selection.reference {e.get('file')}", x) for e in self.sel["reference"].get("non_summary_files", []) for x in e.get("evidence", [])]
        for e in self.sel["std_docs"].get("excluded_includes", []):
            if not isinstance(e, dict) or set(e) != {"file", "include", "reason", "evidence"} or not e.get("reason"):
                self.add("TABLE", f"selection.std_docs excluded_includes: an entry holds exactly file, include, reason and evidence, with a reason: {e!r:.80}")
                continue
            evidence += [(f"selection.std_docs {e.get('file')}", x) for x in e.get("evidence", [])]
        for number, entry in self.t["rfc"].items():
            where, rel = f"rfc {number}", entry.get("file")
            if not number.isdigit() or not re.fullmatch(rf"text/0*{int(number)}-[A-Za-z0-9_.-]+\.md", str(rel)):
                self.add("TABLE", f"{where}: file {rel!r} is not text/<number>-<name>.md")
            elif f"rust-lang/rfcs#{int(number)}]" not in "\n".join((self.trees["rfcs"].lines(rel) or [])[:12]):
                self.add("CITE", f"{where}: {rel} does not name rust-lang/rfcs#{int(number)} in its header at the pin")
            if entry.get("status") not in RFC_STATUSES or not entry.get("status_note") or not entry.get("status_evidence"):
                self.add("TABLE", f"{where}: a status of {RFC_STATUSES}, a status_note and status_evidence")
            evidence += [(where, e) for e in entry.get("status_evidence", [])]
        seen = {}
        for where, item in evidence:
            at = self.cite("CITE", where, item)
            if at and at in seen and seen[at] != where:
                self.add("TABLE", f"{where}: evidence {item['ref']} is also {seen[at]}'s")
            seen.setdefault(at, where)

    # ---- rows: ownership, citations, labels, conflicts, searches
    def rows(self) -> None:
        self.owner = {"fls": {}, "section": {}, "reference": {}, "std": {}}
        self.row_sources, self.part_rows, self.anchors = {}, collections.defaultdict(list), collections.defaultdict(set)
        self.conflicts, self.verdicts, self.formality_evidence = [], collections.Counter(), collections.defaultdict(list)
        self.documents, self.decision_rows = {}, collections.defaultdict(set)
        rfc_files = {e.get("file"): e for e in self.t["rfc"].values()}
        parts = set(self.parts)
        titles = collections.defaultdict(list)
        for rid, row in self.t["row"].items():
            where = f"row {rid}"
            if not all(isinstance(row.get(k), str) for k in ("title", "area", "component", "label")):
                self.add("TABLE", f"{where}: title, area, component and label are text")
                continue
            titles[C.collapse(row["title"]).lower()].append(rid)
            if row["area"] not in AREAS or row["component"] not in COMPONENTS or row["label"] not in LABELS:
                self.add("TABLE", f"{where}: area {row['area']!r}, component {row['component']!r} or label {row['label']!r} is not in the vocabulary")
            owned = self.own(rid, row)
            rank1_rfc = False
            for i, item in enumerate(row.get("std_text", [])):
                if self.cite("CITE", f"{where} std_text[{i}]", item, kinds={"std"}):
                    self.anchor(rid, item["ref"])
            for i, item in enumerate(row.get("formality", [])):
                at = self.cite("CITE", f"{where} formality[{i}]", item, word_key="judgment", kinds={"a-mir-formality"})
                if at and item.get("kind") == "judgment" and self.judgments.get((at[1], at[2])) != item.get("judgment"):
                    self.add("CITE", f"{where} formality[{i}]: {item['ref']} is not the judgment_fn! {item.get('judgment')!r}")
                elif at and item.get("kind") not in ("judgment", "fn"):
                    self.add("TABLE", f"{where} formality[{i}]: kind is judgment or fn")
                if at:
                    self.anchor(rid, item["ref"])
            for i, item in enumerate(row.get("rfcs", [])):
                at = self.cite("CITE", f"{where} rfcs[{i}]", item, kinds={"rfcs"})
                if at and at[1] not in rfc_files:
                    self.add("CITE", f"{where} rfcs[{i}]: {at[1]} is not a registered [[rfc]]")
                elif at:
                    rank1_rfc |= rfc_files[at[1]].get("status") in RANK1_RFC
                    self.rfc_uses.add(at[1])
                    self.anchor(rid, item["ref"])
            for i, item in enumerate(row.get("decisions", [])):
                if self.decision(f"{where} decisions[{i}]", item):
                    self.decision_rows[item["snapshot"]].add(rid)
                    self.anchor(rid, ("decision", item.get("snapshot"), item.get("part"), C.collapse(item.get("quote", ""))))
            for i, doc in enumerate(row.get("documents", [])):
                dwhere = f"{where} documents[{i}]"
                text = self.member_text(doc.get("source"), doc.get("id"))
                if text is None or not isinstance(doc.get("quote"), str) or C.collapse(doc["quote"]) not in text or not doc.get("reason"):
                    self.add("CITE", f"{dwhere}: {doc.get('source')} member {doc.get('id')!r} does not hold the quote, or the citation has no reason")
                elif doc["id"] in owned:
                    self.add("CITE", f"{dwhere}: the row owns {doc['id']}; a documenting citation names a member another row owns")
                else:
                    self.documents[(doc["source"], doc["id"])] = rid
                    self.anchor(rid, ("member", doc["source"], doc["id"]))
            behavior = row.get("rustc_behavior")
            tests = behavior.get("tests", []) if isinstance(behavior, dict) else []
            for i, test in enumerate(tests):
                if self.rustc_test(f"{where} rustc_behavior.tests[{i}]", test):
                    self.anchor(rid, test["ref"])
            own_parts = set()
            for p in row.get("design_parts", []):
                key = (p.get("kind"), p.get("phrase")) if isinstance(p, dict) else None
                if key not in parts:
                    self.add("LABEL", f"{where}: design part {key} is not named by the design's (St) block (stale)")
                else:
                    own_parts.add(key)
                    self.part_rows[key].append(rid)
            gaps = self.conflict_rows(rid, row, own_parts, rfc_files)
            self.row_sources[rid] = {"rank1": bool(owned & (set(self.fls["members"]) | set(self.ref["members"]) | set(self.std) | set(self.std_docs)))
                                     or rank1_rfc or bool(row.get("documents") or row.get("std_text")),
                                     "rank2": bool(row.get("formality") or row.get("decisions")), "label": row["label"], "gaps": gaps}
            self.labels(rid, row, owned, own_parts, tests, rank1_rfc)
            self.searches(rid, row, owned)
        signatures = collections.defaultdict(list)
        for kind, rid, _, anchors in self.conflicts:
            signatures[(kind, anchors)].append(rid)
        for (kind, _), rids in signatures.items():
            if len(rids) > 1:
                self.add("TABLE", f"rows {rids} record the same {kind} conflict (kind and evidence)")
        for sid, rid in self.owner["section"].items():
            members = [p for p, _, _ in self.fls["member_sections"][sid].paragraphs if p in self.fls["members"]]
            if members and not any(self.owner["fls"].get(p) == rid for p in members):
                self.add("UNIVERSE", f"row {rid}: owns FLS section {sid} but none of its member paragraphs")
        for title, ids in titles.items():
            if len(ids) > 1:
                self.add("TABLE", f"rows {ids} share the title {title!r}")
        for anchor, rids in self.anchors.items():
            if len(rids) > 1:
                self.add("TABLE", f"the citation {anchor} is cited by rows {sorted(rids)}; a citation belongs to one row")
        for (source, mid), rid in self.documents.items():
            if self.owner["std" if source == "std" else source].get(mid) is None:
                self.add("CITE", f"row {rid}: documenting citation {source} {mid} is owned by no row")
        for rid, row in self.t["row"].items():
            target = row.get("refines")
            if row.get("label") != "documented" and target is not None:
                other = self.t["row"].get(target, {})
                shared = {(p.get("kind"), p.get("phrase")) for p in row.get("design_parts", [])} & \
                         {(p.get("kind"), p.get("phrase")) for p in other.get("design_parts", [])}
                if other.get("label") != "documented" or not shared:
                    self.add("LABEL", f"row {rid}: refines {target!r}, which is not a documented row sharing one of its design parts")

    def own(self, rid: str, row: dict) -> set:
        owned = set()
        for source, key, universe in (("fls", "fls", self.fls["members"]), ("section", "fls_sections", self.fls["member_sections"]),
                                      ("reference", "reference", self.ref["members"]), ("std", "std", {**self.std, **self.std_docs})):
            for mid in row.get(key, []):
                if mid not in universe:
                    self.add("UNIVERSE", f"row {rid}: {source} member {mid!r} is not in the universe at the pin")
                elif mid in self.owner[source]:
                    self.add("UNIVERSE", f"row {rid}: {source} member {mid} is already owned by row {self.owner[source][mid]}")
                else:
                    self.owner[source][mid] = rid
                    owned.add(mid)
        return owned

    def anchor(self, rid: str, anchor) -> None:
        self.anchors[span(anchor) if isinstance(anchor, str) else anchor].add(rid)

    def rank1_rfc(self, where: str, path: str, what: str) -> None:
        """A citation whose meaning is rank-1 RFC text names a registered stabilized RFC, and uses its entry."""
        self.rfc_uses.add(path)
        if next((e.get("status") for e in self.t["rfc"].values() if e.get("file") == path), None) not in RANK1_RFC:
            self.add("LABEL", f"{where}: {what} cites {path}, which is not a registered rank-1 (stabilized) RFC")

    def rustc_test(self, where: str, test: dict) -> bool:
        at = self.cite("CITE", where, test, kinds={"worktree", "trust-test"})
        if at is not None and not at[1].startswith("tests/"):
            self.add("CITE", f"{where}: a rustc test is a file under tests/")
        return at is not None and at[1].startswith("tests/")

    def decision(self, where: str, item: dict) -> bool:
        snapshot = self.snapshots.get(item.get("snapshot"))
        if snapshot is None or snapshot.get("schema") != DECISION_SNAPSHOT:
            self.add("CITE", f"{where}: {item.get('snapshot')!r} is not a registered decision snapshot")
            return False
        for problem in decision_problems(snapshot, self.sel["decisions"], self.pins.alignment_date):
            self.add("CITE", f"{where}: {snapshot.get('repo')}#{snapshot.get('number')} {problem}")
        part = item.get("part")
        body, edited = (snapshot.get("body"), snapshot.get("body_last_edited_at")) if part == "body" else next(
            ((c.get("body"), c.get("last_edited_at")) for c in snapshot.get("comments", []) if f"comment:{c.get('id')}" == part), (None, None))
        quote = item.get("quote")
        if body is None or not isinstance(quote, str) or len(C.collapse(quote)) < MIN_QUOTE or C.collapse(quote) not in C.collapse(body):
            self.add("CITE", f"{where}: {item.get('snapshot')} {part} does not hold the quote {quote!r}")
            return False
        if edited is not None and edited > self.pins.alignment_date:
            self.add("CITE", f"{where}: {item.get('snapshot')} {part} was last edited at {edited}, after the alignment")
        return True

    def conflict_rows(self, rid: str, row: dict, own_parts: set, rfc_files: dict) -> set:
        gaps = set()
        tests = (row.get("rustc_behavior") or {}).get("tests", [])
        for i, conflict in enumerate(row.get("conflicts", [])):
            kind = conflict.get("kind")
            where = f"row {rid} conflicts[{i}] {kind}"
            if kind not in CONFLICT_SIDES or not conflict.get("summary") or not conflict.get("evidence"):
                self.add("LABEL", f"{where}: a conflict has a kind of {sorted(CONFLICT_SIDES)}, a summary and evidence")
                continue
            if kind == "document-gap":
                if not isinstance(conflict.get("parts"), list):
                    self.add("LABEL", f"{where}: a document-gap lists in parts the design parts it leaves without a full rank-1 statement (possibly none)")
                for p in conflict.get("parts") or []:
                    key = (p.get("kind"), p.get("phrase")) if isinstance(p, dict) else None
                    gaps.add(key)
                    if key not in own_parts:
                        self.add("LABEL", f"{where}: gap part {key} is not one of the row's design parts")
            elif "parts" in conflict:
                self.add("LABEL", f"{where}: parts belongs to a document-gap")
            outcome_key = OUTCOME_KEYS.get(kind)
            outcome = conflict.get(outcome_key)
            if any(k in conflict for k in OUTCOME_KEYS.values() if k != outcome_key) or (outcome_key and outcome not in OPPOSITE):
                self.add("LABEL", f"{where}: {outcome_key or 'no outcome'} must be accept or reject, and no other outcome key")
            admitted, required = CONFLICT_SIDES[kind]
            sides, anchors = set(), []
            for j, item in enumerate(conflict["evidence"]):
                ewhere, side = f"{where} evidence[{j}]", item.get("side")
                if side not in admitted:
                    self.add("LABEL", f"{ewhere}: side {side!r} is not admitted by {kind}")
                    continue
                sides.add(side)
                if side == "decision":
                    if self.decision(ewhere, item):
                        self.decision_rows[item["snapshot"]].add(rid)
                        anchors.append(("decision", item["snapshot"], item.get("part"), C.collapse(item["quote"])))
                    continue
                if side == "rustc" and str(item.get("ref", "")).split(":", 1)[-1].startswith("tests/"):
                    ok = self.rustc_test(ewhere, item)
                    if ok and outcome in OPPOSITE and item.get("expect") not in OPPOSITE[outcome]:
                        self.add("LABEL", f"{ewhere}: {item['ref']} expects {item.get('expect')!r}, the outcome {outcome_key} predicts; it is no evidence of a difference")
                    at = span(item["ref"]) if ok else None
                else:
                    at = self.cite("CITE", ewhere, item, kinds=SIDE_KINDS[side])
                if at is None:
                    continue
                anchors.append(at)
                self.anchor(rid, item["ref"])
                if at[0] == "rfcs" and side == "document":
                    self.rank1_rfc(ewhere, at[1], "document evidence")
                if kind == "formality-rustc" and at[0] == "a-mir-formality":
                    self.formality_evidence[(at[1], at[2])].append(rid)
            if missing := required - sides:
                self.add("LABEL", f"{where}: evidence lacks the required sides {sorted(missing)}")
            if kind in OUTCOME_KEYS and not any(i.get("side") == "rustc" and "tests/" in str(i.get("ref")) for i in conflict["evidence"]):
                self.add("LABEL", f"{where}: a {kind} conflict needs a rustc test with an expect")
            if row.get("label") == "compat-candidate" and kind == "document-rustc" and outcome in OPPOSITE and \
                    not any(t.get("expect") in OPPOSITE[outcome] for t in tests):
                self.add("LABEL", f"{where}: no rustc_behavior test has the outcome opposite to {outcome!r}")
            self.conflicts.append((kind, rid, conflict, tuple(sorted(map(str, anchors)))))
        return gaps

    def labels(self, rid: str, row: dict, owned: set, own_parts: set, tests: list, rank1_rfc: bool) -> None:
        where, label = f"row {rid}", row["label"]
        kinds = {c.get("kind") for c in row.get("conflicts", [])}
        sources = row.get("formality") or row.get("rfcs") or row.get("decisions") or row.get("documents") or row.get("std_text")
        if label == "documented":
            if not (owned or row.get("formality") or rank1_rfc or row.get("decisions") or row.get("documents") or row.get("std_text")):
                self.add("LABEL", f"{where}: documented but cites no FLS, Reference, standard-library, RFC, a-mir-formality or decision source")
            if row.get("rustc_behavior") is not None or "document-rustc" in kinds or row.get("refines") is not None:
                self.add("LABEL", f"{where}: a documented row carries no rustc_behavior, document-rustc conflict or refines")
            return
        if owned or row.get("fls_sections") or sources:
            self.add("LABEL", f"{where}: a {label} row owns no member and cites no row-level source (its documents are conflict evidence or search verdicts)")
        if not own_parts:
            self.add("LABEL", f"{where}: a {label} row maps a design part")
        if not (row.get("rustc_behavior") or {}).get("behavior") or not tests:
            self.add("LABEL", f"{where}: a {label} row states a rustc behavior with rustc tests")
        if label == "compat-candidate" and ("document-rustc" not in kinds or not row.get("refines")):
            self.add("LABEL", f"{where}: a compat-candidate carries a document-rustc conflict and refines a documented row")

    def corpus_files(self, corpus: str) -> list:
        tree = self.trees[corpus if corpus != "fls" else "fls"]
        if corpus == "fls":
            return [f"src/{c}.rst" for c in self.fls["chapters"]]
        if corpus == "reference":
            return [f"src/{r}" for r in self.ref["files"]]
        if corpus == "rfcs":
            return tree.files("text/", (".md",))
        if corpus == "std":
            return tree.files("library/", (".rs",))
        return tree.files("", (".rs", ".md"))

    def searches(self, rid: str, row: dict, owned: set) -> None:
        records, label = row.get("search", []), row["label"]
        verdicts = []
        corpora = collections.Counter(s.get("corpus") for s in records)
        if records or label != "documented":
            if sorted(corpora) != sorted(SEARCH_CORPORA) or max(corpora.values(), default=0) > 1:
                self.add("SEARCH", f"row {rid}: a searched row records exactly one search of each of {SEARCH_CORPORA}, not {dict(corpora)}")
        for s in records:
            corpus, where = s.get("corpus"), f"row {rid} search {s.get('corpus')}"
            if corpus not in SEARCH_CORPORA or not s.get("finding"):
                self.add("SEARCH", f"{where}: a search names a corpus of {SEARCH_CORPORA} and records its finding")
                continue
            verdicts += self.decision_search(where, s) if corpus == "decisions" else self.text_search(where, corpus, s)
        self.verdicts.update(verdicts)
        if label == "de-facto" and any(v in ("documents", "contrary") for _, v in verdicts):
            self.add("LABEL", f"row {rid}: a de-facto row's search records no documents or contrary verdict")
        if label == "compat-candidate" and not any(c in RANK1_CORPORA and v == "contrary" for c, v in verdicts):
            self.add("LABEL", f"row {rid}: a compat-candidate's search records a contrary rank-1 text")
        if label == "documented" and records and not owned and not any(v == "documents" for _, v in verdicts):
            self.add("LABEL", f"row {rid}: a searched documented row that owns no member records a documents verdict")

    def text_search(self, where: str, corpus: str, s: dict) -> list:
        verdicts, scope = [], set()
        if corpus in ("fls", "reference", "std"):
            for item in s.get("scope", []):
                members = {p for p, _, _ in self.fls["member_sections"][item].paragraphs if p in self.fls["members"]} if corpus == "fls" and item in self.fls["member_sections"] else \
                    {r for r in self.ref["members"] if r == item or r.startswith(item + ".")} if corpus == "reference" else \
                    {m for m, (locations, _) in self.std.items() if any(f == item for f, _ in locations)} | \
                    {m for m, (f, _, _) in self.std_docs.items() if f == item} if corpus == "std" else set()
                if not members:
                    self.add("SEARCH", f"{where}: scope {item!r} holds no universe member")
                scope |= members
            if not s.get("scope") and not (corpus == "std" and s.get("scope_note")):
                self.add("SEARCH", f"{where}: names the scope that governs the construct (a std search may instead give a scope_note)")
            listed = collections.Counter(s.get("silent", []) + [a.get("id") for a in s.get("addresses", [])])
            if set(listed) != scope or max(listed.values(), default=1) > 1:
                self.add("SEARCH", f"{where}: silent and addressed must be exactly the scope members, once each: "
                                   f"missing {sorted(scope - set(listed))[:4]}, stale {sorted(set(listed) - scope)[:4]}")
            verdicts += [(corpus, "silent")] if s.get("silent") else []
        elif s.get("scope") or s.get("silent"):
            self.add("SEARCH", f"{where}: scope and silent belong to the fls, reference and std corpora")
        for i, a in enumerate(s.get("addresses", [])):
            awhere = f"{where} addresses[{i}]"
            if a.get("verdict") not in VERDICTS or not a.get("reason"):
                self.add("SEARCH", f"{awhere}: a verdict of {VERDICTS} with a reason")
                continue
            if corpus in ("fls", "reference", "std"):
                text = self.member_text(corpus, a.get("id"))
                if text is None or not isinstance(a.get("quote"), str) or C.collapse(a["quote"]) not in text:
                    self.add("CITE", f"{awhere}: {corpus} member {a.get('id')!r} does not hold the quote")
            else:
                at = self.cite("CITE", awhere, a, kinds={corpus})
                if at and corpus == "rfcs" and a["verdict"] in ("documents", "contrary"):
                    self.rank1_rfc(awhere, at[1], f"a {a['verdict']} verdict")
            verdicts.append((corpus, a["verdict"]))
        terms, files = s.get("terms", []), self.corpus_files(corpus)
        if not terms:
            self.add("SEARCH", f"{where}: a search declares its terms")
        declared = collections.defaultdict(set)
        for i, m in enumerate(s.get("mentions", [])):
            mwhere = f"{where} mentions[{i}]"
            at = self.cite("CITE", mwhere, m, kinds={corpus})
            if at and corpus == "rfcs" and m.get("verdict") in ("documents", "contrary"):
                self.rank1_rfc(mwhere, at[1], f"a {m.get('verdict')} verdict")
            if m.get("term") not in terms or m.get("verdict") not in VERDICTS or not m.get("reason") or \
                    str(m.get("term")).lower() not in C.collapse(str(m.get("quote", ""))).lower():
                self.add("SEARCH", f"{mwhere}: names a declared term its quote holds, a verdict of {VERDICTS} and a reason")
            if at:
                if at[1] in declared[m.get("term")]:
                    self.add("SEARCH", f"{mwhere}: {at[1]} is already a mention of {m.get('term')!r}")
                declared[m.get("term")].add(at[1])
            verdicts.append((corpus, m.get("verdict")))
        tree = self.trees[corpus]
        tree.prefetch(files)
        for term in terms:
            hits = {f for f in files if str(term).lower() in (tree.text(f) or "").lower()}
            if hits != declared[term]:
                self.add("SEARCH", f"{where}: term {term!r} occurs in {len(hits)} files; unrecorded {sorted(hits - declared[term])[:4]}, stale {sorted(declared[term] - hits)[:4]}")
        return verdicts

    def decision_search(self, where: str, s: dict) -> list:
        index = self.snapshots.get(s.get("index"))
        if index is None or index.get("schema") != DECISION_INDEX:
            self.add("SEARCH", f"{where}: {s.get('index')!r} is not a registered decision index snapshot")
            return []
        queries = s.get("queries", [])
        known = {q.get("id"): q for q in index.get("queries", [])}
        if not queries or any(q not in known for q in queries):
            self.add("SEARCH", f"{where}: queries {queries} are not queries of {s.get('index')}")
        items = {i["number"]: i for q in queries if q in known for kind in ("issue", "pull-request")
                 for i in known[q].get("kinds", {}).get(kind, {}).get("items", [])}
        seen, verdicts = collections.Counter(), []
        for d in s.get("dispositions", []):
            number, verdict = d.get("number"), d.get("verdict")
            dwhere = f"{where} #{number}"
            seen[number] += 1
            item = items.get(number)
            if item is None or verdict not in VERDICTS + ("after-alignment",) or not d.get("reason"):
                self.add("SEARCH", f"{dwhere}: a result of the queries with a verdict and a reason")
                continue
            after = item.get("closed_at") is None or item["closed_at"] > self.pins.alignment_date
            if after != (verdict == "after-alignment"):
                self.add("SEARCH", f"{dwhere}: closed at {item.get('closed_at')}; after-alignment is the verdict exactly for results open or closed after the alignment")
            if verdict in ("documents", "contrary", "open"):
                snapshot = self.snapshots.get(d.get("snapshot"), {})
                if not self.decision(dwhere, d) or snapshot.get("number") != number:
                    self.add("SEARCH", f"{dwhere}: a {verdict} verdict quotes the decision's own snapshot")
                else:
                    self.decision_rows[d["snapshot"]].add(where.split()[1])
            verdicts.append(("decisions", verdict))
        for number in sorted(set(items) | set(seen)):
            if seen[number] != 1:
                self.add("SEARCH", f"{where}: #{number} is dispositioned {seen[number]} times, not once")
        return verdicts

    # ---- DISPOSE
    def dispositions(self) -> None:
        components = {rid: row.get("component") for rid, row in self.t["row"].items()}
        member_owner = {**self.owner["fls"], **self.owner["reference"], **self.owner["std"]}
        st = lambda rid: str(components.get(rid, "")).startswith("St.")  # noqa: E731
        predicates = self.sel["predicates"]
        text_p, id_p = re.compile(predicates.get("side_condition_text", "$^"), re.I), re.compile(predicates.get("side_condition_id", "$^"))
        marker_p = re.compile(predicates.get("side_condition_grammar_marker", "$^"))
        self.markers = {r for r, (_, _, lines) in self.ref["members"].items()
                        if any(marker_p.search(re.sub(r"`[^`]*`", "``", g)) for g in grammar_lines(lines))}
        self.candidates = {r for r, (_, _, lines) in self.ref["members"].items()
                           if text_p.search(rule_text(lines, grammar=True)) or id_p.search(r) or r in self.markers}
        cited, names = collections.defaultdict(list), collections.defaultdict(list)
        for sid, condition in self.t["grammar_side_condition"].items():
            where = f"grammar_side_condition {sid}"
            names[C.collapse(str(condition.get("name", ""))).lower()].append(sid)
            members = [("fls", m) for m in condition.get("fls", [])] + [("reference", m) for m in condition.get("reference", [])]
            if not condition.get("name") or not any(m in self.candidates for m in condition.get("reference", [])):
                self.add("DISPOSE", f"{where}: a side condition has a name and cites a Reference rule the predicates select")
            for source, member in members:
                cited[(source, member)].append(sid)
                if components.get(self.owner[source].get(member)) not in GRAMMAR_COMPONENTS:
                    self.add("DISPOSE", f"{where}: {source} {member} is not owned by a grammar row")
        dismissed = collections.defaultdict(list)
        self.dismissal_kinds = collections.Counter()
        for did, dismissal in self.t["grammar_side_condition_dismissal"].items():
            kind = dismissal.get("kind")
            if kind not in DISMISSAL_KINDS or did != kind or not dismissal.get("reason"):
                self.add("DISPOSE", f"grammar_side_condition_dismissal {did}: id equals a kind of {DISMISSAL_KINDS}, with a reason")
            if not dismissal.get("reference"):
                self.add("DISPOSE", f"grammar_side_condition_dismissal {did}: dismisses no candidate (stale)")
            for member in dismissal.get("reference", []):
                dismissed[member].append(did)
                self.dismissal_kinds[kind] += 1
                if member not in self.candidates or ("reference", member) in cited:
                    self.add("DISPOSE", f"dismissal {did}: {member} is not an uncited side-condition candidate (stale)")
                if member in self.markers and kind == "not-a-restriction":
                    self.add("DISPOSE", f"dismissal {did}: {member}'s grammar uses a lookahead, cut or counted repetition, a derivation side condition by the notation's own definition")
        for group in (names, cited, dismissed):
            for key, ids in group.items():
                if len(ids) > 1:
                    self.add("DISPOSE", f"{key} appears in {ids}; each appears once")
        self.undispositioned_side = sorted(c for c in self.candidates if ("reference", c) not in cited and c not in dismissed)
        for member in self.undispositioned_side:
            self.add("DISPOSE", f"side-condition candidate {member} is neither cited by a side condition nor dismissed")
        self.cited_side = {m for s, m in cited if s == "reference" and m in self.candidates}
        self.side_conditions = [c.get("name") for c in self.t["grammar_side_condition"].values()]

        runtime = set(self.sel["fls"].get("runtime_rubrics", []))
        self.outside = {("fls", p): o for p, o in self.owner["fls"].items() if not st(o) and self.fls["members"][p][1] not in runtime}
        self.outside.update({(s, m): o for s in ("reference", "std") for m, o in self.owner[s].items() if not st(o)})
        self.runtime_members = sum(1 for p, o in self.owner["fls"].items() if not st(o) and self.fls["members"][p][1] in runtime)
        self.kind_of, disposed = {}, collections.defaultdict(list)
        for did, entry in self.t["outside_st_static_candidate"].items():
            kind, where = entry.get("kind"), f"outside_st_static_candidate {did}"
            if kind not in DISPOSITION_KINDS or not (did == kind or str(did).startswith(f"{kind}:")) or not entry.get("reason"):
                self.add("DISPOSE", f"{where}: a kind of {DISPOSITION_KINDS}, an id that is the kind or starts with it, and a reason")
            if (kind == "restated") != bool(entry.get("restates")) or any(not st(member_owner.get(m)) for m in entry.get("restates", [])):
                self.add("DISPOSE", f"{where}: restates names (St)-owned members, exactly for kind restated")
            if not any(entry.get(source) for source in ("fls", "reference", "std")):
                self.add("DISPOSE", f"{where}: dispositions no member (stale)")
            for source in ("fls", "reference", "std"):
                for member in entry.get(source, []):
                    disposed[(source, member)].append(did)
                    self.kind_of[(source, member)] = kind
                    if (source, member) not in self.outside:
                        self.add("DISPOSE", f"{where}: {source} {member} is not a member mapped outside (St) (stale)")
        for key, ids in disposed.items():
            if len(ids) > 1:
                self.add("DISPOSE", f"{key[0]} {key[1]} is dispositioned by {ids}")
        self.undispositioned = sorted(k for k in self.outside if k not in disposed)
        for source, member in self.undispositioned:
            self.add("DISPOSE", f"{source} {member} (row {self.outside[(source, member)]}) is mapped outside (St) with no disposition")

        twin_of, self.one_sided = {}, 0
        for tid, group in self.t["twin"].items():
            members = [(s, m) for s in ("fls", "reference", "std") for m in group.get(s, [])]
            if not members or not group.get("note"):
                self.add("DISPOSE", f"twin {tid}: a twin group has members and a note")
                continue
            self.one_sided += len({s for s, _ in members}) < 2
            strata = {str(components.get(self.owner[s].get(m), "?")).split(".")[0] for s, m in members}
            for s, m in members:
                if (s, m) in twin_of:
                    self.add("DISPOSE", f"twin {tid}: {s} {m} is already in twin group {twin_of[(s, m)]}")
                twin_of[(s, m)] = tid
                if self.owner[s].get(m) is None:
                    self.add("DISPOSE", f"twin {tid}: {s} {m} is not a mapped member")
            if len(strata) > 1:
                self.add("DISPOSE", f"twin {tid}: its members sit in the strata {sorted(strata)}; the statements of one rule sit in one stratum")
        self.twin_required = [k for k, kind in self.kind_of.items() if kind in ACKNOWLEDGING and k in self.outside]
        for key in self.twin_required:
            if key not in twin_of:
                self.add("DISPOSE", f"{key[0]} {key[1]} is dispositioned {self.kind_of[key]} and is in no twin group")

        self.note_kinds, seen = collections.Counter(), set()
        for ref, note in self.t["formality_test_note"].items():
            at = self.cite("CITE", f"formality_test_note {ref}", note, kinds={"a-mir-formality"})
            key = (at[1], at[2]) if at else None
            self.note_kinds[note.get("kind")] += 1
            seen.add(key)
            if note.get("kind") not in NOTE_KINDS or not note.get("reason") or key not in self.notes:
                self.add("DISPOSE", f"formality_test_note {ref}: a kind of {NOTE_KINDS} with a reason, on a line the note predicate selects")
            if (note.get("kind") == "divergence") != bool(self.formality_evidence.get(key)):
                self.add("DISPOSE", f"formality_test_note {ref}: a divergence is exactly a note cited as formality-rustc evidence")
        for key in sorted(set(self.notes) - seen):
            self.add("DISPOSE", f"a-mir-formality note {key[0]}:{key[1]} {self.notes[key]!r} has no formality_test_note")
        for key, rids in self.formality_evidence.items():
            if key[0].startswith("tests/") and key not in self.notes:
                self.add("DISPOSE", f"formality-rustc evidence {key[0]}:{key[1]} (rows {rids}) is a test line the note predicate does not select")

        self.error_citations = 0
        grep = C.git(self.o.repo, "grep", "-n", "-E", r"^//@ *reference:", "HEAD", "--", "tests") or ""
        rejecting = {}
        for line in grep.splitlines():
            m = re.match(r"^HEAD:([^:]+):\d+://@ *reference: *(\S+)", line)
            if not m or m.group(2) not in self.ref["members"] or st(self.owner["reference"].get(m.group(2))):
                continue
            path, rule = m.groups()
            if path not in rejecting:
                rejecting[path] = any(kind == "ERROR" for _, kind, _ in annotations(self.trees["worktree"].lines(path) or []))
            if rejecting[path]:
                self.error_citations += 1
                if self.kind_of.get(("reference", rule)) in DESCRIPTIVE + ("run-time-requirement",):
                    self.add("DISPOSE", f"{path} expects an error and cites {rule}, dispositioned {self.kind_of[('reference', rule)]}: "
                                        "a rule a rejecting test cites is (St), or acknowledges the phase that rejects (or no-rejection)")

    # ---- pin exceptions and the post-alignment delta
    def pin_delta(self) -> None:
        self.delta = {"added": {}, "removed": {}, "changed": {}, "formality": []}
        for name, exc in self.t["pin_exception"].items():
            where = f"pin_exception {name}"
            snap = self.snapshots.get(exc.get("snapshot"))
            pins = self.pins
            historical = "historical_at" in exc
            if historical:
                try:
                    pins = historical_exception_pins(self.o.repo, exc, self.t["snapshot"].get(exc.get("snapshot")), self.pins)
                except ValueError as error:
                    self.add("PIN-DELTA", f"{where}: {error}")
                    continue
            source = pins.sources.get(name)
            if snap is None or snap.get("schema") != PIN_DERIVATION or source is None or not exc.get("decision"):
                self.add("PIN-DELTA", f"{where}: names a source of EXTERNAL_PINS.toml, a registered pin-derivation snapshot and a decision")
                continue
            compare, state = snap.get("compare", {}), snap.get("default_branch_state", {})
            successor, merged = snap.get("successor", {}), snap.get("merged_into_default_branch_by", {})
            facts = {"default_branch_state": state.get("sha"), "state_committer_date": state.get("committer_date"),
                     "successor": successor.get("sha"), "successor_committer_date": successor.get("committer_date"),
                     "merged_into_default_branch_by": merged.get("sha"), "merged_at": merged.get("committer_date"),
                     "commits_after_state": len(compare.get("commits", []))}
            problems = [f"{k} is {exc.get(k)!r}, the snapshot records {v!r}" for k, v in facts.items() if exc.get(k) != v]
            ts = pins.alignment_date
            if snap.get("repo") != source.url.removeprefix("https://github.com/") or compare.get("base") != state.get("sha") or \
                    compare.get("head") != source.revision or (compare.get("commits") or [None])[-1] != source.revision:
                problems.append("the snapshot does not compare the recorded state with the pinned revision")
            if compare.get("status") != "ahead" or compare.get("behind_by") != 0 or compare.get("ahead_by") != facts["commits_after_state"]:
                problems.append("the pin is not the state plus descendant commits only (ahead, behind 0)")
            if not (str(state.get("committer_date")) <= ts < str(successor.get("committer_date"))) or \
                    (successor.get("parents") or [None])[0] != state.get("sha") or not ts < str(merged.get("committer_date")):
                problems.append("the state is not the last first-parent commit at the alignment, with the pin merged after it")
            for problem in problems:
                self.add("PIN-DELTA", f"{where}: {problem}")
            if problems:
                continue
            tree = self.trees["fls" if name == "fls" else READS.get(name, name)]
            if historical:
                path = Path(self.o.clones.get(name) or C.sources_root() / source.directory)
                tree = C.GitTree(path, source.revision)
            for f in compare.get("files", []):
                if name != "fls":
                    if not historical:
                        self.delta["formality"] += [line[1:].strip() for line in f.get("patch", "").split("\n") if line.startswith("+")
                                                    and not line.startswith("+++") and (JUDGMENT_OPEN.match(line[1:]) or
                                                    re.search(self.sel["predicates"].get("formality_note", "$^"), line[1:]))]
                    continue
                payload = tree.text(f.get("filename"))
                if historical and payload is None and f.get("status") != "removed":
                    self.add("PIN-DELTA", f"{where}: historical source file {f.get('filename')} is unavailable")
                    continue
                after = payload or ""
                before = "" if f.get("status") == "added" else reverse_patch(after, f["patch"]) if f.get("patch") else None
                if before is None:
                    self.add("PIN-DELTA", f"{where}: the snapshot's patch of {f.get('filename')} does not apply to the pinned file")
                    continue
                if historical:
                    continue
                old, new = fls_paragraphs({f["filename"]: before}), fls_paragraphs({f["filename"]: after})
                for pid in new.keys() - old.keys():
                    if pid in self.fls["members"]:
                        self.delta["added"][pid] = self.owner["fls"].get(pid)
                for pid in old.keys() - new.keys():
                    self.delta["removed"][pid] = f.get("filename")
                for pid in old.keys() & new.keys():
                    if old[pid] != new[pid] and pid in self.fls["members"]:
                        self.delta["changed"][pid] = self.owner["fls"].get(pid)

    # ---- snapshots
    def load_snapshots(self) -> None:
        self.snapshots = {}
        rels, pins = [], {}
        for rel, entry in self.data_table("snapshot").items():
            if not isinstance(rel, str) or not rel.startswith(SNAPSHOT_DIR + "/") or not rel.endswith(".json") or not str(entry.get("sha256", "")).startswith("sha256:"):
                self.add("SNAPSHOT", f"snapshot {rel}: a .json file under {SNAPSHOT_DIR}/ with a sha256")
                continue
            rels.append(rel)
            pins[rel] = entry["sha256"][7:]
            try:
                text = (self.o.repo / rel).read_text(encoding="utf-8")
                parsed = json.loads(text) if text == self.trees["worktree"].text(rel) else None
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                parsed = None
            if not isinstance(parsed, dict):
                self.add("SNAPSHOT", f"snapshot {rel}: is not a JSON object committed at HEAD exactly as the working tree holds it "
                                     "(the bytes the checker parses are the bytes its sha256 and first-version checks compare)")
                continue
            own = (SNAPSHOT_KINDS.get(parsed.get("schema")), parsed.get("retrieved"), snapshot_url(parsed))
            if (entry.get("kind"), entry.get("retrieved"), entry.get("url")) != own:
                self.add("SNAPSHOT", f"snapshot {rel}: kind, retrieved and url are {(entry.get('kind'), entry.get('retrieved'), entry.get('url'))}, the snapshot's own are {own}")
            self.snapshots[rel] = parsed
        C.check_immutable(self.f, "SNAPSHOT", self.o.repo, rels, pins)
        committed = set(self.trees["worktree"].files(SNAPSHOT_DIR + "/", (".json",)))
        for rel in sorted(committed - set(rels)):
            self.add("SNAPSHOT", f"{rel} is committed but not registered")

    def data_table(self, kind: str) -> dict:
        return {r.get(TABLES[kind][0]): r for r in self.data.get(kind, []) if isinstance(r, dict)}

    def uses(self) -> None:
        """No registered snapshot or RFC that nothing uses; every UI test bound to a row is cited by it."""
        used = set(self.decision_rows) | {e.get("snapshot") for e in self.t["pin_exception"].values()}
        used |= {s.get("index") for r in self.t["row"].values() for s in r.get("search", []) if s.get("corpus") == "decisions"}
        for rel in sorted(set(self.snapshots) - used):
            self.add("SNAPSHOT", f"snapshot {rel} is registered but used by no row or pin exception (stale)")
        for number, entry in self.t["rfc"].items():
            if entry.get("file") not in self.rfc_uses:
                self.add("TABLE", f"rfc {number}: {entry.get('file')} is registered but no row source, conflict evidence or documents or contrary verdict cites it (stale)")
        for path, rid in self.bound_tests.items():
            row = self.t["row"].get(rid, {})
            refs = [t.get("ref") for t in (row.get("rustc_behavior") or {}).get("tests", [])] + \
                   [e.get("ref") for c in row.get("conflicts", []) for e in c.get("evidence", [])]
            if not any(str(r).startswith(f"trust-test:{path}:") for r in refs):
                self.add("CITE", f"{path} names row {rid}, which does not cite it as trust-test; a test written for a row is retired or re-bound with it")

    # ---- counts and blocks
    def measure(self) -> dict:
        c, rows = {}, self.t["row"]
        fls, ref = self.fls, self.ref
        c["universe.fls.chapters"], c["excluded.fls.chapters.informational-page"] = len(fls["chapters"]), len(fls["pages"])
        c["universe.fls.sections"] = len(fls["member_sections"])
        c["universe.fls.sections.with-syntax-block"] = sum(1 for s in fls["member_sections"].values() if s.syntax)
        for reason in ("heading-only", "informational-page", "informational-section", "only-excluded-rubrics"):
            c[f"excluded.fls.sections.{reason}"] = fls["excluded_sections"][reason]
        c["universe.fls.paragraphs"] = len(fls["members"])
        for reason in ["informational-page", "informational-section"] + [f"rubric:{r}" for r in self.sel["fls"].get("excluded_rubrics", [])]:
            c[f"excluded.fls.paragraphs.{reason}"] = fls["excluded"][reason]
        for rubric, n in sorted(fls["rubrics"].items()):
            c[f"universe.fls.paragraphs.rubric:{rubric}"] = n
        c["universe.reference.files"], c["excluded.reference.files"] = len(ref["files"]), len(ref["excluded_files"])
        c["universe.reference.rules"] = len(ref["members"])
        c["excluded.reference.rules"] = len(ref["rules"]) - len(ref["members"])
        c["excluded.reference.non-summary-rules"] = sum(len(v) for v in ref["non_summary"].values())
        c["universe.std.members"] = len(self.std)
        for kind in ("attribute", "auto-trait", "keyword", "lang", "macro", "primitive"):
            c[f"universe.std.members.{kind}"] = sum(1 for m in self.std if m.startswith(kind + ":"))
        c["universe.std-docs.sections"] = len(self.std_docs)
        c["universe.std-docs.files"] = len({f for f, _, _ in self.std_docs.values()})
        c["universe.design.parts"], c["universe.formality.judgments"] = len(self.parts), len(self.judgments)
        owned_fls = set(self.owner["fls"])
        c["unmapped.fls.paragraphs"] = len(set(fls["members"]) - owned_fls)
        c["unmapped.fls.sections"] = len(set(fls["member_sections"]) - set(self.owner["section"]))
        c["unmapped.reference.rules"] = len(set(ref["members"]) - set(self.owner["reference"]))
        c["unmapped.std.members"] = len(set(self.std) - set(self.owner["std"]))
        c["unmapped.std-docs.sections"] = len(set(self.std_docs) - set(self.owner["std"]))
        c["unmapped.design.parts"] = sum(1 for p in self.parts if not self.part_rows.get(p))
        cited = {(span(i["ref"]) or (0, 0, 0))[1:3] for r in rows.values() for i in r.get("formality", []) if isinstance(i, dict) and "ref" in i}
        c["unmapped.formality.judgments"] = sum(1 for k in self.judgments if k not in cited)
        c["rows"] = len(rows)
        for label in LABELS:
            c[f"rows.{label}"] = sum(1 for r in rows.values() if r.get("label") == label)
        c["rows.documented.rank-2-only"] = sum(1 for s in self.row_sources.values() if s["label"] == "documented" and s["rank2"] and not s["rank1"])
        c["rows.with-search"] = sum(1 for r in rows.values() if r.get("search"))
        c["rows.with-conflicts"] = len({rid for _, rid, _, _ in self.conflicts})
        for kind in CONFLICT_SIDES:
            c[f"conflicts.{kind}"] = sum(1 for k, _, _, _ in self.conflicts if k == kind)
        st_members = sum(1 for s in ("fls", "reference", "std") for o in self.owner[s].values() if str(rows[o].get("component")).startswith("St."))
        c["members.st"] = st_members
        c["members.outside-st"] = sum(len(self.owner[s]) for s in ("fls", "reference", "std")) - st_members
        c["outside-st.dispositioned"] = len(self.outside)
        for source in ("fls", "reference", "std"):
            c[f"outside-st.dispositioned.{source}"] = sum(1 for s, _ in self.outside if s == source)
        c["outside-st.fls.runtime-rubric-members"] = self.runtime_members
        c["outside-st.twin-required"] = len(self.twin_required)
        c["twins.groups"], c["twins.groups.one-sided"] = len(self.t["twin"]), self.one_sided
        c["undispositioned.outside-st"] = len(self.undispositioned)
        for kind in DISPOSITION_KINDS:
            c[f"outside-st.kind.{kind}"] = sum(1 for k, v in self.kind_of.items() if v == kind)
        c["rustc-error-tests.citing-outside-st-reference-rules"] = self.error_citations
        c["grammar.side-conditions"] = len(self.side_conditions)
        c["grammar.candidates"], c["grammar.candidates.grammar-marker"] = len(self.candidates), len(self.markers)
        c["grammar.candidates.cited"] = len(self.cited_side)
        c["grammar.candidates.dismissed"] = sum(self.dismissal_kinds.values())
        c["undispositioned.side-condition-candidates"] = len(self.undispositioned_side)
        for kind in DISMISSAL_KINDS:
            c[f"grammar.candidates.dismissed.{kind}"] = self.dismissal_kinds[kind]
        c["formality.notes"] = len(self.notes)
        c["formality.notes.tests"] = sum(1 for f, _ in self.notes if f.startswith("tests/"))
        for kind in NOTE_KINDS:
            c[f"formality.notes.kind.{kind}"] = self.note_kinds[kind]
        c["rfcs.registered"] = len(self.t["rfc"])
        for status in RFC_STATUSES:
            c[f"rfcs.{status}"] = sum(1 for e in self.t["rfc"].values() if e.get("status") == status)
        for schema, key in ((DECISION_SNAPSHOT, "decisions"), (PIN_DERIVATION, "pin-derivations")):
            c[f"snapshots.{key}"] = sum(1 for s in self.snapshots.values() if s.get("schema") == schema)
        c["snapshots.decision-index.queries"] = sum(len(s.get("queries", [])) for s in self.snapshots.values() if s.get("schema") == DECISION_INDEX)
        c["ui-tests.bound-to-rows"] = len(self.bound_tests)
        c["post-alignment.fls.added"], c["post-alignment.fls.removed"] = len(self.delta["added"]), len(self.delta["removed"])
        c["post-alignment.fls.changed"], c["post-alignment.a-mir-formality.lines"] = len(self.delta["changed"]), len(self.delta["formality"])
        grades = self.grades()
        for grade in ("rank-1", "rank-1 (gap)", "rank-2-only", "de-facto-only", "compat-candidate-only"):
            c[f"design.parts.{grade.replace(' (gap)', '-gap')}"] = sum(1 for g in grades.values() if g.split(" + ")[0] == grade)
        c["design.parts.with-compat-candidate-rows"] = sum(1 for g in grades.values() if "compat-candidate" in g)
        c["design.parts.with-de-facto-rows"] = sum(1 for g in grades.values() if "de-facto" in g)
        return c

    def grades(self) -> dict:
        out = {}
        for part in self.parts:
            sources = [self.row_sources[r] for r in self.part_rows.get(part, []) if r in self.row_sources]
            documented = [s for s in sources if s["label"] == "documented"]
            labels = {s["label"] for s in sources}
            rank2 = any(s["rank2"] for s in documented)
            grade = "rank-1" if any(s["rank1"] and part not in s["gaps"] for s in documented) else \
                "rank-1 (gap)" + (" + rank-2" if rank2 else "") if any(s["rank1"] for s in documented) else \
                "rank-2-only" if rank2 else "de-facto-only" if "de-facto" in labels else \
                "compat-candidate-only" if "compat-candidate" in labels else "unmapped"
            out[part] = grade + "".join(f" + {lab}" for lab in ("compat-candidate", "de-facto") if lab in labels and not grade.startswith(lab))
        return out

    def render(self, counts: dict) -> dict:
        b, rows = {}, self.t["row"]
        declared = collections.defaultdict(list)
        for key, entry in self.t["count"].items():
            if key not in counts or entry.get("block") not in ("universe", "rows", "dispositions", "pin-delta") or not entry.get("label"):
                self.add("DOC", f"count {key}: a published count names a computed key, a block (universe, rows, dispositions, pin-delta) and a label")
            else:
                declared[entry["block"]].append((entry["label"], counts[key]))
        for key in sorted(set(counts) - set(self.t["count"])):
            self.add("DOC", f"the computed count {key} = {counts[key]} has no [[count]] row")
        for name in ("universe", "rows", "dispositions", "pin-delta"):
            b[name] = "\n".join(["| Count | Value |", "|---|---:|"] + [f"| {label} | {value} |" for label, value in declared[name]])
        b["pin-delta"] += "\n\n" + "\n".join(
            f"* `{key}` {owner}: {', '.join(sorted(pid for pid, o in self.delta[key].items() if o == owner))}"
            for key in ("added", "removed", "changed") for owner in sorted(set(map(str, self.delta[key].values())))
        )
        b["pins"] = "\n".join(["| Source | Revision | Read |", "|---|---|---|"] + [
            f"| {name} | `{s.revision}` | {s.read} |" for name, s in sorted(self.pins.sources.items()) if name in READS
        ] + [f"| rust-lang/rust (standard library) | `{self.pins.alignment}` | objects |"])
        for key, title, index in (("by-component", "Component", "component"), ("by-area", "Area", "area")):
            tally = collections.defaultdict(lambda: [0, 0])
            for rid, row in rows.items():
                tally[row.get(index)][0] += 1
                tally[row.get(index)][1] += sum(len(row.get(k, [])) for k in ("fls", "reference", "std"))
            order = [x for x in COMPONENTS if x in tally] if index == "component" else sorted(tally, key=lambda a: (-tally[a][1], -tally[a][0], str(a)))
            b[key] = "\n".join([f"| {title} | Rows | Members |", "|---|---:|---:|"] + [f"| `{x}` | {tally[x][0]} | {tally[x][1]} |" for x in order])
        grades = self.grades()
        b["design-parts"] = "\n".join(["| Design part (verbatim) | Grade | Rows |", "|---|---|---|"] + [
            f"| {p[1]} | {grades[p]} | {', '.join(sorted(self.part_rows.get(p, [])))} |" for p in self.parts])
        b["labels"] = "\n".join([f"* `{label}`: {', '.join(sorted(r for r, row in rows.items() if row.get('label') == label)) or '(none)'}"
                                 for label in LABELS[1:]] + [
            f"* `{kind}`: {', '.join(sorted({rid for k, rid, _, _ in self.conflicts if k == kind})) or '(none)'}" for kind in CONFLICT_SIDES])
        b["side-conditions"] = "\n".join(f"{i}. {name}" for i, name in enumerate(self.side_conditions, 1))
        b["rfcs"] = "\n".join(["| RFC | File | Status |", "|---|---|---|"] + [
            f"| {e.get('number')} | `{e.get('file')}` | {e.get('status')} |" for e in self.t["rfc"].values()])
        b["decisions"] = "\n".join(["| Decision | Title | Teams | Merged or closed | Cited by |", "|---|---|---|---|---|"] + [
            f"| {s.get('repo')}#{s.get('number')} | {str(s.get('title')).replace('|', '/')} | {', '.join(l for l in s.get('labels', []) if l.startswith('T-'))} | "
            f"{str(s.get('merged_at') or s.get('closed_at'))[:10]} | {', '.join(sorted(self.decision_rows.get(rel, [])))} |"
            for rel, s in sorted(self.snapshots.items()) if s.get("schema") == DECISION_SNAPSHOT])
        b["searches"] = "\n".join(["| Row | Label | Verdicts by corpus |", "|---|---|---|"] + [
            f"| {rid} | {row.get('label')} | " + "; ".join(
                f"{s.get('corpus')}: " + ", ".join(f"{v} {n}" for v, n in sorted(collections.Counter(
                    [a.get("verdict") for a in s.get("addresses", []) + s.get("mentions", []) + s.get("dispositions", [])]
                    + ["silent"] * len(s.get("silent", []))).items())) for s in row.get("search", [])) + " |"
            for rid, row in rows.items() if row.get("search")])
        out = []
        for kind in CONFLICT_SIDES:
            entries = [(rid, c) for k, rid, c, _ in self.conflicts if k == kind]
            out += [f"**`{kind}`** ({len(entries)})", ""]
            for rid, conflict in entries:
                extra = f" ({OUTCOME_KEYS[kind]} **{conflict.get(OUTCOME_KEYS[kind])}**)" if kind in OUTCOME_KEYS else \
                    f" (parts: {', '.join(p.get('phrase', '') for p in conflict.get('parts') or []) or 'none'})" if kind == "document-gap" else ""
                out.append(f"* {rid}{extra}: {C.collapse(str(conflict.get('summary', '')))}")
                for e in conflict.get("evidence", []):
                    where = f"`snapshot:{e.get('snapshot')}` {e.get('part')}" if e.get("side") == "decision" else f"`{e.get('ref')}`"
                    tail = ", ".join(x for x in (f"expect {e['expect']}" if e.get("expect") else "", f"revision `{e['revision']}`" if e.get("revision") else "") if x)
                    out.append(f"  * {e.get('side')}{f' ({tail})' if tail else ''}: \"{C.collapse(str(e.get('quote', '')))}\" ({where})")
            out.append("")
        b["conflicts"] = "\n".join(out).rstrip()
        return b

    # ---- document and judgments
    def document(self, blocks: dict) -> dict:
        path = self.o.doc or self.o.repo / DOC_REL
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            self.add("DOC", f"{path}: {error}")
            return {}
        names = tuple(f"ssm-{name}" for name in BLOCKS)
        for name in BLOCKS:
            C.check_block(self.f, "DOC", text, f"ssm-{name}", blocks[name])
        sections = C.document_judgments(self.f, "DOC", text, generated=names)
        self.counts["doc_citations"] = sum(C.check_prose(self.f, "DOC", jid, body if isinstance(body, str) else "\n".join(body), self.resolver)
                                           for jid, body in sections.items())
        return sections


def pins_entry(pins_text: str) -> dict:
    """The [sources.rfcs] entry this map added to EXTERNAL_PINS.toml (its rank, rule and reading), with the
    comments inside it: a judgment, although the checker re-derives the revision."""
    lines = pins_text.split("\n")
    start = next((i for i, line in enumerate(lines) if line.strip() == "[sources.rfcs]"), len(lines))
    end = next((i for i in range(start + 1, len(lines)) if lines[i].startswith("[")), len(lines))
    return {"entry": ((tomllib.loads(pins_text).get("sources") or {}).get("rfcs")), "comments": C.toml_comments("\n".join(lines[start:end]))}


def judgments(findings: C.Findings, ledger_text: str, document: dict, pins_text: str | None = None) -> dict:
    """Every reviewed judgment: each ledger row (`kind:key`), each [selection.*] table, the ledger's
    comments, the rfcs entry of EXTERNAL_PINS.toml, and the document's prose sections and outline."""
    data = tomllib.loads(ledger_text)
    rows = [(f"{kind}:{row.get(key)}", row) for kind, (key, _) in TABLES.items() for row in data.get(kind, []) if isinstance(row, dict)]
    selections = [(f"selection:{name}", body) for name, body in (data.get("selection") or {}).items()]
    pins = pins_entry(pins_text if pins_text is not None else (REPO_ROOT / C.PINS_REL).read_text(encoding="utf-8"))
    return C.merge_judgments(findings, rows + selections + [("comments:ledger", C.toml_comments(ledger_text)), ("pins:rfcs", pins)]
                             + list(document.items()))


def collect(options: Options | None = None) -> Result:
    options = options or Options()
    checker = Checker(options)
    result = Result(violations=checker.f.violations, counts=checker.counts)
    if not checker.load():
        return result
    checker.universes()
    checker.tables()
    checker.load_snapshots()
    checker.registered()
    checker.rows()
    checker.dispositions()
    checker.pin_delta()
    checker.uses()
    counts = checker.measure()
    for pid in sorted(set(checker.fls["members"]) - set(checker.owner["fls"])):
        checker.add("UNIVERSE", f"unmapped FLS paragraph {pid} (section {checker.fls['members'][pid][0]})")
    for sid in sorted(set(checker.fls["member_sections"]) - set(checker.owner["section"])):
        checker.add("UNIVERSE", f"unmapped FLS section {sid}")
    for rid in sorted(set(checker.ref["members"]) - set(checker.owner["reference"])):
        checker.add("UNIVERSE", f"unmapped Reference rule {rid} ({checker.ref['members'][rid][0]})")
    for mid in sorted((set(checker.std) | set(checker.std_docs)) - set(checker.owner["std"])):
        checker.add("UNIVERSE", f"unmapped standard-library member {mid}")
    for part in checker.parts:
        if not checker.part_rows.get(part):
            checker.add("UNIVERSE", f"unmapped design part {part}")
    cited = {(span(i["ref"]) or (0, 0, 0))[1:3] for r in checker.t["row"].values() for i in r.get("formality", []) if isinstance(i, dict) and "ref" in i}
    for key in sorted(k for k in checker.judgments if k not in cited):
        checker.add("UNIVERSE", f"unmapped a-mir-formality judgment {checker.judgments[key]} ({key[0]}:{key[1]})")
    checker.counts.update(counts)
    result.blocks = checker.render(counts)
    sections = checker.document(result.blocks)
    checker.counts["reviews"] = C.check_reviews(
        checker.f, options.registry or options.repo / REGISTRY_REL, DELIVERABLE,
        judgments(checker.f, checker.ledger_text, sections, (options.pins or options.repo / C.PINS_REL).read_text(encoding="utf-8")),
        JUDGMENT_KINDS, options.repo if options.check_history else None, REGISTRY_REL)
    return result


def main(argv: list | None = None) -> int:
    if tomllib is None:
        print("static_semantics_source_map: Python 3.11+ (tomllib) is required", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", type=Path, default=REPO_ROOT)
    for name in ("ledger", "doc", "registry", "fls", "reference", "formality", "rfcs", "rust"):
        parser.add_argument(f"--{name}", type=Path)
    parser.add_argument("--write-blocks", action="store_true", help="rewrite the document's generated blocks")
    args = parser.parse_args(argv)
    options = Options(repo=args.repo, ledger=args.ledger, doc=args.doc, registry=args.registry,
                      clones={"fls": args.fls, "rust-reference": args.reference, "a-mir-formality": args.formality,
                              "rfcs": args.rfcs, "rust": args.rust})
    try:
        result = collect(options)
    except (C.MissingClone, C.PinsError) as error:
        print(f"static_semantics_source_map: {error}", file=sys.stderr)
        return 2
    if args.write_blocks and result.blocks:
        doc = args.doc or args.repo / DOC_REL
        text = doc.read_text(encoding="utf-8")
        for name, body in result.blocks.items():
            text = C.replace_block(text, f"ssm-{name}", body)
        doc.write_text(text, encoding="utf-8")
    for key, value in result.counts.items():
        if key != "reviews":
            print(f"{key} = {value}")
    if result.violations:
        print(f"\nstatic_semantics_source_map: {len(result.violations)} violation(s)", file=sys.stderr)
        for violation in result.violations:
            print(f"  {violation}", file=sys.stderr)
        return 1
    print(f"\nstatic_semantics_source_map: OK ({result.counts.get('doc_citations', 0)} document citations, "
          f"{result.counts['reviews']['judgments']} reviewed judgments)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
