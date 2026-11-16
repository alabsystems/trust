#!/usr/bin/env python3
"""D0.1 checker: the Trust Language Decisions ledger (LD-1..LD-13) and I-PRECEDENCE.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §3.1 D-1 (the source
precedence rule, the LD table and the I-PRECEDENCE invariant: "a ledger schema check in CI;
the published counts (V11)"), §5.1 item 3, §5.2 Stage 0.2 (D0.1, exit E0.8) and §8.3 OD-5.
Table: docs/trust-core/language-decisions.toml. Document: docs/trust-core/LANGUAGE_DECISIONS.md.
Review registry: docs/trust-core/reviews/language_decisions.toml.

The shared layers (pins, git objects, citation resolution, the Trust-marker guard, uniqueness,
generated blocks, reviewed judgments, snapshot immutability) are scripts/trust_core/common.py's.
This file holds the ledger's own rules; each EXITS NON-ZERO when it fails:

  PIN, TABLE     common: MiniRust, the Reference, the FLS and a-mir-formality at their pins,
                 rust-lang/rfcs as a full clone whose pin is re-derived, this repository's
                 alignment; row keys, no duplicate row, no repeated element, no empty list
                 outside MAY_BE_EMPTY.
  DESIGN         LD-1..LD-13 and the precedence rule appear once, in order, with the design's
                 LD table cells byte for byte and the status derived from the cell; the OD-5
                 flags and the ratification items are the OD-5 row's, which are E0.8's.
  SOURCE         every ranked row resolves (common.Resolver, a quote may omit one leading marker
                 per line, the line range is tight); its rank is its kind's; a rank-1 or rank-2
                 source lies in a declared corpus of its kind (no corpus holds rustc tests); a
                 Reference source is a rule, by rule id (the cited lines lie in the rule's text,
                 which ends at a heading and leaves out every untagged admonition, a blockquote
                 in either spelling, indented or not); an FLS source names its paragraph; an RFC
                 source names its [[rfc]] record and nearest heading; a std-doc source is
                 doc-comment prose, outside a code example, of a #[stable] item or module; a
                 pinning rustc test runs the program,
                 enables no feature and passes no -Z flag, and records its restrictions; a team
                 decision is a completed rfcbot FCP of the named team before the alignment, on a
                 record of the pinned decision index, quoting its proposer or a listed member,
                 written and last edited before completion and the alignment. No two rows of an
                 entry quote one text.
  PRECEDENCE     each aspect's label, resolution, conflicts, rustc divergences and compat
                 candidacy equal what the precedence predicates compute from its sources' ranks
                 and roles; the entry label is its most exceptional aspect label; the owner
                 questions each aspect's result demands are present and no others of those
                 kinds.
  SEARCH         every declared search scope ([[corpus]]) is re-run: each search's hit set and
                 matched lines equal the recorded ones; each matched line lies inside a cited
                 row of its file or in exactly one reason group; every aspect has a search of
                 every corpus. The hit set of a declared scope is mechanical; whether a scope or
                 pattern is wide enough is reviewed judgment.
  DECISIONS      each decision index snapshot has one snapshot of rfcbot's completion notices,
                 covering exactly its records; each record's completion status is computed from
                 them; every opsem record is dispositioned with that status; a record completed
                 after the alignment takes no citation and no reason, any other is cited or
                 gives a reason.
  RFC            an [[rfc]] record is named by a ranked rfc source, or it is stale; its file is
                 under text/ at the pin; its header citations name its RFC PR and tracking
                 issue, and its stabilization evidence resolves (a checked step in the tracking
                 issue snapshot, an accepted feature with the RFC's tracking issue, a #[stable]
                 attribute, or a tracking issue closed as completed).
  SNAPSHOT       common: each snapshot equals its sha256 pin and its first committed version;
                 its row matches its content; every issue snapshot is cited.
  DESIGN-EXIT    every design exit that names an entry is listed by it; every design line that
                 names an entry is covered by a verified design quote of the entry or the rule.
  OQ, RATIFY     owner question references resolve both ways; ratification items quote the OD-5
                 row; `state` follows the rulings; --require-ruled (E0.8's pass line) also fails
                 while a ruling is pending or a conflict or divergence remains.
  DEFERRED       deferred_check rows name real row fields and cite the exits they name: the facts
                 round 18's removed scanners established, recorded as reviewed judgments.
  PROSE          in row free text and document sections: every [ID] is a row id, a quoted fragment
                 is verified quote text (the text of the [ID] it is attributed to), every design
                 line token lies in a verified design quote, RFC, OQ, issue, rule and URL tokens
                 resolve; the document's `REF «quote»` citations resolve (common.check_prose).
  DOC            the generated blocks regenerate exactly; every other line is a reviewed prose
                 section or the outline.
  REVIEW         common.check_reviews over every row, the table's comments, every prose section
                 and the outline.

Usage:
    scripts/trust_core/language_decisions.py [--repo DIR] [--table FILE] [--doc FILE]
        [--registry FILE] [--require-ruled] [--write-blocks]

Exit codes: 0 every predicate holds; 1 a violation; 2 a clone is missing or the pins are unreadable.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common as C  # noqa: E402

tomllib = C.tomllib
REPO_ROOT = C.REPO_ROOT
TABLE_REL = "docs/trust-core/language-decisions.toml"
DOC_REL = "docs/trust-core/LANGUAGE_DECISIONS.md"
REGISTRY_REL = f"{C.REVIEWS_DIR}/language_decisions.toml"
DELIVERABLE = "language_decisions"
SCHEMA = "trust.core.language-decisions.v4"
SNAPSHOT_PREFIX = "docs/trust-core/snapshots/"
READS = {"rust-reference": "reference", "fls": "fls", "minirust": "minirust", "a-mir-formality": "a-mir-formality", "rfcs": "rfcs"}
BLOCKS = ("ld-counts", "ld-findings", "ld-snapshots", "ld-corpora", "ld-deferred", "ld-ratify", "ld-owner-questions",
          "ld-rule-quotes", "ld-rfcs", "ld-entries", "ld-decisions")

LD_IDS = tuple(f"LD-{n}" for n in range(1, 14))
RULE_ID = "I-PRECEDENCE"
ROLES = ("settles", "open", "contrary", "context", "pins")
LABELS = ("normative", "team-decision", "team-model", "de-facto", "de-facto-open", "trust-choice", "compat")  # least to most exceptional
V11 = ("de-facto", "de-facto-open")
RESOLUTIONS = ("settled", "choose", "filled", "unaddressed")
MODELLINGS = ("deterministic", "choose-demonic", "choose-angelic", "parameter")
RULINGS = ("pending", "ratified", "revised", "rejected")
OQ_KINDS = ("labels", "open-reading", "trust-choice", "precedence-conflict", "rustc-divergence", "source-rank", "gap", "search-scope")
COMPUTED_OQ_KINDS = ("open-reading", "trust-choice", "precedence-conflict", "rustc-divergence")
CITED_BY = ("core-definition", "compiler-fact", "checker", "stage", "ruling", "risk", "deliverable", "unknown", "unverified-claim", "review-disposition")
EFFECTS = ("confirms", "revises", "confirms-or-revises", "blocks")
TEAMS, DISPOSITIONS, RFCBOT = ("lang", "opsem", "types"), ("merge", "close"), ("rust-rfcbot", "rfcbot")
STABILIZATIONS = ("checked-step", "accepted-feature", "stable-item", "no-feature-gate")
FCP_STATUSES = ("before-pin", "after-pin", "no-notice")
STATE_DRAFT, STATE_RULED = "draft-for-OD-5", "ruled-for-OD-5"
# kind -> (rank, citation source, path prefix); team decisions are quoted from snapshots.
KINDS = {"reference": (1, "reference", "src/"), "fls": (1, "fls", "src/"), "rfc": (1, "rfcs", "text/"),
         "std-doc": (1, "rustc", "library/"), "team-decision": (2, None, None), "minirust": (2, "minirust", ""),
         "a-mir-formality": (2, "a-mir-formality", ""), "rustc-test": (3, "rustc", "tests/")}
RELATED = {**{k: v[1:] for k, v in KINDS.items() if v[1]}, "miri": ("rustc", "src/tools/miri/"),
           "rustc-source": ("rustc", "compiler/"), "library-source": ("rustc", "library/"), "design": ("design", None)}
SNAPSHOT_SCHEMAS = {1: "trust.core.web-snapshot.v1", 2: "trust.core.web-snapshot.v2"}
FCP_NOTICE = re.compile(r"^(?:The final comment period, with a disposition to \*\*(merge|close|postpone)\*\*, as per the "
                        r"\[review above\]\([^)\s]*\), is now \*\*complete\*\*\.|The final comment period is now complete\.)")
DECISION_LABEL = re.compile(r"^(?:T-|disposition-|finished-final-comment-period$|final-comment-period$)")
EXIT_DEF = re.compile(r"^(\s*)[*-] \*\*(E\d+(?:\.[0-9A-Za-z]+)+)\*\*")
LD_MENTION = re.compile(r"\bLD-(\d+)\b")
ADMONITION = re.compile(r"^\s*>\s*\[!")  # a line that opens a `> [!KIND]` admonition, even directly after another
ID_TOKEN = re.compile(r"\[((?:LD-\d+|I-PRECEDENCE)\.[A-Z]+\d+)\]")
SQUOTE = re.compile(r"(?:(?<=^)|(?<=[\s(]))'([^']+?)'(?=[\s.,;:)]|$)|\"([^\"]+)\"|“([^”]+)”")
DESIGN_TOKEN = re.compile(r"\bdesign:(\d+)(?:-(\d+))?\b")
ISSUE_TOKEN = re.compile(r"(?<![\w/.-])([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)#(\d+)\b|(?<![\w/#&.-])#(\d+)\b")
RFC_TOKEN = re.compile(r"\bRFC (\d{3,4})\b")
OQ_TOKEN = re.compile(r"\bOQ-\d+\b")
RULE_TOKEN = re.compile(r"(?<![\w-])r\[([A-Za-z0-9_.-]+)\]")
URL_TOKEN = re.compile(r"https?://[^\s)\]>'\"`»]+")
LINE_TOKEN = re.compile(r"[\w./-]+\.(?:md|rs|rst|toml|py|stderr|json):[0-9]+|\blines?\s+[0-9]+")
PROSE_KEYS = ("why", "note", "cost", "reason", "question", "consequence", "options", "summary", "recommendation",
              "strongest_argument_against", "decision_summary", "decides", "why_unranked", "claim", "replaces", "title")

# kind -> (allowed keys, required keys, key of a row). Every row is a judgment `kind:key`.
ENTRY_CHILDREN = ("aspect", "source", "related", "alternative", "exit", "cited_by", "search")
ROWS = {
    "corpus": ({"name", "source", "include", "lines", "kinds", "why", "cites"}, {"name", "source", "include", "lines", "kinds", "why"}),
    "snapshot": ({"file", "kind", "issue", "comments", "issue_body", "schema", "queries", "index", "retrieved", "sha256"}, {"file", "kind", "retrieved", "sha256"}),
    "rfc": ({"number", "file", "pr", "tracking_issue", "tracking", "tracking_snapshot", "stabilization", "evidence", "note"},
            {"number", "file", "pr", "tracking_issue", "tracking", "stabilization"}),
    "rule_quote": ({"id", "ref", "quote"}, {"id", "ref", "quote"}),
    "owner_question": ({"id", "kind", "title", "question", "options", "consequence", "evidence"}, {"id", "kind", "title", "question", "options", "consequence", "evidence"}),
    "ratify": ({"item", "blocks", "summary", "recommendation_quote", "recommendation", "strongest_argument_against", "evidence", "owner_questions", "ruling", "ruling_record"},
               {"item", "blocks", "summary", "recommendation_quote", "recommendation", "strongest_argument_against", "evidence", "ruling"}),
    "deferred_check": ({"id", "claim", "fields", "replaces", "checked_by", "cites"}, {"id", "claim", "fields", "replaces", "checked_by", "cites"}),
    "entry": ({"id", "title", "design_line", "design_recommendation", "design_status_cell", "status", "od5", "label", "question",
               "decision_summary", "owner_questions", *ENTRY_CHILDREN},
              {"id", "title", "design_line", "design_recommendation", "design_status_cell", "status", "od5", "label", "question",
               "decision_summary", "aspect", "source", "alternative", "exit", "cited_by", "search"}),
    "aspect": ({"id", "decides", "modelling", "label", "resolution", "conflicts", "divergences", "compat_candidate", "owner_questions",
                "note", "open_text", "upstream"}, {"id", "decides", "modelling", "label", "resolution"}),
    "source": ({"id", "aspects", "role", "roles", "kind", "rank", "ref", "rule", "paragraph", "rfc", "section", "restrictions", "team", "url",
                "snapshot", "disposition", "fcp_proposal", "fcp_complete", "quote", "note", "open_by"}, {"id", "aspects", "kind", "rank", "quote"}),
    "related": ({"id", "kind", "ref", "rule", "quote", "why_unranked"}, {"id", "kind", "ref", "quote", "why_unranked"}),
    "alternative": ({"name", "cost", "evidence", "design_quote"}, {"name", "cost"}),
    "exit": ({"id", "effect", "ref", "quote", "note"}, {"id", "effect", "ref", "quote"}),
    "cited_by": ({"what", "name", "ref", "quote"}, {"what", "name", "ref", "quote"}),
    "search": ({"id", "corpus", "pattern", "aspects", "hit"}, {"id", "corpus", "pattern", "aspects"}),
    "hit": ({"at", "lines", "use", "uncited", "fcp", "reason"}, {"at"}),
    "decision": ({"at", "fcp", "use", "reason"}, {"at", "fcp"}),
}
MAY_BE_EMPTY = {"conflicts", "divergences", "owner_questions", "use", "uncited", "restrictions", "comments", "include"}
TOP_KEYS = {"schema", "state", "precedence_rule", *[k for k in ROWS if k not in ("aspect", "source", "related", "alternative", "exit", "cited_by", "search", "hit")]}
JUDGMENT_KINDS = set(ROWS) | {"precedence_rule", "comments", "prose", "outline"}


@dataclass
class Result:
    violations: list = field(default_factory=list)
    counts: dict = field(default_factory=dict)
    blocks: dict = field(default_factory=dict)


@dataclass
class Options:
    repo: Path = REPO_ROOT
    table: Path | None = None
    doc: Path | None = None
    registry: Path | None = None
    clones: dict = field(default_factory=dict)
    trees: dict = field(default_factory=dict)  # citation source -> tree ("design" too); mutation tests only
    snapshot_root: Path | None = None  # where snapshot bytes are read; mutation tests only
    check_pin_state: bool = True
    check_history: bool = True
    require_ruled: bool = False


def rows_of(data: dict) -> list[tuple[str, str, dict, str]]:
    """(kind, key, row, owning entry) for every row of the table, nested rows included."""
    out = []
    for kind, keyf in (("corpus", "name"), ("snapshot", "file"), ("rfc", "number"), ("rule_quote", "id"), ("owner_question", "id"),
                       ("ratify", "item"), ("deferred_check", "id"), ("decision", "at")):
        out += [(kind, str(r.get(keyf)), r, "") for r in data.get(kind, []) if isinstance(r, dict)]
    for e in data.get("entry", []):
        if not isinstance(e, dict):
            continue
        lid = str(e.get("id"))
        out.append(("entry", lid, e, lid))
        for kind, keyf in (("aspect", "id"), ("source", "id"), ("related", "id"), ("alternative", "name"), ("exit", "id"), ("cited_by", "name"), ("search", "id")):
            for r in e.get(kind, []) if isinstance(e.get(kind), list) else []:
                if isinstance(r, dict):
                    key = str(r.get(keyf)) if kind in ("source", "related", "search") else f"{lid}/{r.get(keyf)}"
                    out.append((kind, key, r, lid))
                    if kind == "search":
                        out += [("hit", f"{r.get('id')}/{h.get('at')}", h, lid) for h in r.get("hit", []) if isinstance(h, dict)]
    return out


def judgment_content(kind: str, row: dict) -> dict:
    children = ENTRY_CHILDREN if kind == "entry" else ("hit",) if kind == "search" else ()
    return {k: v for k, v in row.items() if k not in children}


def import_regions(text: str) -> list[tuple[int, int, str]]:
    """Complete top-level mod/use items, including their attributes.

    The shared Rust lexer keeps braces or keywords in strings, comments and
    nested macro/function bodies from being mistaken for an import boundary.
    """
    from mir_constructor_table import LexError, lex

    tokens = [t for t in lex(text) if t.kind not in ("comment", "doc")]
    lines = text.splitlines(keepends=True)
    regions = []
    stack = []
    start = 0

    def kind(stop: int) -> str | None:
        depth = []
        for token in tokens[start:stop + 1]:
            if not depth and token.kind == "ident" and token.text != "pub":
                return token.text if token.text in ("mod", "use") else None
            if token.text in ("(", "[", "{"):
                depth.append(token.text)
            elif token.text in (")", "]", "}") and depth:
                depth.pop()
        return None

    for i, token in enumerate(tokens):
        word = token.text
        if word in ("(", "[", "{"):
            stack.append(word)
        elif word in (")", "]", "}"):
            if not stack or stack.pop() != {")": "(", "]": "[", "}": "{"}[word]:
                raise LexError("unbalanced import boundary")
        if stack:
            continue
        # A crate attribute is not an attribute of the next declaration.
        if word == "]" and [t.text for t in tokens[start:start + 3]] == ["#", "!", "["]:
            start = i + 1
            continue
        item_kind = kind(i)
        if word == ";" or (word == "}" and item_kind != "use"):
            if item_kind is not None:
                first, last = tokens[start].line, token.end_line
                regions.append((first, last, "".join(lines[first - 1:last])))
            start = i + 1
    if stack:
        raise LexError("unfinished import boundary")
    return regions


def identical_import_region(current: str, upstream: str, first: int, last: int) -> tuple[int, int] | None:
    """Authorize only one complete import whose actual bytes equal upstream."""
    original = import_regions(upstream)
    for a, b, text in import_regions(current):
        if a <= first <= last <= b and sum(other == text for _, _, other in original) == 1:
            return a, b
    return None


def judgments(findings: C.Findings, table_text: str, document: dict) -> dict:
    data = tomllib.loads(table_text)
    pairs = [(f"{kind}:{key}", judgment_content(kind, row)) for kind, key, row, _ in rows_of(data)]
    if isinstance(data.get("precedence_rule"), dict):
        pairs.append((f"precedence_rule:{data['precedence_rule'].get('id')}", data["precedence_rule"]))
    return C.merge_judgments(findings, pairs + [("comments:table", C.toml_comments(table_text))] + list(document.items()))


def source_role(source: dict, aspect: str) -> str | None:
    if aspect not in source.get("aspects", []):
        return None
    return source["roles"].get(aspect) if isinstance(source.get("roles"), dict) else source.get("role")


def compute_aspect(aspect: dict, sources: list[dict]) -> dict:
    """The precedence predicates (design D-1 rules 1-4) over one aspect's sources."""
    aid = aspect.get("id")
    srcs = [(s, source_role(s, aid)) for s in sources if aid in s.get("aspects", [])]
    r12 = [s for s, _ in srcs if s.get("rank") in (1, 2)]
    settles = [s for s, r in srcs if r in ("settles", "pins")]
    min_settle = min((s["rank"] for s in settles if isinstance(s.get("rank"), int)), default=None)
    unsuperseded = [s for s, r in srcs if r == "open" and s.get("rank") in (1, 2) and not (min_settle is not None and min_settle < s["rank"])]
    compat = aspect.get("label") == "compat"
    if compat:
        label = "compat"
    elif not r12:
        label = "de-facto"
    elif any(s.get("rank") == 1 for s in settles):
        label = "normative"
    elif any(s.get("rank") == 2 and s.get("kind") == "team-decision" for s in settles):
        label = "team-decision"
    elif any(s.get("rank") == 2 for s in settles):
        label = "team-model"
    elif any(s.get("rank") == 3 for s in settles):
        label = "de-facto-open"
    else:
        label = "trust-choice"
    if aspect.get("modelling", "deterministic") != "deterministic":
        resolution = "choose"
    elif unsuperseded:
        resolution = "filled" if settles else "unaddressed"
    else:
        resolution = "settled" if settles else "unaddressed"
    by_id = {s.get("id"): s for s in sources}
    conflicts, neutralized, divergences = [], [], []
    for c, r in srcs:
        if r != "contrary":
            continue
        if c.get("kind") == "rustc-test":
            divergences.append(c["id"])
        elif (min_settle is not None and isinstance(c.get("rank"), int) and min_settle < c["rank"]) or (compat and c.get("rank") == 1):
            continue
        elif c.get("open_by") in by_id and same_locator_open(c, by_id[c["open_by"]], aid):
            neutralized.append(c["id"])
        else:
            conflicts.append(c["id"])
    candidate = not compat and any(s.get("rank") == 1 and r == "contrary" for s, r in srcs) and \
        any(s.get("kind") == "rustc-test" and r in ("pins", "settles") for s, r in srcs)
    need = {k for k, cond in (("precedence-conflict", conflicts), ("rustc-divergence", divergences),
                              ("open-reading", (resolution in ("filled", "unaddressed") and unsuperseded) or neutralized),
                              ("trust-choice", label == "trust-choice")) if cond}
    return {"label": label, "resolution": resolution, "conflicts": sorted(conflicts), "neutralized": sorted(neutralized),
            "divergences": sorted(divergences), "compat_candidate": candidate, "required_oq_kinds": sorted(need)}


def same_locator_open(contrary: dict, opener: dict, aspect: str) -> bool:
    return source_role(opener, aspect) == "open" and all(opener.get(k) == contrary.get(k) for k in ("rank", "kind", "rule", "paragraph", "url")) \
        and str(opener.get("ref", "")).rsplit(":", 1)[0] == str(contrary.get("ref", "")).rsplit(":", 1)[0]


def md(text: str) -> str:
    return " ".join(str(text).split()).replace("|", "\\|")


def lines_text(lines: list) -> str:
    return f"line{'s' if len(lines) != 1 else ''} {', '.join(map(str, lines))}"


def headings(lines: list[str]) -> dict[int, str]:
    """line -> text of each markdown heading outside a code fence."""
    out, fence = {}, False
    for i, line in enumerate(lines, 1):
        if line.strip().startswith(("```", "~~~")):
            fence = not fence
        elif not fence and re.match(r"^#{1,6}(\s|$)", line):
            out[i] = re.sub(r"^#+\s*", "", line.strip())
    return out


def std_doc_problem(lines: list[str], a: int, b: int) -> str | None:
    """None when lines a..b are doc-comment prose, outside a code example, of a #[stable] item or module."""
    marker = None
    for n in range(a, b + 1):
        this = next((m for m in ("//!", "///") if lines[n - 1].strip().startswith(m)), None)
        if this is None or marker not in (None, this):
            return f"line {n} is not doc-comment prose of one item or module"
        marker = this
    start, fence = a, False
    while start > 1 and lines[start - 2].strip().startswith(marker):
        start -= 1
    for n in range(start, b + 1):
        if lines[n - 1].strip()[3:].strip().startswith("```"):
            fence = not fence
            if n >= a:
                return f"line {n} is a code fence of a doc comment"
        elif fence and n >= a:
            return f"line {n} is inside a doc-comment code example"
    if marker == "//!":
        inner = [line.strip() for line in lines if line.strip().startswith("#![")]
        return None if any(x.startswith("#![stable(") for x in inner) and not any(x.startswith("#![unstable(") for x in inner) \
            else "the module these //! lines document is not #![stable]"
    while start > 1 and lines[start - 2].strip().startswith(("//", "#[")):
        start -= 1
    attrs, depth, current = [], 0, ""
    for n in range(start, len(lines) + 1):
        s = lines[n - 1].strip()
        if depth == 0 and s.startswith("//") and not s.startswith("//!"):
            continue
        if depth == 0 and not s.startswith("#["):
            break
        current, depth = current + " " + s, depth + s.count("[") - s.count("]")
        if depth <= 0:
            attrs, current, depth = attrs + [current.strip()], "", 0
    if any(x.startswith("#[unstable(") for x in attrs) or not any(x.startswith("#[stable(") for x in attrs):
        return "the documented item carries no #[stable] attribute, or an #[unstable] one"
    return None


class Checker:
    def __init__(self, options: Options) -> None:
        self.o, self.f = options, C.Findings()
        self.counts: dict = {}
        self.design_ranges: dict[str, list] = {}  # owner (an LD id or "*") -> verified design line ranges
        self.quotes: dict[str, str] = {}  # row id -> collapsed quote
        self.verified_quotes: list[str] = []
        self.verified_issues: set[str] = set()
        self.verified_urls: set[str] = set()
        self.cited = 0

    def add(self, kind: str, message: str) -> None:
        self.f.add(kind, message)

    def ok(self, row: dict, kind: str) -> list:
        """A row's well-formed child rows of one kind."""
        return [r for r in row.get(kind, []) if id(r) in self.valid]

    # ---- inputs
    def load(self) -> bool:
        o = self.o
        self.pins = C.load_pins(o.repo / C.PINS_REL)
        trees = {"worktree": C.GitTree(o.repo, "HEAD")}
        missing = [name for name, source in READS.items() if source not in o.trees]
        clones = C.locate_clones(self.pins, missing, o.clones) if missing else {}
        for name, path in clones.items():
            trees[READS[name]] = C.GitTree(path, self.pins.sources[name].revision)
        rust = C.Source("rust", "https://github.com/rust-lang/rust", self.pins.alignment,
                        self.pins.alignment_date, "objects")
        if "upstream" not in o.trees:
            path = Path(o.clones.get("rust") or C.sources_root() / "rust")
            if not (path / ".git").exists():
                raise C.MissingClone(f"the rust clone is missing at {path}; create it with {C.FETCH_COMMAND}")
            clones["rust"] = path
            trees["upstream"] = C.GitTree(path, rust.revision)
        trees.update(o.trees)
        self.trees, self.resolver = trees, C.Resolver(o.repo, trees)
        if o.check_pin_state:
            for name, path in clones.items():
                C.verify_clone(self.f, path, rust if name == "rust" else self.pins.sources[name], self.pins)
            C.verify_objects(self.f, f"repository {o.repo}", o.repo)
            C.verify_alignment(self.f, trees["worktree"], self.pins)
        try:
            self.table_text = (o.table or o.repo / TABLE_REL).read_text(encoding="utf-8")
            self.data = tomllib.loads(self.table_text)
        except (OSError, tomllib.TOMLDecodeError) as error:
            self.add("TABLE", f"{o.table or TABLE_REL}: {error}")
            return False
        self.design = (trees.get("design") or trees["worktree"]).lines(C.DESIGN_REL) or []
        return True

    def cite(self, kind: str, where: str, ref: object, quote: object, owner: str = "", strip: bool = True) -> dict | None:
        """Resolve a citation at its pin, and refuse a line range wider than its quote."""
        self.cited += 1
        parts = C.parse_ref(ref)
        if not self.resolver.resolve(self.f, kind, where, str(ref), quote, strip=strip):
            return None
        if parts["start"] is not None and parts["end"] > parts["start"]:
            base, (a, b) = str(ref).rsplit(":", 1)[0], (parts["start"], parts["end"])
            for x, y in ((a + 1, b), (a, b - 1)):
                sub = f"{base}:{x}" + (f"-{y}" if y > x else "")
                if self.resolver.check(sub, quote, strip=strip) is None:
                    self.add(kind, f"{where}: {ref} is wider than its quote, which {sub} already holds")
                    return None
        if parts["source"] == "design":
            self.design_ranges.setdefault(owner or "*", []).append((parts["start"], parts["end"]))
        self.verified_quotes.append(C.collapse(str(quote)))
        return parts

    # ---- TABLE
    def rows(self) -> None:
        d = self.data
        for key in sorted(set(d) - TOP_KEYS):
            self.add("TABLE", f"top-level key {key!r} is not part of the schema")
        if d.get("schema") != SCHEMA:
            self.add("TABLE", f"schema is not {SCHEMA}")
        self.t: dict[str, dict] = {k: {} for k in ROWS}
        self.valid: set[int] = set()  # the rows whose keys are well-formed; only they are read further
        for kind, key, row, _ in rows_of(d):
            allowed, required = ROWS[kind]
            where = f"{kind} {key}"
            if kind == "source":
                required = required | ({"team", "url", "snapshot", "disposition", "fcp_proposal", "fcp_complete"} if row.get("kind") == "team-decision" else {"ref"})
            if set(row) - allowed or required - set(row):
                self.add("TABLE", f"{where}: unknown keys {sorted(set(row) - allowed)}, missing keys {sorted(required - set(row))}")
                continue
            C.repeated_elements(self.f, "TABLE", where, judgment_content(kind, row))
            for name, value in judgment_content(kind, row).items():
                if isinstance(value, (list, dict)) and not value and name not in MAY_BE_EMPTY:
                    self.add("TABLE", f"{where}: {name} is empty; a list names something, and an optional one is omitted")
                if name in PROSE_KEYS and name != "options" and (not isinstance(value, str) or not value.strip()):
                    self.add("TABLE", f"{where}: {name} must be non-empty text")
            if key in self.t[kind]:
                self.add("TABLE", f"{where}: duplicate row")
                continue
            self.t[kind][key] = row
            self.valid.add(id(row))
        rule = d.get("precedence_rule")
        self.rule = rule if isinstance(rule, dict) else {}
        if not self.rule or set(self.rule) != {"id", "title", "design_line", "design_recommendation", "design_status_cell", "status", "od5", "owner_questions"}:
            self.add("TABLE", "[precedence_rule] holds exactly id, title, design_line, design_recommendation, design_status_cell, status, od5, owner_questions")
        self.entries = [e for e in d.get("entry", []) if id(e) in self.valid]
        self.ids = set(self.t["source"]) | set(self.t["related"]) | {f"{RULE_ID}.{q}" for q in self.t["rule_quote"]}
        self.oq_kind = {q: r["kind"] for q, r in self.t["owner_question"].items()}

    # ---- DESIGN
    def parse_design(self) -> None:
        lines, rows, table_lines = self.design, {}, set()
        header = [i for i, line in enumerate(lines) if line.strip() == "| # | Decision | Recommendation | Owner ratification |"]
        if len(header) != 1:
            self.add("DESIGN", f"expected one LD table header in the design, found {len(header)}")
        i = header[0] + 2 if len(header) == 1 else len(lines)
        while i < len(lines) and lines[i].startswith("|"):
            cells = [c.strip() for c in lines[i].strip()[1:-1].split("|")]
            table_lines.add(i + 1)
            key = RULE_ID if cells[0] == "—" else cells[0]
            if len(cells) != 4 or key in rows:
                self.add("DESIGN", f"design:{i + 1} is not a four-cell row of a new LD id")
            rows[key] = (i + 1, cells)
            i += 1
        self.design_rows = rows
        od5 = [i for i, line in enumerate(lines) if line.startswith("| **OD-5**")]
        cells = [c.strip() for c in lines[od5[0]].strip()[1:-1].split("|")] if len(od5) == 1 else []
        if len(cells) != 5:
            self.add("DESIGN", "expected one five-cell OD-5 row in the design")
            cells = ["", "", "", "", ""]
        items = {f"LD-{n}" for n in re.findall(r"LD-(\d+)", cells[1])} | ({RULE_ID} if "source precedence rule" in cells[1] else set())
        blocks = {RULE_ID if m.strip() == "precedence" else m.strip(): stage
                  for stage, members in re.findall(r"(\d+\.\d+) \(([^)]*)\)", cells[4]) for m in members.split(",")}
        self.od5 = {"line": od5[0] + 1 if od5 else None, "items": items, "blocks": blocks}
        self.exits = {}
        for i, line in enumerate(lines):
            m = EXIT_DEF.match(line)
            if m:
                j = i + 1
                while j < len(lines) and lines[j].strip() and len(lines[j]) - len(lines[j].lstrip()) > len(m.group(1)):
                    j += 1
                if m.group(2) in self.exits:
                    self.add("DESIGN", f"exit {m.group(2)} is defined twice")
                self.exits[m.group(2)] = (i + 1, j, {f"LD-{n}" for n in LD_MENTION.findall(" ".join(lines[i:j]))})
        e08 = self.exits.get("E0.8")
        text = " ".join(lines[e08[0] - 1:e08[1]]) if e08 else ""
        e08_items = {f"LD-{n}" for n in LD_MENTION.findall(text)} | ({RULE_ID} if "precedence rule" in text else set())
        if not e08 or e08_items != items:
            self.add("DESIGN", f"the OD-5 row lists {sorted(items)} but E0.8 lists {sorted(e08_items)}")
        self.mention_lines = [(i, f"LD-{n}") for i, line in enumerate(lines, 1) if i not in table_lines for n in LD_MENTION.findall(line)]

    def design_row(self, where: str, row: dict) -> None:
        found = self.design_rows.get(row.get("id"))
        if found is None:
            self.add("DESIGN", f"{where} has no row in the design's LD table")
            return
        line, cells = found
        want = {"design_line": line, "title": cells[1], "design_recommendation": cells[2], "design_status_cell": cells[3]}
        for k, v in want.items():
            if row.get(k) != v:
                self.add("DESIGN", f"{where}: {k} is not the design's (design:{line})")
        status = re.match(r"^(?:\*\*)?(Required|Recorded)(?:\*\*)?(?:\s|$)", cells[3])
        if row.get("status") != (status.group(1) if status else None):
            self.add("DESIGN", f"{where}: status {row.get('status')!r} is not the design cell's")
        if bool(row.get("od5")) != (row.get("id") in self.od5["items"]) or (row.get("id") in self.od5["items"]) != (row.get("status") == "Required"):
            self.add("DESIGN", f"{where}: od5 = {row.get('od5')} and status {row.get('status')!r} disagree with the OD-5 row")
        self.design_ranges.setdefault(row.get("id"), []).append((line, line))
        self.verified_quotes.extend(cells)

    # ---- SNAPSHOT and DECISIONS
    def snapshots(self) -> None:
        root = self.o.snapshot_root or self.o.repo
        self.snap: dict[str, dict] = {}
        for rel, row in self.t["snapshot"].items():
            where = f"snapshot {rel}"
            pin = str(row["sha256"]).removeprefix("sha256:")
            if not rel.startswith(SNAPSHOT_PREFIX) or not rel.endswith(".json"):
                self.add("SNAPSHOT", f"{where}: not a JSON file under {SNAPSHOT_PREFIX}")
                continue
            if C.check_immutable(self.f, "SNAPSHOT", root, [rel], {rel: pin}) != 1:
                self.add("SNAPSHOT", f"{where}: has no committed version, so nothing fixes what was retrieved; commit a snapshot before citing it")
            try:
                snap = json.loads((Path(root) / rel).read_text(encoding="utf-8"))
            except (OSError, ValueError) as error:
                self.add("SNAPSHOT", f"{where}: {error}")
                continue
            kind, ok = row["kind"], True
            if kind == "issue":
                repo, _, number = str(row.get("issue")).partition("#")
                ok = snap.get("schema") == SNAPSHOT_SCHEMAS.get(row.get("schema")) and snap.get("repo") == repo and str(snap.get("number")) == number \
                    and sorted(c.get("id") for c in snap.get("comments", [])) == sorted(row.get("comments", [])) \
                    and ((snap.get("issue") or {}).get("body") is not None) == bool(row.get("issue_body"))
            elif kind == "index":
                ok = snap.get("schema") == "trust.core.decision-index.v1" and [q.get("q") for q in snap.get("queries", [])] == row.get("queries") \
                    and all(len(q.get("items", [])) == q.get("total_count") for q in snap.get("queries", []))
            elif kind == "fcp":
                ok = snap.get("schema") == "trust.core.fcp-completions.v1" and snap.get("index") == row.get("index")
            else:
                self.add("SNAPSHOT", f"{where}: kind {kind!r} is not issue, index or fcp")
            if not ok or snap.get("retrieved") != row["retrieved"]:
                self.add("SNAPSHOT", f"{where}: the file does not hold what its row records")
            self.snap[rel] = snap
        index = [rel for rel, r in self.t["snapshot"].items() if r["kind"] == "index" and rel in self.snap]
        records_of = {rel: {f"{it.get('repo')}#{it.get('number')}": it for q in self.snap[rel]["queries"] for it in q.get("items", [])} for rel in index}
        self.records = {at: it for records in records_of.values() for at, it in records.items()}
        self.fcp_status, self.notices = {}, {}
        for rel in [r for r, row in self.t["snapshot"].items() if row["kind"] == "fcp" and r in self.snap]:
            seen = []
            for rec in self.snap[rel].get("records", []):
                at = f"{rec.get('repo')}#{rec.get('number')}"
                if at in seen:
                    self.add("DECISION-FCP", f"{rel} records {at} twice")
                seen.append(at)
                good = [n for n in rec.get("notices", []) if n.get("author") in RFCBOT and FCP_NOTICE.match(n.get("body") or "")
                        and str(n.get("html_url", "")).endswith(f"#issuecomment-{n.get('id')}") and issue_of_url(n.get("html_url")) == at
                        and C.parse_date(n.get("created_at")) is not None]
                if len(good) != len(rec.get("notices", [])):
                    self.add("DECISION-FCP", f"{rel} keeps a comment on {at} that is not an rfcbot completion notice of that record")
                self.notices[at] = good
                self.fcp_status[at] = "before-pin" if any(before_pin(n["created_at"], self.pins) for n in good) else "after-pin" if good else "no-notice"
            own = records_of.get(self.snap[rel].get("index"), {})
            if self.snap[rel].get("index") not in index or set(seen) != set(own):
                self.add("DECISION-FCP", f"{rel} does not record exactly the records of the pinned decision index it names "
                                         f"(missing {sorted(set(own) - set(seen))[:3]}, extra {sorted(set(seen) - set(own))[:3]})")
        for rel in index:
            named = [r for r, row in self.t["snapshot"].items() if row["kind"] == "fcp" and row.get("index") == rel]
            if len(named) != 1:
                self.add("DECISION-FCP", f"snapshot {rel}: {len(named)} snapshots of rfcbot's completion notices name this index; exactly one does")
        self.verified_urls |= {(s.get("issue") or {}).get("html_url") for s in self.snap.values()}

    def fcp_disposition(self, where: str, row: dict, at: str, code: str) -> None:
        status = self.fcp_status.get(at)
        if row.get("fcp") != status:
            self.add("DECISION-FCP", f"{where} declares fcp {row.get('fcp')!r}; rfcbot's completion notices give {status!r}")
        if status == "after-pin" and (row.get("use") or "reason" in row):
            self.add("DECISION-FCP", f"{where} completed after the alignment timestamp, which alone disposes of it; it takes no citation and no reason")
        elif status != "after-pin" and not row.get("use") and not str(row.get("reason", "")).strip():
            self.add(code, f"{where} is not cited and gives no reason")
        self.verified_issues.add(at)

    def team_decision(self, where: str, s: dict) -> tuple | None:
        snap = self.snap.get(s.get("snapshot"))
        if snap is None or self.t["snapshot"][s["snapshot"]]["kind"] != "issue":
            self.add("TEAM-DECISION", f"{where}: {s.get('snapshot')!r} is not a pinned issue snapshot")
            return None
        issue = snap.get("issue") or {}
        objects = {c.get("html_url"): c for c in snap.get("comments", [])} | ({issue.get("html_url"): issue} if issue.get("body") is not None else {})
        obj, comments = objects.get(s.get("url")), {c.get("id"): c for c in snap.get("comments", [])}
        if obj is None or C.collapse(s["quote"]) not in C.collapse(obj.get("body") or ""):
            self.add("TEAM-DECISION", f"{where}: {s.get('url')} is not a kept comment or body of the snapshot containing the quote")
            return None
        problems, disposition = [], s.get("disposition")
        proposal, complete = comments.get(s.get("fcp_proposal")), comments.get(s.get("fcp_complete"))
        if s.get("team") not in TEAMS or disposition not in DISPOSITIONS or proposal is None or complete is None:
            problems.append(f"team, disposition, fcp_proposal and fcp_complete must be one of {TEAMS}, one of {DISPOSITIONS} and kept comments")
        else:
            body = complete.get("body") or ""
            proposer = re.search(rf"@([A-Za-z0-9-]+) has proposed to {disposition} this", proposal.get("body") or "")
            members = set(re.findall(r"^\* \[[ x]\] @([A-Za-z0-9-]+)", proposal.get("body") or "", re.M))
            if complete.get("author") not in RFCBOT or f"disposition to **{disposition}**" not in body or "is now **complete**" not in body \
                    or f"#issuecomment-{proposal.get('id')}" not in body or not before_pin(complete.get("created_at"), self.pins):
                problems.append(f"comment {complete.get('id')} is not rfcbot's notice, before the alignment, that the {disposition} FCP of {proposal.get('id')} completed")
            if proposal.get("author") not in RFCBOT or proposer is None:
                problems.append(f"comment {proposal.get('id')} is not rfcbot's record of a proposal to {disposition}")
            else:
                if obj.get("author") not in members | {proposer.group(1)}:
                    problems.append(f"the quoted text is by {obj.get('author')}, neither the proposer nor a listed team member")
                command = re.compile(rf"@rfcbot\s+(?:fcp\s+)?{disposition}\b[ \t]*([a-z-]*)")
                named = [m.group(1) for c in snap.get("comments", []) if c.get("author") == proposer.group(1) for m in command.finditer(c.get("body") or "")]
                if not named or not (s["team"] in named or ("" in named and f"T-{s['team']}" in issue.get("labels", []))):
                    problems.append(f"no @rfcbot {disposition} command by the proposer names T-{s['team']} or runs on an issue labelled with it")
            for stamp in (obj.get("created_at"), obj.get("last_edited_at")):
                if stamp and (not before_pin(stamp, self.pins) or C.parse_date(stamp) > C.parse_date(complete.get("created_at"))):
                    problems.append("the quoted text was written or last edited after the FCP completed or the alignment timestamp")
        at = f"{snap.get('repo')}#{snap.get('number')}"
        record = self.records.get(at)
        if record is None:
            problems.append(f"{at} is not a record of the pinned decision index")
        elif f"T-{s.get('team')}" not in record.get("labels", []) and not (s.get("team") == "opsem" and record.get("repo") == "rust-lang/unsafe-code-guidelines"):
            problems.append(f"the index record {at} is not labelled T-{s.get('team')}")
        elif self.fcp_status.get(at) != "before-pin" or s.get("fcp_complete") not in [n.get("id") for n in self.notices.get(at, [])]:
            problems.append(f"rfcbot's notices for {at} record no completion {s.get('fcp_complete')} before the alignment")
        for problem in problems:
            self.add("TEAM-DECISION", f"{where}: {problem}")
        self.verified_urls.add(s.get("url"))
        self.verified_issues.add(at)
        self.verified_quotes.append(C.collapse(s["quote"]))
        return ("web", s.get("url"), 0, 0)

    # ---- RFC
    def rfcs(self) -> None:
        self.stabilizations: dict[str, int] = {}
        for number, r in self.t["rfc"].items():
            where, rel = f"rfc {number}", r["file"]
            if not re.fullmatch(rf"text/{int(r['number']):04d}-[A-Za-z0-9_.-]+\.md", str(rel)) or self.trees["rfcs"].lines(rel) is None:
                self.add("RFC", f"{where}: {rel!r} is not an accepted RFC under text/ at the pin named by its number")
                continue
            first = min((n for n, h in headings(self.trees["rfcs"].lines(rel)).items()), default=0)
            tracking = re.fullmatch(r"rust-lang/rust#(\d+)", str(r["tracking_issue"]))
            for name, needle in (("pr", f"github.com/rust-lang/rfcs/pull/{r['number']})"), ("tracking", f"github.com/rust-lang/rust/issues/{tracking.group(1) if tracking else '?'})")):
                c, parts = r[name] if isinstance(r[name], dict) else {}, None
                if str(c.get("ref", "")).startswith(f"rfcs:{rel}:"):
                    parts = self.cite("RFC", f"{where} {name}", c["ref"], c.get("quote"))
                if parts is None or needle not in str(c.get("quote")) or parts["end"] >= first:
                    self.add("RFC", f"{where}: {name} is a citation, in the header of {rel}, of a link to {needle[:-1]}")
            self.verified_issues |= {str(r["tracking_issue"]), f"rust-lang/rfcs#{r['number']}"}
            kind, snap = r["stabilization"], self.snap.get(r.get("tracking_snapshot"))
            ev = r["evidence"] if isinstance(r.get("evidence"), dict) else {}
            self.stabilizations[kind] = self.stabilizations.get(kind, 0) + 1
            if kind not in STABILIZATIONS:
                self.add("RFC", f"{where}: stabilization {kind!r} is not one of {STABILIZATIONS}")
                continue
            if r.get("tracking_snapshot") is not None and (snap is None or f"{snap.get('repo')}#{snap.get('number')}" != r["tracking_issue"]):
                self.add("RFC", f"{where}: tracking_snapshot is not a pinned snapshot of {r['tracking_issue']}")
                snap = None
            issue = (snap or {}).get("issue") or {}
            if kind in ("stable-item", "no-feature-gate") and (snap is None or snap.get("schema") != SNAPSHOT_SCHEMAS[2] or issue.get("state") != "closed"
                                                               or issue.get("state_reason") != "completed" or not before_pin(issue.get("closed_at"), self.pins)):
                self.add("RFC", f"{where}: ({kind}) needs a schema-2 snapshot of its tracking issue closed as completed before the alignment")
            if kind == "checked-step":
                body = [C.collapse(x) for x in str(issue.get("body") or "").replace("\r\n", "\n").split("\n")]
                if snap is None or not str(ev.get("quote", "")).startswith("- [x] Stabiliz") or C.collapse(ev.get("quote", "")) not in body \
                        or any(t and not before_pin(t, self.pins) for t in (issue.get("created_at"), issue.get("last_edited_at"))):
                    self.add("RFC", f"{where}: the tracking issue body, not edited after the alignment, records no checked stabilization step quoted whole")
                self.verified_quotes.append(C.collapse(ev.get("quote", "")))
            elif kind in ("accepted-feature", "stable-item"):
                pattern = r"^\(accepted, [a-z0-9_]+, \"[0-9.]+\", Some\((\d+)\)\),?$" if kind == "accepted-feature" else r"^#\[stable\(feature = \"[a-z0-9_]+\", since = \"[0-9.]+\"\)\]$"
                prefix = "rustc:compiler/rustc_feature/src/accepted.rs:" if kind == "accepted-feature" else "rustc:library/"
                m = re.match(pattern, C.collapse(ev.get("quote", "")))
                if not str(ev.get("ref", "")).startswith(prefix) or self.cite("RFC", f"{where} evidence", ev.get("ref"), ev.get("quote")) is None or m is None \
                        or (kind == "accepted-feature" and (not tracking or m.group(1) != tracking.group(1))):
                    self.add("RFC", f"{where}: ({kind}) evidence is not a {prefix}... line of the form {pattern} for its tracking issue")

    # ---- entries
    def entry_rows(self) -> None:
        ids = [e.get("id") for e in self.entries]
        if ids != list(LD_IDS):
            self.add("DESIGN", f"the entries are {ids}, not LD-1..LD-13 once each in order")
        self.computed: dict[str, dict] = {}
        self.oq_refs: dict[str, list] = {}
        self.source_counts = {"rank": {1: 0, 2: 0, 3: 0}, "kind": {}, "role": {}}
        self.locator: dict[str, tuple] = {}  # row id -> (source, rel, first line, last line)
        for e in self.entries:
            lid = str(e.get("id"))
            if lid not in LD_IDS:
                continue
            self.design_row(f"entry {lid}", e)
            self.note_oq(e.get("owner_questions"), lid)
            for q in e.get("owner_questions", []):
                if self.oq_kind.get(q) in COMPUTED_OQ_KINDS:
                    self.add("OQ", f"entry {lid} references {q} ({self.oq_kind.get(q)}), which belongs on the aspect that needs it")
            sources, aspects = self.ok(e, "source"), self.ok(e, "aspect")
            aspect_ids = [a.get("id") for a in aspects]
            seen = []
            for s in sources + self.ok(e, "related"):
                ranked = s in sources
                sid, kind = str(s.get("id")), s.get("kind")
                where = f"{'source' if ranked else 'related'} {sid}"
                if not re.fullmatch(rf"{re.escape(lid)}\.{'S' if ranked else 'R'}\d+", sid):
                    self.add("TABLE", f"{where}: an id of {lid} is {lid}.{'S' if ranked else 'R'}<n>")
                got = self.ranked_source(where, s, lid, aspect_ids) if ranked else self.related_source(where, s)
                if got:
                    self.locator[sid] = got
                    self.quotes[sid] = C.collapse(s.get("quote", ""))
                    for other_id, other in seen:
                        if other[:2] == got[:2] and got[2] <= other[3] and other[2] <= got[3] and \
                                (self.quotes[sid] in self.quotes[other_id] or self.quotes[other_id] in self.quotes[sid]):
                            self.add("DUPLICATE", f"{sid} and {other_id} quote one text of {got[1]}; one citation is one row")
                    seen.append((sid, got))
            self.aspects(lid, e, aspects, sources)
            exits = []
            for x in self.ok(e, "exit"):
                where = f"exit {lid}/{x.get('id')}"
                parts = self.cite("DESIGN-EXIT", where, x.get("ref"), x.get("quote"), owner=lid)
                found = self.exits.get(x.get("id"))
                if x.get("effect") not in EFFECTS or found is None or (parts and not (found[0] <= parts["start"] and parts["end"] <= found[1])):
                    self.add("DESIGN-EXIT", f"{where}: needs an effect in {EFFECTS} and a quote inside the exit the design defines")
                exits.append(x.get("id"))
            for eid, (start, _, names) in sorted(self.exits.items()):
                if lid in names and eid not in exits:
                    self.add("DESIGN-EXIT", f"exit {eid} (design:{start}) names {lid}, but {lid} does not list it")
            for x in self.ok(e, "cited_by"):
                self.cite("DESIGN-EXIT", f"cited_by {lid}/{x.get('name')}", x.get("ref"), x.get("quote"), owner=lid)
                if x.get("what") not in CITED_BY:
                    self.add("TABLE", f"cited_by {lid}/{x.get('name')}: what is one of {CITED_BY}")
            for alt in self.ok(e, "alternative"):
                where = f"alternative {lid}/{alt.get('name')}"
                if not alt.get("evidence") and not alt.get("design_quote"):
                    self.add("EVIDENCE", f"{where}: states a cost with no evidence")
                for ref in alt.get("evidence", []):
                    if not str(ref).startswith(f"{lid}.") or ref not in self.ids:
                        self.add("EVIDENCE", f"{where}: cites {ref}, which is not a source or related row of {lid}")
                for q in alt.get("design_quote", []):
                    self.cite("DESIGN-EXIT", where, q.get("ref"), q.get("quote"), owner=lid)

    def ranked_source(self, where: str, s: dict, lid: str, aspect_ids: list) -> tuple | None:
        kind = s.get("kind")
        if kind not in KINDS or s.get("rank") != KINDS[kind][0]:
            self.add("SOURCE", f"{where}: kind {kind!r} is not a ranked kind, or rank {s.get('rank')} is not its rank")
            return None
        roles = [source_role(s, a) for a in s.get("aspects", [])]
        if ("role" in s) == ("roles" in s) or ("roles" in s and sorted(s["roles"]) != sorted(s.get("aspects", []))) \
                or not s.get("aspects") or any(a not in aspect_ids for a in s["aspects"]) or any(r not in ROLES for r in roles) \
                or ("pins" in roles and kind != "rustc-test") or (s.get("open_by") is not None and "contrary" not in roles):
            self.add("SOURCE", f"{where}: needs aspects of {lid}, one role or roles per aspect from {ROLES} (pins only for a rustc test), and open_by only when contrary")
        self.source_counts["rank"][s.get("rank")] = self.source_counts["rank"].get(s.get("rank"), 0) + 1
        self.source_counts["kind"][kind] = self.source_counts["kind"].get(kind, 0) + 1
        for r in roles:
            self.source_counts["role"][r] = self.source_counts["role"].get(r, 0) + 1
        owners = {"rule": "reference", "paragraph": "fls", "rfc": "rfc", "section": "rfc", "restrictions": "rustc-test",
                  **dict.fromkeys(("team", "url", "snapshot", "disposition", "fcp_proposal", "fcp_complete"), "team-decision")}
        for key in sorted(set(s) & (set(owners) | {"ref"})):
            if owners.get(key, kind) != kind or (key == "ref" and kind == "team-decision"):
                self.add("SOURCE", f"{where}: {key} does not belong to a {kind} source")
        if kind == "team-decision":
            return self.team_decision(where, s)
        _, source, prefix = KINDS[kind]
        parts = C.parse_ref(s.get("ref"))
        if parts is None or parts["source"] != source or not str(parts.get("path") or "").startswith(prefix):
            self.add("SOURCE", f"{where}: a {kind} source cites `{source}:{prefix}...`, not {s.get('ref')!r}")
            return None
        if not self.cite("SOURCE", where, s["ref"], s["quote"]):
            return None
        rel, a, b = parts["path"], parts["start"], parts["end"]
        if s["rank"] < 3 and not any(source == c["source"] and any(rel.startswith(i["path"]) and rel.endswith(i["suffix"]) for i in c["include"])
                                     for c in self.t["corpus"].values() if kind in c["kinds"]):
            self.add("CORPUS", f"{where}: {rel} lies outside every declared search scope of kind {kind}, so its file was never searched")
        if kind == "reference":
            problem = self.rule_problem(rel, s.get("rule"), a, b)
            if problem:
                self.add("RULE-ID", f"{where}: a Reference source is a rule, by rule id; {problem}")
        elif kind == "fls":
            found = self.resolver.spans("fls").get(str(s.get("paragraph")), [])
            if len(found) != 1 or found[0][0] != rel or found[0][1] > a or self.resolver.check(f"fls:{s.get('paragraph')}", s["quote"]) is not None:
                self.add("FLS-ID", f"{where}: an FLS source is a paragraph; the quote is not in paragraph {s.get('paragraph')!r} of {rel}")
        elif kind == "rfc":
            record = self.t["rfc"].get(str(s.get("rfc")))
            heads = headings(self.trees["rfcs"].lines(rel) or [])
            heading = heads.get(max((n for n in heads if n <= a), default=0))
            if record is None or record["file"] != rel or s.get("section") != heading:
                self.add("RFC", f"{where}: names RFC {s.get('rfc')} (an [[rfc]] record of {rel}) and its nearest heading {heading!r}")
        elif kind == "std-doc":
            problem = std_doc_problem(self.trees["worktree"].lines(rel) or [], a, b)
            if problem:
                self.add("STD-DOC", f"{where}: {problem}")
        elif kind == "rustc-test":
            self.test_source(where, s, rel, roles)
        return (source, rel, a, b)

    def related_source(self, where: str, r: dict) -> tuple | None:
        source, prefix = RELATED.get(r.get("kind"), (None, None))
        parts = C.parse_ref(r.get("ref"))
        if parts is None or parts["source"] != source or (prefix and not str(parts.get("path") or "").startswith(prefix)):
            self.add("SOURCE", f"{where}: a {r.get('kind')} related row cites `{source}:{prefix or ''}...`, not {r.get('ref')!r}")
            return None
        if not self.cite("SOURCE", where, r["ref"], r["quote"], owner="*"):
            return None
        if "rule" in r:
            problem = self.rule_problem(parts["path"], r["rule"], parts["start"], parts["end"]) if source == "reference" else "a rule id names Reference text"
            if problem:
                self.add("RULE-ID", f"{where}: {problem}")
        return (source, parts.get("path") or C.DESIGN_REL, parts["start"], parts["end"])

    def rule_problem(self, rel: str, rule: object, a: int, b: int) -> str | None:
        """None when lines a..b lie in the text of r[rule]: the lines from its marker to the next rule marker, or to
        a heading after a blank line outside a code fence, less every untagged admonition, indented or not (the
        text resumes after one). An admonition is a blockquote: its `>` lines, from a line that starts one to the
        last `>` line after it, in either spelling the Reference uses, `> [!NOTE]` or the legacy `> **Example**:`.
        An admonition on the line after the marker is tagged: it is that rule's text."""
        lines = self.trees["reference"].lines(rel) or []
        marks = [i for i, line in enumerate(lines, 1) if C.REFERENCE_RULE.match(line)]
        own = [k for k, m in enumerate(marks) if C.REFERENCE_RULE.match(lines[m - 1]).group(1) == rule]
        if len(own) != 1:
            return f"lines {a}-{b} are not inside the text of r[{rule}]"
        m = marks[own[0]]
        end = marks[own[0] + 1] if own[0] + 1 < len(marks) else len(lines) + 1
        runs, quote, fence = [], None, False  # quote: None, or whether the blockquote the line is in is tagged
        for n in range(m + 1, end):
            line = lines[n - 1]
            if not line.lstrip().startswith(">"):
                quote = None
            elif quote is None or ADMONITION.match(line):
                quote = n == m + 1
            fence ^= quote is None and line.lstrip().startswith(("```", "~~~"))
            if line.startswith("#") and not fence and not lines[n - 2].strip():
                break
            if quote is not False:
                runs = runs[:-1] + [(runs[-1][0], n)] if runs and runs[-1][1] == n - 1 else runs + [(n, n)]
        if any(x <= a and b <= y for x, y in runs):
            return None
        return f"lines {a}-{b} are not inside the text of r[{rule}] ({'lines ' + ', '.join(f'{x}-{y}' for x, y in runs) if runs else 'no text'})"

    def test_source(self, where: str, s: dict, rel: str, roles: list) -> None:
        rs = rel if rel.endswith(".rs") else re.sub(r"(\.[A-Za-z0-9]+)+$", ".rs", rel)
        lines = [line.strip() for line in self.trees["worktree"].lines(rs) or []]
        if not lines:
            self.add("TEST", f"{where}: {rel}'s test {rs} does not exist")
            return
        restrictions = sorted({m.group(1) for line in lines if (m := re.match(r"^//@\s*((?:ignore|only|needs)-[A-Za-z0-9_-]+)", line))})
        if sorted(s.get("restrictions", [None])) != restrictions:
            self.add("TEST", f"{where}: restrictions are {s.get('restrictions')!r}; {rs} declares {restrictions}")
        if set(roles) & {"pins", "settles", "contrary"} and (
                not any(re.match(r"^//@\s*(run-pass|run-fail|run-crash)\s*$", line) for line in lines)
                or any(line.startswith("#![feature(") for line in lines)
                or any(re.match(r"^//@\s*(compile-flags\s*:.*\s-Z|rustc-env\s*:\s*RUSTC_BOOTSTRAP)", line + " ") for line in lines)
                or (rs != rel and "//@ check-run-results" not in lines)):
            self.add("TEST", f"{where}: a pinning test runs the program (run-pass, run-fail or run-crash, checking its output when an output file is cited), enables no feature and passes no -Z flag")

    def aspects(self, lid: str, e: dict, aspects: list, sources: list) -> None:
        results = {}
        for a in aspects:
            aw = f"aspect {lid}/{a.get('id')}"
            c = results[a.get("id")] = dict(compute_aspect(a, sources), row=a)
            if a.get("modelling") not in MODELLINGS or a.get("label") not in LABELS:
                self.add("TABLE", f"{aw}: modelling in {MODELLINGS} and label in {LABELS}")
            if not any(a.get("id") in s.get("aspects", []) for s in sources):
                self.add("PRECEDENCE", f"{aw}: has no source")
            if a.get("label") != c["label"]:
                self.add("PRECEDENCE", f"{aw}: is labelled {a.get('label')!r}; the precedence predicates compute {c['label']!r}")
            for key, want in (("resolution", c["resolution"]), ("conflicts", c["conflicts"]), ("divergences", c["divergences"]),
                              ("compat_candidate", c["compat_candidate"])):
                have = a.get(key, [] if key in ("conflicts", "divergences") else False if key == "compat_candidate" else None)
                if (sorted(have) if isinstance(have, list) else have) != want:
                    self.add("PRECEDENCE", f"{aw}: declares {key} {have!r}; computed {want!r}")
            if c["label"] in V11 and not any(s.get("kind") == "rustc-test" and source_role(s, a.get("id")) in ("pins", "settles") for s in sources):
                self.add("PRECEDENCE", f"{aw}: is {c['label']} but cites no rustc test that pins it")
            if c["label"] == "compat" and not (any(s.get("rank") == 1 and source_role(s, a["id"]) == "contrary" for s in sources)
                                               and any(s.get("kind") == "rustc-test" and source_role(s, a["id"]) in ("pins", "settles") for s in sources)
                                               and re.fullmatch(r"rust-lang/[A-Za-z0-9_.-]+#\d+", str(a.get("upstream")))):
                self.add("PRECEDENCE", f"{aw}: compat needs a contrary rank-1 text, a pinning rustc test and an upstream issue")
            if (c["resolution"] == "choose") != bool(a.get("open_text")) or any(
                    source_role(next((s for s in sources if s.get("id") == t), {}), a.get("id")) not in ("open", "settles")
                    or next((s for s in sources if s.get("id") == t), {}).get("rank") not in (1, 2) for t in a.get("open_text", [])):
                self.add("PRECEDENCE", f"{aw}: a Choose or parameter cites the rank-1 or rank-2 texts that leave the choice open (open_text), and only it does")
            refs = a.get("owner_questions", [])
            self.note_oq(refs, f"{lid}/{a.get('id')}")
            kinds = {self.oq_kind.get(q) for q in refs}
            for q in refs:
                if self.oq_kind.get(q) in COMPUTED_OQ_KINDS and self.oq_kind.get(q) not in c["required_oq_kinds"]:
                    self.add("OQ", f"{aw}: references {q} ({self.oq_kind.get(q)}), which its sources do not call for")
            for kind in c["required_oq_kinds"]:
                if kind not in kinds:
                    self.add("OQ", f"{aw}: needs an owner question of kind {kind!r}")
        for s in sources:
            if s.get("open_by") is not None and not any(source_role(s, a) == "contrary" and s["open_by"] in {x.get("id") for x in sources}
                                                        and same_locator_open(s, next(x for x in sources if x.get("id") == s["open_by"]), a) for a in s.get("aspects", [])):
                self.add("PRECEDENCE", f"source {s.get('id')}: open_by {s['open_by']} is not an open source at the same rank and locator")
        label = max((c["label"] for c in results.values()), key=LABELS.index, default=None)
        if e.get("label") != label:
            self.add("PRECEDENCE", f"entry {lid}: label {e.get('label')!r}; its aspects compute {label!r}")
        self.computed[lid] = {"label": label, "aspects": results}

    def note_oq(self, refs, who: str) -> None:
        for q in refs or []:
            self.oq_refs.setdefault(q, []).append(who)

    # ---- SEARCH
    def corpus_hits(self, name: str, pattern: str) -> dict[str, list[int]]:
        """file -> the lines of a declared scope that `pattern` matches, cached on the tree (a test shares trees)."""
        c = self.t["corpus"][name]
        tree = self.trees["worktree" if c["source"] == "rustc" else c["source"]]
        cache = tree.__dict__.setdefault("_ld_scopes", {})
        scope = (json.dumps(c["include"], sort_keys=True), c["lines"])
        if scope not in cache:
            files = sorted({f for i in c["include"] for f in tree.files(i["path"], (i["suffix"],))})
            tree.prefetch(files)
            doc = c["lines"] == "doc-comment"
            numbered = {f: [(n, line) for n, line in enumerate(tree.lines(f) or [], 1) if not doc or line.strip().startswith(("///", "//!"))] for f in files}
            cache[scope] = (numbered, {})
        lines, hits = cache[scope]
        if pattern not in hits:
            # Every line is searched on its own: no whole-file shortcut decides that a file holds no hit.
            compiled = re.compile(pattern)
            found = {f: [n for n, line in ns if compiled.search(line)] for f, ns in lines.items()}
            hits[pattern] = {f: ns for f, ns in found.items() if ns}
        return hits[pattern]

    def verify_corpus_import(self, ref: object) -> None:
        """Compare a complete import with aligned Rust before relaxing its file guard."""
        parts = C.parse_ref(ref) if isinstance(ref, str) else None
        if not parts or parts["source"] != "rustc" or not str(parts["path"]).startswith("library/"):
            return
        rel = parts["path"]
        current = self.trees["worktree"].text(rel)
        upstream = self.trees["upstream"].text(rel)
        if current is None or upstream is None:
            self.add("PIN", f"corpus import {rel}: current or aligned upstream source is unavailable")
            return
        try:
            region = identical_import_region(current, upstream, parts["start"], parts["end"])
        except ValueError as error:
            self.add("PIN", f"corpus import {rel}: {error}")
            return
        if region is not None:
            self.resolver.upstream_region(self.f, rel, *region, "unchanged upstream import")

    def corpora(self) -> None:
        for name, corpus in list(self.t["corpus"].items()):
            ok = corpus["source"] in ("decisions", *READS.values(), "rustc") and corpus["lines"] in ("all", "doc-comment", "title") \
                and (corpus["source"] == "decisions") == (corpus["lines"] == "title") == (not corpus["include"]) \
                and all(isinstance(i, dict) and set(i) == {"path", "suffix"} for i in corpus["include"]) and all(k in KINDS for k in corpus["kinds"])
            if not ok:
                self.add("CORPUS", f"corpus {name}: a source tree (or decisions, by title), include {{path, suffix}} rows, a line rule and ranked kinds")
                del self.t["corpus"][name]
            for x in corpus.get("cites", []):
                self.verify_corpus_import(x.get("ref") if isinstance(x, dict) else x)
                self.cite("CORPUS", f"corpus {name}", x.get("ref") if isinstance(x, dict) else x, x.get("quote") if isinstance(x, dict) else None)

    def searches(self) -> None:
        c = self.search_counts = {"searches": 0, "hits": 0, "cited": 0, "uncited": 0, "lines": 0, "lines_cited": 0, "lines_reason": 0}
        self.dispositioned: set[str] = set()
        coverage: dict[str, set] = {}
        for e in self.entries:
            lid = e.get("id")
            for sr in self.ok(e, "search"):
                sid, corpus = str(sr.get("id")), sr.get("corpus")
                aspect_ids = {a.get("id") for a in e.get("aspect", [])}
                if not re.fullmatch(rf"{re.escape(str(lid))}\.Q\d+", sid) or corpus not in self.t["corpus"] or not set(sr.get("aspects", [])) <= aspect_ids:
                    self.add("SEARCH", f"search {sid}: an id {lid}.Q<n>, a declared corpus and aspects of {lid}")
                    continue
                for a in sr["aspects"]:
                    coverage.setdefault(f"{lid}/{a}", set()).add(corpus)
                try:
                    pattern = re.compile(sr["pattern"])
                except re.error as error:
                    self.add("SEARCH", f"search {sid}: the pattern does not compile: {error}")
                    continue
                if corpus == "decisions":
                    computed = {at: [] for at, it in self.records.items() if pattern.search(it.get("title") or "")}
                else:
                    computed = self.corpus_hits(corpus, sr["pattern"])
                recorded = {h.get("at"): h for h in self.ok(sr, "hit")}
                for at in sorted(set(computed) ^ set(recorded)):
                    self.add("SEARCH", f"search {sid} ({corpus}): {at} {'matches lines ' + str(computed[at]) + ' and is not recorded' if at in computed else 'is recorded but not matched'}")
                c["searches"] += 1
                for at, h in recorded.items():
                    if at not in computed:
                        continue
                    hw = f"hit {sid}/{at}"
                    c["hits"] += 1
                    c["cited" if h.get("use") else "uncited"] += 1
                    for uid in h.get("use", []):
                        loc = self.locator.get(uid)
                        if not str(uid).startswith(f"{lid}.") or loc is None or (corpus == "decisions") != (loc[0] == "web") or \
                                (corpus != "decisions" and loc[1] != at) or (corpus == "decisions" and at not in self.verified_issues_of(uid)):
                            self.add("SEARCH", f"{hw}: is cited by {uid}, which is not a verified {lid} row at {at}")
                    if corpus == "decisions":
                        self.dispositioned.add(at)
                        self.fcp_disposition(hw, h, at, "SEARCH")
                        continue
                    self.lines_disposition(hw, h, at, computed[at])

        for lid in LD_IDS:
            e = next((x for x in self.entries if x.get("id") == lid), {})
            for a in e.get("aspect", []):
                missing = sorted(set(self.t["corpus"]) - coverage.get(f"{lid}/{a.get('id')}", set()))
                if missing:
                    self.add("SEARCH", f"aspect {lid}/{a.get('id')} has no search of {missing}")

    def verified_issues_of(self, uid: str) -> set:
        s = self.t["source"].get(uid) or {}
        snap = self.snap.get(s.get("snapshot")) or {}
        return {f"{snap.get('repo')}#{snap.get('number')}"}

    def lines_disposition(self, hw: str, h: dict, at: str, matched: list) -> None:
        c = self.search_counts
        if h.get("lines") != matched or "reason" in h or "fcp" in h:
            self.add("SEARCH", f"{hw}: records lines {h.get('lines')}; the pattern matches {matched}, and a file hit's reasons are per line (uncited groups)")
        covered = set()
        for uid in h.get("use", []):
            loc = self.locator.get(uid)
            inside = {n for n in matched if loc and loc[1] == at and loc[2] <= n <= loc[3]}
            if loc and loc[1] == at and not inside:
                self.add("SEARCH", f"{hw}: lists {uid}, which contains none of the matched lines")
            covered |= inside
        grouped: dict[int, int] = {}
        for gi, g in enumerate(h.get("uncited", [])):
            if not isinstance(g, dict) or set(g) != {"lines", "reason"} or not g["lines"] or not str(g["reason"]).strip():
                self.add("SEARCH", f"{hw}: uncited[{gi}] is {{lines, reason}}, both non-empty")
                continue
            for n in g["lines"]:
                if n not in matched or n in covered or n in grouped:
                    self.add("SEARCH", f"{hw}: uncited[{gi}] lists line {n}, which is not matched or already has a disposition; a line has one")
                grouped.setdefault(n, gi)
        missing = [n for n in matched if n not in covered and n not in grouped]
        if missing:
            self.add("SEARCH", f"{hw}: matches lines {missing}, which no citation covers and no reason disposes of")
        c["lines"] += len(matched)
        c["lines_cited"] += len(covered)
        c["lines_reason"] += len(set(grouped) - covered)

    def opsem(self) -> None:
        universe = {at for at, it in self.records.items() if it.get("repo") == "rust-lang/unsafe-code-guidelines" or "T-opsem" in it.get("labels", [])}
        for at in sorted(universe ^ set(self.t["decision"])):
            self.add("DECISIONS", f"{at} {'is an opsem record of the decision index with no disposition' if at in universe else 'is dispositioned but is not an opsem record of the index'}")
        for at, d in self.t["decision"].items():
            for uid in d.get("use", []):
                if self.locator.get(uid, ("",))[0] != "web" or at not in self.verified_issues_of(uid):
                    self.add("DECISIONS", f"decision {at}: is cited by {uid}, which is not a verified team-decision row of it")
            if at in universe:
                self.dispositioned.add(at)
                self.fcp_disposition(f"decision {at}", d, at, "DECISIONS")

    # ---- rule, owner questions, ratification, deferred checks
    def rule_rows(self) -> None:
        self.design_row("precedence_rule", self.rule)
        self.note_oq(self.rule.get("owner_questions"), RULE_ID)
        for qid, q in self.t["rule_quote"].items():
            if not re.fullmatch(r"P\d+", qid):
                self.add("TABLE", f"rule_quote {qid}: an id is P<n>")
            if self.cite("DESIGN-EXIT", f"rule_quote {qid}", q["ref"], q["quote"]):
                self.quotes[f"{RULE_ID}.{qid}"] = C.collapse(q["quote"])
        self.pending = 0
        if set(self.t["ratify"]) != self.od5["items"]:
            self.add("RATIFY", f"ratify items {sorted(self.t['ratify'])} are not the OD-5 row's {sorted(self.od5['items'])}")
        for item, r in self.t["ratify"].items():
            where = f"ratify {item}"
            parts = self.cite("RATIFY", where, r["recommendation_quote"].get("ref"), r["recommendation_quote"].get("quote"), owner=item) \
                if isinstance(r["recommendation_quote"], dict) else None
            if r["blocks"] != self.od5["blocks"].get(item) or parts is None or parts["start"] != self.od5["line"]:
                self.add("RATIFY", f"{where}: blocks is the OD-5 row's stage and recommendation_quote quotes the OD-5 row")
            if r["ruling"] not in RULINGS or (r["ruling"] != "pending") != bool(r.get("ruling_record")):
                self.add("RATIFY", f"{where}: ruling in {RULINGS}, with a ruling_record exactly when ruled")
            self.pending += r["ruling"] == "pending"
            self.note_oq(r.get("owner_questions"), where)
            for ref in r["evidence"]:
                if ref not in self.ids:
                    self.add("EVIDENCE", f"{where}: cites {ref}, which is not a source, related or rule quote id")
        want = STATE_DRAFT if self.pending or not self.t["ratify"] else STATE_RULED
        if self.data.get("state") != want:
            self.add("STATE", f"state is {self.data.get('state')!r}; with {self.pending} ruling(s) pending it is {want!r}")

    def owner_questions(self) -> None:
        for qid, q in self.t["owner_question"].items():
            where = f"owner_question {qid}"
            if q["kind"] not in OQ_KINDS or len(q["options"]) < 2 or not re.fullmatch(r"OQ-\d+", qid):
                self.add("OQ", f"{where}: an id OQ-<n>, a kind in {OQ_KINDS} and at least two options")
            if qid not in self.oq_refs:
                self.add("OQ", f"{where}: no entry, aspect, rule or ratification item references it")
            for ref in q["evidence"]:
                if ref not in self.ids:
                    self.add("EVIDENCE", f"{where}: cites {ref}, which is not a source, related or rule quote id")
        for ref, who in sorted(self.oq_refs.items()):
            if ref not in self.t["owner_question"]:
                self.add("OQ", f"{', '.join(who)} reference {ref}, which is not defined")

    def deferred(self) -> None:
        for did, row in self.t["deferred_check"].items():
            for name in row["fields"]:
                kind, _, key = str(name).partition(".")
                if kind not in ROWS or key not in ROWS[kind][0]:
                    self.add("DEFERRED", f"deferred_check {did}: {name!r} is not a <row kind>.<field> of the table")
            cited = [x.get("quote", "") for x in row["cites"] if isinstance(x, dict) and self.cite("DEFERRED", f"deferred_check {did}", x.get("ref"), x.get("quote"))]
            for exit_id in row["checked_by"]:
                if exit_id not in self.exits or not any(f"**{exit_id}**" in q for q in cited):
                    self.add("DEFERRED", f"deferred_check {did}: checked_by {exit_id!r} is a design exit quoted by one of its citations")

    def stale(self) -> None:
        """An issue snapshot no source or RFC record cites, and an RFC record no ranked source names, are stale."""
        for rel, row in self.t["snapshot"].items():
            if row["kind"] == "issue" and not any(s.get("snapshot") == rel for s in self.t["source"].values()) \
                    and not any(r.get("tracking_snapshot") == rel for r in self.t["rfc"].values()):
                self.add("SNAPSHOT", f"snapshot {rel}: nothing cites it (stale)")
        named = {str(s.get("rfc")) for s in self.t["source"].values() if s.get("kind") == "rfc"}
        for number in sorted(set(self.t["rfc"]) - named):
            self.add("RFC", f"rfc {number}: no ranked rfc source names it (stale); an [[rfc]] record is an RFC the ledger cites")

    def mentions(self) -> None:
        for line, lid in self.mention_lines:
            ranges = self.design_ranges.get(lid, []) + self.design_ranges.get("*", [])
            if lid not in LD_IDS or not any(a <= line <= b for a, b in ranges):
                self.add("DESIGN-EXIT", f"design:{line} names {lid}, but no verified design quote of {lid} or of the rule covers it")

    # ---- PROSE
    def prose(self, where: str, text: str, doc: bool = False) -> None:
        for m in ID_TOKEN.finditer(text):
            if m.group(1) not in self.ids:
                self.add("PROSE", f"{where}: [{m.group(1)}] is not a source, related or rule quote id")
        for m in SQUOTE.finditer(text):
            fragment = C.collapse(next(g for g in m.groups() if g is not None))
            attributed = re.match(r"\s*\[((?:LD-\d+|I-PRECEDENCE)\.[A-Z]+\d+)\]", text[m.end():])
            if not any(fragment in q for q in self.verified_quotes) or (attributed and fragment not in self.quotes.get(attributed.group(1), "")):
                self.add("PROSE", f"{where}: the quoted {fragment[:60]!r} is not text of {'[' + attributed.group(1) + ']' if attributed else 'a verified quote'}")
        stripped = C.PROSE_CITATION.sub(" ", text) if doc else text  # a document's line citations are common.check_prose's
        for m in () if doc else DESIGN_TOKEN.finditer(text):
            if not all(any(x <= n <= y for rs in self.design_ranges.values() for x, y in rs) for n in range(int(m.group(1)), int(m.group(2) or m.group(1)) + 1)):
                self.add("PROSE", f"{where}: {m.group(0)} is not inside a verified design quote")
        for m in () if doc else LINE_TOKEN.finditer(text):
            self.add("PROSE", f"{where}: {m.group(0)!r} is a line citation no predicate checks; cite a row by [ID]")
        for m in RFC_TOKEN.finditer(text):
            if m.group(1).lstrip("0") not in {str(n) for n in self.t["rfc"]}:
                self.add("PROSE", f"{where}: RFC {m.group(1)} has no [[rfc]] record")
        for m in OQ_TOKEN.finditer(text):
            if m.group(0) not in self.t["owner_question"]:
                self.add("PROSE", f"{where}: {m.group(0)} is not an owner question")
        for m in ISSUE_TOKEN.finditer(stripped):
            known = f"{m.group(1)}#{m.group(2)}" in self.verified_issues if m.group(1) else any(i.endswith(f"#{m.group(3)}") for i in self.verified_issues)
            if not known:
                self.add("PROSE", f"{where}: {m.group(0)} is not a verified snapshot, RFC, tracking issue or dispositioned decision record")
        for m in RULE_TOKEN.finditer(text):
            if not self.resolver.spans("reference").get(m.group(1)):
                self.add("PROSE", f"{where}: r[{m.group(1)}] is not a rule of the pinned Reference")
        for m in URL_TOKEN.finditer(stripped):
            if m.group(0).rstrip(".,;:") not in self.verified_urls:
                self.add("PROSE", f"{where}: {m.group(0)} is not the URL of a verified source")

    def table_prose(self) -> None:
        def walk(where, value, key=""):
            if isinstance(value, dict):
                for k, v in value.items():
                    walk(where, v, k)
            elif isinstance(value, list):
                for v in value:
                    walk(where, v, key)
            elif isinstance(value, str) and key in PROSE_KEYS:
                self.prose(where, value)
        for kind, key, row, _ in rows_of(self.data):
            walk(f"{kind} {key}", judgment_content(kind, row))

    # ---- counts, blocks, document
    def summary(self) -> None:
        aspects = [(f"{lid}/{aid}", c["row"], c) for lid, x in self.computed.items() for aid, c in x["aspects"].items()]
        labels = [c["label"] for _, _, c in aspects]
        conflicts = sorted(i for _, _, c in aspects for i in c["conflicts"])
        divergences = sorted(i for _, _, c in aspects for i in c["divergences"])
        s = self.search_counts
        self.counts.update({
            "entries": len(self.computed), "entries_by_status": {k: sum(1 for e in self.entries if e.get("status") == k) for k in ("Required", "Recorded")},
            "entries_by_label": {k: sum(1 for x in self.computed.values() if x["label"] == k) for k in LABELS},
            "aspects": len(aspects), "aspects_by_label": {k: labels.count(k) for k in LABELS},
            "aspects_by_resolution": {k: sum(1 for _, _, c in aspects if c["resolution"] == k) for k in RESOLUTIONS},
            "de_facto_entries": sum(1 for x in self.computed.values() if x["label"] in V11), "de_facto_aspects": sum(labels.count(k) for k in V11),
            "compat_candidates": sum(1 for _, _, c in aspects if c["compat_candidate"]),
            "sources": sum(self.source_counts["rank"].values()), "sources_by_rank": dict(sorted(self.source_counts["rank"].items())),
            "sources_by_kind": dict(sorted(self.source_counts["kind"].items())), "readings_by_role": {r: self.source_counts["role"].get(r, 0) for r in ROLES},
            "related": len(self.t["related"]),
            "team_decisions": len({(r.get("snapshot"), r.get("fcp_complete")) for r in self.t["source"].values() if r.get("kind") == "team-decision"}),
            "rfcs": len(self.t["rfc"]), "rfcs_by_stabilization": dict(sorted(self.stabilizations.items())),
            "issue_snapshots": sum(1 for r in self.t["snapshot"].values() if r["kind"] == "issue"),
            "index_records": len(self.records), "index_by_fcp": {k: sum(1 for v in self.fcp_status.values() if v == k) for k in FCP_STATUSES},
            "opsem_dispositioned": len(self.t["decision"]), "records_dispositioned": len(self.dispositioned),
            "records_dispositioned_by_fcp": {k: sum(1 for at in self.dispositioned if self.fcp_status.get(at) == k) for k in FCP_STATUSES},
            **{f"search_{k}": v for k, v in s.items()}, "corpora": len(self.t["corpus"]),
            "conflicts": conflicts, "divergences": divergences, "od5_items": len(self.od5["items"]), "rulings_pending": self.pending,
            "owner_questions": len(self.t["owner_question"]), "deferred_checks": len(self.t["deferred_check"]),
        })
        self.aspect_rows = aspects

    def render(self) -> dict[str, str]:
        c, b = self.counts, {}

        def fmt(d):
            return ", ".join(f"{k} {n}" for k, n in d.items())
        b["ld-counts"] = "\n".join(["```text",
            f"entries: {c['entries']} ({fmt(c['entries_by_status'])})", f"entries by label: {fmt(c['entries_by_label'])}",
            f"aspects: {c['aspects']}; by label: {fmt(c['aspects_by_label'])}", f"aspects by resolution: {fmt(c['aspects_by_resolution'])}",
            f"de-facto (V11, de-facto + de-facto-open): entries {c['de_facto_entries']}, aspects {c['de_facto_aspects']}",
            f"compat (V11): entries {c['entries_by_label']['compat']}; compat candidates (rank-1 text contrary, rustc test pins): {c['compat_candidates']}",
            f"ranked sources: {c['sources']}; by rank: " + ", ".join(f"rank {k} {n}" for k, n in c["sources_by_rank"].items()),
            f"ranked sources by kind: {fmt(c['sources_by_kind'])}", f"source readings by role (source x aspect): {fmt(c['readings_by_role'])}",
            f"related (unranked) rows: {c['related']}",
            f"team decisions (completed FCPs cited): {c['team_decisions']}; RFC records: {c['rfcs']} ({fmt(c['rfcs_by_stabilization'])}); issue snapshots: {c['issue_snapshots']}",
            f"decision index: {c['index_records']} records; by rfcbot completion: {fmt(c['index_by_fcp'])}",
            f"decision records dispositioned: {c['records_dispositioned']} ({fmt(c['records_dispositioned_by_fcp'])}); opsem records dispositioned: {c['opsem_dispositioned']}",
            f"declared search scopes: {c['corpora']}; searches: {c['search_searches']}; hits (files or decision records) {c['search_hits']} (cited {c['search_cited']}, not cited {c['search_uncited']})",
            f"matched lines: {c['search_lines']} (inside a citation {c['search_lines_cited']}, with a reason of their own {c['search_lines_reason']})",
            f"precedence conflicts: {len(c['conflicts'])}" + (f" ({', '.join(c['conflicts'])})" if c["conflicts"] else "") + f"; rustc divergences: {len(c['divergences'])}",
            f"OD-5 items: {c['od5_items']}; rulings pending: {c['rulings_pending']}; owner questions: {c['owner_questions']}; deferred checks: {c['deferred_checks']}",
            "```"])
        groups = [
            ("Precedence conflicts: a contrary source with no settling source ranked above it", lambda a, x: x["conflicts"], lambda a, x: f"contrary {', '.join(x['conflicts'])}"),
            ("rustc divergences: a rustc test contrary to the decision", lambda a, x: x["divergences"], lambda a, x: f"contrary {', '.join(x['divergences'])}"),
            ("Compat candidates: a rank-1 text contrary and a rustc test that pins the decision", lambda a, x: x["compat_candidate"], lambda a, x: f"label `{x['label']}`"),
            ("Contrary texts set aside only by an open text at the same locator (owner ruling needed)", lambda a, x: x["neutralized"], lambda a, x: f"neutralized {', '.join(x['neutralized'])}"),
            ("Trust choices: rank-1 or rank-2 sources address the aspect and nothing settles it", lambda a, x: x["label"] == "trust-choice", lambda a, x: f"resolution `{x['resolution']}`"),
            ("Open questions answered deterministically instead of by Choose", lambda a, x: "open-reading" in x["required_oq_kinds"], lambda a, x: f"resolution `{x['resolution']}`, label `{x['label']}`"),
            ("Modelled as Choose or as a parameter, citing the text that leaves the choice open", lambda a, x: x["resolution"] == "choose", lambda a, x: f"`{a.get('modelling')}`, open text {', '.join(a.get('open_text', []))}"),
            ("Settled only by a rank-2 model, with no recorded team decision", lambda a, x: x["label"] == "team-model", lambda a, x: "MiniRust or a-mir-formality text"),
            ("De-facto: rank 3 is the only source", lambda a, x: x["label"] == "de-facto", lambda a, x: "pinned by rustc tests"),
            ("De-facto-open: only rustc's tests settle it, and a rank-1 or rank-2 text leaves it open", lambda a, x: x["label"] == "de-facto-open", lambda a, x: "pinned by rustc tests"),
            ("Compat: rustc's behavior adopted over a rank-1 text", lambda a, x: x["label"] == "compat", lambda a, x: f"upstream {a.get('upstream')}"),
        ]
        b["ld-findings"] = "\n".join(
            f"* **{heading}:** " + ("; ".join(f"`{k}` ({detail(a, x)}; {', '.join(a.get('owner_questions', [])) or 'no owner question'})"
                                             for k, a, x in self.aspect_rows if test(a, x)) or "none") + "."
            for heading, test, detail in groups)
        out = []
        for rel, row in self.t["snapshot"].items():
            snap = self.snap.get(rel, {})
            if row["kind"] == "index":
                out.append(f"* `{rel}`: decision index, queries " + "; ".join(f"`{q.get('q')}` ({q.get('total_count')})" for q in snap.get("queries", []))
                           + f"; retrieved {row['retrieved']}; `{row['sha256']}`")
            elif row["kind"] == "fcp":
                out.append(f"* `{rel}`: rfcbot's completion notices for each of the {len(snap.get('records', []))} records of `{row['index']}` "
                           f"({sum(len(r.get('notices', [])) for r in snap.get('records', []))} notices); retrieved {row['retrieved']}; `{row['sha256']}`")
            else:
                out.append(f"* `{rel}`: {row['issue']}, \"{md((snap.get('issue') or {}).get('title', ''))}\"; comments {', '.join(map(str, row['comments'])) or 'none'}"
                           f"{'; issue body' if row['issue_body'] else ''}; schema {row['schema']}; retrieved {row['retrieved']}; `{row['sha256']}`")
        b["ld-snapshots"] = "\n".join(out)
        b["ld-corpora"] = "\n".join(["| Scope | Read from | Files | Lines | Ranked kinds it admits |", "|---|---|---|---|---|"] + [
            f"| `{n}` | {'the pinned decision index' if r['source'] == 'decisions' else ('this repository at HEAD' if r['source'] == 'rustc' else 'the ' + str(r['source']) + ' pin')} | "
            f"{', '.join('`' + str(i['path']) + '`…`' + str(i['suffix']) + '`' for i in r['include']) or 'record titles'} | {r['lines']} | {', '.join(r['kinds'])} |"
            for n, r in self.t["corpus"].items()] + [""] + [f"* `{n}`: {r['why']}" for n, r in self.t["corpus"].items()])
        b["ld-deferred"] = "\n".join(f"* **{d}** (checked by {', '.join(r['checked_by'])}; fields {', '.join(f'`{x}`' for x in r['fields'])}). {r['claim']} "
                                     f"*Replaces:* {r['replaces']}." for d, r in self.t["deferred_check"].items())
        titles = {e.get("id"): e.get("title") for e in self.entries} | {RULE_ID: self.rule.get("title")}
        b["ld-ratify"] = "\n\n".join(
            f"### {item}: {titles.get(item)}\n\n* **Blocks:** stage {r['blocks']} and E0.8. **Ruling:** {r['ruling']}.\n* **In plain terms.** {r['summary']}\n"
            f"* **Recommendation** (OD-5, {r['recommendation_quote']['ref']}): \"{md(r['recommendation_quote']['quote'])}\". {r['recommendation']}\n"
            f"* **Strongest argument against.** {r['strongest_argument_against']}"
            + (f"\n* **Questions this ruling must also settle:** {', '.join(r['owner_questions'])}." if r.get("owner_questions") else "")
            for item, r in self.t["ratify"].items())
        b["ld-owner-questions"] = "\n\n".join(
            f"### {q}: {r['title']} ({r['kind']})\n\n{r['question']}\n\n" + "\n".join(f"{k}. {opt}" for k, opt in enumerate(r["options"], 1))
            + f"\n\n*Consequence.* {r['consequence']}\n\n*Applies to (computed):* {', '.join(f'`{x}`' for x in sorted(w for w in self.oq_refs.get(q, []) if not w.startswith('ratify '))) or 'ratification items only'}."
            f" *Evidence:* {', '.join(r['evidence'])}." for q, r in self.t["owner_question"].items())
        b["ld-rule-quotes"] = "\n\n".join(f"> **[{RULE_ID}.{q}]** {r['ref']}\n>\n> {C.collapse(r['quote'])}" for q, r in self.t["rule_quote"].items())
        b["ld-rfcs"] = "\n".join(
            f"* RFC {r['number']}, `{r['file']}`, tracking issue {r['tracking_issue']}; stabilization `{r['stabilization']}`"
            + (f", {r['evidence']['ref']}: \"{md(r['evidence']['quote'])}\"" if r.get("evidence", {}).get("ref") else f", \"{md(r['evidence']['quote'])}\"" if r.get("evidence") else "")
            + (f"; tracking snapshot `{r['tracking_snapshot']}`" if r.get("tracking_snapshot") else "") + "." + (f" {r['note']}" if r.get("note") else "")
            for r in self.t["rfc"].values())
        b["ld-entries"] = "\n\n".join(self.render_entry(e) for e in self.entries if e.get("id") in self.computed)
        b["ld-decisions"] = "\n".join(
            f"* `{at}` \"{md(self.records.get(at, {}).get('title', ''))}\" (labels {', '.join(x for x in self.records.get(at, {}).get('labels', []) if DECISION_LABEL.match(x))}): "
            f"{self.fcp_text(at)}; {self.use_text(d)}" for at, d in self.t["decision"].items())
        return b

    def fcp_text(self, at: str) -> str:
        notices = self.notices.get(at, [])
        if not notices:
            return "no rfcbot completion notice"
        first = next((n for n in notices if before_pin(n["created_at"], self.pins)), notices[0])
        return f"FCP completed {first['created_at']} ({'before' if before_pin(first['created_at'], self.pins) else 'after'} the alignment timestamp; rfcbot notice {first['id']})"

    @staticmethod
    def use_text(d: dict) -> str:
        if d.get("use"):
            return f"cited by {', '.join(d['use'])}" + (f": {d['reason']}" if d.get("reason") else ".")
        return f"not cited: {d['reason']}" if d.get("reason") else "not a rank-2 source at the pin."

    def render_entry(self, e: dict) -> str:
        lid, comp = e["id"], self.computed[e["id"]]
        w = [f"### {lid}: {e['title']}", "",
             f"* **Status:** {e['status']}{' (OD-5)' if e.get('od5') else ''}. **Label:** `{comp['label']}`.",
             f"* **Question.** {e['question']}", f"* **Decision (design:{e['design_line']}, quoted).** \"{md(e['design_recommendation'])}\"",
             f"* **What it decides.** {e['decision_summary']}"]
        if e.get("owner_questions"):
            w.append(f"* **Owner questions:** {', '.join(e['owner_questions'])}.")
        w += ["", "| Aspect | Decides | Label | Resolution | Modelling | Conflicts | Owner questions |", "|---|---|---|---|---|---|---|"]
        for a in self.ok(e, "aspect"):
            x = comp["aspects"][a["id"]]
            w.append(f"| `{a['id']}` | {md(a['decides'])} | `{x['label']}` | `{x['resolution']}` | `{a['modelling']}` | "
                     f"{', '.join(x['conflicts'] + [d + ' (rustc)' for d in x['divergences']]) or '—'} | {', '.join(a.get('owner_questions', [])) or '—'} |")
        w += [""] + [f"*{a['id']}:* {a['note']}\n" for a in self.ok(e, "aspect") if a.get("note")] + ["**Ranked sources.**", ""]
        for s in self.ok(e, "source"):
            roles = "; ".join(f"`{r}` for {a}" for a, r in s["roles"].items()) if isinstance(s.get("roles"), dict) else f"`{s.get('role')}` ({', '.join(s['aspects'])})"
            where = (f"T-{s['team']} decision ({s['disposition']} FCP), {s['url']} (FCP completed: comment {s['fcp_complete']}; snapshot `{s['snapshot']}`)"
                     if s["kind"] == "team-decision" else f"{s['kind']} `{s['ref']}`" + (f", r[{s['rule']}]" if s.get("rule") else "")
                     + (f", `{s['paragraph']}`" if s.get("paragraph") else "") + (f", RFC {s['rfc']} section \"{s['section']}\"" if s.get("rfc") else "")
                     + (f", restrictions: {', '.join(f'`{x}`' for x in s['restrictions']) or 'none'}" if "restrictions" in s else ""))
            w.append(f"* **[{s['id']}]** rank {s['rank']}, {roles}{'; open_by ' + str(s['open_by']) if s.get('open_by') else ''}; "
                     f"{where}: \"{md(s['quote'])}\"" + (f" — {s['note']}" if s.get("note") else ""))
        if self.ok(e, "related"):
            w += ["", "**Related, unranked** (verified locators; not precedence sources).", ""]
            w += [f"* **[{r['id']}]** {r['kind']} `{r['ref']}`{', r[' + str(r['rule']) + ']' if r.get('rule') else ''}: \"{md(r['quote'])}\" — {r['why_unranked']}" for r in self.ok(e, "related")]
        w += ["", "**Alternatives considered and what each costs.**", ""]
        for alt in self.ok(e, "alternative"):
            tail = "; ".join(x for x in ("*Design text:* " + "; ".join(f"{q['ref']}, \"{md(q['quote'])}\"" for q in alt.get("design_quote", [])) if alt.get("design_quote") else "",
                                         f"*Evidence:* {', '.join(alt['evidence'])}" if alt.get("evidence") else "") if x)
            w.append(f"* **{alt['name']}.** {alt['cost']}" + (f" ({tail})" if tail else ""))
        w += ["", "**Later exits that confirm or revise it.**", ""]
        w += [f"* {x['id']} ({x['effect']}), {x['ref']}: \"{md(x['quote'])}\"" + (f" — {x['note']}" if x.get("note") else "") for x in self.ok(e, "exit")]
        w += ["", "**What cites it.**", ""] + [f"* {x['what']}: {x['name']}, {x['ref']}: \"{md(x['quote'])}\"" for x in self.ok(e, "cited_by")]
        w += ["", "**Searches of the declared scopes.** Every line a pattern matches is listed and dispositioned; the checker re-runs each pattern.", ""]
        for sr in self.ok(e, "search"):
            hits = self.ok(sr, "hit")
            w.append(f"* **[{sr['id']}]** `{sr['corpus']}`, pattern `{sr['pattern']}`, aspects {', '.join(sr['aspects'])}: {len(hits)} hit{'s' if len(hits) != 1 else ''}.")
            for h in hits:
                if sr["corpus"] == "decisions":
                    w.append(f"  * `{h['at']}` \"{md(self.records.get(h['at'], {}).get('title', ''))}\": {self.fcp_text(h['at'])}; {self.use_text(h)}")
                    continue
                w.append(f"  * `{h['at']}` {lines_text(h.get('lines', []))}: {'cited by ' + ', '.join(h['use']) if h.get('use') else 'not cited'}.")
                w += [f"    * {lines_text(g['lines'])}: {g['reason']}" for g in h.get("uncited", [])]
        return "\n".join(w)

    def document(self, blocks: dict) -> dict:
        path = self.o.doc or self.o.repo / DOC_REL
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            self.add("DOC", f"{path}: {error}")
            return {}
        for name in BLOCKS:
            C.check_block(self.f, "DOC", text, name, blocks[name])
        sections = C.document_judgments(self.f, "DOC", text, generated=BLOCKS)
        for revision in [self.pins.alignment] + [self.pins.sources[name].revision for name in READS]:
            if f"`{revision}`" not in text:
                self.add("DOC", f"the document does not record the pin `{revision}`")
        for jid, body in sections.items():
            if isinstance(body, str):
                self.counts["doc_citations"] = self.counts.get("doc_citations", 0) + C.check_prose(self.f, "DOC", jid, body, self.resolver)
                for m in C.PROSE_CITATION.finditer(body):
                    ref, _, quote = m.group(0).partition(" «")
                    parts = C.parse_ref(ref)
                    if parts and parts["source"] == "design" and self.resolver.check(ref, quote[:-1]) is None:
                        self.design_ranges.setdefault("*", []).append((parts["start"], parts["end"]))
                        self.verified_quotes.append(C.collapse(quote[:-1]))
        self.sections = sections
        return sections


def issue_of_url(url: object) -> str | None:
    m = re.match(r"^https://github\.com/([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)/(?:issues|pull)/(\d+)", str(url or ""))
    return f"{m.group(1)}#{m.group(2)}" if m else None


def before_pin(stamp: object, pins: C.Pins) -> bool:
    when = C.parse_date(stamp)
    return when is not None and when <= C.parse_date(pins.alignment_date)


def collect(options: Options | None = None) -> Result:
    options = options or Options()
    checker = Checker(options)
    result = Result(violations=checker.f.violations, counts=checker.counts)
    if not checker.load():
        return result
    checker.rows()
    checker.parse_design()
    checker.snapshots()
    checker.rfcs()
    checker.corpora()
    checker.entry_rows()
    checker.rule_rows()
    checker.searches()
    checker.opsem()
    checker.owner_questions()
    checker.deferred()
    checker.stale()
    checker.summary()
    result.blocks = checker.render()
    sections = checker.document(result.blocks)
    checker.mentions()
    checker.table_prose()
    for jid, body in sections.items():
        if isinstance(body, str):
            checker.prose(jid, body, doc=True)
    if options.require_ruled:
        c = checker.counts
        if c["rulings_pending"]:
            checker.add("RULING-PENDING", f"{c['rulings_pending']} OD-5 item(s) await the owner's ruling (E0.8)")
        if c["conflicts"] or c["divergences"]:
            checker.add("CONFLICT-UNRULED", f"precedence conflicts {c['conflicts']} and rustc divergences {c['divergences']} remain")
    checker.counts["citations"] = checker.cited
    checker.counts["reviews"] = C.check_reviews(checker.f, options.registry or options.repo / REGISTRY_REL, DELIVERABLE,
                                                judgments(checker.f, checker.table_text, sections), JUDGMENT_KINDS,
                                                options.repo if options.check_history else None, REGISTRY_REL)
    return result


def main(argv: list[str] | None = None) -> int:
    if tomllib is None:
        print("language_decisions: Python 3.11+ (tomllib) is required", file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", type=Path, default=REPO_ROOT)
    for name in ("table", "doc", "registry"):
        parser.add_argument(f"--{name}", type=Path)
    for name in READS:
        parser.add_argument(f"--{name}", type=Path, help=f"the {name} clone")
    parser.add_argument("--require-ruled", action="store_true", help="E0.8's pass line: also fail while rulings are pending or conflicts remain")
    parser.add_argument("--write-blocks", action="store_true", help="rewrite the document's generated blocks")
    args = parser.parse_args(argv)
    options = Options(repo=args.repo, table=args.table, doc=args.doc, registry=args.registry, require_ruled=args.require_ruled,
                      clones={name: getattr(args, name.replace("-", "_")) for name in READS})
    try:
        result = collect(options)
    except (C.MissingClone, C.PinsError) as error:
        print(f"language_decisions: {error}", file=sys.stderr)
        return 2
    if args.write_blocks and result.blocks:
        doc = args.doc or args.repo / DOC_REL
        text = doc.read_text(encoding="utf-8")
        for name in BLOCKS:
            text = C.replace_block(text, name, result.blocks[name])
        doc.write_text(text, encoding="utf-8")
    if result.blocks:
        print("\n".join(result.blocks["ld-counts"].split("\n")[1:-1]))
    if result.violations:
        print(f"\nlanguage_decisions: {len(result.violations)} violation(s)", file=sys.stderr)
        for violation in result.violations:
            print(f"  {violation}", file=sys.stderr)
        return 1
    print(f"\nlanguage_decisions: OK ({result.counts['citations']} citations, {result.counts.get('doc_citations', 0)} document citations, "
          f"{result.counts['reviews']['judgments']} reviewed judgments)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
