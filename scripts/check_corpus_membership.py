#!/usr/bin/env python3
"""check_corpus_membership.py — a pinned corpus must name exactly the documents
its rule selects, in the tree being pushed (CORPUS-MEMBERSHIP-AT-LANDING-1).

Two Rust acceptance gates pin a corpus MEMBERSHIP, and each fails on any
difference in either direction:

  crates/trust-json/tests/corpus_manifest.txt  every tracked `*.json` outside
      `first-party/` and `vendor/`, smaller than 1 MiB; judged by
      `corpus_membership_matches_the_pinned_manifest` in
      crates/trust-json/tests/acceptance_gate.rs
  crates/trust-toml/tests/corpus_manifest.txt  every tracked `*.toml` outside
      `first-party/` and `vendor/`; judged by the test of the same name in
      crates/trust-toml/tests/differential_corpus.rs (which also requires more
      than 1000 pinned documents)

The exactness is the point: a sample that changes underneath its test is not a
pin, and a corpus that quietly SHRINKS reads as a green run. But tracked JSON
and TOML documents are added by ordinary work everywhere (crate fixtures,
`reports/`, `docs/qualification/`), and no landing ran either Rust test, so
dev `main` went red each time one landed without its re-pin (2026-11-10: re-
pinned at +118 and +7, and +24 more JSON within two hours). This row moves the
check to the moment the membership changes: it applies both rules to the PUSHED
tree, from git objects, with no Rust compile (about a second), so a landing
that changes a membership must carry the re-pin in the same push.

WHICH TREE IS JUDGED. With TRUST_PUSHED_REFS set and non-blank (the pre-push
hook and `scripts/land_gate.py push-rows` export git's
`<local_ref> <local_sha> <remote_ref> <remote_sha>` lines) every non-deletion
pushed sha's own tree, read from git objects: never the index or the working
tree. A deletion-only push prints `SKIPPED:`; a malformed line exits 2; a sha
this clone cannot read is a red that is not keyed. With it unset, HEAD's tree
(or `--rev REV`'s), also from objects.

ONE RULE ON THIS SIDE, TIED SO IT CANNOT DRIFT SILENTLY. Each manifest's header
documents its rule as a shell command (its `REGENERATE` block), and the Rust
membership test compares the Rust rule against the body that command printed.
This file implements each rule once (`members_and_findings`) and binds itself
to the header two ways:
  * every run requires the pushed header's REGENERATE block to be byte for byte
    the command in CORPORA (else `RULE-DOCUMENTED-DIFFERENTLY` /
    `RULE-UNDOCUMENTED`), so a rule edited in the header goes red here at the
    landing that edits it, until this file is taught the new rule;
  * scripts/tests/check_corpus_membership_test.py runs that documented command
    and this rule on the same trees (this checkout's, and adversarial ones) and
    requires the same set.
Since this rule and the Rust rule are both compared against the same body, a
Rust rule that drifted from this one turns one of the two red on the next run
of the Rust test; it cannot stay green beside this row.

WHERE A GIT-OBJECT READING CANNOT ANSWER FOR THE CHECKOUT, IT REFUSES (keyed,
so the hook's INHERITED-RED still applies): the documented rules read the
working tree (`stat -f %z` for the size cap; `std::fs::metadata`, which follows
links, in the Rust test) and the manifest is one path per line, read as Rust
reads it (lines trimmed of Unicode white space, `#` lines skipped).
  * UNPINNABLE <why> <path>: a selected path the manifest cannot carry: not
    UTF-8 (the Rust tests panic on the listing), a line break, leading white
    space, or a leading `#`; for TOML also any name `git ls-files` C-quotes
    (`core.quotepath`), whose spelling then depends on the clone's config.
  * NON-REGULAR <mode> <path>: a `*.json` symlink or gitlink; the shell rule
    stats the link, the Rust rule its target.
  * CHECKOUT-CONVERTED <attribute> <path>: a `*.json` whose checkout bytes the
    tree's attributes change (filter, working-tree-encoding, ident; eol=crlf
    only where it can carry the size across the cap). The clone's own
    info/attributes and core.autocrlf are the clone's, not the tree's.

FINDING KEYS. A red prints one `FINDING: <key>` per cause and `FINDINGS:
complete` when every cause was keyed, so the hook and `land_gate.py push-rows`
grade a red the destination already carries INHERITED (an unrelated landing is
not blocked) and FAIL a push that adds one. A key names the corpus and the
cause, never the push:
  <corpus> NEW <path>                 selected by the rule, not pinned
  <corpus> GONE <path>                pinned, not selected
  <corpus> UNPINNABLE|NON-REGULAR|CHECKOUT-CONVERTED ... (above)
  <corpus> MANIFEST-ABSENT | MANIFEST-NOT-A-FILE <mode> | MANIFEST-NOT-UTF-8
  <corpus> RULE-UNDOCUMENTED | RULE-DOCUMENTED-DIFFERENTLY <sha256 prefix>
  trust-toml PINNED-AT-MOST <floor> <count>
A path is shown with every control character, backslash and byte that is not
UTF-8 written `\\xNN`.

REPAIR. `python3 scripts/check_corpus_membership.py --write` rewrites the body
of each manifest whose membership moved, from this checkout's INDEX (a
`git write-tree`) under the same rule, keeping the header byte for byte and
writing the body in byte order. It refuses every other finding. Read the diff
(a GONE path is a document the corpus loses), add a dated line to the header
naming the change, and commit it with the change that moved the membership.

Usage:
    scripts/check_corpus_membership.py              # the push, else HEAD
    scripts/check_corpus_membership.py --rev REV    # one revision's tree
    scripts/check_corpus_membership.py --write      # re-pin from the index

Exit codes: 0 every membership matches (or nothing pushed); 1 a red (keyed or
not); 2 usage, or a malformed TRUST_PUSHED_REFS.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

ROOT = Path(__file__).resolve().parents[1]
SIZE_CAP = 1 << 20
EXCLUDED_PREFIXES = (b"first-party/", b"vendor/")
REGENERATE_MARK = "# REGENERATE (and read the diff before committing it):"
WRITE_COMMAND = "python3 scripts/check_corpus_membership.py --write"
HEX_SHA = re.compile(r"^(?:[0-9a-f]{40}|[0-9a-f]{64})$")
ZERO_SHA = re.compile(r"^0+$")
REGULAR_MODES = ("100644", "100755")

# What git must not take from the caller's environment (as scripts/lib/
# land_select.py's GIT_ENV_DROPPED): a hook's repository-local variables would
# choose another repository's objects, and the pathspec switches change what a
# pattern matches. Replace objects are never read.
GIT_ENV_DROPPED = frozenset({
    "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_CONFIG", "GIT_CONFIG_PARAMETERS", "GIT_CONFIG_COUNT",
    "GIT_OBJECT_DIRECTORY", "GIT_DIR", "GIT_WORK_TREE", "GIT_IMPLICIT_WORK_TREE", "GIT_GRAFT_FILE",
    "GIT_INDEX_FILE", "GIT_NO_REPLACE_OBJECTS", "GIT_REPLACE_REF_BASE", "GIT_PREFIX", "GIT_SHALLOW_FILE",
    "GIT_COMMON_DIR", "GIT_LITERAL_PATHSPECS", "GIT_GLOB_PATHSPECS", "GIT_NOGLOB_PATHSPECS",
    "GIT_ICASE_PATHSPECS", "GIT_ATTR_SOURCE"})
GIT_CONFIG_INDEXED = re.compile(r"GIT_CONFIG_(?:KEY|VALUE)_\d+$")

# Rust's `char::is_whitespace` (Unicode White_Space), which `str::trim` strips.
# Python's own str.strip() also strips U+001C..U+001F, which Rust keeps.
RUST_WHITESPACE = ("\t\n\x0b\x0c\r \x85\xa0 " + "".join(chr(c) for c in range(0x2000, 0x200B))
                   + "    　")


@dataclass(frozen=True)
class Corpus:
    name: str
    manifest: str
    suffix: bytes
    size_cap: Optional[int]  # members are strictly smaller; None: no cap
    quoted_listing: bool     # the rule lists with `git ls-files` WITHOUT -z, so git C-quotes some names
    pinned_floor: int        # the Rust membership test also requires more pinned paths than this; 0: none
    documented: str          # the header's REGENERATE block, byte for byte
    rust_test: str


CORPORA: Tuple[Corpus, ...] = (
    Corpus(
        "trust-json", "crates/trust-json/tests/corpus_manifest.txt", b".json", SIZE_CAP, False, 0,
        r"""git ls-files -z -- '*.json' \
  | tr '\0' '\n' \
  | grep -v '^first-party/' | grep -v '^vendor/' \
  | while read -r f; do [ "$(stat -f %z "$f")" -lt 1048576 ] && echo "$f"; done \
  | sort""",
        "crates/trust-json/tests/acceptance_gate.rs: corpus_membership_matches_the_pinned_manifest"),
    Corpus(
        "trust-toml", "crates/trust-toml/tests/corpus_manifest.txt", b".toml", None, True, 1000,
        "git ls-files -- '*.toml' | grep -v '^first-party/' | grep -v '^vendor/' | sort",
        "crates/trust-toml/tests/differential_corpus.rs: corpus_membership_matches_the_pinned_manifest"),
)


class GateError(Exception):
    """A tree, object or attribute this clone cannot read: a red with no key."""


@dataclass(frozen=True)
class Entry:
    mode: str
    oid: str
    size: Optional[int]  # None for a gitlink
    path: bytes


@dataclass
class Verdict:
    corpus: Corpus
    pinned: int = 0
    selected: int = 0
    members: List[str] = field(default_factory=list)
    new: List[str] = field(default_factory=list)
    gone: List[str] = field(default_factory=list)
    findings: List[str] = field(default_factory=list)  # keys, corpus name included
    notes: List[str] = field(default_factory=list)     # why each non-NEW/GONE finding is one

    @property
    def blocking(self) -> List[str]:
        """Findings a re-pin cannot clear."""
        prefix = (f"{self.corpus.name} NEW ", f"{self.corpus.name} GONE ")
        return [k for k in self.findings if not k.startswith(prefix)]


# ---------------------------------------------------------------------------
# Reading the subject from git objects
# ---------------------------------------------------------------------------

def git_env() -> Dict[str, str]:
    env = {k: v for k, v in os.environ.items() if k not in GIT_ENV_DROPPED and not GIT_CONFIG_INDEXED.match(k)}
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env["GIT_ATTR_NOSYSTEM"] = "1"  # the tree's attributes, not this machine's
    return env


def git(root: Path, args: Sequence[str], stdin: Optional[bytes] = None) -> bytes:
    proc = subprocess.run(["git", "--no-replace-objects", "-C", str(root), *args], input=stdin,
                          capture_output=True, env=git_env())
    if proc.returncode != 0:
        said = (proc.stderr.decode("utf-8", "replace").strip().splitlines() or [f"exit {proc.returncode}"])[-1]
        raise GateError(f"`git {' '.join(args[:3])}` failed: {said}")
    return proc.stdout


def tree_entries(root: Path, tree: str) -> List[Entry]:
    """Every entry of `tree` whose path ends in a corpus suffix (case as
    written: git's `*.json` pathspec is case-sensitive)."""
    suffixes = tuple(c.suffix for c in CORPORA)
    out: List[Entry] = []
    for record in git(root, ["ls-tree", "-r", "-z", "--full-tree", "-l", tree]).split(b"\0"):
        if not record:
            continue
        meta, tab, path = record.partition(b"\t")
        fields = meta.split()
        if not tab or len(fields) != 4:
            raise GateError(f"unreadable `git ls-tree` record {record[:80]!r}")
        if not path.endswith(suffixes):
            continue
        mode, _kind, oid, size = (f.decode("ascii") for f in fields)
        out.append(Entry(mode, oid, None if size == "-" else int(size), path))
    return out


def manifest_blob(root: Path, tree: str, manifest: str) -> Tuple[Optional[bytes], Optional[str]]:
    """(the manifest's bytes, None) or (None, the finding's kind and detail)."""
    listing = git(root, ["ls-tree", "-z", "--full-tree", tree, "--", manifest]).split(b"\0")
    rows = [r for r in listing if r]
    if not rows:
        return None, "MANIFEST-ABSENT"
    mode, kind, oid = rows[0].partition(b"\t")[0].decode("ascii").split()
    if kind != "blob" or mode not in REGULAR_MODES:
        return None, f"MANIFEST-NOT-A-FILE {mode}"
    return git(root, ["cat-file", "blob", oid]), None


def converting_attributes(root: Path, tree: str, paths: Sequence[bytes]) -> Dict[bytes, Dict[str, str]]:
    """The checkout-conversion attributes the tree's .gitattributes give each
    path (`git check-attr --source`; the global attributes file and the
    system's are not read)."""
    if not paths:
        return {}
    names = ("filter", "working-tree-encoding", "ident", "eol", "text")
    out = git(root, ["-c", "core.attributesFile=/dev/null", "check-attr", f"--source={tree}", "-z", "--stdin",
                     *names], stdin=b"".join(p + b"\0" for p in paths))
    fields = out.split(b"\0")
    attrs: Dict[bytes, Dict[str, str]] = {}
    for i in range(0, len(fields) - 2, 3):
        attrs.setdefault(fields[i], {})[fields[i + 1].decode("ascii")] = fields[i + 2].decode("utf-8", "replace")
    return attrs


# ---------------------------------------------------------------------------
# The rule (one implementation; see the module docstring for how it is tied)
# ---------------------------------------------------------------------------

def shown(path: bytes) -> str:
    """A path as a key and a line of output: control characters, backslash
    and bytes that are not UTF-8 written `\\xNN`, so every key is one line."""
    out = []
    for ch in path.decode("utf-8", "surrogateescape"):
        o = ord(ch)
        if 0xDC80 <= o <= 0xDCFF:
            out.append(f"\\x{o - 0xDC00:02x}")
        elif o < 0x20 or o == 0x7F or ch == "\\":
            out.append(f"\\x{o:02x}")
        else:
            out.append(ch)
    return "".join(out)


def rust_trim(text: str) -> str:
    return text.strip(RUST_WHITESPACE)


def git_quotes(path: bytes) -> bool:
    """Whether `git ls-files` (core.quotepath, its default) C-quotes `path`."""
    return any(b < 0x20 or b == 0x7F or b >= 0x80 or b in b'"\\' for b in path)


def unpinnable(corpus: Corpus, path: bytes) -> Optional[str]:
    """Why the manifest cannot carry `path` as the rule lists it, or None."""
    if corpus.quoted_listing and git_quotes(path):
        return "quoted-by-git"
    try:
        text = path.decode("utf-8")
    except UnicodeDecodeError:
        return "not-utf-8"
    if "\n" in text or "\r" in text:
        return "line-break"
    if rust_trim(text) != text:
        return "edge-white-space"
    if text.startswith("#"):
        return "comment-mark"
    return None


def conversion(corpus: Corpus, entry: Entry, attrs: Dict[str, str]) -> Optional[str]:
    """The attribute that makes the checkout's size unknowable from the blob
    for the size cap, or None. An eol=crlf checkout is at least the blob and
    at most twice it, so it only matters when that range straddles the cap."""
    def given(name: str) -> bool:
        return attrs.get(name, "unspecified") not in ("unspecified", "unset")
    for name in ("filter", "working-tree-encoding"):
        if given(name):
            return f"{name}={attrs[name]}"
    if attrs.get("ident") == "set":
        return "ident"
    if (attrs.get("eol") == "crlf" and attrs.get("text") != "unset" and corpus.size_cap is not None
            and entry.size is not None and entry.size < corpus.size_cap <= 2 * entry.size):
        return "eol=crlf"
    return None


def pinned_paths(text: str) -> List[str]:
    """The manifest as the Rust tests read it: `.lines()`, `str::trim`, and
    neither empty nor `#` lines."""
    out = []
    for line in text.split("\n"):
        line = rust_trim(line)
        if line and not line.startswith("#"):
            out.append(line)
    return out


def documented_command(text: str) -> Optional[str]:
    """The header's REGENERATE block: the `#   ` lines after the mark (and
    its `#` spacer line), each without that prefix."""
    lines = text.split("\n")
    if REGENERATE_MARK not in lines:
        return None
    j = lines.index(REGENERATE_MARK) + 1
    if j < len(lines) and lines[j] == "#":
        j += 1
    block = []
    while j < len(lines) and lines[j].startswith("#   "):
        block.append(lines[j][4:])
        j += 1
    return "\n".join(block) or None


def members_and_findings(corpus: Corpus, entries: Sequence[Entry],
                         attrs: Dict[bytes, Dict[str, str]]) -> Tuple[List[str], List[str], List[str], List[str]]:
    """(members, findings, notes, undecided paths): the documents the rule
    selects, and every selected path it cannot answer for."""
    members, findings, notes, undecided = [], [], [], []
    for e in entries:
        if not e.path.endswith(corpus.suffix):
            continue
        excluded = e.path.startswith(EXCLUDED_PREFIXES)
        why = unpinnable(corpus, e.path)
        # The listing itself fails on these wherever they are: the Rust tests
        # decode the whole listing, and git quotes before the prefix filters
        # see a line, so a quoted excluded path is not excluded.
        if why in ("not-utf-8", "quoted-by-git") or (why and not excluded):
            findings.append(f"{corpus.name} UNPINNABLE {why} {shown(e.path)}")
            notes.append(f"{shown(e.path)}: the manifest cannot carry this path as the rule lists it ({why})")
            undecided.append(shown(e.path))
            continue
        if excluded:
            continue
        if corpus.size_cap is not None:
            if e.mode not in REGULAR_MODES:
                findings.append(f"{corpus.name} NON-REGULAR {e.mode} {shown(e.path)}")
                notes.append(f"{shown(e.path)}: mode {e.mode}; the documented command stats the entry, the Rust "
                             "test its target, so the size cap has no single answer")
                undecided.append(shown(e.path))
                continue
            converted = conversion(corpus, e, attrs.get(e.path, {}))
            if converted:
                findings.append(f"{corpus.name} CHECKOUT-CONVERTED {converted} {shown(e.path)}")
                notes.append(f"{shown(e.path)}: the tree's attributes ({converted}) change its checkout bytes, "
                             "and the size cap reads the checkout")
                undecided.append(shown(e.path))
                continue
            if e.size is None or e.size >= corpus.size_cap:
                continue
        members.append(e.path.decode("utf-8"))
    return sorted(set(members)), findings, notes, undecided


def judge_corpus(corpus: Corpus, entries: Sequence[Entry], manifest: Optional[bytes], problem: Optional[str],
                 attrs: Dict[bytes, Dict[str, str]]) -> Verdict:
    v = Verdict(corpus)
    members, findings, notes, undecided = members_and_findings(corpus, entries, attrs)
    v.members, v.selected = members, len(members)
    v.findings.extend(findings)
    v.notes.extend(notes)
    if problem is not None:
        v.findings.append(f"{corpus.name} {problem}")
        v.notes.append(f"{corpus.manifest}: {problem}")
        return v
    assert manifest is not None
    try:
        text = manifest.decode("utf-8")
    except UnicodeDecodeError:
        v.findings.append(f"{corpus.name} MANIFEST-NOT-UTF-8")
        v.notes.append(f"{corpus.manifest} is not UTF-8 (`include_str!` refuses it)")
        return v
    documented = documented_command(text)
    if documented is None:
        v.findings.append(f"{corpus.name} RULE-UNDOCUMENTED")
        v.notes.append(f"{corpus.manifest}'s header has no `{REGENERATE_MARK}` block")
    elif documented != corpus.documented:
        digest = hashlib.sha256(documented.encode("utf-8")).hexdigest()[:16]
        v.findings.append(f"{corpus.name} RULE-DOCUMENTED-DIFFERENTLY {digest}")
        v.notes.append(f"{corpus.manifest}'s header documents another rule than this check applies; teach "
                       "scripts/check_corpus_membership.py (CORPORA) the new rule and re-run "
                       "scripts/tests/check_corpus_membership_test.py, which ties the two")
    pinned = set(pinned_paths(text))
    v.pinned = len(pinned)
    member_set = set(members)
    v.new = sorted(member_set - pinned)
    v.gone = sorted(pinned - member_set - set(undecided))
    v.findings.extend(f"{corpus.name} NEW {shown(p.encode('utf-8'))}" for p in v.new)
    v.findings.extend(f"{corpus.name} GONE {shown(p.encode('utf-8'))}" for p in v.gone)
    if corpus.pinned_floor and v.pinned <= corpus.pinned_floor:
        v.findings.append(f"{corpus.name} PINNED-AT-MOST {corpus.pinned_floor} {v.pinned}")
        v.notes.append(f"{corpus.manifest} pins {v.pinned} documents; {corpus.rust_test} requires more than "
                       f"{corpus.pinned_floor}")
    return v


def judge_tree(root: Path, tree: str) -> List[Verdict]:
    entries = tree_entries(root, tree)
    capped = [e.path for c in CORPORA if c.size_cap is not None for e in entries
              if e.path.endswith(c.suffix) and not e.path.startswith(EXCLUDED_PREFIXES)]
    attrs = converting_attributes(root, tree, capped)
    verdicts = []
    for corpus in CORPORA:
        blob, problem = manifest_blob(root, tree, corpus.manifest)
        verdicts.append(judge_corpus(corpus, entries, blob, problem, attrs))
    return verdicts


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def report_tree(label: str, verdicts: Sequence[Verdict]) -> bool:
    """Print one tree's verdicts; True when every membership matches."""
    ok = True
    for v in verdicts:
        c = v.corpus
        exact = not v.findings
        ok = ok and exact
        print(f"[{label}] {c.name}: {v.pinned} pinned, {v.selected} selected by the documented rule "
              f"({c.manifest}){': exact' if exact else ''}")
        for title, paths in (("NEW in the tree, not pinned", v.new), ("GONE from the tree, still pinned", v.gone)):
            if paths:
                print(f"[{label}] {c.name}: {title} ({len(paths)}):")
                for p in paths:
                    print(f"[{label}]     {shown(p.encode('utf-8'))}")
        for note in v.notes:
            print(f"[{label}] {c.name}: {note}")
    return ok


def repair_lines(verdicts: Sequence[Verdict]) -> List[str]:
    moved = sorted({v.corpus.manifest for v in verdicts if v.new or v.gone})
    blocked = [k for v in verdicts for k in v.blocking]
    lines = ["CORPUS MEMBERSHIP MISMATCH: a pinned corpus does not match the tree it is pushed in, so its Rust "
             "membership test fails there.",
             "  A landing that changes a membership carries the re-pin in the same push "
             "(docs/DECISION_QUEUE.md CORPUS-MEMBERSHIP-AT-LANDING-1)."]
    if moved:
        lines += [f"  regenerate {', '.join(moved)}, in a checkout of the refused tree:",
                  f"      {WRITE_COMMAND}",
                  "  then READ THE DIFF (a GONE path is a document the corpus loses), add a dated line to the "
                  "header naming the change, and commit the re-pin with the change that moved the membership."]
    if blocked:
        lines.append("  a re-pin cannot clear the other finding(s); each is explained above.")
    return lines


def emit_findings(keys: Sequence[str], complete: bool) -> None:
    for key in sorted(set(keys)):
        print(f"FINDING: {key}")
    if complete and keys:
        print("FINDINGS: complete")


# ---------------------------------------------------------------------------
# Subjects
# ---------------------------------------------------------------------------

def parse_pushed_refs(raw: str) -> List[Tuple[str, str]]:
    pushed = []
    for line in raw.splitlines():
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 4 or not HEX_SHA.match(fields[1]) or not HEX_SHA.match(fields[3]):
            raise ValueError(f"malformed TRUST_PUSHED_REFS line {line!r}; expected "
                             "`<local_ref> <local_sha> <remote_ref> <remote_sha>`")
        pushed.append((fields[0], fields[1]))
    return pushed


def resolve_tree(root: Path, rev: str) -> str:
    return git(root, ["rev-parse", "--verify", "--quiet", f"{rev}^{{tree}}"]).decode("ascii").strip()


def judge_subjects(root: Path, subjects: Sequence[Tuple[str, str]], heading: str) -> int:
    """Judge each (label, revision); one verdict per distinct tree."""
    trees: Dict[str, List[str]] = {}
    unreadable: List[str] = []
    for label, rev in subjects:
        try:
            trees.setdefault(resolve_tree(root, rev), []).append(label)
        except GateError:
            unreadable.append(f"[{label}] CORPUS MEMBERSHIP UNREADABLE: {rev} does not name a tree in this clone; "
                              "a tree this check cannot read is not a pass")
    print(heading, flush=True)
    keys: List[str] = []
    complete, ok = not unreadable, not unreadable
    for line in unreadable:
        print(line)
    all_verdicts: List[Verdict] = []
    for tree, labels in trees.items():
        label = ", ".join(labels)
        try:
            verdicts = judge_tree(root, tree)
        except GateError as exc:
            print(f"[{label}] CORPUS MEMBERSHIP UNREADABLE: {exc}")
            complete = ok = False
            continue
        all_verdicts.extend(verdicts)
        ok = report_tree(label, verdicts) and ok
        keys.extend(k for v in verdicts for k in v.findings)
    if ok:
        print("PASS: every pinned corpus membership matches its tree")
        return 0
    for line in repair_lines(all_verdicts):
        print(line)
    emit_findings(keys, complete)
    return 1


def judge_push(root: Path, raw: str) -> int:
    try:
        pushed = parse_pushed_refs(raw)
    except ValueError as exc:
        print(f"CORPUS MEMBERSHIP INVALID: {exc}", file=sys.stderr)
        return 2
    live = [(ref, sha) for ref, sha in pushed if not ZERO_SHA.match(sha)]
    deletions = len(pushed) - len(live)
    if not live:
        print(f"SUBJECT: the pushed trees (TRUST_PUSHED_REFS: {deletions} deletion(s), nothing else)")
        print("SKIPPED: deletion(s) only, no tree pushed — nothing to judge")
        return 0
    names = ", ".join(f"{ref} {sha[:12]}" for ref, sha in live)
    extra = f"; {deletions} deletion(s) not judged" if deletions else ""
    return judge_subjects(root, [(f"{ref} {sha[:12]}", sha) for ref, sha in live],
                          f"SUBJECT: the pushed trees (TRUST_PUSHED_REFS: {names}{extra}), from git objects, "
                          "not the working tree")


# ---------------------------------------------------------------------------
# --write: the re-pin
# ---------------------------------------------------------------------------

def split_header(text: str) -> Tuple[Optional[str], Optional[str]]:
    """(the header: every line up to the last `#` line and the blank lines
    after it, None) or (None, why the file is not a header and a body)."""
    parts = text.split("\n")
    lines = [p + "\n" for p in parts[:-1]] + ([parts[-1]] if parts[-1] else [])
    comments = [i for i, line in enumerate(lines) if rust_trim(line).startswith("#")]
    if not comments:
        return None, "it has no header"
    last = comments[-1]
    early = [i for i in range(last) if rust_trim(lines[i]) and not rust_trim(lines[i]).startswith("#")]
    if early:
        return None, f"line {early[0] + 1} pins a path above the header's last comment line (line {last + 1})"
    end = last + 1
    while end < len(lines) and not rust_trim(lines[end]):
        end += 1
    header = "".join(lines[:end])
    return (header if header.endswith("\n") else header + "\n"), None


def write(root: Path) -> int:
    try:
        tree = git(root, ["write-tree"]).decode("ascii").strip()
        entries = tree_entries(root, tree)
        capped = [e.path for e in entries if e.path.endswith(b".json") and not e.path.startswith(EXCLUDED_PREFIXES)]
        attrs = converting_attributes(root, tree, capped)
    except GateError as exc:
        print(f"CORPUS MEMBERSHIP: cannot read this checkout's index ({exc}); nothing written")
        return 1
    print(f"SUBJECT: this checkout's index (tree {tree[:12]}); each manifest's header is taken from the working "
          "tree file and kept byte for byte")
    rc = 0
    for corpus in CORPORA:
        path = root / corpus.manifest
        try:
            data: Optional[bytes] = path.read_bytes()
            problem = None
        except FileNotFoundError:
            data, problem = None, "MANIFEST-ABSENT"
        v = judge_corpus(corpus, entries, data, problem, attrs)
        if v.blocking:
            report_tree("index", [v])
            print(f"REFUSED: {corpus.manifest} not written: {', '.join(v.blocking)}")
            rc = 1
            continue
        if not v.new and not v.gone:
            print(f"{corpus.manifest}: {v.pinned} pinned, exact; unchanged")
            continue
        assert data is not None
        header, why = split_header(data.decode("utf-8"))
        if header is None:
            print(f"REFUSED: {corpus.manifest} not written: {why}; edit it by hand")
            rc = 1
            continue
        path.write_bytes((header + "".join(p + "\n" for p in v.members)).encode("utf-8"))
        print(f"{corpus.manifest}: re-pinned {v.pinned} -> {len(v.members)} (+{len(v.new)} -{len(v.gone)})")
        for sign, paths in (("+", v.new), ("-", v.gone)):
            for p in paths:
                print(f"    {sign} {shown(p.encode('utf-8'))}")
    if rc == 0:
        print("READ THE DIFF, add a dated line to each re-pinned header naming the change, and commit it with the "
              "change that moved the membership.")
    return rc


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--rev", help="judge this revision's tree (ignores TRUST_PUSHED_REFS)")
    mode.add_argument("--write", action="store_true",
                      help="re-pin each moved manifest from this checkout's index, keeping its header")
    args = ap.parse_args(argv)
    if args.write:
        return write(ROOT)
    if args.rev:
        return judge_subjects(ROOT, [(args.rev, args.rev)], f"SUBJECT: {args.rev}'s tree, from git objects")
    raw = os.environ.get("TRUST_PUSHED_REFS", "")
    if raw.strip():
        return judge_push(ROOT, raw)
    return judge_subjects(ROOT, [("HEAD", "HEAD")],
                          "SUBJECT: HEAD's tree, from git objects (no push in flight: TRUST_PUSHED_REFS unset or "
                          "empty)")


if __name__ == "__main__":
    sys.exit(main())
