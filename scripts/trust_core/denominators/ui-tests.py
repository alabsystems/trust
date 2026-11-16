#!/usr/bin/env python3
"""E0.12 denominator `ui-tests`: the strict pass-header count in tests/ui/borrowck and tests/ui/nll.

Design of record: docs/design/2026-09-16-trust-core-architecture.md, §5.2 Stage 0.5 ("The strict
`^//@ *(check|run|build)-pass` count in `tests/ui/borrowck` and `tests/ui/nll` [M†: 193 of 850]",
exit E0.12 "All published, each with its predicate: 0 denominators without one"). The count is
consumed by E3.2.2 (BorrowCert v1: "every strict-pass-header borrowck and NLL UI file (E0.12's
count) is accepted"); the design's D-5 "Denominators" bullet and erratum D.39 state it.

Every number below is recomputed from git objects, never from a working tree and never copied:

  TRUST     the superproject at `--rev` (default HEAD): tests/ as ported to the upstream alignment
            that release/trust-version.toml [rust_alignment] and tests/upstream-rust/baseline.toml
            [upstream] both name, which must equal docs/trust-core/EXTERNAL_PINS.toml [alignment].
  DESIGN    the superproject at the commit the design's header says the document was "Written
            read-only against" (read from the design text at `--rev`). The design does not say
            where its [M†] numbers were measured (round-16 investigations, "not re-read here");
            this side reads tests/ at the one commit the document names. strict-pass, loose-pass
            and all-rs record the paths added and removed since then, so a design number that
            equals value - added + removed is shown to hold at the document's own pin, with the
            same predicate, while tests/ moved. A header that names no single commit, or one
            this clone cannot resolve, is a DESIGN-PIN finding.
  UPSTREAM  rust-lang/rust at that alignment commit, from the blob-filtered clone
            scripts/trust_core/fetch_sources.py keeps ($TRUST_CORE_SOURCES/rust, checked by
            common.verify_clone). That clone holds the trees but not these blobs (it is a sparse
            checkout of library/), so a blob is read from the clone when present and otherwise from
            the superproject's object store BY OBJECT ID: an id names exactly one content, so the
            bytes are upstream's. A blob in neither store makes every upstream row `blocked`.

The predicates (each row of docs/trust-core/denominators/ui-tests.toml repeats its own):

  test-files     the denominator. compiletest's ui collection rule (src/tools/compiletest/src/
                 lib.rs collect_tests_from_dir and is_test) restricted to the two directories: a
                 blob path under tests/ui/borrowck/ or tests/ui/nll/ whose file name ends in `.rs`
                 and does not start with `.`, `#` or `~`, with no `auxiliary` directory between
                 tests/ui and the file, and no directory from tests/ui down to the file's own
                 holding a `compiletest-ignore-dir` file.
  strict-pass    test-files with at least one line (the file split on "\\n") that matches the regex
                 `^//@ *(check|run|build)-pass` (Python re.match; the same language as grep -E).
                 "Header" is not positional: compiletest reads a directive on any line.
  all-rs         every `.rs` blob under the two directories, auxiliary/ included: the design's
                 "hold 850 `.rs` files" predicate.
  loose-pass     test-files whose text contains `(check|run|build)-pass` anywhere: the design's
                 "loose grep for the words anywhere in the file".
  compiletest-unconditional   test-files with a directive compiletest itself parses
                 (src/tools/compiletest/src/directives/line.rs line_directive, on each trimmed line)
                 as check-pass, build-pass or run-pass with no `[revision]` condition.
                 strict-vs-compiletest.differ publishes the files on which the two sets differ: where
                 the regex disagrees with the test runner it stands for.
  revision-conditional-pass   test-files with a `//@ [rev] <mode>-pass` directive and no
                 unconditional one: they pass under some revisions only, so the strict predicate
                 excludes them. loose-vs-strict.unexplained publishes the files that make loose-pass
                 minus strict-pass differ from this set.

Usage (the checkers need Python 3.11+, common.py's floor; macOS's /usr/bin/python3 is 3.9):
    python3.14 scripts/trust_core/denominators/ui-tests.py            # measure and print
    python3.14 scripts/trust_core/denominators/ui-tests.py --list     # also print every file list
    python3.14 scripts/trust_core/denominators/ui-tests.py --write    # rewrite the TOML record
    python3.14 scripts/trust_core/denominators/ui-tests.py --check    # the TOML equals a re-measurement

Exit codes: 0 measured (a row may be `blocked`, with its reason) and, with --check, the record
matches; 1 a finding (the alignment records disagree with EXTERNAL_PINS, a tree entry is not a plain
file, a test file is not UTF-8) or a record mismatch; 2 the pins or the superproject cannot be read.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor (scripts/tests/python_floor_test.py). This file needs tomllib (3.11+) and plain
# `python3` is 3.9 on macOS CommandLineTools, so an old interpreter re-execs here, before any import
# that needs 3.11 runs.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("ui-tests.py requires Python 3.11+ (tomllib); none found on PATH")

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import common as C  # noqa: E402

import tomllib  # noqa: E402  (common.py has already refused an interpreter without it)

KEY = "ui-tests"
SCHEMA = "trust.core.denominator.v1"
RECORD_REL = f"docs/trust-core/denominators/{KEY}.toml"
SCRIPT_REL = f"scripts/trust_core/denominators/{KEY}.py"
BASELINE_REL = "tests/upstream-rust/baseline.toml"
RUST_URL = "https://github.com/rust-lang/rust"
UI_ROOT = "tests/ui"
DIRS = ("tests/ui/borrowck", "tests/ui/nll")
MODES = ("check-pass", "build-pass", "run-pass")
STRICT_TEXT = r"^//@ *(check|run|build)-pass"
STRICT = re.compile(STRICT_TEXT)
LOOSE_TEXT = r"(check|run|build)-pass"
LOOSE = re.compile(LOOSE_TEXT)
IGNORE_DIR = "compiletest-ignore-dir"
FETCH = "python3.14 scripts/trust_core/fetch_sources.py"
DIGEST_RULE = "sha256 over the sorted lines `<path>\\t<blob id>\\n` of test-files"

# What the design says, found by these patterns in the design text at the same revision, so the
# record states whether each [M†] number is reproduced. A pattern that no longer matches is
# reported as "not found", never as agreement.
DESIGN_CLAIMS = (
    ("all-rs", r"`tests/ui/borrowck`\s+and\s+`tests/ui/nll`\s+hold\s+(\d[\d,]*)\s+`\.rs`\s+files"),
    ("strict-pass", r"strict\s+`\^//@\s\*\(check\|run\|build\)-pass`\s+header\s+predicate\s+finds\s+(\d[\d,]*)\s+of"),
    ("loose-pass", r"loose\s+grep\s+for\s+the\s+words\s+anywhere\s+in\s+the\s+file\s+finds\s+(\d[\d,]*)"),
    ("strict-pass", r"`tests/ui/nll`\s+\[M†:\s+(\d[\d,]*)\s+of\s+\d[\d,]*\]"),
    ("all-rs", r"`tests/ui/nll`\s+\[M†:\s+\d[\d,]*\s+of\s+(\d[\d,]*)\]"),
    ("strict-pass", r"strict\s+header\s+predicate\s+gives\s+(\d[\d,]*)\s+of\s+\d[\d,]*"),
    ("all-rs", r"strict\s+header\s+predicate\s+gives\s+\d[\d,]*\s+of\s+(\d[\d,]*)"),
    ("loose-pass", r"(\d[\d,]*)\s+is\s+a\s+loose\s+word\s+match"),
)
# The rows whose design numbers are also read at the design's own pin (common.design_header_pin:
# the superproject commit the design's header says it was written against).
DESIGN_PIN_ROWS = ("strict-pass", "loose-pass", "all-rs")


class Fatal(Exception):
    """An input the measurement cannot proceed without (exit 2)."""


# --------------------------------------------------------------------------
# git objects
# --------------------------------------------------------------------------


def ls_tree(repo: Path, rev: str, paths: tuple) -> dict[str, tuple[str, str, str]] | None:
    """path -> (mode, type, oid) for every entry below `paths` at `rev`, recursively."""
    out = C.git(repo, "ls-tree", "-r", "-z", "--full-tree", rev, "--", *paths)
    if out is None:
        return None
    entries = {}
    for record in out.split("\0"):
        if not record:
            continue
        meta, _, path = record.partition("\t")
        mode, kind, oid = meta.split()
        entries[path] = (mode, kind, oid)
    return entries


def tree_id(repo: Path, rev: str, path: str) -> str | None:
    out = C.git(repo, "rev-parse", "--verify", "--quiet", f"{rev}:{path}")
    return out.strip() if out else None


def read_blobs(stores: list[Path], oids) -> tuple[dict[str, bytes], dict[str, str]]:
    """oid -> bytes, and oid -> the store it came from, trying `stores` in order; no read fetches."""
    want = sorted(set(oids))
    got: dict[str, bytes] = {}
    where: dict[str, str] = {}
    for store in stores:
        need = [o for o in want if o not in got]
        if not need:
            break
        out = C.git(store, "cat-file", "--batch", binary=True, stdin="".join(f"{o}\n" for o in need).encode())
        if out is None:
            continue
        pos = 0
        for oid in need:
            end = out.find(b"\n", pos)
            if end < 0:
                break
            header = out[pos:end].split()
            pos = end + 1
            if len(header) == 2 and header[1] == b"missing":
                continue
            if len(header) != 3:
                break
            size = int(header[2])
            if header[1] == b"blob" and header[0].decode() == oid:
                got[oid] = out[pos:pos + size]
                where[oid] = str(store)
            pos += size + 1
    return got, where


# --------------------------------------------------------------------------
# predicates
# --------------------------------------------------------------------------


def is_test_path(path: str, ignore_dirs: set[str]) -> bool:
    """compiletest's collection rule below tests/ui, for one blob path (see the module docstring)."""
    if not path.startswith(UI_ROOT + "/"):
        return False
    parts = path.split("/")
    name = parts[-1]
    if not name.endswith(".rs") or name.startswith((".", "#", "~")):
        return False
    below = parts[2:-1]  # the directories between tests/ui and the file
    if "auxiliary" in below:
        return False
    for depth in range(2, len(parts)):
        if "/".join(parts[:depth]) in ignore_dirs:
            return False
    return True


def directives(text: str) -> list[tuple[str | None, str]]:
    """(revision, name) per directive line, as compiletest's line_directive parses a trimmed line."""
    found = []
    for line in text.split("\n"):
        line = line.strip()
        if not line.startswith("//@"):
            continue
        rest = line[3:].lstrip()
        revision = None
        if rest.startswith("["):
            revision, sep, after = rest[1:].partition("]")
            if not sep:
                revision, after = "<malformed>", ""
            rest = after.lstrip()
        name = re.split(r"[: ]", rest, maxsplit=1)[0]
        found.append((revision, name))
    return found


@dataclass
class FileFacts:
    path: str
    oid: str
    strict_modes: list[str]
    loose: bool
    unconditional_modes: list[str]
    conditional: dict[str, list[str]]  # pass mode -> revisions naming it
    revisions: list[str]
    known_bug: bool
    trust_marker: bool  # a `Trust:` edit marker (common.is_trust_marker) on some line


def facts_of(path: str, oid: str, text: str) -> FileFacts:
    lines = text.split("\n")
    strict = sorted({m.group(1) + "-pass" for m in (STRICT.match(line) for line in lines) if m})
    parsed = directives(text)
    unconditional = sorted({name for rev, name in parsed if rev is None and name in MODES})
    conditional: dict[str, list[str]] = {}
    for rev, name in parsed:
        if rev is not None and name in MODES:
            conditional.setdefault(name, [])
            if rev not in conditional[name]:
                conditional[name].append(rev)
    revisions: list[str] = []
    for line in lines:
        stripped = line.strip()
        m = re.match(r"//@\s*revisions\s*:(.*)", stripped)
        if m:
            revisions.extend(r for r in m.group(1).split() if r not in revisions)
    known_bug = any(name == "known-bug" for _, name in parsed)
    return FileFacts(path, oid, strict, LOOSE.search(text) is not None, unconditional, conditional, revisions, known_bug,
                     any(C.is_trust_marker(line) for line in lines))


@dataclass
class Side:
    """One tree's measurement: TRUST (the superproject) or UPSTREAM (rust-lang/rust at the pin)."""
    label: str
    revision: str = ""
    status: str = "measured"
    blocked: str = ""
    unblock: str = ""
    trees: dict = field(default_factory=dict)
    all_rs: list = field(default_factory=list)
    excluded: list = field(default_factory=list)
    tests: dict = field(default_factory=dict)  # path -> FileFacts
    blob_sources: dict = field(default_factory=dict)  # store -> count

    def digest(self) -> str:
        body = "".join(f"{p}\t{f.oid}\n" for p, f in sorted(self.tests.items()))
        return "sha256:" + hashlib.sha256(body.encode()).hexdigest()

    def select(self, pred) -> list[FileFacts]:
        return [f for _, f in sorted(self.tests.items()) if pred(f)]


def measure(findings: C.Findings, side: Side, repo: Path, rev: str, stores: list[Path]) -> None:
    for d in DIRS:
        side.trees[d] = tree_id(repo, rev, d)
        if side.trees[d] is None:
            raise Fatal(f"{side.label}: {repo} at {rev} has no tree {d}")
    entries = ls_tree(repo, rev, DIRS)
    if entries is None:
        raise Fatal(f"{side.label}: cannot list {', '.join(DIRS)} at {rev} in {repo}")
    ui_marker = ls_tree(repo, rev, (f"{UI_ROOT}/{IGNORE_DIR}",)) or {}
    ignore_dirs = {p.rsplit("/", 1)[0] for p in list(entries) + list(ui_marker) if p.endswith("/" + IGNORE_DIR)}
    odd = sorted(p for p, (mode, kind, _) in entries.items() if kind != "blob" or mode not in ("100644", "100755"))
    if odd:
        findings.add("TREE", f"{side.label}: entries that are not plain files (a symlink or a gitlink changes what a path means): {odd[:5]}")
    side.all_rs = sorted(p for p, (_, kind, _) in entries.items() if kind == "blob" and p.endswith(".rs"))
    candidates = {p: entries[p][2] for p in side.all_rs if is_test_path(p, ignore_dirs)}
    side.excluded = sorted(set(side.all_rs) - set(candidates))
    blobs, where = read_blobs(stores, candidates.values())
    missing = sorted(p for p, oid in candidates.items() if oid not in blobs)
    if missing:
        side.status = "blocked"
        side.blocked = (f"{len(missing)} of {len(candidates)} test-file blobs are in none of the object stores "
                        f"{[str(s) for s in stores]} (first: {missing[0]})")
        side.unblock = ("hydrate the blobs at the pin, e.g. `git -C <rust clone> sparse-checkout add /tests/ui/borrowck "
                        "/tests/ui/nll` (fetches them into the shared clone), then re-run")
        return
    for store in where.values():
        side.blob_sources[store] = side.blob_sources.get(store, 0) + 1
    for path, oid in sorted(candidates.items()):
        try:
            text = blobs[oid].decode("utf-8")
        except UnicodeDecodeError:
            findings.add("TREE", f"{side.label}: {path} is not UTF-8, so no line predicate can be applied to it")
            continue
        side.tests[path] = facts_of(path, oid, text)


def cross_checks(side: Side) -> dict[str, list[str]]:
    """The file sets on which two predicates that should agree disagree (each published as a row)."""
    strict = {f.path for f in side.select(lambda f: f.strict_modes)}
    uncond = {f.path for f in side.select(lambda f: f.unconditional_modes)}
    loose = {f.path for f in side.select(lambda f: f.loose)}
    conditional_only = {f.path for f in side.select(lambda f: f.conditional and not f.unconditional_modes)}
    return {"strict-vs-compiletest": sorted(strict ^ uncond),
            "loose-minus-strict-vs-revision-conditional": sorted(((loose - strict) ^ conditional_only) | (strict - loose))}


# --------------------------------------------------------------------------
# pins
# --------------------------------------------------------------------------


def read_alignments(repo: Path, rev: str) -> dict[str, str | None]:
    """The alignment each in-tree record names at `rev`."""
    found = {}
    for rel, table in ((C.TRUST_VERSION_REL, "rust_alignment"), (BASELINE_REL, "upstream")):
        text = C.git(repo, "show", f"{rev}:{rel}")
        try:
            found[f"{rel} [{table}].revision"] = tomllib.loads(text or "")[table]["revision"]
        except (KeyError, TypeError, tomllib.TOMLDecodeError):
            found[f"{rel} [{table}].revision"] = None
    return found


def design_side(findings: C.Findings, repo: Path, rev: str) -> Side | None:
    """tests/ at the commit the design at `rev` says it was written against, or None (with a
    DESIGN-PIN finding) when its header names no single commit. A named pin this clone cannot
    resolve is a blocked side and a finding, never a silent absence."""
    named, pinned = C.design_header_pin(repo, C.git(repo, "show", f"{rev}:{C.DESIGN_REL}") or "")
    if len(named) != 1:
        findings.add("DESIGN-PIN", f"{C.DESIGN_REL} at {rev[:10]}: its header names {len(named)} superproject commits it "
                                   f"was written against {named}, not one, so no row is read at the design's pin")
        return None
    side = Side("design", revision=pinned or named[0])
    unblock = "read the design's pin from a full clone of the superproject (its history holds the commit), then re-run"
    if pinned is None:
        findings.add("DESIGN-PIN", f"{C.DESIGN_REL} at {rev[:10]}: its header pin {named[0]} is no single commit of {repo}")
        side.status, side.blocked, side.unblock = "blocked", f"the design's pin {named[0]} is no single commit of {repo}", unblock
        return side
    try:
        measure(findings, side, repo, pinned, [repo])
    except Fatal as error:
        side.status, side.blocked, side.unblock = "blocked", str(error), unblock
    return side


def pin_paths(side: Side, row: str) -> set[str]:
    """The paths a DESIGN_PIN_ROWS row counts on `side`."""
    if row == "strict-pass":
        return {f.path for f in side.select(lambda f: f.strict_modes)}
    if row == "loose-pass":
        return {f.path for f in side.select(lambda f: f.loose)}
    if row == "all-rs":
        return set(side.all_rs)
    raise ValueError(row)


def design_claims(repo: Path, rev: str) -> list[dict]:
    text = C.git(repo, "show", f"{rev}:{C.DESIGN_REL}") or ""
    claims = []
    for row, pattern in DESIGN_CLAIMS:
        m = re.search(pattern, text)
        if m is None:
            claims.append({"row": row, "pattern": pattern, "found": False})
            continue
        line = text.count("\n", 0, m.start(1)) + 1
        claims.append({"row": row, "pattern": pattern, "found": True, "line": line,
                       "value": int(m.group(1).replace(",", ""))})
    return claims


# --------------------------------------------------------------------------
# the record
# --------------------------------------------------------------------------


def q(value) -> str:
    """A TOML basic string (JSON's escapes are a subset of TOML's)."""
    return json.dumps(value, ensure_ascii=False)


def key(name: str) -> str:
    """A TOML key: bare when it may be, else quoted."""
    return name if re.fullmatch(r"[A-Za-z0-9_-]+", name) else q(name)


def tv(value) -> str:
    """A TOML value: a string, an integer, a boolean, an inline table, or an array (one element per line)."""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return q(value)
    if isinstance(value, dict):
        return "{ " + ", ".join(f"{key(k)} = {tv(v)}" for k, v in value.items()) + " }" if value else "{}"
    if isinstance(value, (list, tuple)):
        if not value:
            return "[]"
        if all(isinstance(v, str) and len(v) < 40 for v in value) and len(value) <= 6:
            return "[" + ", ".join(tv(v) for v in value) + "]"
        return "[\n" + "".join(f"  {tv(v)},\n" for v in value) + "]"
    raise TypeError(f"no TOML rendering for {type(value).__name__}")


def build_rows(trust: Side, upstream: Side, claims: list[dict], design: Side | None = None) -> list[dict]:
    t = trust
    checks = cross_checks(t)
    strict = t.select(lambda f: f.strict_modes)
    conditional = t.select(lambda f: f.conditional and not f.unconditional_modes)
    per_dir = {d: [f for f in strict if f.path.startswith(d + "/")] for d in DIRS}
    per_dir_den = {d: [p for p in t.tests if p.startswith(d + "/")] for d in DIRS}
    rows = [
        {"name": "test-files", "value": len(t.tests), "side": "trust",
         "predicate": "blob paths under tests/ui/borrowck/ and tests/ui/nll/ that compiletest collects as ui tests: file "
                      "name ends in `.rs` and does not start with `.`, `#` or `~`; no `auxiliary` directory between "
                      "tests/ui and the file; no directory from tests/ui down holding `compiletest-ignore-dir` "
                      "(src/tools/compiletest/src/lib.rs collect_tests_from_dir, is_test)",
         "digest": t.digest(), "excluded": t.excluded},
        {"name": "strict-pass", "value": len(strict), "side": "trust", "of": "test-files",
         "predicate": f"test-files with at least one line matching the regex `{STRICT_TEXT}` (the file split on "
                      "newlines; any line, not only a leading header block)",
         "files": [{"path": f.path, "modes": f.strict_modes} for f in strict]},
    ]
    for mode in MODES:
        rows.append({"name": f"strict-pass.{mode}", "value": sum(1 for f in strict if mode in f.strict_modes),
                     "side": "trust", "of": "strict-pass",
                     "predicate": f"strict-pass files whose matching lines include `{mode}`"})
    for d in DIRS:
        leaf = d.rsplit("/", 1)[1]
        rows.append({"name": f"test-files.{leaf}", "value": len(per_dir_den[d]), "side": "trust", "of": "test-files",
                     "predicate": f"test-files under {d}/"})
        rows.append({"name": f"strict-pass.{leaf}", "value": len(per_dir[d]), "side": "trust", "of": f"test-files.{leaf}",
                     "predicate": f"strict-pass files under {d}/"})
    rows += [
        {"name": "strict-pass.known-bug", "value": sum(1 for f in strict if f.known_bug), "side": "trust",
         "of": "strict-pass",
         "predicate": "strict-pass files that also carry a `known-bug` directive (conditional or not): a known "
                      "unsound acceptance E3.2.2 would otherwise require a borrow certificate to accept"},
        {"name": "strict-pass.with-revisions", "value": sum(1 for f in strict if f.revisions), "side": "trust",
         "of": "strict-pass",
         "predicate": "strict-pass files declaring `//@ revisions:` (the pass mode then holds for every revision)"},
        {"name": "compiletest-unconditional", "value": len(t.select(lambda f: f.unconditional_modes)), "side": "trust",
         "of": "test-files",
         "predicate": "test-files with a directive compiletest parses (each line trimmed, `//@`, optional spaces, no "
                      "`[revision]`, name up to `:` or space) as check-pass, build-pass or run-pass "
                      "(src/tools/compiletest/src/directives/line.rs line_directive)"},
        {"name": "strict-vs-compiletest.differ", "value": len(checks["strict-vs-compiletest"]), "side": "trust",
         "of": "test-files",
         "predicate": "test-files in exactly one of strict-pass and compiletest-unconditional: where the regex "
                      "disagrees with the test runner it stands for (0 means the regex is the runner's rule here)",
         "files": checks["strict-vs-compiletest"]},
        {"name": "revision-conditional-pass", "value": len(conditional), "side": "trust", "of": "test-files",
         "predicate": "test-files with a `//@ [rev] check-pass|build-pass|run-pass` directive and no unconditional "
                      "one",
         "files": [{"path": f.path, "revisions": f.revisions,
                    "pass": {m: r for m, r in sorted(f.conditional.items())}} for f in conditional]},
        {"name": "revision-conditional-pass.all-revisions", "side": "trust", "of": "revision-conditional-pass",
         "value": sum(1 for f in conditional if f.revisions and set(f.revisions) <= {r for rs in f.conditional.values() for r in rs}),
         "predicate": "revision-conditional-pass files in which every declared revision carries a pass directive "
                      "(a file the strict predicate misses although it passes everywhere)"},
        {"name": "loose-pass", "value": len(t.select(lambda f: f.loose)), "side": "trust", "of": "test-files",
         "predicate": f"test-files whose text matches the regex `{LOOSE_TEXT}` anywhere (a loose word match)"},
        {"name": "loose-vs-strict.unexplained", "side": "trust", "of": "test-files",
         "value": len(checks["loose-minus-strict-vs-revision-conditional"]),
         "predicate": "test-files in loose-pass minus strict-pass but not revision-conditional-pass, or the reverse, "
                      "or in strict-pass but not loose-pass (0 means the loose surplus is exactly the "
                      "revision-conditional pass files)",
         "files": checks["loose-minus-strict-vs-revision-conditional"]},
        {"name": "all-rs", "value": len(t.all_rs), "side": "trust",
         "predicate": "every blob path ending in `.rs` under tests/ui/borrowck/ and tests/ui/nll/, auxiliary/ "
                      "included (the design's \"hold 850 `.rs` files\" predicate; not a test count)"},
    ]
    up_paths, t_paths = set(upstream.tests), set(t.tests)
    added = sorted(t_paths - up_paths)
    removed = sorted(up_paths - t_paths)
    changed = sorted(p for p in t_paths & up_paths if t.tests[p].oid != upstream.tests[p].oid)
    if upstream.status == "measured":
        u_strict = upstream.select(lambda f: f.strict_modes)
        rows += [
            {"name": "upstream.test-files", "value": len(upstream.tests), "side": "upstream",
             "predicate": "test-files' predicate over rust-lang/rust at the alignment commit", "digest": upstream.digest(),
             "excluded": upstream.excluded},
            {"name": "upstream.strict-pass", "value": len(u_strict), "side": "upstream", "of": "upstream.test-files",
             "predicate": "strict-pass's predicate over rust-lang/rust at the alignment commit"},
            {"name": "upstream.all-rs", "value": len(upstream.all_rs), "side": "upstream",
             "predicate": "all-rs's predicate over rust-lang/rust at the alignment commit"},
            {"name": "trust-vs-upstream.added", "value": len(added), "side": "both",
             "predicate": "test-files at the superproject revision whose path is not a test file at the alignment "
                          "commit (tests Trust added)",
             "files": [{"path": p, "strict_modes": t.tests[p].strict_modes, "trust_marker": t.tests[p].trust_marker}
                       for p in added]},
            {"name": "trust-vs-upstream.removed", "value": len(removed), "side": "both",
             "predicate": "test files at the alignment commit whose path is not a test file at the superproject revision",
             "files": removed},
            {"name": "trust-vs-upstream.changed", "value": len(changed), "side": "both",
             "predicate": "test files present in both whose blob ids differ (Trust edits to an upstream test)",
             "files": changed},
        ]
    else:
        for name, pred in (("upstream.test-files", "test-files' predicate over rust-lang/rust at the alignment commit"),
                           ("upstream.strict-pass", "strict-pass's predicate over rust-lang/rust at the alignment commit")):
            rows.append({"name": name, "side": "upstream", "status": "blocked", "predicate": pred,
                         "blocked": upstream.blocked, "unblock": upstream.unblock})
    by_name = {r["name"]: r for r in rows}
    if design is not None and design.status == "measured":
        for name in DESIGN_PIN_ROWS:
            now, then = pin_paths(t, name), pin_paths(design, name)
            by_name[name]["added_since_design_pin"] = sorted(now - then)
            by_name[name]["removed_since_design_pin"] = sorted(then - now)
    for claim in claims:
        row = by_name.get(claim["row"])
        if row is None:
            continue
        if not claim["found"]:
            row.setdefault("design", []).append(f"not found: /{claim['pattern']}/")
            continue
        value = row.get("value")
        at_pin = None
        if "added_since_design_pin" in row:
            at_pin = value - len(row["added_since_design_pin"]) + len(row["removed_since_design_pin"])
        if claim["value"] == value:
            verdict = "reproduced"
        elif claim["value"] == at_pin:
            verdict = (f"reproduced at the design's pin {design.revision[:10]} ({at_pin}); the measured pin has {value}: "
                       "tests/ moved, not the predicate")
        else:
            verdict = f"NOT reproduced (measured {value}" + (f"; {at_pin} at the design's pin" if at_pin is not None else "") + ")"
        row.setdefault("design", []).append(f"design:{claim['line']} says {claim['value']} [M†]: {verdict}")
    for row in rows:
        row.setdefault("status", "measured")
    return rows


def explain(trust: Side, upstream: Side, rows: list[dict], design: Side | None = None) -> list[str]:
    """The record's opening comment: how the measurement compares with the design, from the rows."""
    v = {r["name"]: r.get("value") for r in rows}
    claims = {r["name"]: r.get("design", []) for r in rows}
    aux = list(trust.excluded)
    lines = [
        "How this measurement compares with the design's [M†] numbers (D-5 Denominators, Stage 0.5, D.39):",
    ]
    if design is None:
        lines.append("* the design's header names no single superproject commit it was written against (a DESIGN-PIN "
                     "finding), so no row is read at it.")
    elif design.status == "measured":
        by = {r["name"]: r for r in rows}
        lines.append(f"* the design was written against superproject {design.revision[:10]}; since then, "
                     + ", ".join(f"{n} gained {len(by[n]['added_since_design_pin'])} and lost "
                                 f"{len(by[n]['removed_since_design_pin'])} paths" for n in DESIGN_PIN_ROWS) + ".")
    else:
        lines.append(f"* the design's pin {design.revision[:10]} is not measured: {design.blocked}")
    lines += [
        f"* strict-pass = {v['strict-pass']}; design: {'; '.join(claims['strict-pass']) or 'no claim found'}.",
        f"  compiletest's own directive parser finds {v['compiletest-unconditional']} (compiletest-unconditional);",
        f"  the two file sets differ in {v['strict-vs-compiletest.differ']} files (strict-vs-compiletest.differ).",
        f"* all-rs = {v['all-rs']}; design: {'; '.join(claims['all-rs']) or 'no claim found'}.",
        "  all-rs is not a test count: it includes files compiletest never collects as tests, namely",
        f"  {', '.join(aux) or '(none)'}. The test denominator is test-files = {v['test-files']},",
        f"  so the published fraction is {v['strict-pass']} of {v['test-files']}.",
    ]
    if upstream.status == "measured":
        added = next(r for r in rows if r["name"] == "trust-vs-upstream.added")
        lines += [
            f"* rust-lang/rust at the alignment commit has {v['upstream.strict-pass']} of {v['upstream.test-files']}"
            f" (all-rs {v['upstream.all-rs']}). The superproject's tests/ adds {v['trust-vs-upstream.added']},"
            f" removes {v['trust-vs-upstream.removed']} and changes {v['trust-vs-upstream.changed']} test files here:",
            *[f"    {f['path']} (strict modes: {', '.join(f['strict_modes']) or 'none'};"
              f" {'carries' if f['trust_marker'] else 'no'} `Trust:` marker)" for f in added.get("files", [])],
            "  E3.2.2 runs over the superproject's tests/, so strict-pass (not upstream.strict-pass) is its count.",
        ]
    else:
        lines.append(f"* the upstream comparison is blocked: {upstream.blocked}")
    lines += [
        f"* loose-pass = {v['loose-pass']}; design: {'; '.join(claims['loose-pass']) or 'no claim found'}.",
        f"  loose-pass minus strict-pass is {v['loose-pass'] - v['strict-pass']}; revision-conditional-pass"
        f" (`//@ [rev] check-pass` and no unconditional pass) is {v['revision-conditional-pass']},",
        f"  and {v['loose-vs-strict.unexplained']} files are in one set and not the other (loose-vs-strict.unexplained).",
        "  Such a file passes under some revisions only, so the strict predicate excludes it;",
        f"  {v['revision-conditional-pass.all-revisions']} of them pass under every declared revision.",
    ]
    return lines


def render(pins: C.Pins, trust: Side, upstream: Side, rows: list[dict], alignments: dict, rust_clone: Path,
           measured_at: str, design: Side | None = None) -> str:
    out = [
        f"# E0.12 denominator `{KEY}`: the strict pass-header count in tests/ui/borrowck and tests/ui/nll.",
        "#",
        "# GENERATED by scripts/trust_core/denominators/ui-tests.py --write; do not edit. Its --check re-measures",
        "# from git objects and fails when any datum differs, except measured_at_commit and each row's `design`",
        "# reading (the design text is compared, not measured). These comments are regenerated from the rows.",
        "# Design of record: docs/design/2026-09-16-trust-core-architecture.md §5.2 Stage 0.5 (exit E0.12);",
        "# consumed by E3.2.2 (BorrowCert v1 accepts every strict-pass file), stated in D-5 and D.39.",
        "#",
        *[f"# {line}".rstrip() for line in explain(trust, upstream, rows, design)],
        "",
        f"schema = {q(SCHEMA)}",
        f"key = {q(KEY)}",
        f"design = {q(C.DESIGN_REL)}",
        f"script = {q(SCRIPT_REL)}",
        f"exit = {q('E0.12')}",
        f"consumers = {tv(['E3.2.2 BorrowCert v1: every strict-pass file is accepted', 'D-5 Denominators bullet', 'D.39 erratum (215 vs the strict count)'])}",
        "# The pin: the superproject commit this record was measured at. scripts/trust_core/denominators.py",
        "# re-measures every row at it (--rev); this script's own --check measures at --rev (default HEAD)",
        "# and ignores this line, so it also says whether HEAD still gives the record.",
        f"measured_at_commit = {q(measured_at)}",
        "",
        "[inputs.trust]",
        f"what = {q('the superproject tests/ read from git objects at the measured revision')}",
        "trees = { " + ", ".join(f"{q(d)} = {q(trust.trees[d])}" for d in DIRS) + " }",
        f"test_files_digest = {q(trust.digest())}",
        "digest_rule = " + q(DIGEST_RULE),
        "alignment_records = { " + ", ".join(f"{q(k)} = {q(v)}" for k, v in sorted(alignments.items())) + " }",
        "",
        "[inputs.upstream]",
        f"repo = {q(RUST_URL)}",
        f"revision = {q(pins.alignment)}",
        f"committer_date = {q(pins.alignment_date)}",
        f"pin_record = {q(C.PINS_REL + ' [alignment]')}",
        f"clone = {q('$TRUST_CORE_SOURCES/rust (' + FETCH + '; blob-filtered, trees read at the pin)')}",
        f"status = {q(upstream.status)}",
    ]
    if upstream.status == "measured":
        out += [
            "trees = { " + ", ".join(f"{q(d)} = {q(upstream.trees[d])}" for d in DIRS) + " }",
            f"test_files_digest = {q(upstream.digest())}",
            f"blob_rule = {q('each blob read by object id from the clone when present, else from the superproject object store (same id, same bytes); no read fetches')}",
        ]
    else:
        out += [f"blocked = {q(upstream.blocked)}", f"unblock = {q(upstream.unblock)}"]
    if design is not None:
        out += [
            "",
            "[inputs.design]",
            f"what = {q('the superproject tests/ at the commit the design says it was written against, read from git objects')}",
            f"revision = {q(design.revision)}",
            f"pin_record = {q(C.DESIGN_REL + ' header, **Written read-only against** superproject')}",
            f"status = {q(design.status)}",
        ]
        if design.status == "measured":
            out += ["trees = { " + ", ".join(f"{q(d)} = {q(design.trees[d])}" for d in DIRS) + " }",
                    f"test_files_digest = {q(design.digest())}"]
        else:
            out += [f"blocked = {q(design.blocked)}", f"unblock = {q(design.unblock)}"]
    for row in rows:
        out += ["", "[[row]]", f"name = {q(row['name'])}"]
        if "value" in row:
            out.append(f"value = {row['value']}")
        for key in ("of", "side", "status", "predicate", "digest", "blocked", "unblock"):
            if key in row:
                out.append(f"{key} = {tv(row[key])}")
        for key in ("design", "excluded", "files", "added_since_design_pin", "removed_since_design_pin"):
            if key in row:
                out.append(f"{key} = {tv(row[key])}")
    return "\n".join(out) + "\n"


def measured_content(text: str) -> dict:
    """The record's data without what is not a measured input: the generation commit and each row's
    reading of the design (the design text is compared, not measured, and moves on its own)."""
    data = tomllib.loads(text)
    data.pop("measured_at_commit", None)
    for row in data.get("row", []):
        row.pop("design", None)
    return data


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", type=Path, default=C.REPO_ROOT, help="the superproject (default: this checkout)")
    parser.add_argument("--rev", default="HEAD", help="the superproject revision to measure (default HEAD)")
    parser.add_argument("--rust", type=Path, help="the rust-lang/rust clone (default $TRUST_CORE_SOURCES/rust)")
    parser.add_argument("--record", type=Path, help=f"the record (default {RECORD_REL} in --repo)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="rewrite the record from this measurement")
    mode.add_argument("--check", action="store_true", help="fail unless the record equals this measurement")
    parser.add_argument("--list", action="store_true", help="print every row's file list")
    args = parser.parse_args(argv)
    repo, rev = args.repo.resolve(), args.rev
    record = args.record or repo / RECORD_REL
    findings = C.Findings()
    try:
        pins = C.load_pins(repo / C.PINS_REL)
        commit = (C.git(repo, "rev-parse", "--verify", f"{rev}^{{commit}}") or "").strip()
        if not C.HEX40.match(commit):
            raise Fatal(f"{repo}: {rev} is not a commit")
        alignments = read_alignments(repo, commit)
        for where, value in sorted(alignments.items()):
            if value != f"rust-lang/rust:{pins.alignment}":
                findings.add("PIN", f"{where} is {value!r}, not rust-lang/rust:{pins.alignment} ({C.PINS_REL} [alignment])")
        C.verify_objects(findings, f"repository {repo}", repo)
        trust = Side("trust")
        measure(findings, trust, repo, commit, [repo])
    except (C.PinsError, Fatal) as error:
        print(f"{KEY}: {error}", file=sys.stderr)
        return 2
    upstream = Side("upstream")
    rust_clone = Path(args.rust or C.sources_root() / "rust")
    rust = C.Source("rust", RUST_URL, pins.alignment, pins.alignment_date, "objects")
    if not (rust_clone / ".git").exists():
        upstream.status = "blocked"
        upstream.blocked = f"the rust-lang/rust clone is missing at {rust_clone}"
        upstream.unblock = f"run `{FETCH}` (fills $TRUST_CORE_SOURCES/rust at the alignment), then re-run"
    else:
        pin_findings = C.Findings()
        C.verify_clone(pin_findings, rust_clone, rust, pins)
        if pin_findings.violations:
            upstream.status = "blocked"
            upstream.blocked = "; ".join(pin_findings.violations)
            upstream.unblock = f"restore the clone to its pin with `{FETCH}`, then re-run"
        else:
            try:
                measure(findings, upstream, rust_clone, pins.alignment, [rust_clone, repo])
            except Fatal as error:
                upstream.status, upstream.blocked = "blocked", str(error)
                upstream.unblock = f"re-fetch the clone with `{FETCH}`, then re-run"
    claims = design_claims(repo, commit)
    design = design_side(findings, repo, commit)
    rows = build_rows(trust, upstream, claims, design)
    text = render(pins, trust, upstream, rows, alignments, rust_clone, commit, design)
    try:
        tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:  # pragma: no cover - a renderer defect
        findings.add("RECORD", f"the rendered record is not TOML: {error}")

    print(f"{KEY}: superproject {commit} (tests/ at alignment rust-lang/rust:{pins.alignment[:12]})")
    for row in rows:
        value = row.get("value", "-")
        of = f" of {row['of']}" if "of" in row else ""
        print(f"  {row['name']:<42} {str(value):>5}{of}  [{row['status']}]")
        for note in row.get("design", []):
            print(f"      {note}")
        if row["status"] == "blocked":
            print(f"      blocked: {row['blocked']}\n      unblock: {row['unblock']}")
        if args.list:
            for path in row.get("excluded", []):
                print(f"      excluded {path}")
            for item in row.get("files", []):
                if isinstance(item, dict):
                    rest = "; ".join(f"{k} {v}" for k, v in item.items() if k != "path")
                    print(f"      {item['path']}  ({rest})")
                else:
                    print(f"      {item}")
    if upstream.status == "measured":
        print(f"  upstream distinct blob ids read, per object store: {dict(sorted(upstream.blob_sources.items()))}")

    status = 0
    if args.write and not findings.violations:
        record.parent.mkdir(parents=True, exist_ok=True)
        record.write_text(text, encoding="utf-8")
        print(f"{KEY}: wrote {record}")
    elif args.check:
        try:
            committed = measured_content(record.read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError) as error:
            findings.add("RECORD", f"{record}: {error}")
            committed = None
        if committed is not None and committed != measured_content(text):
            findings.add("RECORD", f"{record} differs from a re-measurement at {commit}; re-run with --write and review the diff")
        elif committed is not None:
            print(f"{KEY}: {record} matches the re-measurement")
    for violation in findings.violations:
        print(violation, file=sys.stderr)
        status = 1
    return status


if __name__ == "__main__":
    raise SystemExit(main())
