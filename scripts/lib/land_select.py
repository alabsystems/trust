"""The landing gate's selector: changed paths -> owning packages -> what reads
them -> the legs whose inputs they are. Imported by scripts/land_gate.py and
scripts/tests/land_gate_test.py; it runs nothing and builds nothing.

THE QUESTION. A leg (x.py check, the tests/ui/trust suite, a compiler crate's
unit tests, a crates/ member's tests, ...) can change its verdict only if one of
its INPUTS changed. This module computes each leg's inputs from the tree being
landed and intersects them with the change. Every rule below is fail-closed:
anything it cannot place selects EVERYTHING, and says why.

WHAT A LEG READS, in three parts:
  1. CODE: the dependency closure of the leg's root packages, over the declared
     dependencies of every Cargo.toml in the tree (normal, dev, build, every
     target table, optional or not, `workspace = true` resolved through its
     workspace root, `[patch]` and path dependencies resolved to the package or
     submodule they name). Declared, not feature-resolved: an edge cargo might
     not take is still an edge here, so the closure is a SUPERSET of what any
     build of the leg compiles. scripts/tests/land_gate_test.py holds it to
     `targo metadata` (every edge cargo reports among local packages is here).
  2. FILES THE CODE READS OUTSIDE ITS OWN PACKAGE: include_str!/include_bytes!/
     include!, #[path], build.rs `rerun-if-changed`, and string literals that
     climb out of the package (`"../../docs/TCB.md"`), resolved against the
     package and the source file. Two classes: COMPILE (macros, #[path], every
     literal in a build script or a proc-macro crate) and RUNTIME (literals in
     any other source, which a test or the compiler may open when it runs). A
     read that cannot be resolved statically — CARGO_MANIFEST_DIR walked up with
     parent()/ancestors()/"..", a computed include, a `git` subprocess, a path
     outside the repository — marks the package UNRESOLVED for that class, and an
     unresolved package reads EVERYTHING.
  3. NON-PACKAGE INPUTS the leg names itself (tests/ui/trust/, the trust
     run-make fixtures, x.py's own inputs).

PATHS THAT SELECT EVERYTHING (EVERYTHING_RULES): build inputs (Cargo.lock,
other lockfiles, Cargo.toml, build.rs, rust-toolchain*, .cargo/, .gitmodules,
src/stage0, src/bootstrap/, x.py, the vendored sources, the first-party
submodule pins), unclassified scripts and the registries themselves (scripts/,
tests/run_trust_comprehensive_harness.sh, tests/trust-comprehensive/,
tests/known-red/), and any path no package owns and no rule classifies.
Declared validation programs instead run their own tests and reach compiled
targets only through the same actual-reader graph as other classified inputs.
They are declared in the row table, gates/land.toml (LAND_ROWS_FILE), which
this module reads at import and which is classified as this file is.
One bounded Cargo exception is proved from BOTH committed trees by
land_manifest: additions of already-locked local dependency edges, with exact
unchanged package/source/global/feature inputs. These route through their
owning packages AND activated dependency readers; direct raw-file readers and
unresolved inputs still count. Every unrecognized delta keeps the global rule.

PROSE (PROSE_RULES) — docs/, reports/, top-level *.md and license texts — is
crossable for a leg only when no package in the leg's closure reads it (part 2
above) and no package in it is unresolved.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import bisect
import builtins
import collections.abc
import copy
import copyreg
import fnmatch
import hashlib
import io
import itertools
import json
import os
import pickle
import posixpath
import re
import stat
import subprocess
import sys
import tempfile
import time
import unicodedata
import zlib
from dataclasses import dataclass, field, replace
from typing import AbstractSet, Callable, Dict, FrozenSet, Iterable, List, NamedTuple, Optional, Sequence, Set, Tuple

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - land_gate.py re-execs under >= 3.11
    tomllib = None  # type: ignore[assignment]

EVERYTHING = "*"

# ---------------------------------------------------------------------------
# The row table (gates/land.toml): which validation tests a changed path runs.
# ---------------------------------------------------------------------------

# The landing gate's checked-in row table (docs/PLAN.md PKG-LIVE-4). It is the
# one source of the four names built below; this module holds no copy of them.
# Its header documents every key and rule. Not under scripts/: every lab repo
# keeps its table at this path, and scripts/ is what PKG-LIVE-4 empties.
LAND_ROWS_FILE = "gates/land.toml"
LAND_ROWS_SCHEMA = "trust.land-rows.v1"
# This module reads the table at import, so the table is this selector's data,
# as the dict literals it replaced were this file's text. A change to the table
# is classified as a change to this file is, and selects what this file selects
# (is_validation_program, validation_program_tests): never every leg by falling
# through the rules unmapped, and never less than an edit to those literals did.
LAND_ROWS_READER = "scripts/lib/land_select.py"
# The argv of a validation row, less its module: the one command this reader knows.
VALIDATION_ROW_COMMAND = ("python3", "-B", "scripts/land_gate.py", "validation-tests")
_ROW_ID = re.compile(r"validation\.([A-Za-z_][A-Za-z0-9_]*)\Z")
_NOT_RUN_KINDS = ("red", "unjudgeable")
_LAND_TYPE_NAMES = {str: "a string", list: "an array", dict: "a table"}


class LandRowsError(ValueError):
    """The row table is missing, unreadable, or breaks one of its rules."""


class LandRows(NamedTuple):
    """gates/land.toml as loaded: its rows by the file each one runs, and the
    four tables the selector and its tests read."""
    covered: Tuple[str, ...]
    row_files: Dict[str, str]        # [[row]] id -> the tracked file of the module it runs
    not_run_files: Dict[str, str]    # [[not_run]] id -> its file
    program_tests: Dict[str, Tuple[str, ...]]
    test_subjects: Dict[str, Tuple[str, ...]]
    unjudged_modules: Dict[str, str]
    unmapped_red: Dict[str, str]


def _land_fields(where: str, value: object, fields: Dict[str, type]) -> dict:
    """`value` as a table holding exactly `fields`, each of its type."""
    if not isinstance(value, dict):
        raise LandRowsError(f"{where}: not a table")
    unknown = sorted(set(value) - set(fields))
    if unknown:
        raise LandRowsError(f"{where}: unknown key {', '.join(map(repr, unknown))} (this reader knows "
                            f"{', '.join(fields)})")
    for key, kind in fields.items():
        if key not in value:
            raise LandRowsError(f"{where}: missing key {key!r}")
        if type(value[key]) is not kind:
            raise LandRowsError(f"{where}: {key} is not {_LAND_TYPE_NAMES[kind]}")
    return value


def _land_strings(where: str, values: list, *, ordered: bool) -> Tuple[str, ...]:
    """A non-empty array of non-empty strings without a repeat; sorted, when `ordered`."""
    if not values:
        raise LandRowsError(f"{where}: empty")
    for value in values:
        if type(value) is not str or not value.strip():
            raise LandRowsError(f"{where}: {value!r} is not a non-empty string")
    if len(set(values)) != len(values):
        raise LandRowsError(f"{where}: {sorted(v for v in set(values) if values.count(v) > 1)[0]!r} is listed twice")
    if ordered and values != sorted(values):
        raise LandRowsError(f"{where}: not sorted ({next(b for a, b in zip(values, values[1:]) if b < a)!r} "
                            "is out of order)")
    return tuple(values)


def _land_ids(kind: str, entries: list, fields: Dict[str, type]) -> List[Tuple[str, str, dict]]:
    """(id, module name, entry) of each [[kind]] entry: known keys, and ids
    that are well formed, unique and sorted."""
    out: List[Tuple[str, str, dict]] = []
    seen: Set[str] = set()
    for position, entry in enumerate(entries, 1):
        if not isinstance(entry, dict) or type(entry.get("id")) is not str:
            raise LandRowsError(f"[[{kind}]] #{position}: no string id")
        identity = entry["id"]
        where = f"[[{kind}]] {identity}"
        _land_fields(where, entry, fields)
        named = _ROW_ID.match(identity)
        if not named:
            raise LandRowsError(f"{where}: the id is not validation.<module> (the one kind of row this reader knows)")
        if identity in seen:
            raise LandRowsError(f"{where}: duplicate id")
        if out and identity < out[-1][0]:
            raise LandRowsError(f"{where}: ids are not sorted (it follows {out[-1][0]})")
        seen.add(identity)
        out.append((identity, named.group(1), entry))
    return out


def parse_land_rows(text: str) -> LandRows:
    """The row table from its text, or LandRowsError naming the first rule it
    breaks. Pure: it reads no file and asks git nothing, so the rule that needs
    the tree (`covered`) is land_rows_coverage's."""
    if tomllib is None:
        raise LandRowsError("the row table needs Python >= 3.11 (tomllib)")
    try:
        doc = tomllib.loads(text)
    except tomllib.TOMLDecodeError as exc:
        raise LandRowsError(f"not TOML: {exc}") from exc
    _land_fields("the table", doc, {"schema": str, "covered": list, "validation_programs": dict,
                                    "row": list, "not_run": list})
    if doc["schema"] != LAND_ROWS_SCHEMA:
        raise LandRowsError(f"schema is {doc['schema']!r}; this reader knows {LAND_ROWS_SCHEMA!r}")
    covered = _land_strings("covered", doc["covered"], ordered=True)

    modules: Dict[str, str] = {}          # row id -> the module its command runs
    row_files: Dict[str, str] = {}
    selected_by: Dict[str, List[str]] = {}  # path -> the ids of the rows it selects, in id order
    for identity, name, row in _land_ids("row", doc["row"], {
            "id": str, "command": list, "selects_on": list, "catches": str, "not_yet_targo": str}):
        where = f"[[row]] {identity}"
        module = "scripts.tests." + name
        if row["command"] != [*VALIDATION_ROW_COMMAND, module]:
            raise LandRowsError(f"{where}: command is not this row's validation runner "
                                f"{[*VALIDATION_ROW_COMMAND, module]!r}")
        if not row["selects_on"]:
            raise LandRowsError(f"{where}: empty selects_on (a row no path selects never runs: declare what "
                                "selects it, or move it to [[not_run]] with the reason)")
        for path in _land_strings(f"{where}: selects_on", row["selects_on"], ordered=True):
            selected_by.setdefault(path, []).append(identity)
        if not row["catches"].strip():
            raise LandRowsError(f"{where}: empty catches (say what defect the row exists to catch)")
        if not row["not_yet_targo"].strip():
            raise LandRowsError(f"{where}: empty not_yet_targo (the command is not a targo verb or a test "
                                "target; say why not yet)")
        modules[identity] = module
        row_files[identity] = f"scripts/tests/{name}.py"

    not_run_files: Dict[str, str] = {}
    reasons: Dict[str, Dict[str, str]] = {kind: {} for kind in _NOT_RUN_KINDS}
    for identity, name, entry in _land_ids("not_run", doc["not_run"], {
            "id": str, "path": str, "kind": str, "why": str}):
        where = f"[[not_run]] {identity}"
        if identity in modules:
            raise LandRowsError(f"{where}: also a [[row]] (scripts/tests/{name}.py is one or the other, never both)")
        if entry["path"] != f"scripts/tests/{name}.py":
            raise LandRowsError(f"{where}: path is {entry['path']!r}, not its module's file "
                                f"'scripts/tests/{name}.py'")
        if entry["kind"] not in _NOT_RUN_KINDS:
            raise LandRowsError(f"{where}: kind is {entry['kind']!r}, not one of {', '.join(_NOT_RUN_KINDS)}")
        if not entry["why"].strip():
            raise LandRowsError(f"{where}: empty why")
        not_run_files[identity] = entry["path"]
        reasons[entry["kind"]]["scripts.tests." + name] = entry["why"]

    program_tests: Dict[str, Tuple[str, ...]] = {}
    for path, listed in doc["validation_programs"].items():
        where = f"validation_programs {path!r}"
        if type(listed) is not list:
            raise LandRowsError(f"{where}: not an array of row ids")
        ids = _land_strings(where, listed, ordered=False)
        unknown = [identity for identity in ids if identity not in modules]
        if unknown:
            raise LandRowsError(f"{where}: {unknown[0]} is not a [[row]]")
        if set(ids) != set(selected_by.get(path, ())):
            differ = sorted(set(ids) ^ set(selected_by.get(path, ())))
            raise LandRowsError(f"{where}: its rows are not exactly the rows whose selects_on names the path "
                                f"({', '.join(differ)} is in one and not the other)")
        program_tests[path] = tuple(modules[identity] for identity in ids)
    test_subjects = {path: tuple(sorted(modules[identity] for identity in ids))
                     for path, ids in sorted(selected_by.items()) if path not in program_tests}
    return LandRows(covered, row_files, not_run_files, program_tests, test_subjects,
                    reasons["unjudgeable"], reasons["red"])


def read_land_rows_text(root: str) -> str:
    """The table's text under `root`, read only from a regular file reached
    through real directories. Git can track a symbolic link at either name, and
    a link's target is a file the gate knows nothing of: the gate hashes and
    watches the table by this one path (land_gate's GATE_FILES and loaded
    readers), so a table read through a link could change with no key and no
    reload noticing. OSError when the table is absent or unreadable;
    LandRowsError when a name on the way is not what it must be."""
    parts = LAND_ROWS_FILE.split("/")
    here = root
    for position, part in enumerate(parts, 1):
        here = os.path.join(here, part)
        mode = os.lstat(here).st_mode
        name = "/".join(parts[:position])
        if stat.S_ISLNK(mode):
            raise LandRowsError(f"{name} is a symbolic link under {root}; the row table is read only from a "
                                "regular file in a real directory (the gate hashes and watches this path, not "
                                "a link's target)")
        if position < len(parts) and not stat.S_ISDIR(mode):
            raise LandRowsError(f"{name} is not a directory under {root}")
        if position == len(parts) and not stat.S_ISREG(mode):
            raise LandRowsError(f"{name} is not a regular file under {root}")
    descriptor = os.open(here, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    with os.fdopen(descriptor, "rb") as source:
        if not stat.S_ISREG(os.fstat(source.fileno()).st_mode):
            raise LandRowsError(f"{LAND_ROWS_FILE} is not a regular file under {root}")
        return source.read().decode("utf-8")


def load_land_rows(root: Optional[str] = None) -> LandRows:
    """The table of the checkout that holds this module (or of `root`)."""
    if root is None:
        root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
    try:
        text = read_land_rows_text(root)
    except LandRowsError as exc:
        raise LandRowsError(f"{LAND_ROWS_FILE}: {exc}; the selector selects nothing without it") from None
    except (OSError, UnicodeDecodeError) as exc:
        raise LandRowsError(f"{LAND_ROWS_FILE}: the landing gate's row table cannot be read under {root} "
                            f"({exc.__class__.__name__}: {exc}); the selector selects nothing without it") from exc
    try:
        return parse_land_rows(text)
    except LandRowsError as exc:
        raise LandRowsError(f"{LAND_ROWS_FILE}: {exc}") from None


def _covered_match(path: str, pattern: str) -> bool:
    """A `covered` glob: `*` stays inside one path component."""
    parts, wanted = path.split("/"), pattern.split("/")
    return len(parts) == len(wanted) and all(fnmatch.fnmatchcase(a, b) for a, b in zip(parts, wanted))


class LandRowsGap(NamedTuple):
    """One break of the `covered` rule: `kind` is "uncovered" (a covered file
    no entry names), "doubly-covered" (one more than one entry names) or
    "untracked" (an entry whose file the tree does not track); `text` is
    land_rows_coverage's line for it."""
    kind: str
    path: str
    text: str


def land_rows_gaps(table: LandRows, tracked: Iterable[str]) -> List[LandRowsGap]:
    """land_rows_coverage with each break's kind and file: the one
    implementation of the rule, for a caller that keys or repairs each break
    (`land_gate.py rows --check`, the push row fast.land-rows-coverage)."""
    tracked = set(tracked)
    owners: Dict[str, List[str]] = {}
    for kind, files in (("row", table.row_files), ("not_run", table.not_run_files)):
        for identity, path in files.items():
            owners.setdefault(path, []).append(f"[[{kind}]] {identity}")
    gaps = []
    for path in sorted(tracked):
        if any(_covered_match(path, pattern) for pattern in table.covered):
            mine = owners.get(path, [])
            if not mine:
                gaps.append(LandRowsGap("uncovered", path, f"{path}: neither a [[row]] nor a [[not_run]]"))
            elif len(mine) > 1:
                gaps.append(LandRowsGap("doubly-covered", path,
                                        f"{path}: {' and '.join(mine)} (exactly one, never both)"))
    for path, mine in sorted(owners.items()):
        if path not in tracked:
            gaps.append(LandRowsGap("untracked", path, f"{mine[0]}: {path} is not a tracked file"))
    return gaps


def land_rows_coverage(table: LandRows, tracked: Iterable[str]) -> List[str]:
    """What breaks the table's `covered` rule in a tree that tracks `tracked`:
    a covered file that is not exactly one [[row]] or exactly one [[not_run]],
    and an entry whose file the tree does not track. Empty when the rule holds."""
    return [gap.text for gap in land_rows_gaps(table, tracked)]


_LAND_ROWS = load_land_rows()
# Validation programs do not themselves produce compiler inputs. Their tests
# must run when they change, while a compiler/package that actually reads one
# still reaches it through the normal input graph. Unknown scripts retain the
# conservative all-legs rule below. This is an execution dependency declaration,
# not permission to reuse a proof with different premises. The table's
# [validation_programs].
VALIDATION_PROGRAM_TESTS: Dict[str, Tuple[str, ...]] = _LAND_ROWS.program_tests
# Every other scripts/tests module, by what it tests (LAND-SELECT-VALIDATION-REACH-1,
# 2026-11-10): the selects_on paths of the table's rows that are not validation
# programs. ADDITIVE: unlike VALIDATION_PROGRAM_TESTS, a key here keeps every
# other rule, EVERYTHING_RULES included, so it never narrows any leg's selection.
VALIDATION_TEST_SUBJECTS: Dict[str, Tuple[str, ...]] = _LAND_ROWS.test_subjects
# The table's [[not_run]] entries, by kind: scripts/tests/*_test.py modules that
# `land_gate.py validation-tests` cannot judge ("unjudgeable"), and modules red on
# main when the rest were mapped ("red"; docs/OPEN_ISSUES.md VALIDATION-UNMAPPED-RED-1),
# each with its reason. Nothing selects either.
VALIDATION_UNJUDGED_MODULES: Dict[str, str] = _LAND_ROWS.unjudged_modules
VALIDATION_UNMAPPED_RED: Dict[str, str] = _LAND_ROWS.unmapped_red
# Only the four names above are read after import: _compose_discovery replaces
# the first two when incoming main changes the table.
del _LAND_ROWS


def is_validation_program(path: str) -> bool:
    """A declared validation program, or the row table that declares them
    (classified as its reader is: LAND_ROWS_READER)."""
    return (path in VALIDATION_PROGRAM_TESTS
            or (path == LAND_ROWS_FILE and LAND_ROWS_READER in VALIDATION_PROGRAM_TESTS))


def validation_program_tests(path: str) -> Tuple[str, ...]:
    """The tests a changed validation program runs; for the row table, its reader's."""
    return VALIDATION_PROGRAM_TESTS.get(LAND_ROWS_READER if path == LAND_ROWS_FILE else path, ())


def validation_program_paths() -> List[str]:
    """Every path is_validation_program accepts."""
    return [*VALIDATION_PROGRAM_TESTS, *([LAND_ROWS_FILE] if is_validation_program(LAND_ROWS_FILE) else ())]


def validation_test_modules(changed: Sequence[str]) -> List[str]:
    """Tests of changed validation programs, of the changed subjects of every
    other scripts/tests module, and of the normal Cargo feature graph."""
    modules = {module for path in changed
               for selected in (validation_program_tests(path), VALIDATION_TEST_SUBJECTS.get(path, ()))
               for module in selected}
    # These are still compiler inputs under EVERYTHING_RULES. Also exercise
    # actual normal/test feature resolution whenever an activation edge changes.
    if any(fold(path).rsplit("/", 1)[-1] == "cargo.toml" for path in changed):
        modules.add("scripts.tests.mir_test_oracle_feature_test")
    return sorted(modules)

# ---------------------------------------------------------------------------
# Path rules.
# ---------------------------------------------------------------------------

# (pattern, reason). A changed path matching any of these selects every leg.
# Patterns are fnmatch globs over the repo-relative path; `**` is spelled as a
# prefix match by ending the pattern with `/`.
EVERYTHING_RULES: Tuple[Tuple[str, str], ...] = (
    ("Cargo.lock", "a lockfile is a build input"),
    ("*/Cargo.lock", "a lockfile is a build input"),
    ("*.lock", "a lockfile is a build input"),
    ("Cargo.toml", "a manifest is a build input (it moves the graph this selector reads)"),
    ("*/Cargo.toml", "a manifest is a build input (it moves the graph this selector reads)"),
    ("build.rs", "a build script is a build input"),
    ("*/build.rs", "a build script is a build input"),
    ("rust-toolchain", "a toolchain pin is a build input"),
    ("rust-toolchain.toml", "a toolchain pin is a build input"),
    ("*/rust-toolchain", "a toolchain pin is a build input"),
    ("*/rust-toolchain.toml", "a toolchain pin is a build input"),
    ("lean-toolchain", "a toolchain pin is a build input"),
    ("*/lean-toolchain", "a toolchain pin is a build input"),
    (".cargo/", "Cargo configuration is a build input"),
    ("*/.cargo/", "Cargo configuration is a build input"),
    (".gitmodules", "the submodule table is a pin file"),
    ("first-party/", "a first-party submodule pin moved"),
    ("src/stage0", "the stage0 pin is a build input"),
    ("src/version", "the version file is a build input"),
    ("src/rust-compat-version", "the version file is a build input"),
    ("release/trust-version.toml", "the release/alignment pin is a build input"),
    ("src/bootstrap/", "the build system itself"),
    ("x.py", "the build entry point"),
    ("x", "the build entry point"),
    ("x.ps1", "the build entry point"),
    ("bootstrap.example.toml", "the build configuration template"),
    ("tools/preflight.*", "x.py runs the preflight before every build"),
    ("vendor/", "a vendored dependency is a build input"),
    ("src/llvm-project/", "LLVM is a build input of every compiler leg"),
    ("scripts/", "a gate script or a script a leg runs (fail-closed: every script)"),
    ("tests/run_trust_comprehensive_harness.sh", "the gate manifest (registry)"),
    ("tests/trust-comprehensive/", "the quarantine ledger (registry)"),
    ("tests/known-red/", "a ratchet baseline (registry)"),
)

# Prose: crossable unless a leg's closure reads it (see module doc).
PROSE_RULES: Tuple[str, ...] = (
    "docs/",
    "reports/",
    "*.md",                # top-level only: a package-owned .md is that package's file
    "LICENSE-APACHE",
    "LICENSE-MIT",
    "LICENSES/",
    "COPYRIGHT",
    "NOTICE",
    "REUSE.toml",
    "license-metadata.json",
)

# Test-suite trees that no landing leg runs except the two named here, and
# that are read by code only through the escape scan. Paths under them are
# crossable for a leg unless the leg names them (ui-trust, run-make-trust) or
# its closure reads them. Every other tests/ subtree is NOT here: it stays
# unclassified (everything) until someone measures its readers.
SUITE_RULES: Tuple[str, ...] = (
    "tests/ui/",
    "tests/run-make/",
    "tests/run-make-cargo/",
    "tests/codegen-llvm/",
    "tests/codegen-units/",
    "tests/assembly-llvm/",
    "tests/incremental/",
    "tests/debuginfo/",
    "tests/mir-opt/",
    "tests/pretty/",
    "tests/crashes/",
    "tests/coverage/",
    "tests/rustdoc-html/",
    "tests/rustdoc-ui/",
    "tests/rustdoc-json/",
    "tests/rustdoc-js/",
    "tests/rustdoc-js-std/",
    "tests/rustdoc-gui/",
    "tests/ui-fulldeps/",
    "tests/build-std/",
    "tests/coverage-run-rustdoc/",
)


def _match(path: str, pattern: str) -> bool:
    if pattern.endswith("/"):
        if pattern.startswith("*/"):
            needle = pattern[1:]
            return needle in "/" + path + "/" if "/" in path else False
        return path.startswith(pattern) or path == pattern[:-1]
    if "/" not in pattern and "*" in pattern:
        # A bare glob like "*.md" or "*.lock": top-level for prose, any depth for locks.
        return fnmatch.fnmatchcase(path, pattern)
    return fnmatch.fnmatchcase(path, pattern)


def everything_reason(path: str) -> Optional[str]:
    # Each rule also matches the path as the landing host's file system
    # compares it (fold): Cargo there runs `<pkg>/build.RS` as the default build
    # script and reads Cargo.TOML as the manifest, and `Vendor/x` is in vendor/.
    # Folding only adds matches, so it can only select more. (Until
    # LAND-GATE-EW1-FOLLOWUP-REVIEW-3 a rule matched only its exact spelling.)
    if is_validation_program(path):
        return None
    folded = fold(path)
    for pattern, reason in EVERYTHING_RULES:
        if pattern == "*.lock":
            if path.endswith(".lock") or folded.endswith(".lock"):
                return f"{reason} ({pattern})"
            continue
        if _match(path, pattern) or _match(folded, fold(pattern)):
            return f"{reason} ({pattern})"
    return None


def is_prose(path: str) -> bool:
    for pattern in PROSE_RULES:
        if pattern == "*.md":
            if "/" not in path and path.endswith(".md"):
                return True
            continue
        if _match(path, pattern):
            return True
    return False


def is_suite_path(path: str) -> bool:
    return any(path.startswith(p) for p in SUITE_RULES)


# ---------------------------------------------------------------------------
# Reading a tree from git objects (never the worktree: the landing judges a
# commit).
# ---------------------------------------------------------------------------


# What git must not take from the gate's environment: its repository-local
# variables (`git rev-parse --local-env-vars`, as land_gate's git_query_env
# drops them), the configuration they carry, and the pathspec switches. A
# GIT_DIR, GIT_OBJECT_DIRECTORY or GIT_INDEX_FILE chose another repository's
# objects and replace refs, and GIT_LITERAL_PATHSPECS or GIT_NOGLOB_PATHSPECS
# made `:(icase)*.rs` match no file: the escape scan read nothing and left
# nothing unresolved. Replace objects are never read: the landing judges the
# commit's own. (Round 6 of LAND-GATE-EW1-FOLLOWUP-REVIEW-4, the IR reader
# audit.)
GIT_ENV_DROPPED = frozenset({
    "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_CONFIG", "GIT_CONFIG_PARAMETERS", "GIT_CONFIG_COUNT",
    "GIT_OBJECT_DIRECTORY", "GIT_DIR", "GIT_WORK_TREE", "GIT_IMPLICIT_WORK_TREE", "GIT_GRAFT_FILE",
    "GIT_INDEX_FILE", "GIT_NO_REPLACE_OBJECTS", "GIT_REPLACE_REF_BASE", "GIT_PREFIX", "GIT_SHALLOW_FILE",
    "GIT_COMMON_DIR", "GIT_LITERAL_PATHSPECS", "GIT_GLOB_PATHSPECS", "GIT_NOGLOB_PATHSPECS",
    "GIT_ICASE_PATHSPECS", "GIT_ATTR_SOURCE"})
GIT_ENV_CONFIG_INDEXED = re.compile(r"GIT_CONFIG_(?:KEY|VALUE)_\d+$")


def git_env(**extra: str) -> Dict[str, str]:
    """The environment every git query of the selector runs in (GIT_ENV_DROPPED)."""
    env = {k: v for k, v in os.environ.items() if k not in GIT_ENV_DROPPED and not GIT_ENV_CONFIG_INDEXED.match(k)}
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env.update(extra)
    return env


def git(repo: str, *args: str, input_bytes: Optional[bytes] = None) -> bytes:
    proc = subprocess.run(["git", "-C", repo, *args], input=input_bytes, capture_output=True, env=git_env())
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {proc.stderr.decode('utf-8', 'replace').strip()}")
    return proc.stdout


def _tree_entries(repo: str, treeish: str) -> Dict[str, Tuple[str, str]]:
    """path -> (mode, object id) of every entry of a commit's or a tree's tree."""
    raw = git(repo, "ls-tree", "-r", "-z", "--full-tree", treeish)
    entries: Dict[str, Tuple[str, str]] = {}
    for rec in raw.split(b"\0"):
        if not rec:
            continue
        meta, _, path = rec.partition(b"\t")
        mode, _typ, sha = meta.decode().split(" ")
        entries[path.decode("utf-8", "surrogateescape")] = (mode, sha)
    return entries


@dataclass
class TreeIndex:
    repo: str
    rev: str
    tree: str
    entries: Dict[str, Tuple[str, str]]  # path -> (mode, object sha)
    # Classification inputs only; these do not authorize execution-cache reuse.
    _content_reads: Set[str] = field(default_factory=set, init=False, repr=False, compare=False)
    # Immutable object bytes only, private to this index's discovery. A new
    # path still records a content read and all graph/selection roles remain
    # fresh; worktree bytes are never cache authority. Bytes carried in a
    # stored graph (the graph store below) are used only after each hashes to
    # the object id it is filed under. Object identity, rather than path,
    # handles aliases and prevents a newly selected blob from inheriting an
    # older path's bytes.
    _blob_bytes: Dict[str, bytes] = field(default_factory=dict, init=False, repr=False, compare=False)

    @classmethod
    def load(cls, repo: str, rev: str) -> "TreeIndex":
        commit = git(repo, "rev-parse", "--verify", f"{rev}^{{commit}}").decode().strip()
        tree = git(repo, "rev-parse", f"{commit}^{{tree}}").decode().strip()
        return cls(repo, commit, tree, _tree_entries(repo, commit))

    def gitlinks(self) -> List[str]:
        return sorted(p for p, (mode, _) in self.entries.items() if mode == "160000")

    def read_blobs(self, paths: Sequence[str]) -> Dict[str, bytes]:
        self._content_reads.update(paths)
        if not paths:
            return {}
        missing = {}
        for p in paths:
            sha = self.entries[p][1]
            if sha not in self._blob_bytes:
                missing.setdefault(sha, p)
        if not missing:
            return {p: self._blob_bytes[self.entries[p][1]] for p in paths}
        req = b"".join(sha.encode() + b"\n" for sha in missing)
        out = git(self.repo, "cat-file", "--batch", input_bytes=req)
        retained: Dict[str, bytes] = {}
        pos = 0
        for sha, p in missing.items():
            nl = out.find(b"\n", pos)
            if nl < 0:
                raise RuntimeError(f"incomplete Git blob response for {p} ({sha}) at {self.rev}")
            header = out[pos:nl].split()
            # cat-file --batch succeeds even when a promised object is absent.
            # Refuse the whole read so the gate cannot judge an incomplete graph.
            if len(header) == 2 and header[1] == b"missing":
                raise RuntimeError(
                    f"missing Git blob for {p} ({self.entries[p][1]}) at {self.rev}; "
                    "restore or hydrate missing objects before selecting landing gates")
            if (len(header) != 3 or header[0] != sha.encode() or header[1] != b"blob"
                    or not header[2].isdigit()):
                raise RuntimeError(f"invalid Git blob response for {p} ({sha}) at {self.rev}")
            size = int(header[2])
            body = out[nl + 1: nl + 1 + size]
            if len(body) != size or out[nl + 1 + size:nl + 2 + size] != b"\n":
                raise RuntimeError(f"incomplete Git blob response for {p} ({sha}) at {self.rev}")
            # Authenticate retained bytes once, including the Git object kind
            # and size. Future hits reuse those exact bytes, never a prior
            # classification, package role or validation outcome.
            digest = hashlib.new("sha1" if len(sha) == 40 else "sha256")
            digest.update(f"blob {size}\0".encode())
            digest.update(body)
            if digest.hexdigest() != sha:
                raise RuntimeError(f"Git blob identity mismatch for {p} ({sha}) at {self.rev}")
            retained[sha] = body
            pos = nl + 1 + size + 1
        if pos != len(out):
            raise RuntimeError(f"trailing Git blob response bytes at {self.rev}")
        # A failed or partial batch contributes no retained byte authority.
        self._blob_bytes.update(retained)
        return {p: self._blob_bytes[self.entries[p][1]] for p in paths}

    def fingerprint(self, prefixes: Iterable[str]) -> str:
        """sha256 over every (path, mode, sha) under any of `prefixes`
        (EVERYTHING = the whole tree). The prefix set itself is hashed too, so
        two legs with different input sets never share a fingerprint."""
        prefixes = sorted(set(prefixes))
        h = hashlib.sha256()
        h.update(json.dumps(prefixes).encode())
        if EVERYTHING in prefixes:
            h.update(self.tree.encode())
            return h.hexdigest()
        # A glob input (an audit's "*.json", a suite's collection "tests/ui/*.rs")
        # names every path it matches: those are inputs exactly as a prefix's are.
        globs = [p for p in prefixes if any(ch in p for ch in "*?[")]
        exact = set(prefixes) - set(globs)
        for path in sorted(self.entries):
            if _under_any(path, exact) or any(fnmatch.fnmatchcase(path, gl) for gl in globs):
                mode, sha = self.entries[path]
                h.update(f"{mode} {sha} {path}\n".encode("utf-8", "surrogateescape"))
        return h.hexdigest()


def _under_any(path: str, prefixes: Set[str]) -> bool:
    if path in prefixes:
        return True
    i = path.find("/")
    while i != -1:
        if path[:i] in prefixes:
            return True
        i = path.find("/", i + 1)
    return False


# ---------------------------------------------------------------------------
# The package graph.
# ---------------------------------------------------------------------------

DEP_TABLES = ("dependencies", "dev-dependencies", "build-dependencies")


@dataclass
class Package:
    dir: str
    name: str
    proc_macro: bool = False
    dep_names: Set[str] = field(default_factory=set)
    path_deps: Set[str] = field(default_factory=set)  # repo-relative dirs (may sit inside a gitlink)
    deps: Set[str] = field(default_factory=set)       # resolved node ids (package dirs or gitlinks)
    reads: List["Read"] = field(default_factory=list)
    unresolved: List["Read"] = field(default_factory=list)
    history: List["Read"] = field(default_factory=list)  # sites whose result depends on git history
    walks: List["Walk"] = field(default_factory=list)            # files reaching above the package
    # Packages (or gitlinks) whose SOURCE this package compiles as its own: a
    # Cargo target `path`/`build` outside the package, a `#[path]` module or an
    # `include!`d .rs file owned by another package. Edges of the graph (in
    # `deps`) as much as a declared dependency is: their files, their escape
    # reads and their own dependencies are inputs of whatever compiles this one.
    foreign: List[str] = field(default_factory=list)
    build_scripts: Set[str] = field(default_factory=set)  # repo-relative build script path(s)


@dataclass
class Graph:
    index: TreeIndex
    packages: Dict[str, Package]                 # dir -> package
    by_name: Dict[str, Set[str]]
    gitlinks: List[str]
    opaque: Dict[str, str]                       # dir of an unparsable manifest -> error
    workspace_members: Dict[str, Set[str]]       # workspace root dir -> member dirs
    _grep_pathspecs: Set[Tuple[str, ...]] = field(default_factory=set, init=False, repr=False, compare=False)
    _classification_reads_complete: bool = field(default=False, init=False, repr=False, compare=False)
    # Live refresh reuses only fully bounded scans with identical complete inputs.
    global_scan_packages: Set[str] = field(default_factory=set)
    reused_packages: Set[str] = field(default_factory=set)
    reused_tokenizations: int = 0
    # (grep args, positive pathspec) -> (the files a whole-tree listing query
    # listed, the literal paths it excluded): _listed_by_grep's answers, which
    # a later graph takes for each file whose blob is unchanged.
    grep_listings: Dict[Tuple[Tuple[str, ...], str], Tuple[FrozenSet[str], FrozenSet[str]]] = field(
        default_factory=dict, repr=False, compare=False)
    # (fact kind, Git object id of the exact bytes it was computed from, the
    # exact global parameter it read) -> a pure text predicate's answer
    # (BLOB_FACT_KINDS), which a later graph takes for any file holding
    # that blob (_blob_fact). No fact holds a path, owner or context.
    blob_facts: Dict[Tuple[str, str, object], object] = field(default_factory=dict, repr=False, compare=False)
    lex_cache: Dict[str, object] = field(default_factory=dict)
    test_path_modules: Set[str] = field(default_factory=set)
    prod_path_modules: Set[str] = field(default_factory=set)
    blob_cache: Dict[str, bytes] = field(default_factory=dict)
    # pkg dir -> (_build_reach: the files it compiles, whether that is all, why not)
    build_reach_cache: Dict[str, Tuple[FrozenSet[str], bool, Optional[str]]] = field(default_factory=dict,
                                                                                     repr=False)
    # Derived only from this graph's immutable committed TreeIndex. Tuples and
    # frozensets keep a caller (or a copied graph) from changing another result.
    run_make_dirs_cache: Optional[Tuple[str, ...]] = field(default=None, repr=False)
    run_make_reads_cache: Optional[Tuple[Tuple[str, FrozenSet[str]], ...]] = field(default=None, repr=False)
    link_targets_cache: Optional[Tuple[Tuple[str, Optional[str]], ...]] = field(default=None, repr=False)

    def owner(self, path: str) -> Optional[str]:
        """The deepest package dir (or gitlink) containing `path`."""
        for g in self.gitlinks:
            if path == g or path.startswith(g + "/"):
                return g
        best = None
        parts = path.split("/")
        for i in range(len(parts) - 1, 0, -1):
            d = "/".join(parts[:i])
            if d in self.packages:
                best = d
                break
        if best is None and "" in self.packages:
            best = ""
        return best

    def opaque_owner(self, path: str) -> Optional[str]:
        for d, err in self.opaque.items():
            if d == "" or path == d or path.startswith(d + "/"):
                return f"{d or '.'}/Cargo.toml does not parse ({err})"
        return None

    def closure(self, roots: Iterable[str]) -> Set[str]:
        seen: Set[str] = set()
        stack = [r for r in roots if r in self.packages or r in self.gitlinks]
        while stack:
            n = stack.pop()
            if n in seen:
                continue
            seen.add(n)
            pkg = self.packages.get(n)
            if pkg is not None:
                stack.extend(d for d in pkg.deps if d not in seen)
        return seen


def _norm(base: str, rel: str) -> Optional[str]:
    """Repo-relative normalised join, or None when it leaves the repository."""
    joined = posixpath.normpath(posixpath.join(base, rel)) if base else posixpath.normpath(rel)
    if joined == ".":
        return ""
    if joined.startswith("../") or joined == ".." or joined.startswith("/"):
        return None
    return joined


def _dep_specs(table: dict) -> Iterable[Tuple[str, object]]:
    for key, spec in (table or {}).items():
        yield key, spec


def _collect_dep_tables(doc: dict) -> List[dict]:
    tables = [doc.get(t, {}) for t in DEP_TABLES]
    for _target, ttab in (doc.get("target", {}) or {}).items():
        if isinstance(ttab, dict):
            tables.extend(ttab.get(t, {}) for t in DEP_TABLES)
    return [t for t in tables if isinstance(t, dict)]


def _expand_members(index: TreeIndex, root: str, patterns: Sequence[str], manifest_dirs: Set[str]) -> Set[str]:
    out: Set[str] = set()
    for pat in patterns:
        full = _norm(root, pat)
        if full is None:
            continue
        if any(ch in full for ch in "*?["):
            out.update(d for d in manifest_dirs if fnmatch.fnmatchcase(d, full))
        else:
            out.add(full)
    return out


def _scan_structure(index: TreeIndex):
    # New regular files in existing directories are judged against each
    # complete footprint. Resolution structure and dependency declarations
    # remain global inputs, including previously absent audit registries.
    directories = {parent for path in index.entries for parent in _proper_ancestors(path)}
    top = {path.partition("/")[0] for path in index.entries}
    declarations = {path: entry for path, entry in index.entries.items()
                    if entry[0] not in REGULAR or path.lower().endswith(("cargo.toml", "cargo.lock"))
                    or path in (".gitmodules", ".cargo/config", ".cargo/config.toml",
                                "rust-toolchain", "rust-toolchain.toml")}
    return directories, top, declarations


def _reusable_package_scans(previous: Optional[Graph], current: Graph) -> Set[str]:
    if (previous is None or previous.index.repo != current.index.repo
            or not previous.__dict__.get("_scan_complete", False)):
        return set()
    if AUDITS_OVERRIDE is not None or _scan_structure(previous.index) != _scan_structure(current.index):
        return set()
    common = previous.index.entries.keys() & current.index.entries.keys()
    if any(previous.index.entries[path][0] != current.index.entries[path][0] for path in common):
        return set()
    # Review data is source-scoped. A changed premise expires that source's
    # exemption, even when neither its own blob nor the row text changed.
    def reviews(graph):
        result = {}
        for kind, rows in (("audit", load_audits(graph)), ("not_path", load_not_paths(graph))):
            for path, row in rows.items():
                paths = [path, *(pin["file"] for pin in row.get("premises", []))]
                signature = (kind, json.dumps({key: value for key, value in row.items() if key != "reason"},
                                              sort_keys=True, default=str),
                             tuple((source, graph.index.entries.get(source)) for source in paths))
                result.setdefault(path, []).append(signature)
        return result
    old_reviews, new_reviews = reviews(previous), reviews(current)
    changed_reviews = {path for path in old_reviews.keys() | new_reviews.keys()
                       if old_reviews.get(path) != new_reviews.get(path)}
    # Compare each immutable path/mode/blob identity once. Testing the small
    # delta against complete readsets avoids rehashing the whole repository
    # separately for every package during an otherwise unchanged refresh.
    changed = {path for path in previous.index.entries.keys() | current.index.entries.keys()
               if previous.index.entries.get(path) != current.index.entries.get(path)}
    changed.update(changed_reviews)
    reusable = set()
    for owner in previous.packages.keys() & current.packages.keys():
        if owner in previous.global_scan_packages or previous.packages[owner].walks:
            continue
        inputs, unknown, history = leg_inputs(previous, {owner}, ("compile", "runtime"))
        if unknown or history or EVERYTHING in inputs:
            continue
        footprint = _InputSet(inputs)
        if not any(_reads(previous, path, footprint) for path in changed):
            reusable.add(owner)
    return reusable


def build_manifest_graph(index: TreeIndex) -> Graph:
    """Declared manifest ownership only, without Rust source reachability.

    This is insufficient for ordinary diagnostic selection or cache reuse.
    The declared development owner consumes it only with fresh checks.
    """
    if tomllib is None:
        raise RuntimeError("the selector needs Python >= 3.11 (tomllib)")
    manifests = sorted(p for p, (mode, _) in index.entries.items()
                       if (p == "Cargo.toml" or p.endswith("/Cargo.toml")) and mode != "160000")
    blobs = index.read_blobs(manifests)
    docs: Dict[str, dict] = {}
    opaque: Dict[str, str] = {}
    for m in manifests:
        d = posixpath.dirname(m)
        try:
            docs[d] = tomllib.loads(blobs[m].decode("utf-8"))
        except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
            opaque[d] = str(exc).splitlines()[0][:120]
    gitlinks = index.gitlinks()
    manifest_dirs = set(docs)

    # Workspaces: their members and [workspace.dependencies].
    ws_members: Dict[str, Set[str]] = {}
    ws_deps: Dict[str, Dict[str, object]] = {}
    patch_targets: Dict[str, Set[str]] = {}  # dep name -> repo-relative paths
    for d, doc in docs.items():
        ws = doc.get("workspace")
        if isinstance(ws, dict):
            ws_members[d] = _expand_members(index, d, ws.get("members", []) or [], manifest_dirs)
            ws_deps[d] = ws.get("dependencies", {}) or {}
        for section in ("patch", "replace"):
            tab = doc.get(section, {}) or {}
            if section == "replace":
                tab = {"_": tab}
            for _src, entries in tab.items():
                if not isinstance(entries, dict):
                    continue
                for key, spec in entries.items():
                    if isinstance(spec, dict) and "path" in spec:
                        target = _norm(d, spec["path"])
                        if target is not None:
                            name = spec.get("package", key.split(":")[0])
                            patch_targets.setdefault(name, set()).add(target)

    def workspace_root_of(pkg_dir: str) -> Optional[str]:
        # The nearest ancestor (or self) whose [workspace] lists it, else the nearest [workspace].
        cand = pkg_dir
        nearest = None
        while True:
            if cand in ws_members:
                if pkg_dir in ws_members[cand] or cand == pkg_dir:
                    return cand
                nearest = nearest or cand
            if cand == "":
                break
            cand = posixpath.dirname(cand)
        return nearest

    packages: Dict[str, Package] = {}
    by_name: Dict[str, Set[str]] = {}
    for d, doc in docs.items():
        pkg = doc.get("package")
        if not isinstance(pkg, dict) or "name" not in pkg:
            continue
        lib = doc.get("lib", {}) or {}
        p = Package(dir=d, name=str(pkg["name"]),
                    proc_macro=bool(lib.get("proc-macro") or lib.get("proc_macro")))
        root = workspace_root_of(d)
        for table in _collect_dep_tables(doc):
            for key, spec in _dep_specs(table):
                name = key
                if isinstance(spec, dict):
                    if spec.get("workspace") is True and root is not None:
                        wspec = ws_deps.get(root, {}).get(key)
                        if isinstance(wspec, dict):
                            name = wspec.get("package", key)
                            if "path" in wspec:
                                t = _norm(root, wspec["path"])
                                if t is not None:
                                    p.path_deps.add(t)
                    name = spec.get("package", name)
                    if "path" in spec:
                        t = _norm(d, spec["path"])
                        if t is not None:
                            p.path_deps.add(t)
                p.dep_names.add(str(name))
        packages[d] = p
        by_name.setdefault(p.name, set()).add(d)

    def node_for(path: str) -> Optional[str]:
        for g in gitlinks:
            if path == g or path.startswith(g + "/"):
                return g
        return path if path in packages else None

    unresolved_paths: List[str] = []
    for p in packages.values():
        for t in p.path_deps:
            n = node_for(t)
            if n is not None:
                p.deps.add(n)
            elif t in opaque:
                p.deps.add(t)
                unresolved_paths.append(f"{p.dir} -> {t} (unparsable manifest)")
        # A dependency without a path resolves to a registry or git source,
        # never to a package of this tree, unless a [patch]/[replace] names it:
        # those are the only name-based edges. (Applied tree-wide, whichever
        # workspace root declares the patch: a superset of cargo's scoping.)
        # Vendored sources sit under vendor/, which selects every leg.
        for name in p.dep_names:
            for t in patch_targets.get(name, ()):
                n = node_for(t)
                if n is not None and n != p.dir:
                    p.deps.add(n)
    g = Graph(index, packages, by_name, gitlinks, opaque, ws_members)
    if unresolved_paths:
        # A package depends on a manifest the selector cannot read: the graph
        # is unparsable for that package, and fail-closed means for every leg.
        g.opaque.setdefault("", "path dependencies on unparsable manifests: " + "; ".join(unresolved_paths[:3]))
    # Cargo targets whose source is outside the package: compiler/rustc_proc_macro
    # compiles library/proc_macro/src/lib.rs (`[lib] path = "../../library/..."`),
    # library/compiler-builtins/builtins-shim its sibling's lib.rs and build.rs.
    targets: Set[str] = set()  # every manifest-named target source, folded (_named_in_production)
    main_targets: Set[str] = set()  # those of a library, a binary or a build script (_main_production_name)
    # Those the package's own scan does not read as its own (_compiled_elsewhere):
    # outside it, in a package nested in it, not named Rust source, through a link.
    elsewhere: Dict[str, List[str]] = {}
    for d, doc in docs.items():
        pkg = packages.get(d)
        if pkg is None:
            continue
        _find_build_scripts(g, pkg, doc)
        main_targets.update(fold(t) for t in (_norm(d, sp) for sp in _target_paths(doc, main=True)) if t)
        for spelled in _target_paths(doc):
            target = _norm(d, spelled)
            if target is not None:
                targets.add(fold(target))
                if (g.owner(target) != d or not _rust_source(target)
                        or index.entries.get(target, ("",))[0] not in REGULAR):
                    elsewhere.setdefault(d, []).append(target)
            why = f"{d}/Cargo.toml: a target's source at {spelled}"
            if target is None:
                pkg.unresolved.append(Read("compile", f"{why}, outside the repository", False, why))
            elif not (target == d or target.startswith(d + "/")):
                _foreign_source(g, pkg, target, why, False)
    g.__dict__["_cargo_targets"] = targets
    g.__dict__["_cargo_main_targets"] = main_targets
    g.__dict__["_targets_elsewhere"] = elsewhere
    return g


def _report_discovery(progress, phase, state, **counts):
    """Optional synchronous observations, never graph or cache inputs."""
    if progress is not None:
        progress(phase, state, counts)


def _grep_may_read(path: str, specs: Tuple[str, ...]) -> bool:
    """Only the scanner's known literal and Rust pathspecs can exclude a file.

    Unknown Git pathspec semantics conservatively invalidate classification reuse.
    Include nonmatching candidates: a later match can introduce a new code edge.
    """
    # Literal exclusions only subtract from an explicit positive scope.
    # An exclusion-only query implicitly starts from the whole repository.
    positives = tuple(spec for spec in specs
                      if not isinstance(spec, str) or not spec.startswith(":(exclude,literal)"))
    if not positives:
        return True
    for spec in positives:
        if not isinstance(spec, str):
            return True
        if spec == ":(icase)*.rs":
            if _rust_source(path):
                return True
        else:
            literal = spec.removeprefix(":(literal)")
            if (not literal or not literal.isascii() or literal.startswith("/")
                    or any(part in ("", ".", "..") for part in literal.rstrip("/").split("/"))
                    or any(c in literal for c in "*?[\\:")
                    or path == literal or path.startswith(literal.rstrip("/") + "/")):
                return True
    return False


def _prose_classification_refresh(index: TreeIndex, previous: Optional[Graph]) -> Optional[Graph]:
    """Reuse computed graph *classification*, never selection or leg evidence.

    Every path and mode stays exact; only existing ASCII root *.md or
    docs/*.md / docs/*.toml bytes may differ. No changed file may have supplied
    parsed content, an audit premise, or any recorded grep's candidate input.
    Unknown/history obligations remain
    in the copied graph. Fresh selection uses the new index and its new hashes.
    `previous` is a completed scan under the same reader: a graph of this
    process, or one from the graph store, whose derived classification is
    authority only because its identity names this scanner, interpreter, git
    and git config (graph_store_identity) and whose inventory and blobs were
    re-checked against Git on load (_load_stored_graph).
    """
    if (previous is None or type(index) is not TreeIndex or type(previous.index) is not TreeIndex
            or index.repo != previous.index.repo or AUDITS_OVERRIDE is not None
            or not previous._classification_reads_complete
            or not previous.__dict__.get("_scan_complete", False)):
        return None
    before, after = previous.index.entries, index.entries
    if before.keys() != after.keys() or any(before[p][0] != after[p][0] for p in before):
        return None
    changed = {p for p in before if before[p] != after[p]}
    if any(not (p.isascii() and (("/" not in p and p.endswith(".md"))
                                or (p.startswith("docs/") and p.endswith((".md", ".toml"))))
                and after[p][0] in REGULAR and is_prose(p)) for p in changed):
        return None
    parsed = previous.index._content_reads | set(previous.blob_cache)
    if changed & parsed or any(_grep_may_read(p, specs) for p in changed for specs in previous._grep_pathspecs):
        return None
    # Pin comparisons consume identities without reading those files' content.
    for rows in (load_audits(previous), load_not_paths(previous)):
        for source, row in rows.items():
            if changed & {source, *(pin["file"] for pin in row.get("premises", []))}:
                return None
    refreshed = copy.deepcopy(previous)
    refreshed.index = index
    index._content_reads.update(previous.index._content_reads)
    # Do not import per-selection derived caches into a new landing subject.
    refreshed.run_make_dirs_cache = refreshed.run_make_reads_cache = None
    refreshed.link_targets_cache = None
    refreshed.reused_packages = _reusable_package_scans(previous, refreshed)
    refreshed.reused_tokenizations = 0
    refreshed.__dict__["_reused_grep_answers"] = 0
    refreshed.__dict__["_reused_blob_facts"] = 0
    refreshed.__dict__["_classification_reused_from"] = previous.index.rev
    return refreshed


def build_graph(index: TreeIndex, previous: Optional[Graph] = None, *, progress=None) -> Graph:
    _report_discovery(progress, "prose classification", "start")
    refreshed = _prose_classification_refresh(index, previous)
    _report_discovery(progress, "prose classification", "complete", reusable=refreshed is not None)
    if refreshed is not None:
        _report_discovery(progress, "graph classification reuse", "complete",
                          packages=len(refreshed.packages), changed_subject=index.rev[:12])
        _report_discovery(progress, "graph", "complete", packages=len(refreshed.packages),
                          reused_packages=len(refreshed.reused_packages),
                          reused_tokenizations=refreshed.reused_tokenizations, reused_blob_facts=0)
        return refreshed
    _report_discovery(progress, "manifest graph", "start")
    g = build_manifest_graph(index)
    _report_discovery(progress, "manifest graph", "complete", packages=len(g.packages))
    _symlinks_out_of_packages(g)
    _report_discovery(progress, "reuse analysis", "start", packages=len(g.packages))
    reusable = _reusable_package_scans(previous, g)
    _report_discovery(progress, "reuse analysis", "complete", eligible_packages=len(reusable))
    # Each whole-tree listing query's answer for a file is its blob's: one
    # the earlier graph judged is taken from it (_listed_by_grep). Held only
    # while this scan runs: never stored with the graph.
    g.__dict__["_reused_grep_answers"] = 0  # reported only (land_gate's run record)
    # So is each pure text predicate's answer for a blob (_blob_fact), from
    # the same earlier graph on the same terms; a table of which any entry
    # is malformed gives none (_usable_blob_facts).
    g.__dict__["_reused_blob_facts"] = 0  # reported only
    if _prior_listings_usable(previous, g):
        g.__dict__["_prior_listings"] = (previous.index.entries, previous.grep_listings)
        g.__dict__["_prior_blob_facts"] = _usable_blob_facts(previous.__dict__.get("blob_facts"))
    try:
        if progress is None:
            scan_escapes(g, reusable, previous)
        else:
            scan_escapes(g, reusable, previous, progress=progress)
    finally:
        g.__dict__.pop("_prior_listings", None)
        g.__dict__.pop("_prior_blob_facts", None)
        g.__dict__.pop("_pathspec_scopes", None)
    if not g.__dict__.get("_scan_complete", False):
        reusable = set()
    for owner in reusable:
        g.packages[owner] = copy.deepcopy(previous.packages[owner])
        if owner in previous.build_reach_cache:
            g.build_reach_cache[owner] = previous.build_reach_cache[owner]
    g.reused_packages = reusable
    if reusable:
        # Copied classifications retain the observations that originally
        # computed them, even when this pass did not reread those blobs.
        index._content_reads.update(previous.index._content_reads)
        g._grep_pathspecs.update(previous._grep_pathspecs)
    g._classification_reads_complete = (type(index) is TreeIndex and AUDITS_OVERRIDE is None
                                         and g.__dict__.get("_scan_complete", False)
                                         and (not reusable or previous._classification_reads_complete))
    _report_discovery(progress, "graph", "complete" if g.__dict__.get("_scan_complete", False) else "conservative",
                      packages=len(g.packages), reused_packages=len(reusable),
                      reused_tokenizations=g.reused_tokenizations,
                      reused_blob_facts=g.__dict__["_reused_blob_facts"])
    return g


# ---------------------------------------------------------------------------
# The graph store: a completed graph, kept for the next process.
# ---------------------------------------------------------------------------
#
# build_graph(index, previous) reuses what an earlier graph scanned from inputs
# that did not change (_prose_classification_refresh, _reusable_package_scans),
# but only a graph the same process built was ever handed to it, and each gate
# command is its own process: `plan` built its one graph from nothing, 416 s for
# a two-file documentation change, "0/1089 package scans and 0 tokenizations
# reused". The store hands a later process that earlier graph. It decides no
# reuse itself: what a stored graph may answer is decided by the same two rules
# from the two trees' Git identities, as for a graph of this process.
#
# An entry is a function of its tree and of GRAPH_STORE_CODE, the interpreter and
# git (graph_store_identity), and is named by both, so it serves every commit and
# every worktree of the clone that reads the same objects. What it is trusted
# for is bounded when it is read (_load_stored_graph): its bytes must be the
# bytes the writer hashed, its file inventory is read again from Git by tree id,
# and it carries no blob: the files the graph had read (blob_cache) are named
# only, and read again from Git by the object ids the stored tree gives them
# (LAND-GATE-DISCOVERY-COST-1: blob bytes were about a quarter of a 321 MB
# entry, and every one was hashed again on each read anyway). A stored
# graph that fails any of that, or names another scanner, is not used. What the
# scanner derived (packages, reads, walks, grep scopes) cannot be re-checked
# without rescanning; it is trusted because the identity names the code that
# derived it, so a writer of the clone's common git directory could forge it,
# as that writer can already install hooks (docs/DECISION_QUEUE.md GRAPH-STORE-1).
GRAPH_STORE_SCHEMA = "trust-land-graph-store/2"
# The modules whose code computes a graph: this one, its lexer, and the crates
# lane's member rule it imports. host_budget only sizes a grep's worker pool.
GRAPH_STORE_CODE = ("land_select.py", "rust_lex.py", "crates_lane_members.py")
# Entries kept, of any scanner: the trees landings on this clone are cut from.
GRAPH_STORE_KEEP = 3
_GRAPH_ENTRY = re.compile(r"([0-9a-f]{64})-([0-9a-f]{40}|[0-9a-f]{64})\.graph")
_STORE_BUILTINS = ("bytearray", "bytes", "complex", "dict", "frozenset", "list", "object", "range", "set",
                   "slice", "tuple")


def _graph_code_digest() -> Optional[str]:
    digest = hashlib.sha256()
    here = os.path.dirname(os.path.abspath(__file__))
    try:
        for name in GRAPH_STORE_CODE:
            with open(os.path.join(here, name), "rb") as source:
                body = source.read()
            digest.update(f"{name} {len(body)}\0".encode())
            digest.update(body)
    except OSError:
        return None
    return digest.hexdigest()


# The code this process runs. A file that changes under a running gate names
# code this process did not load, so the store then serves and keeps nothing.
_GRAPH_CODE_LOADED = _graph_code_digest()


def graph_store_directory(repo: str) -> Optional[str]:
    """The store of the clone that holds `repo`'s objects: one directory for
    every worktree of it, or None when it cannot be named."""
    try:
        common = git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir").decode().strip()
    except (OSError, RuntimeError, UnicodeDecodeError):
        return None
    return os.path.join(common, "trust-land", "graphs") if os.path.isabs(common) and os.path.isdir(common) else None


def graph_store_identity(repo: str) -> Optional[str]:
    """Everything beside its tree that a graph is a function of, or None when
    this process cannot name it (then nothing is stored or served)."""
    code = _graph_code_digest()
    if code is None or code != _GRAPH_CODE_LOADED or AUDITS_OVERRIDE is not None or tomllib is None:
        return None
    try:
        version = git(repo, "version")
        # What changes which files a `git grep` lists beside its arguments
        # (core: case folding and Unicode composition of the paths it names).
        config = subprocess.run(["git", "-C", repo, "config", "--null", "--get-regexp",
                                 r"^(grep|submodule|core)\."],
                                capture_output=True, env=git_env())
    except (OSError, RuntimeError):
        return None
    if config.returncode not in (0, 1):
        return None
    parts = [GRAPH_STORE_SCHEMA, sys.version, sys.platform, pickle.HIGHEST_PROTOCOL, code,
             version.decode("utf-8", "replace"), config.stdout.decode("utf-8", "replace")]
    return hashlib.sha256(json.dumps(parts).encode()).hexdigest()


class _GraphUnpickler(pickle.Unpickler):
    """Builds the selector's own data classes and plain containers, nothing else."""

    def find_class(self, module: str, name: str):
        if module == "builtins" and name in _STORE_BUILTINS:
            return getattr(builtins, name)
        if (module, name) == ("re", "_compile"):
            return re._compile
        if (module, name) == ("copyreg", "_reconstructor"):
            return copyreg._reconstructor
        owner = None
        if module == __name__:
            owner = sys.modules[__name__]
        elif module == "rust_lex":
            import rust_lex  # scripts/lib is on sys.path for every caller
            owner = rust_lex
        found = getattr(owner, name, None) if owner is not None else None
        # A data class the module itself defines: no imported name, no
        # exception, and not this unpickler.
        if (isinstance(found, type) and found.__module__ == module
                and not issubclass(found, (BaseException, pickle.Unpickler))):
            return found
        raise pickle.UnpicklingError(f"a stored graph may not name {module}.{name}")


def _load_stored_graph(path: str, identity: str, tree: str, index: TreeIndex) -> Optional[Graph]:
    try:
        with open(path, "rb") as entry:
            header = json.loads(entry.readline(4096))
            if (not isinstance(header, dict) or header.get("schema") != GRAPH_STORE_SCHEMA
                    or header.get("identity") != identity or header.get("tree") != tree
                    or type(header.get("size")) is not int or header["size"] < 0):
                return None
            payload = entry.read(header["size"] + 1)
        if len(payload) != header["size"] or hashlib.sha256(payload).hexdigest() != header.get("sha256"):
            return None
        g = _GraphUnpickler(io.BytesIO(zlib.decompress(payload))).load()
        if (type(g) is not Graph or type(g.index) is not TreeIndex or g.index.tree != tree
                or not g.__dict__.get("_scan_complete", False) or not g._classification_reads_complete):
            return None
        # The inventory every comparison with the new tree reads is Git's answer
        # for this tree id; an entry carries no blob bytes, and the files its
        # graph had read are read again from Git by the ids this tree gives them.
        entries = _tree_entries(index.repo, tree)
        if (type(g.index._blob_bytes) is not dict or g.index._blob_bytes or type(g.blob_cache) is not dict
                or any(type(name) is not str or name not in entries or body is not None
                       for name, body in g.blob_cache.items())):
            return None
        g.index.repo, g.index.entries = index.repo, entries
        g.blob_cache = g.index.read_blobs(sorted(g.blob_cache))
    except Exception:  # a torn, foreign or damaged entry raises whatever its bytes spell
        return None
    return g


def stored_graph(directory: str, index: TreeIndex, *, progress=None) -> Optional[Graph]:
    """The stored graph nearest `index`'s tree, to hand build_graph as its
    `previous`; None when the store holds none this scanner may read."""
    identity = graph_store_identity(index.repo) if type(index) is TreeIndex else None
    if identity is None:
        return None
    _report_discovery(progress, "graph store read", "start")
    g = _stored_graph(directory, index, identity, progress)
    _report_discovery(progress, "graph store read", "complete", served=g is not None)
    return g


def _stored_graph(directory: str, index: TreeIndex, identity: str, progress) -> Optional[Graph]:
    try:
        names = os.listdir(directory)
    except OSError:
        names = []
    ranked = []
    for name in names:
        match = _GRAPH_ENTRY.fullmatch(name)
        if match is None or match.group(1) != identity:
            continue
        tree, distance = match.group(2), 0
        if tree != index.tree:
            # How far apart the two trees are; a tree Git no longer holds is no candidate.
            diff = subprocess.run(["git", "-C", index.repo, "diff-tree", "-r", "-z", "--name-only", "--no-renames",
                                   tree, index.tree], capture_output=True, env=git_env())
            if diff.returncode != 0:
                continue
            distance = 1 + diff.stdout.count(b"\0")
        ranked.append((distance, tree, name))
    for distance, tree, name in sorted(ranked):
        g = _load_stored_graph(os.path.join(directory, name), identity, tree, index)
        if g is not None:
            _report_discovery(progress, "graph store", "read", tree=tree[:12], paths_apart=max(distance - 1, 0))
            return g
        # Named for this scanner and this tree, and not what its writer wrote
        # or no longer comparable: dropped, so the next completed graph replaces it.
        _report_discovery(progress, "graph store", "entry not usable", tree=tree[:12])
        try:
            os.unlink(os.path.join(directory, name))
        except OSError:
            pass
    _report_discovery(progress, "graph store", "nothing stored for this scanner", entries=len(ranked))
    return None


def store_graph(directory: str, g: Graph, *, progress=None) -> bool:
    """Keep completed `g` for a later process. Written whole under another
    name and renamed into place, so a reader sees an entry entire or not at all."""
    if (type(g) is not Graph or type(g.index) is not TreeIndex or not g.__dict__.get("_scan_complete", False)
            or not g._classification_reads_complete):
        return False
    identity = graph_store_identity(g.index.repo)
    if identity is None:
        return False
    _report_discovery(progress, "graph store write", "start")
    kept = _store_graph(directory, g, identity, progress)
    _report_discovery(progress, "graph store write", "complete", kept=kept)
    return kept


def _store_graph(directory: str, g: Graph, identity: str, progress) -> bool:
    path = os.path.join(directory, f"{identity}-{g.index.tree}.graph")
    temporary = None
    try:
        os.makedirs(directory, exist_ok=True)
        if os.path.exists(path):
            os.utime(path)  # still in use: the last to be dropped
            return True
        # Deflated at its fastest setting: about a fifth of the size (the source
        # text and its tokenizations are most of a graph) for a few seconds.
        # Without blob bytes: names only, read again by object id on load.
        kept = copy.copy(g)
        kept.index = copy.copy(g.index)
        kept.index._blob_bytes = {}
        kept.blob_cache = dict.fromkeys(g.blob_cache)
        kept.__dict__.pop("_grep_complaint", None)
        payload = zlib.compress(pickle.dumps(kept, protocol=pickle.HIGHEST_PROTOCOL), 1)
        header = {"schema": GRAPH_STORE_SCHEMA, "identity": identity, "tree": g.index.tree, "size": len(payload),
                  "sha256": hashlib.sha256(payload).hexdigest()}
        descriptor, temporary = tempfile.mkstemp(prefix=".writing-", dir=directory)
        with os.fdopen(descriptor, "wb") as entry:
            entry.write(json.dumps(header, sort_keys=True).encode() + b"\n")
            entry.write(payload)
            entry.flush()
            os.fsync(entry.fileno())
        # The scanner may have changed on disk while this graph was built.
        if graph_store_identity(g.index.repo) != identity:
            return False
        os.replace(temporary, path)
        temporary = None
        kept = []
        for name in os.listdir(directory):
            full = os.path.join(directory, name)
            try:
                modified = os.stat(full).st_mtime
            except OSError:
                continue
            if _GRAPH_ENTRY.fullmatch(name):
                kept.append((modified, full))
            elif name.startswith(".writing-") and modified < time.time() - 86400:
                os.unlink(full)  # a writer that died
        for _modified, full in sorted(kept, reverse=True)[GRAPH_STORE_KEEP:]:
            os.unlink(full)
    except (OSError, pickle.PicklingError, TypeError, AttributeError, RecursionError, MemoryError, zlib.error) as error:
        _report_discovery(progress, "graph store", "not written", why=f"{error.__class__.__name__}: {error}"[:200])
        return False
    finally:
        if temporary is not None:
            try:
                os.unlink(temporary)
            except OSError:
                pass
    _report_discovery(progress, "graph store", "written", tree=g.index.tree[:12], bytes=len(payload))
    return True


def refresh_graph(index: TreeIndex, directory: Optional[str], previous: Optional[Graph] = None, *,
                  build=None, progress=None) -> Graph:
    """build_graph(index, previous) with the store at `directory`: a process
    that holds no earlier graph starts from the stored one, and the completed
    graph is kept for the next process. `build(previous)`: the caller's own
    call of build_graph."""
    if build is None:
        def build(earlier):
            return build_graph(index, earlier, progress=progress)
    g = stored = None
    if previous is None and directory is not None:
        stored = stored_graph(directory, index, progress=progress)
        if stored is not None:
            try:
                g = build(stored)
            except RuntimeError as error:
                # Git no longer holds an object the stored tree names: it cannot
                # be compared with this one, which is scanned as if none were stored.
                _report_discovery(progress, "graph store", "abandoned", why=str(error)[:200])
                stored = None
    if g is None:
        g = build(previous)
    g.__dict__.pop("_stored_tree", None)
    if directory is not None:
        store_graph(directory, g, progress=progress)
    if stored is not None:
        # Reported only (land_gate's discovery line); never a reuse input.
        g.__dict__["_stored_tree"] = stored.index.tree
    return g


def _target_paths(doc: dict, main: bool = False) -> List[str]:
    """Every source path a manifest names for its targets and build script;
    `main`: only its library's, binaries' and build script's (not a test,
    bench or example target's)."""
    out: List[str] = []
    lib = doc.get("lib")
    if isinstance(lib, dict) and isinstance(lib.get("path"), str):
        out.append(lib["path"])
    for kind in ("bin",) if main else ("bin", "test", "bench", "example"):
        for t in doc.get(kind, []) or []:
            if isinstance(t, dict) and isinstance(t.get("path"), str):
                out.append(t["path"])
    pkg = doc.get("package")
    if isinstance(pkg, dict):
        # `build = "x.rs"`, or an array of them (targo's multiple build
        # scripts: until review 4 of LAND-GATE-EW1 none was a target).
        build = pkg.get("build")
        out.extend(b for b in (build if isinstance(build, list) else [build]) if isinstance(b, str))
    return out


def _find_build_scripts(g: "Graph", pkg: Package, doc: dict) -> None:
    """Whether `pkg` has a build script, into pkg.build_scripts: Cargo's
    default, a file at the package root named build.rs as the landing host
    compares names (fold: build.RS, Build.rs), unless the manifest says
    `build = false`; or each path the manifest's `build` names (a string, or
    an array of them, which targo accepts; `true` is build.rs). Each is kept
    as named and as the host opens it (_opened_files: through the links of
    every component), for _is_build_script; one that opens no tracked
    regular file (missing, a gitlink, outside the repository, an
    unresolvable link) leaves the package unresolved in both classes: what
    builds it is then code the scan never reads. (Review 4 of
    LAND-GATE-EW1: an array was read as the default build.rs, and a key
    through a directory link named no file, so the script was runtime code.)"""
    manifest = posixpath.join(pkg.dir, "Cargo.toml") if pkg.dir else "Cargo.toml"
    package = doc.get("package")
    build = package.get("build") if isinstance(package, dict) else None
    default = posixpath.join(pkg.dir, "build.rs") if pkg.dir else "build.rs"
    if build is False:
        return
    if build is None and not any(q in g.index.entries for q in _index_spellings(g).get(fold(default), ())):
        return  # no build.rs (in any case): Cargo's default is no build script
    # The crates the build script's code names (review 4 of LAND-GATE-EW1,
    # round 3), from its build-dependency tables only (it sees no other:
    # library/std's [dependencies] name core): each by its key, or, a path
    # one not renamed, by its `[lib] name`; to the tracked package of a path
    # one, None for any other or two of one name (_dep_macro_unread). One
    # named std, core, alloc or rustfmt makes the reach incomplete:
    # `alloc::format!` or `#[rustfmt::skip]` is then its macro (targo builds
    # one renamed alloc or core).
    tables = [doc.get(k) for k in ("build-dependencies", "build_dependencies")] + [
        t.get(k) for t in (doc.get("target") or {}).values() if isinstance(t, dict)
        for k in ("build-dependencies", "build_dependencies")]
    crates: Dict[str, Optional[str]] = {}
    shadowing: List[str] = []
    for table in (t for t in tables if isinstance(t, dict)):
        for key, spec in table.items():
            dep, name = None, key
            if isinstance(spec, dict) and isinstance(spec.get("path"), str) and "workspace" not in spec:
                real = _realpath(g, pkg.dir, spec["path"])
                dep = real if real is not None and real == _norm(pkg.dir, spec["path"]) and real in g.packages else None
            if dep is not None and "package" not in spec:
                dm = posixpath.join(dep, "Cargo.toml") if dep else "Cargo.toml"
                try:
                    lib = tomllib.loads(g.index.read_blobs([dm])[dm].decode("utf-8")).get("lib")
                except (KeyError, RuntimeError, ValueError, UnicodeDecodeError):
                    lib, dep = None, None
                if isinstance(lib, dict) and "name" in lib:
                    name, dep = (lib["name"], dep) if isinstance(lib["name"], str) else (key, None)
            code = name.replace("-", "_")
            crates[code] = dep if crates.get(code, dep) == dep else None
            if code in STD_ROOTS | {"rustfmt"}:
                shadowing.append(f"{manifest}: the build-dependency {key!r}, which the build script names {code}")
    g.__dict__.setdefault("_build_crates", {})[pkg.dir] = (crates, shadowing)
    # Its targets' roots as the manifest spells them, as written and through
    # links: a build script that is one is that target's code too (_build_role).
    lib = doc.get("lib")
    spelt = [lib["path"]] if isinstance(lib, dict) and isinstance(lib.get("path"), str) else []
    for kind in ("bin", "test", "bench", "example"):
        spelt += [t["path"] for t in doc.get(kind, []) or [] if isinstance(t, dict) and isinstance(t.get("path"), str)]
    g.__dict__.setdefault("_build_target_roots", {})[pkg.dir] = {
        fold(t) for sp in spelt for t in (_norm(pkg.dir, sp), _realpath(g, pkg.dir, sp)) if t is not None}
    if build is None or build is True:
        named: List[object] = ["build.rs"]
    else:
        named = build if isinstance(build, list) else [build]
    for spelled in named:
        why = f"{manifest}: the build script {spelled!r}"
        if not isinstance(spelled, str):
            # A key Cargo rejects or the selector cannot read: what builds the package is unknown.
            pkg.build_scripts.add(default)
            for cls in ("compile", "runtime"):
                pkg.unresolved.append(Read(cls, f"{why}, a `build` value that is not a path", False, why))
            continue
        target = _norm(pkg.dir, spelled)
        if target is None:
            opened, reason = [], "outside the repository"
            pkg.build_scripts.add(posixpath.normpath(posixpath.join(pkg.dir, spelled)))  # it has one
        else:
            # As named, and where a link takes it (another case of the name
            # is one already: _is_build_script folds).
            opened, reason = _opened_files(g, target)
            pkg.build_scripts.add(target)
            pkg.build_scripts.update(q for q in opened if fold(q) != fold(target))
        if reason:
            for cls in ("compile", "runtime"):
                pkg.unresolved.append(Read(cls, f"{why} opens no tracked regular file ({reason})", False, why))


def _opened_files(g: "Graph", path: str) -> Tuple[List[str], Optional[str]]:
    """The tracked regular files the landing host opens at the repository path
    `path`: through the links of every component (_realpath from the root),
    or, spelt in another case or normalization, as the index spells it; and
    why there is none (None when there is one)."""
    entries = g.index.entries
    real = _realpath(g, "", path)
    found = {real} if real is not None else set()
    found.update(_realpath(g, "", q) for q in _index_spellings(g).get(fold(path), ()) if q in entries)
    opened = sorted(q for q in found if q is not None and entries.get(q, ("",))[0] in REGULAR)
    if opened:
        return opened, None
    if real is None:
        return [], "through a link that cannot be resolved, or in another case"
    gitlink = next((q for q in g.gitlinks if real == q or real.startswith(q + "/")), None)
    if gitlink is not None:
        return [], f"{real} is a gitlink" if real == gitlink else f"{real} is in the gitlink {gitlink}"
    return [], f"{real} is not a tracked regular file"


def _foreign_source(g: "Graph", pkg: Package, target: str, why: str, test_only: bool) -> None:
    """`pkg` compiles the Rust source file `target`, which it does not own: the
    file's whole module directory is an input (a module file declares children
    by name: `mod x;` beside or below it), and so is the package (or gitlink)
    that owns it, as an edge of the graph."""
    owner = g.owner(target)
    if owner is not None and owner != pkg.dir and (owner in g.packages or owner in g.gitlinks):
        pkg.deps.add(owner)
        pkg.foreign.append(owner)
    module_dir = posixpath.dirname(target)
    if module_dir and g.owner(module_dir) != pkg.dir:
        pkg.reads.append(Read("compile", module_dir, test_only, f"{why} (its module directory)"))


def _symlinks_out_of_packages(g: "Graph") -> None:
    """A symbolic link a package owns that points outside it is a read of what
    it points at (a test or a macro that opens the link opens the target), in
    both classes; one that leaves the repository makes the package unresolved."""
    links = [p for p, (mode, _) in g.index.entries.items() if mode == "120000"]
    owned = {p: g.owner(p) for p in links}
    links = [p for p in links if owned[p] in g.packages]
    texts = _link_texts(g)
    for p in links:
        pkg = g.packages[owned[p]]
        text = texts[p]
        # Lexically and over the index: `../../first-party/trust/docs` is docs/.
        targets = {_norm(posixpath.dirname(p), text), _realpath(g, posixpath.dirname(p), text)}
        why = f"{p}: a symbolic link"
        if None in targets:
            for cls in ("compile", "runtime"):
                pkg.unresolved.append(Read(cls, f"{why} out of the repository", False, why))
            continue
        for target in targets:
            if not (pkg.dir == "" or target == pkg.dir or target.startswith(pkg.dir + "/")):
                prefix, _ = _cut_glob(target)
                for cls in ("compile", "runtime"):
                    pkg.reads.append(Read(cls, prefix or EVERYTHING, False, why))


# ---------------------------------------------------------------------------
# The escape scan.
# ---------------------------------------------------------------------------

# Which files the scan reads: any that may hold one of the escape sites below.
# (Until 2026-10-14 this prefilter left out the working-directory anchors and
# the build-tree literals _scan_file looks for, so a file whose only escape was
# `current_dir()`, `"TRUST_RUSTC"` or a `build/host/stage1` literal, such as
# trust-router's ay_discovery.rs, was never scanned at all.)
# Every spelling of a git literal the classifier decodes (_git_literal_sites)
# from a literal rustc accepts, as git grep reads it: line by line, a CRLF
# line ending in CR, bytes (scan_escapes runs it under LC_ALL=C). The word
# begins a value, a path component or a command (GIT_PROGRAM,
# GIT_PATH_LITERAL, GIT_COMMAND_LINE), so before it stands a line start, a
# quote, whitespace, a path or command separator, ANY escape (`\x20git`,
# `\x3bgit`, `\u{9}git`: the classifier decodes them all), or a byte outside
# printable ASCII (Unicode whitespace, which Python's `\s` takes); after it a
# quote, whitespace, an escape, a line end or such a byte. Besides: git
# followed by an escape (`git\x2eexe`), an escaped letter of git or of a path
# separator, and a line continuation inside the word: a backslash at a line
# end, before an optional CR, after a `g` or `gi` that any of those may
# precede (`;g\`, `&&gi\`), or right after a quote or a path separator as
# before (one before the whole word leaves it at the next line's start).
# Python's case-insensitive match also takes İ and ı for i. It admits every
# line the prefilter admitted before.
# (Reviews of LAND-GATE-EW1-FOLLOWUP-REVIEW-1 and -2: the prefilter dropped
# `"\x67it"`, `"git\tstatus"`, `"cd x;\x20git status"`, `"cd x;g\` + newline
# + `it status"` and every continuation of a CRLF file, which the classifier
# counts.) Prose matches too; measured 2026-11-06 the scan opens 3811 of 49862
# Rust files, three more than before.
_GIT_ESC = r'\\x[0-9A-Fa-f]{2}|\\u[{][0-9A-Fa-f_]*[}]|\\.'
_GIT_BEFORE = r'(^|[[:space:]]|["/\\;&|(`]|[^ -~]|' + _GIT_ESC + r')'
GIT_SCAN_RE = (r'|' + _GIT_BEFORE + r'[Gg][Ii][Tt](\.[Ee][Xx][Ee])?("|[[:space:]]|\\|$|[^ -~])'
               r'|[Gg][Ii][Tt](\.[EeXx]*)?\\'
               r'|\\x(6[79]|4[79]|[57]4|2[Ff]|5[Cc])|\\u[{][0_]*[2-7]_*[0-9A-Fa-f]_*[}]'
               r'|["/\\]\\[[:space:]]?$|' + _GIT_BEFORE + r'[Gg]([Ii]|[^ -~]{1,2})?\\[[:space:]]?$'
               r'|[Gg][^ -~]{1,2}[Tt]|\\u[{][0_]*1_*3_*[01]_*[}]')
# A build-tree literal in every spelling STAGE_LITERAL matches after fold: any
# case, and one to three characters outside printable ASCII for the s of stage
# (ſ; ﬅ and ﬆ, which fold to st).
STAGE_SCAN_RE = r'|([Ss]|[^ -~]{1,3})[Tt]?[Aa][Gg][Ee][12]|[Bb][Uu][Ii][Ll][Dd]/'
# A path attribute in any spelling rustc takes (PATH_ATTR, below), by the line
# that holds its `path` token.
# An include!, include_str! or include_bytes! call by the line that holds
# its name: rustc takes whitespace and comments between the name and its
# `!` (`include_str !(..)`, `include_str/**/![..]`, the `!` on the next
# line); and file!, with whitespace or a comment before its `!`, or the
# `!` on the next line where only `(`, a comment or nothing stands before
# `file` on its line, as in FILE_ANCHOR_CODE's `Path::new(file!())` (any
# line ending in `file` opened 310 files more). A macro's `mod $name` by the
# line that holds `mod` (_index_module_macros). (Until the review of
# LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only `include_str!` and `file!` spelt
# together counted: a file whose only escape was spelt so was never
# scanned; and no file was opened for its `mod $name`. Measured on
# d146318e21 the scan opens 119 files more, 3992 of them.) A `use` renaming an
# include macro (`use std::include as inc;`), whose calls no alternative
# names (INCLUDE_RENAME). Any line holding Rust whitespace that
# [[:space:]] does not take (rust_lex.RUST_SPACES: U+0085, U+200E, U+200F,
# U+2028, U+2029, each its UTF-8 bytes), which may stand between any two
# tokens above (`mod<U+200E>gen;`). (Until the review of
# LAND-GATE-EW1-FOLLOWUP-REVIEW-3 neither: such a file was never scanned.)
SCAN_RE = (r'include(_str|_bytes)?[[:space:]]*(!|/[*/]|$)'
           r'|(^|[,(]|\[|\*/)[[:space:]]*(r#)?path[[:space:]]*(=|/[*/]|$)'
           r'|(^|[^A-Za-z0-9_])mod[[:space:]]*(\$|/[*/]|$)'
           r'|rerun-if-changed|CARGO_MANIFEST_DIR'
           r'|"\.\./|"\.\."|"git"' + GIT_SCAN_RE +
           r'|REPO_ROOT|show-toplevel'
           r'|current_dir|current_exe|file[[:space:]]*(!|/[*/])|(^|\(|\*/)[[:space:]]*file[[:space:]]*$'
           r'|/\.\./|/\.\."|TRUST_RUSTC|TRUST_TARGO_TRUST_BIN' + STAGE_SCAN_RE +
           r'|SRC_ROOT|TRUST_ROOT|CHECKOUT'
           r'|include(_str|_bytes)?[[:space:]]+as([^A-Za-z0-9_]|$)'
           '|\u0085|\u200e|\u200f|\u2028|\u2029')
# A doc attribute whose value is no plain string (`#[doc = m!()]`,
# `doc = concat!(..)`, `doc = r"..."`; the value, or the `=`, on the next line
# or after a comment): the text of its doctests need not be in the file, so
# SCAN_RE cannot tell the file holds none to read; the scan reads it
# (_doc_units reads a value or blinds it). Until review 4 round 2 a file whose
# only doctest a macro computes was never scanned.
DOC_VALUE_SCAN_RE = r'|(^|[^A-Za-z0-9_])doc[[:space:]]*(=[[:space:]]*([^"[:space:]]|$)|/[*/]|$)'
# A macro call takes any delimiter: rustc compiles `include!(..)`,
# `include![..]` and `include!{..}` alike, and so for include_str!,
# include_bytes!, concat! and env! (until LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only
# `(` counted: a bracketed include! was no read, no edge, no harvested file
# and, unresolvable, no blind). MACRO_CLOSE pairs each opening delimiter with
# its closing one; a value's end is any of them. Whitespace may stand before
# and after each `!`, and so may a comment (until the review of
# LAND-GATE-EW1-FOLLOWUP-REVIEW-3 neither: `include_str !(..)` was no read):
# INCLUDE_CALL is matched in a lexed file's code, where comments are blank
# (_include_calls); the ARG_* regexes read the text after it with its
# comments blank too (Lexed.without_comments: `concat /**/ !(env !(..), ..)`
# is a manifest-dir include), and _include_arg, in that code, what they do
# not match.
INCLUDE_CALL = re.compile(r'\binclude(?:_str|_bytes)?\s*!\s*[(\[{]')
MACRO_CLOSE = {"(": ")", "[": "]", "{": "}"}
ARG_LIT = re.compile(r'\s*"((?:[^"\\]|\\.)*)"\s*[,)\]}]')
ARG_MANIFEST = re.compile(r'\s*concat\s*!\s*[(\[{]\s*env\s*!\s*[(\[{]\s*"CARGO_MANIFEST_DIR"\s*[)\]}]\s*,\s*'
                          r'"((?:[^"\\]|\\.)*)"\s*([,)\]}])')
ARG_CONCAT_LIT = re.compile(r'\s*concat\s*!\s*[(\[{]\s*"((?:[^"\\]|\\.)*)"\s*([,)\]}])')
ARG_OUT_DIR = re.compile(r'\s*concat\s*!\s*[(\[{]\s*env\s*!\s*[(\[{]\s*"OUT_DIR"\s*[)\]}]'
                         r'|\s*env\s*!\s*[(\[{]\s*"(?:OUT_DIR|CARGO_[A-Z_]*FILE[A-Za-z0-9_-]*)"\s*[)\]}]')


# Whitespace between two tokens of a text before it is lexed: Python's `\s`
# and the Pattern_White_Space characters it does not take, which rustc's
# lexer skips (rust_lex.RUST_SPACES; lexed code holds them as spaces).
RUST_WS = r'[\s\u200e\u200f]'
# Whether a text may hold an include! call, before it is lexed (any text
# that has one matches: the name, then whitespace and either the `!` or a
# comment's start).
INCLUDE_HINT = re.compile(r'\binclude(?:_str|_bytes)?' + RUST_WS + r'*(?:!|/[*/])')
# A `use` that renames an include macro (`use std::include as inc;`,
# `pub use core::{include_str as text};`, not `as _`): the calls of the new
# name are include!s that INCLUDE_CALL does not see, so the file's include!s
# cannot all be told (review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3: `inc!("..")`
# compiled a file the harvest never read, and blinded nothing). In lexed code.
INCLUDE_RENAME = re.compile(r'(?<![\w$])use\b[^;]*?(?<![\w$])(?:r#)?include(?:_str|_bytes)?\s+as\s+(?!_(?![\w$]))')


def _include_calls(lx) -> List["re.Match"]:
    """Each include!, include_str! and include_bytes! call in a lexed file's
    code (INCLUDE_CALL): its match ends after the opening delimiter."""
    return list(INCLUDE_CALL.finditer(lx.code))


def _include_arg_spans(lx, calls: Sequence["re.Match"]) -> List[Tuple[int, int]]:
    """Each include call's (start, end after its closing delimiter) in a
    lexed file's code (literals and comments blanked), to its matching
    delimiter; an unclosed one spans nothing."""
    code, out = lx.code, []
    for m in calls:
        close, depth, end = MACRO_CLOSE[code[m.end() - 1]], 1, m.start()
        for b in INCLUDE_ARG_DELIM.finditer(code, m.end()):
            depth += 1 if b.group(0) in MACRO_CLOSE else -1
            if depth == 0:
                end = b.end() if b.group(0) == close else m.start()
                break
        out.append((m.start(), end))
    return out


INCLUDE_ARG_DELIM = re.compile(r'[()\[\]{}]')


def _includes_source(m: "re.Match") -> bool:
    """Whether an INCLUDE_CALL match is include!, which compiles a file as
    source (include_str! and include_bytes! read data)."""
    return m.group(0)[len("include"):len("include") + 1] != "_"


# Whether a text may hold a path attribute, line by line (SCAN_RE's alternative):
# the `path` token after `[`, `,`, `(`, a comment or nothing on its line, and
# `=`, a comment or nothing after it. rustc takes `#[path = ".."]` with spaces
# and line breaks anywhere between the tokens (`#[ path = ".." ]`, `#\n[path`),
# a raw string (`#[path = r".."]`) and `#[cfg_attr(pred, path = "..")]`;
# _path_attrs reads the value. (Until LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only
# `#[path = "plain"]` counted, here and in the scan's prefilter: a module
# named any other way was neither recorded as a read nor harvested.) Rust
# whitespace outside ASCII counts as a space (RUST_WS), on a line or across one.
PATH_ATTR = re.compile(r'(?:^|[,(]|\[|\*/)[ \t\r\f\v\x85\u200e\u200f\u2028\u2029]*(?:r#)?path'
                       r'[ \t\r\f\v\x85\u200e\u200f\u2028\u2029]*(?:=|/[*/]|$)', re.M)
ATTR_START = re.compile(r'#\s*!?\s*\[')
PATH_KEY = re.compile(r'(?<![\w$])(?:r#)?path\s*=(?!=)')
# A WALK is an ANCHOR (a directory the code can name at run or build time) and a
# CLIMB (an operation that leaves it) in the same file, in any order and any
# distance apart: `let m = env!("CARGO_MANIFEST_DIR"); ... m.parent()` is a walk
# whatever lies between. (Until 2026-10-14 the two had to sit within 160
# characters with no `;` between them, and the regex's first match could start in
# a comment and swallow the code after it: both hid real walks, among them
# trust-backprop's repository root and trust-types' reads of trust-thir-lower's
# and trust-mir-extract's sources.) Anchors: the manifest directory's name as a
# string literal (so `env!`, `env::var` and a `const` spelling all count),
# `current_dir()` (a test's working directory is its
# package), `current_exe()` (it sits in a target directory inside the checkout),
# and `file!()` handed to a path constructor. Climbs: `.parent()`,
# `Path::parent`, `.ancestors()`, a path literal with a `..` component, and,
# shortly after an anchor, `.pop()` (PathBuf::pop; Vec::pop is too common to
# count anywhere else). A `..` literal handed to a path call (`Path::new("..")`,
# `.join("..")`, `.push("..")`, a file-system call) climbs from the working
# directory by itself, so it is a walk with no anchor at all; elsewhere a bare
# `..` is the range operator's spelling (rustc's pretty-printers and parser).
# OUT_DIR and the target directories are not anchors: they lie in the untracked
# build tree, and a climb from them (a build script's `out.parent()` before a
# create_dir_all) stays there; reaching the source tree would take a climb out
# of the target directory itself, which no code in the tree does (grep,
# 2026-10-14). The branch that added this scan never counted them either.
ANCHOR_LITERALS = frozenset(("CARGO_MANIFEST_DIR",))
# Whitespace may stand at each `::` (`Path :: new(file!())`, `Path :: parent`:
# rustc takes it; review 4, round 3).
FILE_ANCHOR_CODE = re.compile(r'Path(?:Buf)?\s*::\s*(?:new|from)\s*\(\s*file\s*!\s*[(\[{]\s*[)\]}]')
CWD_ANCHOR_CODE = re.compile(r'(?<![.\w])current_dir\s*\(\s*\)|\bcurrent_exe\s*\(\s*\)')
CLIMB_CODE = re.compile(r'\.\s*parent\s*\(\s*\)|\bPath\s*::\s*parent\b|\.\s*ancestors\s*\(\s*\)')
POP_CODE = re.compile(r'\.\s*pop\s*\(\s*\)')
POP_WINDOW = 400
# A ".." literal that is unambiguously a path: handed to a path constructor, a
# PathBuf push or a file-system call. (`.join("..")` is a climb beside an anchor,
# but on its own it is as often a slice join with ".." as the separator.)
# Whitespace may stand at each `.` and `::` (rustc takes `Path :: new("..")`
# and `p . join("..")`: review 4, round 3), and `(?:&\s*)?`, not `&?\s*`,
# keeps the match linear.
BARE_UP_BEFORE = re.compile(
    r'(?:Path(?:Buf)?\s*::\s*(?:new|from)|set_current_dir|current_dir|canonicalize|read_dir|read_to_string'
    r'|fs\s*::\s*\w+|File\s*::\s*(?:open|create)|\.\s*push)\s*\(\s*(?:&\s*)?$')
JOIN_BEFORE = re.compile(r'\.\s*join\s*\(\s*(?:&\s*)?$')
GIT_SPAWN = re.compile(r'Command::new\(\s*"git"\s*\)|show-toplevel')
# Git named by a string literal (LAND-GATE-GIT-HELPERS-1, and its review): a
# literal whose value is the git program ("git", "Git", "git.exe", raw or not)
# is a git site unless it sits where no program is run (_git_literal_inert):
# whichever helper, wrapper or binding later hands it to a process
# (`command("git")`, `run_capture(root.as_path(), "git", ..)`,
# `OsStr::new("git")`, `const GIT: &str = "git"`) is not this scan's to tell.
# So is a literal naming a git executable by absolute path ("/usr/bin/git",
# "C:/Git/cmd/git.exe", a UNC path), wherever it is spelt, and a git command
# line ("git status") inside `cmd!(..)` or after a "-c"/"/C" argument. A call
# to a git wrapper defined in another file, or a program name built from
# escapes or pieces, is not seen (docs/KNOWN_HAZARDS.md).
GIT_PROGRAM = re.compile(r'(?i)^git(?:\.exe)?$')
GIT_PATH_LITERAL = re.compile(r'(?i)^(?:/|[a-z]:[\\/]|\\\\)[^"]*[/\\]git(?:\.exe)?$')
GIT_COMMAND_LINE = re.compile(r'(?i)(?:^|[\s;&|(`])git(?:\.exe)?\s+\S')
SHELL_FLAG_BEFORE = re.compile(r'"(?:-[A-Za-z]*c|/[Cc])"\s*(?:,|\)\s*\.\s*arg\s*\()\s*$')
# Where a program literal runs nothing: the argument of a call that only
# compares, looks up, formats or declares a CLI argument (Arg::new); an index
# (`report["git"]`); a map key (`"git": ..`); a match pattern; a comparison; a
# `.join("git")` whose path is only queried (`.exists()`, `.display()`).
GIT_INERT_CALLEES = frozenset("""
    get get_mut get_one contains contains_key starts_with ends_with strip_prefix strip_suffix eq ne cmp
    find rfind position split replace trim_start_matches trim_end_matches
    matches assert assert_eq assert_ne debug_assert debug_assert_eq debug_assert_ne
    format format_args print println eprint eprintln write writeln panic unreachable todo bail anyhow
    expect context with_context long short alias aliases value_name help long_help conflicts_with requires
    must_have field key
    """.split())
GIT_INERT_NEW = frozenset({"Arg"})
GIT_PATH_QUERY_AFTER = re.compile(
    r'\s*\)\s*\.\s*(?:exists|try_exists|is_dir|is_file|is_symlink|display|metadata|symlink_metadata)\s*\(')
# A file runs processes when it names a process API; a program literal in a
# file that runs none must leave the file to be run (the cross-file case,
# docs/KNOWN_HAZARDS.md), unless the call it is handed to is named for running.
PROCESS_API = re.compile(r'\b(?:Command|ProcessBuilder|ProcessCommand|Popen|Exec)\b|\bprocess\s*\(|\bcommand\s*\('
                         r'|\bcmd!|spawn\w*\s*\(|\bexec\w*\s*\(|process::|\bduct\b|\bxshell\b')
SPAWN_CALLEE = re.compile(r'(?i)^(?:cmd|sh|shell|exec\w*|run|run_\w*|\w*(?:command|process|output|capture|spawn)\w*)$')
SPAWN_TYPE = re.compile(r'(?i)(?:command|process\w*)$')
# (`code` blanks every string, so a later alternative is spaces or a name.)
GIT_PATTERN_AFTER = re.compile(r'\s*(?:\|\s*(?:[A-Za-z_][\w:]*)?\s*)*(?:=>|if\b)')


# Keywords after which `[` opens an array, not an index (`for t in ["git", ..]`,
# `return [..]`, `match [..]`, `&mut [..]`).
NOT_EXPRESSION_END = frozenset("""
    as async box become break const continue do dyn else enum extern false fn for if impl in let loop
    macro match mod move mut priv pub ref return static struct trait true try type typeof unsafe
    unsized use virtual where while yield
    """.split())


def _ends_expression(code: str) -> bool:
    """Whether `code` (stripped) ends with an expression a `[` would index: a
    name that is neither a keyword nor a label, `)` or `]`."""
    m = re.search(r"(')?(r#)?([A-Za-z_]\w*)$", code)
    if m:
        return not m.group(1) and (bool(m.group(2)) or m.group(3) not in NOT_EXPRESSION_END)
    return code[-1:] in (")", "]")


def _callee_before(code: str, i: int) -> Optional[str]:
    """The callee path of the call whose `(` is code[i]: macros keep their `!`,
    a turbofish is skipped, a unary `!` in front is dropped (`!run(`)."""
    j = i - 1
    while j >= 0 and code[j].isspace():
        j -= 1
    if j >= 0 and code[j] == ">":  # `new::<&str>(`
        d = 0
        while j >= 0:
            d += code[j] == ">"
            d -= code[j] == "<"
            if d == 0:
                break
            j -= 1
        j -= 1
        while j >= 0 and code[j] in ": \t\n":
            j -= 1
    end = j + 1
    while j >= 0 and (code[j].isalnum() or code[j] in "_:!"):
        j -= 1
    return code[j + 1:end].lstrip("!").strip(":") or None


def _enclosing_call(code: str, pos: int) -> Tuple[Optional[str], Optional[str]]:
    """(callee, bracket) of the innermost bracket holding `pos` in `code`
    (strings and comments blanked); (None, "[" or "{") for another bracket,
    (None, None) at item level."""
    depth, i = 0, pos - 1
    while i >= 0:
        c = code[i]
        if c in ")]}":
            depth += 1
        elif c in "([{":
            if depth:
                depth -= 1
            elif c != "(":
                return None, c
            else:
                return _callee_before(code, i), "("
        i -= 1
    return None, None


BRACKET = re.compile(r'[()\[\]{}]')


def _bracket_tree(code: str, positions: Sequence[int]) -> Tuple[Dict[int, int], Dict[int, int]]:
    """One pass over `code`'s brackets: for each of `positions`, the innermost
    open bracket before it that is still open there (-1 at item level), and
    for each open bracket the one enclosing it."""
    targets = sorted(set(positions))
    inner: Dict[int, int] = {}
    parent: Dict[int, int] = {}
    stack: List[int] = []
    k = 0
    for m in BRACKET.finditer(code):
        i = m.start()
        while k < len(targets) and targets[k] <= i:
            inner[targets[k]] = stack[-1] if stack else -1
            k += 1
        if code[i] in "([{":
            parent[i] = stack[-1] if stack else -1
            stack.append(i)
        elif stack:
            stack.pop()
    for t in targets[k:]:
        inner[t] = stack[-1] if stack else -1
    return inner, parent


def _git_literal_inert(code: str, s: int, e: int) -> bool:
    """Whether the program literal spanning code[s:e] sits where nothing runs it."""
    before = code[:s].rstrip()
    after = code[e:]
    tail = after.lstrip()
    if tail.startswith(("==", "!=")) or before.endswith(("==", "!=")):
        return True
    if GIT_PATTERN_AFTER.match(after):
        return True
    if tail.startswith(":") and not tail.startswith("::"):
        return True  # a map key: json!({"git": ..})
    if before.endswith("[") and _ends_expression(before[:-1].rstrip()):
        return True  # an index: report["git"]; `["git", ..]` after `=`, `(`, `,` or `in` is an array
    callee, bracket = _enclosing_call(code, s)
    if bracket != "(" or not callee:
        return False
    parts = callee.rstrip("!").split("::")
    name = parts[-1]
    if name in GIT_INERT_CALLEES:
        return True
    if name == "new" and len(parts) > 1 and parts[-2] in GIT_INERT_NEW:
        return True
    return name == "join" and GIT_PATH_QUERY_AFTER.match(after) is not None


def _spawn_named(callee: Optional[str]) -> bool:
    if not callee:
        return False
    parts = callee.rstrip("!").split("::")
    if parts[-1] == "new":
        return len(parts) > 1 and SPAWN_TYPE.search(parts[-2]) is not None
    return SPAWN_CALLEE.match(parts[-1]) is not None


def _handed_to_a_spawn(code: str, opened: int, parent: Dict[int, int]) -> bool:
    """Whether a call named for running encloses the bracket opened at
    code[opened], through any brackets (`run(&["git", ..])`,
    `exec_capture(vec![sudo, "git"])`) and any calls whose value it takes
    (`Command::new(format!("{}", "git"))`, `Command::new(find("git"))`)."""
    while opened >= 0:
        if code[opened] == "(" and _spawn_named(_callee_before(code, opened)):
            return True
        opened = parent.get(opened, -1)
    return False


def _git_literal_sites(lx, text: str) -> List[int]:
    """The starts of the string literals that name git to a process (see GIT_PROGRAM)."""
    sites: List[int] = []
    code = lx.code
    runs_processes = PROCESS_API.search(code) is not None
    tree: Optional[Tuple[Dict[int, int], Dict[int, int]]] = None
    for s, e, v in lx.strings:
        if text[s] == "'" or lx.in_comment(s):
            continue
        value = v if text[s] in "rR" or text[s:s + 2] in ("br", "cr") else _unescape(v)
        if GIT_PATH_LITERAL.match(value):
            sites.append(s)
            continue
        program = GIT_PROGRAM.match(value) is not None
        if not program and GIT_COMMAND_LINE.search(value):
            callee, _bracket = _enclosing_call(code, s)
            if (callee or "").endswith("!") and callee.rstrip("!").split("::")[-1] == "cmd":
                sites.append(s)
                continue
            if SHELL_FLAG_BEFORE.search(lx.without_comments(), max(0, s - 80), s):  # Rust whitespace a space
                sites.append(s)
                continue
        elif not program:
            continue
        # The program, or a command line, runs wherever it may be handed to a
        # process: through an enclosing call named for running, or anywhere
        # but an inert place in a file that runs processes.
        if tree is None:
            tree = _bracket_tree(code, [t[0] for t in lx.strings])
        if (_handed_to_a_spawn(code, tree[0][s], tree[1])
                or (runs_processes and not _git_literal_inert(code, s, e))):
            sites.append(s)
    return sites


# `\u{..}`: rustc_lexer takes any run of hex digits and underscores to the
# brace (round 8 of review 4: one of more than 8 decoded to a bare `u`).
_ESCAPE = re.compile(r'\\(?:x([0-9a-fA-F]{2})|u\{([0-9a-fA-F_]+)\}|(\r?\n[ \t\r\n]*)|(.))', re.S)


def _unescape(v: str) -> str:
    """A Rust string literal's value from its source body (an escape that does
    not decode is dropped, which only shortens a path toward a prefix)."""
    def one(m: "re.Match") -> str:
        if m.group(1):
            return chr(int(m.group(1), 16))
        if m.group(2):
            try:
                return chr(int(m.group(2).replace("_", ""), 16))
            except (ValueError, OverflowError):
                return ""
        if m.group(3) is not None:
            return ""  # a line continuation
        return {"n": "\n", "t": "\t", "r": "\r", "0": "\0"}.get(m.group(4), m.group(4))
    return _ESCAPE.sub(one, v) if "\\" in v else v


def _decoded_literal(lx, s: int, v: str) -> str:
    """The value of the literal lx.strings gives as (s, _, v) (_literal_value):
    a raw string's body as written, any other's with its escapes and line
    continuations decoded."""
    return _literal_value(lx.text, s, v)[0]


def _literal_values(lx) -> List[str]:
    """Each literal of a lexed file, decoded (_decoded_literal), in order.
    (Round 7 of review 4: the harvest took a literal's body as written, so
    `inner!("..\\x2f..\\x2fx.md")` handed a bare parameter one path component
    of the package's own, and nothing was read or unresolved.)"""
    return [_decoded_literal(lx, s, v) for s, _e, v in lx.strings]


CHAIN_JOIN = re.compile(r'\)\s*\.\s*join\s*\(\s*')  # `) . join (` too (review 4, round 3)
# The call a chain's first literal must be the argument of: `.join(`,
# `::join(`, `Path::new(`, `PathBuf::from(`. A literal handed to any other call
# (`.expect("repo root").join("src")`, `checkout("main").join("src")`) is no
# path segment, and the literal joined after it is a path on its own.
CHAIN_HEAD = re.compile(r'(?:(?:\.|::)\s*join|Path(?:Buf)?\s*::\s*(?:new|from))\s*\(\s*&?\s*$')
# A `.` or `..` component. A literal is not joined onto a chain when the joined
# path would hold one after its leading walk (`../..`, which the harvest drops):
# the harvest joins the parts as written (`crates/../docs/x.md`), which names no
# changed path, while each literal read on its own (`crates`, `../docs/x.md`)
# does, as before the merge (round 3 of review 4's harvest verifier:
# `root.join("crates") . join ("../docs/x.md")`, and the same with U+200E or no
# space before the `.`).
DOT_COMPONENT = re.compile(r'(?:^|/)\.\.?(?:/|$)')


def _joins_past_a_dot(parts: Sequence[str]) -> bool:
    """Whether `parts` joined as the harvest joins a chain (_harvest_package_literals,
    _discover_run_make_reads) hold a `.` or `..` component after the leading run of them."""
    v = "/".join(p.strip("/") for p in parts if p.strip("/"))
    return DOT_COMPONENT.search(re.sub(r"^(?:\.\.?(?:/|$))+", "", v)) is not None


def _string_chains(lx, text: str) -> List[Tuple[int, int, List[str]]]:
    """The string literals of a lexed Rust file, each with the literals
    `.join`ed straight onto it (`.join("tests").join("js262")` is one path),
    from the lexer's own tokens: (start of the first, end of the last, values).
    Char literals and comments are left out; escapes are decoded. (Until the
    review of LAND-GATE-EW1-RESIDUAL-1 a regex re-paired the quotes, and one
    literal holding an escape, an empty literal or a '"' char put it out of
    step: every literal after it in the file went unharvested.)"""
    wc = lx.without_comments()
    chains: List[Tuple[int, int, List[str]]] = []
    for s, e, v in lx.strings:
        if text[s] == "'" or lx.in_comment(s):
            continue
        raw = text[s] in "rR" or text[s:s + 2] in ("br", "cr")
        value = v if raw else _unescape(v)
        prev = chains[-1] if chains else None
        if (prev is not None and CHAIN_JOIN.fullmatch(wc[prev[1]:s])
                and not _joins_past_a_dot(prev[2] + [value])
                and (len(prev[2]) > 1 or CHAIN_HEAD.search(wc, max(0, prev[0] - 160), prev[0]))):
            chains[-1] = (prev[0], e, prev[2] + [value])
        else:
            chains.append((s, e, [value]))
    return chains


# A [[not_path]] literal is exempt only where no path, file-system or process
# API takes it: no call enclosing it (through any brackets: behind comments, in
# any argument, nested in `unwrap_or`/`format!`/`if`) is named for one, and the
# rest of its statement (to the nearest `;`, `{` or `}` on either side) names
# none (`[r, "docs"].iter().collect::<PathBuf>()`). A statement edge further
# than STATEMENT_WINDOW counts as naming one. A name is one when it is a path
# or file-system call or method (`join`, `read_dir`, `open`), a name the
# git-spawn scan counts as running a process (PROCESS_API, SPAWN_CALLEE: `run`,
# `sh`, `output`), or holds a path, file, directory, walker or process word
# anywhere, in any case (`Utf8PathBuf`, `ignore::Walk`, `WalkBuilder`,
# `TempDir`, `duct::cmd!`, `xshell::Shell`, `ProcessBuilder`; `fs` and `duct`
# as a whole word or `_` part: `fs_err`, not `offsets` or `product`).
# (Until LAND-GATE-EW1-FOLLOWUP-REVIEW-3 the list was exact, word-bounded and
# without the process names, and each of those took a "docs" read away.) A
# file that binds such an item to another name exempts nothing at all
# (_path_api_aliased): `list(..)` after `use std::fs::read_dir as list;`; nor
# does a file that names an item another file of its package binds to such an
# item (_package_path_aliases).
PATH_API = re.compile(
    r'\b(?:join\w*|push\w*|extend|collect|from_iter|read\w*|write\w*|open\w*|create\w*|remove\w*|copy\w*'
    r'|rename|hard_link|symlink\w*|metadata|canonicalize|exists|try_exists|is_file|is_dir|is_symlink'
    r'|with_file_name|with_extension|set_file_name|set_extension|set_permissions|unlink|chmod|chown|l?stat'
    r'|include\w*|arg|args|current_dir|set_current_dir|env|sh|run|run_\w*|output|status|watch\w*)\b'
    r'|(?i:path|osstr|file|dir|walk|glob|command|process|popen|exec|spawn|cmd|shell|capture|output'
    r'|(?<![a-z0-9])(?:fs|duct)(?![a-z0-9]))')
STATEMENT_WINDOW = 4000
# An item bound to another name: a `use` or `extern crate` with a rename
# (`as _` binds none), a type alias, and a binding (_binding_aliases). Read
# over code (strings and comments blanked).
ALIAS_USE = re.compile(r'\b(?:use|extern\s+crate)\b[^;]*?\bas\s+(?:r#)?(?!_\b)(?:[^\W\d]|\$)[^;]*;')
ALIAS_TYPE = re.compile(r'(?<![\w$])type\s+((?:\$|r#)?[^\W\d]\w*)[^=;{]*=([^;]*);')
# A binding: `let`, `const` or `static` (not `'static`, `*const`, `const fn`,
# a const generic or an inline `const {}`), and the parts of it that can make
# an alias: a path (with turbofish or generic arguments and a qualified self,
# `<PathBuf as From<String>>::from`), an initializer that is a closure (behind
# `&`, brackets or calls: `Box::new(move |p| ..)`, not `x.map(|p| ..)`), and a
# callable type.
BINDING_START = re.compile(r"(?<![\w$'*])(let|const|static)(?![\w$])")
ITEM_BINDING_START = re.compile(r"(?<![\w$'*])(const|static|let(?=\s+(?:mut\s+)?\$))(?![\w$])")
GENERIC_ARGS = r'<(?:->|[^<>;{}]|<(?:->|[^<>;{}]|<(?:->|[^<>;{}])*>)*>)*>'
PATH_EXPR = re.compile(r'(?<![\w$])(?:' + GENERIC_ARGS + r'\s*::\s*)?(?:::\s*)?(?:\$|r#)?[^\W\d]\w*'
                       r'(?:\s*::\s*(?:' + GENERIC_ARGS + r'|(?:\$|r#)?[^\W\d]\w*))*')
CLOSURE_START = re.compile(r'\s*(?:[&*(\[{]\s*|(?:(?:\$|r#)?[^\W\d]\w*\s*::\s*)*(?:\$|r#)?[^\W\d]\w*\s*\(\s*)*'
                           r'(?:move\s*)?\|')
CALLABLE_TYPE = re.compile(r'(?<![\w$])(?:fn|Fn|FnMut|FnOnce)\s*\(')
RUST_KEYWORDS = frozenset("""
    as async await box break const continue crate dyn else enum extern false fn for if impl in let loop match
    mod move mut pub ref return self Self static struct super trait true type union unsafe use where while
    """.split())
BINDING_PUNCT = re.compile(r'[()\[\]{}<>;=]')


def _alias_api(names: Set[str]):
    """A test of whether a text names a path, file-system or process item:
    PATH_API, a name in `names` (bound to one elsewhere), or a macro
    parameter (`$p`, which can be any of them)."""
    extra = re.compile(r'(?<![\w$])(?:%s)(?![\w$])' % "|".join(sorted(map(re.escape, names)))) if names else None
    return lambda t: bool(PATH_API.search(t) or "$" in t or (extra is not None and extra.search(t)))


def _binding_parts(code: str, start: int) -> Optional[Tuple[str, str, str, int]]:
    """The binding whose keyword ends at `start`: (pattern, type, initializer,
    end), or None when it has no initializer or is not a binding. The
    initializer runs to the `;` that ends the statement, the bracket that
    closes around it, or, after `if let` and `while let`, the `{` of the body;
    at most STATEMENT_WINDOW characters."""
    head_end = colon = -1
    depth = angle = 0
    for m in BINDING_PUNCT.finditer(code, start, start + STATEMENT_WINDOW):
        i, c = m.start(), m.group(0)
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth < 0:
                return None
        elif c == "<":
            angle += 1
        elif c == ">" and code[i - 1] != "-":
            angle = max(0, angle - 1)
        elif c == ";" and depth == 0:
            return None  # `let x;`, `static X: T;`
        elif (c == "=" and depth == 0 and angle == 0 and code[i + 1:i + 2] not in ("=", ">")
              and code[i - 1] not in "=!<>+-*/%^&|"):
            head_end = i
            break
    if head_end < 0:
        return None
    head = code[start:head_end]
    for m in re.finditer(r'(?<!:):(?!:)', head):
        colon = m.start()
        break
    pattern, typ = (head[:colon], head[colon + 1:]) if colon >= 0 else (head, "")
    before = code[max(0, start - 80):start].rstrip()
    body_ends = re.search(r'(?<![\w$])(?:if|while)\s+let$|&&\s*let$', before) is not None
    depth = 0
    end = min(len(code), head_end + 1 + STATEMENT_WINDOW)
    for m in BINDING_PUNCT.finditer(code, head_end + 1, end):
        i, c = m.start(), m.group(0)
        if c == "{" and depth == 0 and body_ends:
            end = i
            break
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
            if depth < 0:
                end = i
                break
        elif c == ";" and depth == 0:
            end = i
            break
    return pattern, typ, code[head_end + 1:end], end


def _whole_path(init: str) -> Optional[str]:
    """The path an initializer is, modulo `&`, `&mut`, `*`, parentheses, a
    block around it and a trailing `as` cast (`(std::fs::read_dir)`,
    `read_dir::<String> as fn(String) -> R`); None for any other expression."""
    t = init.strip()
    while True:
        if t[:1] in ("&", "*"):
            t = t[1:].lstrip()
            if re.match(r'mut(?![\w$])', t):
                t = t[3:].lstrip()
            continue
        if t[:1] in ("(", "{") and t[-1:] == {"(": ")", "{": "}"}[t[0]]:
            inner, _parent = _bracket_tree(t, [len(t) - 1])
            if inner[len(t) - 1] == 0:  # the opening bracket closes last
                t = t[1:-1].strip()
                continue
        break
    m = PATH_EXPR.match(t)
    if m is None or m.group(0) in RUST_KEYWORDS:
        return None
    rest = t[m.end():]
    return m.group(0) if not rest.strip() or re.match(r'\s+as(?![\w$])', rest) else None


def _calls_api(text: str, api) -> bool:
    """Whether `text` calls a path, file-system or process item (`api`): a
    path or method so named before `(` or `!` (`std::fs::read_dir(p)`,
    `p.join(..)`, `cmd!(..)`), not a variable or constant that holds such a
    word (`include_dependencies`)."""
    for m in PATH_EXPR.finditer(text):
        nxt = text[m.end():].lstrip()
        if (nxt[:1] == "(" or (nxt[:1] == "!" and nxt[1:2] != "=")) and api(m.group(0)):
            return True
    return False


def _binding_aliases(code: str, api, local: bool) -> Tuple[Set[str], bool]:
    """The names `code`'s bindings make callable for a path, file-system or
    process item (`api`), and whether one binds a name a macro parameter gives
    (`let $n = ..`, which can be any name). A binding is such an alias when its
    initializer uses such an item as a value rather than calling it: as the
    whole initializer (`let list = read_dir;`, with a turbofish, in
    parentheses, behind `&` or an `as` cast), as a qualified path anywhere in
    it (`Some(std::fs::read_dir)`, not `x.collect::<PathBuf>()`), called in a
    closure it is (`|p| std::fs::read_dir(p)`, _calls_api), or when its type is
    callable and names one
    (`const LIST: fn(String) -> io::Result<ReadDir> = ..`). `local`: whether
    `let` counts; another file's `let` binds no name this file can use, unless
    a macro parameter names it (ITEM_BINDING_START)."""
    names: Set[str] = set()
    unknown = False
    for b in (BINDING_START if local else ITEM_BINDING_START).finditer(code):
        after = code[b.end():b.end() + 24].lstrip()
        if re.match(r'(?:fn|unsafe|async|extern)(?![\w$])|\{', after):
            continue  # `const fn`, `const unsafe fn`, an inline `const { .. }`
        if b.group(1) == "const" and code[max(0, b.start() - 80):b.start()].rstrip()[-1:] in ("<", ","):
            continue  # a const generic parameter
        parts = _binding_parts(code, b.end())
        if parts is None:
            continue
        pattern, typ, init, _end = parts
        bound = [n for n in re.findall(r'(?:\$|r#)?[^\W\d]\w*', pattern) if n not in RUST_KEYWORDS and n != "_"]
        whole = _whole_path(init)
        alias = (whole is not None and api(whole)) \
            or (CLOSURE_START.match(init) is not None and _calls_api(init, api)) \
            or (CALLABLE_TYPE.search(typ) is not None and (api(typ) or api(init)))
        if not alias:
            for m in PATH_EXPR.finditer(init):
                p = m.group(0)
                if "::" not in p or not api(p):
                    continue
                if init[:m.start()].rstrip().endswith(".") and not init[:m.start()].rstrip().endswith(".."):
                    continue  # a method or a field: `x.collect::<PathBuf>()`
                nxt = init[m.end():].lstrip()
                if nxt[:1] in ("(", "{", ".") or (nxt[:1] == "!" and nxt[1:2] != "="):
                    continue  # called, a macro, a struct literal, a method of it
                alias = True
                break
        if alias:
            for n in bound:
                if n.startswith("$"):
                    unknown = True
                else:
                    names.add(n.removeprefix("r#"))
    return names, unknown


def _use_renames(code: str) -> List[Tuple[str, str]]:
    """Each (source path, name) a `use` or `extern crate` of `code` renames
    (`as _` binds none): the source with the prefixes of the braces around it
    (`use std::fs::{read_dir as list}`: std::fs::read_dir)."""
    out: List[Tuple[str, str]] = []
    for stmt in re.finditer(r'(?<![\w$])(?:use|extern\s+crate)(?![\w$])([^;]*);', code):
        if re.search(r'(?<![\w$])as(?![\w$])', stmt.group(1)) is None:
            continue
        prefixes = [""]
        element = ""
        for tok in re.finditer(r'[{},]|(?<![\w$])as\s+((?:\$|r#)?[^\W\d]\w*)|[^{},]', stmt.group(1)):
            t = tok.group(0)
            if t == "{":
                prefixes.append(prefixes[-1] + element)
                element = ""
            elif t == "}":
                if len(prefixes) > 1:
                    prefixes.pop()
                element = ""
            elif t == ",":
                element = ""
            elif tok.group(1) is not None:
                if tok.group(1) != "_":
                    out.append((prefixes[-1] + element, tok.group(1)))
                element = ""
            else:
                element += t
    return out


def _item_aliases(code: str, api, local: bool) -> Tuple[Set[str], bool]:
    """The names `code` binds to a path, file-system or process item (`api`):
    renaming imports, type aliases and bindings (_binding_aliases); and
    whether a macro parameter names one (any name, then)."""
    names, unknown = _binding_aliases(code, api, local)
    for source, name in _use_renames(code):
        if api(source):
            if name.startswith("$"):
                unknown = True
            else:
                names.add(name.removeprefix("r#"))
    for m in ALIAS_TYPE.finditer(code):
        if api(m.group(2)):
            if m.group(1).startswith("$"):
                unknown = True
            else:
                names.add(m.group(1).removeprefix("r#"))
    return names, unknown


def _path_api_aliased(code: str) -> bool:
    """Whether a file (code: strings and comments blanked) binds a path,
    file-system or process item to another name (ALIAS_USE, ALIAS_TYPE,
    _binding_aliases): a call by that name names no PATH_API."""
    api = _alias_api(set())
    names, unknown = _binding_aliases(code, api, True)
    return (any(PATH_API.search(m.group(0)) for m in ALIAS_USE.finditer(code))
            or any(PATH_API.search(m.group(2)) for m in ALIAS_TYPE.finditer(code))
            or bool(names) or unknown)


def _package_path_aliases(codes: Sequence[str]) -> Tuple[Set[str], bool]:
    """Across the code of every file a package compiles: the names bound to a
    path, file-system or process item (_item_aliases), to a fixed point (`pub
    use crate::util::list as fetch;` after `use std::fs::read_dir as list;`),
    and whether a macro parameter names one. A [[not_path]] file that names
    one, or any file when a macro parameter does, exempts nothing: the row's
    file need not bind the alias itself (`use crate::util::list;`). (Until
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only the row's file was read, and only a
    bare path bound by `let`, `const` or `static`: a turbofish, parentheses,
    an `as` cast or a closure exempted.)"""
    names: Set[str] = set()
    todo = list(codes)
    while todo:
        api = _alias_api(names)
        found: Set[str] = set()
        for code in todo:
            n, unknown = _item_aliases(code, api, False)
            if unknown:
                return names | found | n, True
            found |= n
        new = found - names
        if not new:
            return names, False
        names |= new
        # Only a file that names a new one can bind another name to it.
        named = re.compile(r'(?<![\w$])(?:%s)(?![\w$])' % "|".join(sorted(map(re.escape, new))))
        todo = [code for code in codes if named.search(code)]
    return names, False


def _in_path_call(code: str, s: int, e: int) -> bool:
    inner, parent = _bracket_tree(code, [s])
    opened = inner[s]
    while opened >= 0:
        if code[opened] == "(" and PATH_API.search(_callee_before(code, opened) or ""):
            return True
        opened = parent.get(opened, -1)
    before = max(code.rfind(c, max(0, s - STATEMENT_WINDOW), s) for c in ";{}")
    after = [i for i in (code.find(c, e, e + STATEMENT_WINDOW) for c in ";{}") if i >= 0]
    if (before < 0 and s > STATEMENT_WINDOW) or not after:
        return True
    return (PATH_API.search(code, before + 1, s) is not None
            or PATH_API.search(code, e, min(after)) is not None)


# A [[not_path]] literal is exempt only where every call around it calls an
# item by its name (a function, a method, a constructor, a qualified path),
# which the alias guards above read. A call through a value can be a call of a
# path API under any name, wherever the value came from (another file, another
# crate): `list(..)` after `let list; list = std::fs::read_dir;`, `for list in
# [..]`, a match arm, a closure's or function's parameter (`apply(read_dir, r)`
# calls its `g(..)`), `let list = pick();`, `pick()(..)`, `(s.g)(..)`,
# `fs[0](..)`. (Until LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only a `let`, `const` or
# `static` initializer that named a path API made a name an alias.)
FN_NAMED = re.compile(r'(?<![\w$])fn\s+(?:r#)?[^\W\d]\w*')
BINDING_NAME = re.compile(r'(?:\$|r#)?[^\W\d]\w*')
MACRO_ARGS = re.compile(r'(?<![\w$])(?:r#)?[^\W\d]\w*\s*!\s*[(\[{]')


def _callee_kind(code: str, o: int) -> Tuple[str, Optional[str]]:
    """What the `(` at code[o] (strings and comments blanked) follows:
    ("value", None) after a call, an index, a block, a `?` or a macro
    parameter (`pick()(..)`, `fs[0](..)`, `(s.g)(..)`, `$f(..)`); ("name", n)
    after an unqualified name (`list(..)`, `list::<String>(..)`); ("item",
    None) after a qualified path or a method (`std::fs::read_dir(..)`,
    `p.join(..)`); ("none", None) where nothing is called: a tuple, a
    grouping, a macro's arguments, a keyword's operand (`if (..)`), a
    callable type (`fn(..)`, `Fn(..)`)."""
    j = o - 1
    while j >= 0 and code[j].isspace():
        j -= 1
    if j >= 0 and code[j] == ">" and code[j - 1:j] != "-":  # a turbofish: `list::<String>(`
        depth = 0
        while j >= 0:
            if code[j] == ">" and code[j - 1:j] != "-":
                depth += 1
            elif code[j] == "<":
                depth -= 1
                if depth == 0:
                    break
            j -= 1
        j -= 1
        while j >= 0 and code[j].isspace():
            j -= 1
        if code[j - 1:j + 1] != "::":
            return "none", None  # a comparison: `a > (b)`
        j -= 2
        while j >= 0 and code[j].isspace():
            j -= 1
    if j < 0:
        return "none", None
    if code[j] in ")]}?":
        return "value", None
    if not (code[j].isalnum() or code[j] in "_$"):
        return "none", None
    end = j + 1
    while j >= 0 and (code[j].isalnum() or code[j] in "_$"):
        j -= 1
    name = code[j + 1:end]
    if name.startswith("$"):
        return "value", None
    if code[j - 1:j + 1] == "r#":
        j -= 2
    elif name[0].isdigit() or name in RUST_KEYWORDS or name in ("Fn", "FnMut", "FnOnce"):
        return "none", None
    while j >= 0 and code[j].isspace():
        j -= 1
    if j >= 0 and (code[j] == "." or code[j - 1:j + 1] == "::"):
        return "item", None
    return "name", unicodedata.normalize("NFC", name.removeprefix("r#"))


def _fn_params(code: str, i: int) -> int:
    """The `(` of the parameters of the `fn` whose name ends at code[i],
    past its generics (`fn apply<F: Fn(String)>(g: F)`); -1 for none."""
    angle = 0
    while i < len(code):
        c = code[i]
        if c == "<":
            angle += 1
        elif c == ">" and code[i - 1] != "-":
            angle -= 1
        elif c == "(" and angle <= 0:
            return i
        elif c in "{;=" and angle <= 0:
            return -1
        i += 1
    return -1


def _fn_scopes(code: str) -> List[Tuple[int, int, int, int]]:
    """Each `fn` item with a body: (its parameters' `(`, their `)`, its
    body's `{`, its `}`)."""
    pairs = _pairs(code, BRACKET)
    out: List[Tuple[int, int, int, int]] = []
    for m in FN_NAMED.finditer(code):
        params = _fn_params(code, m.end())
        close = pairs.get(params, -1) if params >= 0 else -1
        if close < 0:
            continue
        depth, i = 0, close + 1
        while i < len(code):
            c = code[i]
            if c in "([":
                depth += 1
            elif c in ")]":
                depth -= 1
            elif c == ";" and depth <= 0:
                break  # no body
            elif c == "{" and depth <= 0:
                if i in pairs:
                    out.append((params, close, i, pairs[i]))
                break
            i += 1
    return out


def _pattern_names(span: str) -> Set[str]:
    """The names a pattern (or a parameter list, or a macro's arguments) can
    bind: every identifier that is no keyword and not called, a macro, a
    struct or a path's segment (`Some(list)`: list; `S { g, .. }`: g), NFC as
    rustc compares them; {"$"} when a macro parameter can bind any name."""
    out: Set[str] = set()
    for m in BINDING_NAME.finditer(span):
        name = m.group(0)
        if name.startswith("$"):
            return {"$"}
        after = span[m.end():].lstrip()
        before = span[:m.start()].rstrip()
        if (name in RUST_KEYWORDS or after[:1] in ("(", "{", "!") or after.startswith("::")
                or before.endswith(("::", ".", "'"))):
            continue
        out.add(unicodedata.normalize("NFC", name.removeprefix("r#")))
    return out


def _value_bindings(code: str, lo: int, hi: int) -> Set[str]:
    """The names code[lo:hi] (a function's parameters and body, or a whole
    file) can bind to a value: `let` patterns (with or without an
    initializer), `for` patterns, match arms, closure and function
    parameters, and a macro's arguments (`bind!(list, ..)` can expand to
    `let list = ..`); {"$"} when a macro parameter names one."""
    out: Set[str] = set()
    for m in re.finditer(r'(?<![\w$])let(?![\w$])', code[lo:hi]):
        s = lo + m.end()
        stop = re.compile(r'(?<![=!<>])=(?![=>])|;').search(code, s, min(hi, s + STATEMENT_WINDOW))
        out |= _pattern_names(code[s:stop.start() if stop else min(hi, s + STATEMENT_WINDOW)])
    for m in re.finditer(r'(?<![\w$])for(?![\w$])([^{};]*?)(?<![\w$])in(?![\w$])', code[lo:hi]):
        out |= _pattern_names(m.group(1))
    for m in re.finditer(r'\|([^|;{}]*)\|', code[lo:hi]):
        out |= _pattern_names(m.group(1))
    pairs = _pairs(code, BRACKET)
    opening = {c: o for o, c in pairs.items()}
    for m in re.finditer(r'=>', code[lo:hi]):
        # Back to the arm's start: a `,` or `;`, the bracket around it, or the
        # block of the arm before (a struct pattern's braces are skipped).
        arrow = lo + m.start()
        j, depth = arrow - 1, 0
        while j > max(lo, arrow - STATEMENT_WINDOW):
            c = code[j]
            if (c == "}" and depth == 0 and j in opening
                    and code[max(0, opening[j] - 40):opening[j]].rstrip().endswith("=>")):
                break
            if c in ")]}":
                depth += 1
            elif c in "([{":
                if depth == 0:
                    break
                depth -= 1
            elif c in ",;" and depth == 0:
                break
            j -= 1
        out |= _pattern_names(code[j + 1:arrow])
    # Parameters: the function's own (code[lo] is their `(`) and any nested
    # one's; a macro's arguments.
    opens = [lo] + [_fn_params(code, m.end()) for m in FN_NAMED.finditer(code, lo, hi)] + \
            [m.end() - 1 for m in MACRO_ARGS.finditer(code, lo, hi)]
    for i in opens:
        if i in pairs and code[i] in "([{":
            out |= _pattern_names(code[i + 1:pairs[i]])
    return out


def _in_value_call(code: str, s: int, memo: Optional[Dict[object, object]] = None) -> bool:
    """Whether a call through a value encloses code[s] (strings and comments
    blanked; see FN_NAMED): a call's result, an index or a block called, or a
    name that the innermost function around the call (its parameters and
    body), or outside any function the file, can bind to a value."""
    memo = {} if memo is None else memo
    inner, parent = _bracket_tree(code, [s])
    opened = inner[s]
    while opened >= 0:
        if code[opened] == "(":
            kind, name = _callee_kind(code, opened)
            if kind == "value":
                return True
            if kind == "name":
                if "scopes" not in memo:
                    memo["scopes"] = _fn_scopes(code)
                around = [(b, p, e) for p, _c, b, e in memo["scopes"] if b < opened < e]
                lo, hi = (max(around)[1], max(around)[2]) if around else (0, len(code))
                if (lo, hi) not in memo:
                    memo[(lo, hi)] = _value_bindings(code, lo, hi)
                bound = memo[(lo, hi)]
                if name in bound or "$" in bound:
                    return True
        opened = parent.get(opened, -1)
    return False


# A repository-root variable read by a call, or by env! or option_env! with
# any delimiter and whitespace or a comment around the `!` (matched in the
# text with comments blank; until the review of
# LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only `env!(`, and file!'s anchor
# FILE_ANCHOR_CODE only `file!()`, counted); `env :: var(..)` too (review 4, round 3).
REPO_ROOT_ENV = re.compile(r'(?:(?:env\s*::\s*var|var_os)\s*\(|(?:env|option_env)\s*!\s*[(\[{])'
                           r'\s*"[A-Z_]*(?:REPO_ROOT|SRC_ROOT|TRUST_ROOT|CHECKOUT)[A-Z_]*"')
GLOB_CHARS = re.compile(r'[*?\[{]')
PLACEHOLDER = re.compile(r'\{[^{}]*\}')
# A literal that is a path (or a format string of one), not prose that mentions one.
PATHISH = re.compile(r'^[A-Za-z0-9_{}:.,/+*?@=-]*$')
HARVEST_RE = r'"[^"\\]{1,240}"(\)[[:space:]]*\.join\([[:space:]]*"[^"\\]{1,240}")*'


# (path, owner, blob, proc_macro, audit) -> what scanning that file recorded.
# Valid across trees: a file's records depend only on its bytes, its package
# and the package's kind, and _declared_only_under_test's parent files, which
# the key does not hold; a replay over history accepts that (a parent whose
# cfg(test) declaration moved while the child's bytes did not), the live gate
# builds one graph per process and starts with an empty cache.
# None (the default, and always in the live gate and the tests) disables it.
SCAN_CACHE: Optional[Dict[tuple, tuple]] = None

# Audits of escape sites the scan cannot resolve, each held to the blob it was
# read at: a changed file lapses its audit and the site is unresolved again.
AUDITS_FILE = "scripts/gates/land-escape-audits.toml"


@dataclass
class Read:
    cls: str          # "compile" | "runtime"
    target: str       # repo-relative prefix, or a glob (fnmatch) over repo paths
    test_only: bool
    site: str
    # True for a read through the working directory or the running executable
    # (`current_dir()`, `current_exe()`, a bare `Path::new("..")`) in production
    # code: it reaches the checkout only where a test runs (Cargo starts a test,
    # and a test's helpers, in the package directory, from a binary in a target
    # directory inside the checkout). Under the stage-1 suites rustc runs in
    # compiletest's build directory from build/<host>/stage1/bin, so there it
    # reaches the build tree, which is those suites' input already (@stage1).
    cwd: bool = False
    # True for a read of which paths exist under `target` (a listing, an
    # `exists()`), never of their content: an audit row's `lists`. Only a
    # change that keeps a regular file a regular file at the same path
    # (Selection.in_place) does not reach it; every caller that does not know
    # the diff's statuses treats it as a content read.
    listing: bool = False
    # True for a record of a doctest's code (_scan_doctests; test-only too):
    # only a leg that builds doctests counts it, and `cargo check`
    # (compiler-check) builds none (LegSpec.doctests).
    doctest: bool = False


@dataclass
class Walk:
    file: str
    test_only: bool   # every walk in the file is in test code
    cwd: bool         # every walk in the file is anchored only at the working directory / executable
    cls: str          # "compile" (build script, proc macro) | "runtime"


def _cut_glob(path: str) -> Tuple[str, bool]:
    """(prefix, is_glob): a literal with glob/format characters becomes the
    directory before the first one."""
    m = GLOB_CHARS.search(path)
    if not m:
        return path.rstrip("/"), False
    return posixpath.dirname(path[: m.start()]).rstrip("/"), True


def _test_only_file(g: Graph, pkg: Package, path: str) -> bool:
    """Whether `pkg` compiles its file `path` only into its tests: the one
    rule every reader of a file's test-only context asks."""
    rel = path[len(pkg.dir) + 1:] if pkg.dir else path
    first = rel.split("/", 1)[0]
    if first in ("tests", "benches", "examples"):
        # Cargo's test, bench and example targets and their modules, unless
        # production code compiles the file (_main_production_name: until
        # LAND-GATE-EW1-FOLLOWUP-REVIEW-3 `#[path = "../tests/common/mod.rs"]
        # mod common;` in lib.rs, and until its review a binary's
        # `path = "tests/support/tool.rs"`, left it test-only).
        return not _named_in_production(g, path, main=True)
    # A module declared only inside #[cfg(test)] items, by a path attribute
    # (test_path_modules) or by `#[cfg(test)] mod <stem>;` in the files that
    # may declare it (_declared_only_under_test), and named by no production
    # declaration at all (_named_in_production: a Cargo target, a path
    # attribute, an include!, a module item, a module a macro declares).
    # (Review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3: a file declared only
    # under test was test-only whatever else named it, so rustc-main's
    # `[[bin]] path = "src/x.rs"` beside lib.rs's `#[cfg(test)] mod x;`
    # left x.rs's reads out of ui-trust.)
    # Only with positive evidence: no module of a package that may declare
    # one by macro (_may_declare_modules_by_macro) is test-only by its
    # declarations, since a production declaration may then be one no
    # reading of the gate sees. (Review 4 of LAND-GATE-EW1-FOLLOWUP-REVIEW-3:
    # a `#[cfg(test)] #[cfg_attr(unix, path = "x.rs")] mod x2;`, which the gate
    # read only since that review, turned the x.rs `lit!();` compiles
    # test-only, where `macro_rules! lit { () => { mod x; } }`. Such a
    # spelling is no evidence now (_index_path_modules); this rule keeps a
    # plain one from doing the same.)
    declared_only_under_test = _declared_only_under_test(g, pkg, path)
    return (path in g.test_path_modules or declared_only_under_test) and not _named_in_production(g, path) \
        and not _may_declare_modules_by_macro(g, pkg)


def _own_context(g: Graph, pkg: Package, path: str,
                 lazy: bool = False) -> Tuple[Optional[str], Optional[bool], bool]:
    """How _scan_file reads `pkg`'s own file `path`: (what builds it,
    _build_role's "build", "both" or None; test-only; never run).
    `lazy`: test-only is None, for the caller to tell when it needs it."""
    test_only = None if lazy else _test_only_file(g, pkg, path)
    return _build_role(g, pkg, path), test_only, _never_runs(pkg, path)


def _index_path_modules(g: Graph, files: Sequence[str], blobs: Dict[str, bytes],
                        compilers: Optional[Dict[str, Set[str]]] = None) -> None:
    """Where each path attribute points, split by whether it sits in
    test-only code (test_path_modules, prod_path_modules); and, production
    only, every file an include! names, as spelt and through links: a
    target any production declaration names is production
    (_named_in_production, which reads plain module items itself). A path
    attribute or include! that is not a literal names every path-like
    literal of its file (as _scan_file reads it). `compilers`: the packages,
    beside the owner, whose CARGO_MANIFEST_DIR an include! of a file
    resolves from (_compiled_elsewhere's). What a file under its package's
    tests/, benches/ or examples/ names is kept apart, by the file naming
    it (_prod_main_via): production only when that file is
    (_main_production_name)."""
    evidence: Dict[str, Set[str]] = {}
    for path in files:
        text = blobs[path].decode("utf-8", "replace")
        if g.owner(path) is not None or path in (compilers or {}):  # a ui test's macro is its own
            _index_module_macros(g, path, text)
        if not PATH_ATTR.search(text) and not INCLUDE_HINT.search(text):
            continue
        lx = _lexed(g, path, text)
        oid = _blob_id(g, path, blobs[path])
        fdir = posixpath.dirname(path)
        stem = posixpath.splitext(posixpath.basename(path))[0]
        bases = (fdir, posixpath.join(fdir, stem))
        guesses = [(b, v) for _s, _e, v in lx.strings if _pathlike(v) for b in bases]
        prod: List[Tuple[str, str]] = []
        # Test-only only as the gate read a #[cfg(test)] path attribute before
        # LAND-GATE-EW1-FOLLOWUP-REVIEW-3, in the scan's own files
        # (_paths_read_before, _scanned_before): one that review first read
        # (cfg_attr, raw, spaced or escaped, in helper.RS or a file holding a
        # NUL), or one found only by _compiled_elsewhere (`compilers`,
        # helper.txt), may name a module test-only that a production
        # declaration the gate cannot see compiles (a procedural or external
        # macro's module: docs/KNOWN_HAZARDS.md). (Review of that review: a
        # helper.txt's turned production modules test-only; review 4: so did
        # a `#[cfg(test)] #[cfg_attr(unix, path = "x.rs")] mod x2;`.) What
        # either reading takes for production stays production.
        if compilers is None:
            evidence[path], before = _paths_read_before(lx, path, text)
            g.prod_path_modules.update(before)
        for pos, value, _end in _path_attrs_of(g, oid, lx, text):
            if value is None:
                if not lx.in_test(pos):
                    prod += guesses
                continue  # no target to sort (_scan_file leaves the package unresolved)
            targets = {_norm(fdir, value), _norm(posixpath.join(fdir, stem), value)}
            if lx.in_test(pos):
                continue  # test-only evidence only as the gate read it before (below)
            g.prod_path_modules.update(t for t in targets if t)
            prod += [(b, value) for b in bases]
        owner = g.owner(path)
        owners = {fdir if owner is None else owner, *(compilers or {}).get(path, ())}
        for start, end, source in _include_calls_of(g, oid, lx):
            if lx.in_test(start) or not source:
                continue
            kind, value = _include_arg(lx, text, end)
            if kind == "file":
                prod += [(b, value) for b in bases]
            elif kind == "manifest":
                prod += [(d, value) for d in owners]
            elif kind == "unknown":
                prod += guesses
        named = {t for base, rel in prod for t in (_norm(base, rel), _realpath(g, base, rel)) if t}
        g.prod_path_modules.update(named)
        rel = path[len(owner) + 1:] if owner else path
        if owner is None or rel.split("/", 1)[0] not in ("tests", "benches", "examples"):
            g.__dict__.setdefault("_prod_main", set()).update(named)  # outside test, bench and example code
        else:  # inside: production only when the naming file is (_main_production_name)
            via = g.__dict__.setdefault("_prod_main_via", {})
            for t in named:
                via.setdefault(fold(t), set()).add(path)
    for path in _scanned_before(g, sorted(p for p, t in evidence.items() if t), blobs):
        g.test_path_modules.update(evidence[path])
    # What was told from the sets before this call no longer holds.
    g.__dict__.update(_production_memo={}, _prod_folded=None, _prod_main_folded=None, _declared_memo={})


# A path attribute as the gate read one before LAND-GATE-EW1-FOLLOWUP-REVIEW-3
# (commit 6ec42b3f2e): `#[path = "x.rs"]` in any spacing, its literal as
# written (an escape names no file), in a file holding `#[path`.
PATH_ATTR_6EC = re.compile(r'#\s*\[\s*path\s*=\s*"([^"]+)"\s*\]')
# A path git grep prints quoted (core.quotePath), which the scan then dropped.
GIT_QUOTED = re.compile(r'[\x00-\x1f\x7f"\\]|[^\x00-\x7f]')


def _paths_read_before(lx, path: str, text: str) -> Tuple[Set[str], Set[str]]:
    """(test, production): the files the path attributes of the lexed file
    `path` name as the gate read them before LAND-GATE-EW1-FOLLOWUP-REVIEW-3,
    each PATH_ATTR_6EC in code, in a file holding `#[path` or `# [path`.
    Test: one both the lexer and its reading then (Lexed.legacy) take for
    test code, in a file holding `#[path` (the prefilter then took `# [path`
    too, in a file git grep listed for another escape: such a file gives
    none here, fewer test-only modules). Production: one that reading takes
    for production code (`#[cfg(test<U+200E>)]` is none)."""
    test: Set[str] = set()
    prod: Set[str] = set()
    if "#[path" not in text and "# [path" not in text:
        return test, prod
    old = lx.legacy()
    fdir = posixpath.dirname(path)
    stem = posixpath.splitext(posixpath.basename(path))[0]
    for m in PATH_ATTR_6EC.finditer(text):
        if not lx.in_code(m.start()):
            continue
        targets = {t for t in (_norm(fdir, m.group(1)), _norm(posixpath.join(fdir, stem), m.group(1))) if t}
        if not old.in_test(m.start()):
            prod.update(targets)
        elif lx.in_test(m.start()) and "#[path" in text:
            test.update(targets)
    return test, prod


def _scanned_before(g: Graph, paths: Sequence[str], blobs: Dict[str, bytes]) -> Set[str]:
    """Which of `paths`, files of the scan holding `#[path`, the escape scan
    read before LAND-GATE-EW1-FOLLOWUP-REVIEW-3: an audited file, or one
    `git grep -l -I .. -- '*.rs'` listed: named `.rs` in lower case, text to
    git (no NUL in its first 8000 bytes, no `binary` or `-diff` mark: git
    grep -I tells, the last of -a and -I counting), at a path git does not
    quote. It ran in the caller's locale, where a byte that is not UTF-8
    before a match on its line hid it: here any such byte does. Only the
    audited ones when git grep fails (no test-only evidence)."""
    audited = load_audits(g)
    out = {p for p in paths if p in audited}
    rest = []
    for p in paths:
        if p in out or not p.endswith(".rs") or GIT_QUOTED.search(p):
            continue
        try:
            blobs[p].decode("utf-8")
        except UnicodeDecodeError:
            continue
        rest.append(p)
    if rest:
        found = _git_grep(g, ["-l", "-z", "-I", "-F", "-e", "#[path"], [":(literal)" + p for p in rest])
        out.update(_grep_listed(g, found) if found is not None else ())
    return out


def _named_in_production(g: Graph, path: str, main: bool = False) -> bool:
    """Whether a production declaration names the module file `path`, at its
    own path or any other that tracked links show it at (link_aliases; none
    told: yes): a path attribute, a module item or an include! outside test
    code naming it or a directory above it (prod_path_modules), a `mod` item
    outside test code in a file of its directory or a directory above it
    that takes it, or a module a macro declares there (_declared_in: `mod
    x;`, `mod a { mod x; }`, `mod $name;`, `m!(x);` of a macro defined
    elsewhere that declares one), or a Cargo target; names
    compared as the landing host compares them (fold). `main`: for a file
    under tests/, benches/ or examples/, whether production code compiles
    it (_main_production_name).
    (LAND-GATE-EW1-FOLLOWUP-REVIEW-3: until then only a path attribute
    counted, so a `#[cfg(test)] #[path = "x.rs"] mod x2;` anywhere turned
    the x.rs a plain `mod x;` compiles test-only, and the legs that leave
    tests out skipped its reads.)
    The `main` question recurses through the files that name `path` from
    inside those directories; a file met again on the way is taken as not
    production there (the least answer: a cycle of modules is production
    only when something outside it is), and an answer that rests on such a
    file still being decided is not kept."""
    memo = g.__dict__.setdefault("_production_memo", {})
    key = (path, main)
    if key in memo:
        return memo[key]
    stack: List[str] = g.__dict__.setdefault("_main_stack", [])
    if main and path in stack:
        g.__dict__["_main_cut"] = True
        return False
    aliases = link_aliases(g, path)
    if aliases is None:
        memo[key] = True
        return True
    if not main:
        memo[key] = any(_production_name(g, n) for n in (path, *aliases))
        return memo[key]
    outer_cut = g.__dict__.get("_main_cut", False)
    g.__dict__["_main_cut"] = False
    stack.append(path)
    try:
        result = any(_main_production_name(g, alias) for alias in (path, *aliases))
    finally:
        stack.pop()
        cut = g.__dict__["_main_cut"]
        g.__dict__["_main_cut"] = outer_cut or cut
    if result or not cut or not stack:
        memo[key] = result
    return result


def _in_test_directory(g: Graph, path: str) -> bool:
    """Whether `path` lies under its package's tests/, benches/ or examples/."""
    owner = g.owner(path)
    if owner is None:
        return False
    rel = path[len(owner) + 1:] if owner else path
    return rel.split("/", 1)[0] in ("tests", "benches", "examples")


def _main_production_name(g: Graph, name: str) -> bool:
    """Whether production code compiles the file `name`, which lies under its
    package's tests/, benches/ or examples/: a path attribute or include!
    outside test code in a file outside those directories naming it or a
    directory above it (_prod_main), the source of a library, binary or
    build-script target (Cargo's [lib], [[bin]], `build`: a test, bench or
    example target's is test code), or a production module item, path
    attribute or include! of a file outside those directories, or of one
    inside them that production code compiles in turn (`mod tests;` in a
    root lib.rs, then tests/mod.rs's `mod common;`). (Review of
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3: only the first counted, so
    `[[bin]] path = "tests/support/tool.rs"` was test-only, and the legs
    that leave tests out skipped its reads.)"""
    folded = g.__dict__.get("_prod_main_folded")
    if folded is None:
        folded = g.__dict__["_prod_main_folded"] = {fold(t) for t in g.__dict__.get("_prod_main", ())}
    fname = fold(name)
    if _under_any(fname, folded) or fname in _cargo_targets(g, main=True):
        return True
    via = g.__dict__.get("_prod_main_via", {})
    parts = fname.split("/")
    for i in range(len(parts), 0, -1):  # it, or a directory above it
        for namer in sorted(via.get("/".join(parts[:i]), ())):
            if _named_in_production(g, namer, main=True):
                return True
    d, base = posixpath.split(name)
    stem = posixpath.basename(d) if fold(base) == "mod.rs" else posixpath.splitext(base)[0]
    for a in [d, *reversed(_proper_ancestors(d)), ""] if d else [""]:
        for declarer, taken in _declarations_in(g, a, fold(stem)):
            if (None in taken or fname in taken) and (
                    not _in_test_directory(g, declarer) or _named_in_production(g, declarer, main=True)):
                return True
    return False


def _production_name(g: Graph, name: str) -> bool:
    folded = g.__dict__.get("_prod_folded")
    if folded is None:
        folded = g.__dict__["_prod_folded"] = {fold(t) for t in g.prod_path_modules}
    fname = fold(name)
    if _under_any(fname, folded):
        return True
    owner = g.owner(name)
    pkg = g.packages.get(owner) if owner is not None else None
    if fname in _cargo_targets(g) or (pkg is not None and (
            name in pkg.build_scripts or AUTO_TARGET.fullmatch(fold(name[len(pkg.dir) + 1:] if pkg.dir else name)))):
        return True
    d, base = posixpath.split(name)
    stem = posixpath.basename(d) if fold(base) == "mod.rs" else posixpath.splitext(base)[0]
    for a in [d, *reversed(_proper_ancestors(d)), ""] if d else [""]:
        declared = _declared_in(g, a, fold(stem))
        if None in declared or fname in declared:
            return True
    return False


def _cargo_targets(g: Graph, main: bool = False) -> Set[str]:
    """Every source a manifest names for a target or build script, folded
    (build_graph's; Cargo's default ones are told by their path); `main`:
    only a library's, a binary's or a build script's."""
    key = "_cargo_main_targets" if main else "_cargo_targets"
    out = g.__dict__.get(key)
    if out is None:
        out = set()
        for pkg in g.packages.values():
            manifest = posixpath.join(pkg.dir, "Cargo.toml") if pkg.dir else "Cargo.toml"
            try:
                doc = tomllib.loads(g.index.read_blobs([manifest])[manifest].decode("utf-8"))
            except (KeyError, RuntimeError, ValueError, UnicodeDecodeError):
                doc = {}
            out.update(fold(t) for t in (_norm(pkg.dir, sp) for sp in _target_paths(doc, main)) if t)
            out.update(fold(b) for b in pkg.build_scripts)
        g.__dict__[key] = out
    return out


def _dir_children(g: Graph, d: str) -> List[str]:
    """The index's entries directly in the directory `d` ("" is the root)."""
    children = g.__dict__.get("_dir_children")
    if children is None:
        children = g.__dict__["_dir_children"] = {}
        for p in g.index.entries:
            children.setdefault(posixpath.dirname(p), []).append(p)
    return children.get(d, [])


def _module_files_in(g: Graph, base: str) -> List[str]:
    """Every file a module of the directory `base` may take, relative to it:
    each Rust file in it and each `<dir>/mod.rs` (a link may show one), as
    the file system resolves `base` (through links)."""
    real = _realpath(g, posixpath.dirname(base), posixpath.basename(base)) if base else ""
    if real is None:
        return []
    _dir_children(g, real)
    subdirs = g.__dict__.get("_subdirs")
    if subdirs is None:
        subdirs = g.__dict__["_subdirs"] = {}
        for d in g.__dict__["_dir_children"]:
            if d:
                subdirs.setdefault(posixpath.dirname(d), []).append(d)
    out: Set[str] = set()
    for c in _dir_children(g, real):
        name = posixpath.basename(c)
        if _rust_source(c):
            out.add(name)
        if g.index.entries[c][0] == "120000":
            out.add(name + "/mod.rs")
    for d in subdirs.get(real, ()):
        out.update(f"{posixpath.basename(d)}/{posixpath.basename(c)}" for c in _dir_children(g, d)
                   if fold(posixpath.basename(c)) == "mod.rs")
    return sorted(out)


# A Rust identifier as a module or macro name: Unicode XID (rustc takes `mod
# ñ;` with a path attribute, E0754 without), read wide, any character outside
# ASCII but Rust whitespace (a combining mark Python's `\w` does not take too),
# never an ASCII digit first; `r#` before it is the regexes'. (Until the
# review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only an ASCII first letter: the
# harvest neither followed nor blinded on `#[path = ".."] mod ñ;`.) Each
# position is one character class, everything but an ASCII character that
# is no word character, whitespace, U+200E and U+200F, so that every regex
# holding it matches in linear time. (Review 4, round 2: two overlapping
# alternatives repeated, `(?:\w|[^\x00-\x7f..])*`, backtracked exponentially
# where MOD_ITEM failed: `mod ` and 30 letters outside ASCII with no `;`
# after took minutes.)
IDENT = (r'[^\x00-\x40\x5b-\x5e\x60\x7b-\x7f\s\u200e\u200f]'
         r'[^\x00-\x2f\x3a-\x40\x5b-\x5e\x60\x7b-\x7f\s\u200e\u200f]*')
MOD_NAME = re.compile(r'\bmod' + RUST_WS + r'+(?:r#)?(' + IDENT + ')')  # in a text before lexing
REGULAR = ("100644", "100755")


def _declared_in(g: Graph, d: str, fstem: str) -> Set[Optional[str]]:
    """The files (folded) that a production `mod` item named `fstem` (folded)
    may take, declared in the Rust files directly in `d`: every file's of
    _declarations_in. None among them: one that may take any."""
    return {t for _declarer, taken in _declarations_in(g, d, fstem) for t in taken}


def _declarations_in(g: Graph, d: str, fstem: str) -> List[Tuple[str, Set[Optional[str]]]]:
    """Each Rust file directly in `d` (_rust_source, a link named so read
    through, and any a production path attribute or include! names) that
    may declare a module named `fstem` (folded) in production, with the
    files (folded) it may take, by _module_items. None among them: an item
    whose file cannot be told (a path attribute that is not a literal, a
    link that cannot be resolved), or a module a macro declares outside
    test code (`macro_rules! m { ($n:ident) => { mod $n; } }`, or `m!(x);`
    where m is defined elsewhere: _macro_module_sites), whose name cannot
    be told: either may take any file. (Review of
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3: a macro's module named nothing, so the
    mac/x.rs that `m!(x);` compiles was test-only when a #[cfg(test)] path
    attribute named it too.)"""
    memo = g.__dict__.setdefault("_declared_memo", {})
    key = (d, fstem)
    if key in memo:
        return memo[key]
    if d not in memo:  # the directory's declaring files, once: (file, its text's file, its names, a macro's module)
        entries, texts = g.index.entries, _link_texts(g)
        files: Dict[str, str] = {}
        unknown: List[str] = []
        for f in _dir_children(g, d):
            if not (_rust_source(f) or f in g.prod_path_modules):
                continue
            real = f if entries[f][0] in REGULAR else (
                _realpath(g, d, texts[f]) if entries[f][0] == "120000" else None)
            if entries[f][0] == "120000" and real is None:
                unknown.append(f)
            elif real is not None and entries.get(real, ("",))[0] in REGULAR:
                files[f] = real
        cache = g.blob_cache
        cache.update(g.index.read_blobs(sorted({r for r in files.values() if r not in cache})))
        listed = []
        for f, real in sorted(files.items()):
            text = cache[real].decode("utf-8", "replace")
            oid = _blob_id(g, real, cache[real])
            macro = False
            if _may_declare_by_macro(g, text, oid):
                lx = _lexed(g, real, text)
                at = _macro_module_sites(g, lx, text, oid)
                macro = any(not lx.in_test(a) for a in at)
            listed.append((f, real, {fold(n) for n in _mod_names_of(g, oid, text)}, macro))
        memo[d] = (unknown, listed)
    unknown, declarers = memo[d]
    out: List[Tuple[str, Set[Optional[str]]]] = [(f, {None}) for f in unknown]
    for f, real, names, macro in declarers:
        if macro:
            out.append((f, {None}))
            continue
        if fstem not in names:
            continue
        text = g.blob_cache[real].decode("utf-8", "replace")
        lx = _lexed(g, real, text)
        oid = _blob_id(g, real, g.blob_cache[real])
        stem = posixpath.splitext(posixpath.basename(f))[0]
        taken: Set[Optional[str]] = set()
        for pos, name, attrs, chains in _module_items_of(g, oid, lx, text):
            if name is None or fold(name) != fstem or lx.in_test(pos):
                continue
            if None in attrs or chains is None:
                taken.add(None)
                continue
            for rel in _module_rels(name, attrs, chains):
                for base in (d, posixpath.join(d, stem)):
                    taken.update(fold(t) for t in (_norm(base, rel), _realpath(g, base, rel)) if t)
        if taken:
            out.append((f, taken))
    memo[key] = out
    return out


def _never_runs(pkg: Package, path: str) -> bool:
    """examples/ and benches/ are compiled by a test build (cargo builds
    examples) but no landing leg RUNS them: their runtime reads do not count."""
    rel = path[len(pkg.dir) + 1:] if pkg.dir else path
    return rel.split("/", 1)[0] in ("benches", "examples")


# Pseudo-inputs a test reads through the build tree or the environment.
STAGE1 = "@stage1"            # build/<host>/stage{1,2}, or TRUST_RUSTC: the stage-1 leg's inputs
TARGO_TRUST = "@targo-trust"  # TRUST_TARGO_TRUST_BIN: the targo-trust closure
# A build-tree path: a stage1/stage2 segment, or "build/..." (a bare "build" is a
# cargo subcommand far more often than a directory; in a walking package the
# harvest maps a bare "build" too). Matched against the literal as the landing
# host's file system compares names (fold), as the harvest anchors: "Build/x"
# and "Stage1/bin" open build/x and stage1/bin there. (Until
# LAND-GATE-EW1-FOLLOWUP-REVIEW-3 the match was exact, in the scan's prefilter
# too: a package that does not walk read no build tree through "Build/x".)
STAGE_LITERAL = re.compile(r'(?:^|/)(?:stage[12](?:-[a-z]+)?)(?:/|$)|^build/')
ENV_PSEUDO = {"TRUST_RUSTC": STAGE1, "TRUST_TARGO_TRUST_BIN": TARGO_TRUST}

# How every git grep of the selector reads a file: as text (-a), whatever git
# takes for binary (a NUL in its first 8000 bytes, which trustc compiles in a
# comment or a string, or a .gitattributes `binary`, `-diff` or `-text` mark),
# and as stored (--no-textconv: no diff driver's conversion stands in for it);
# and prints what it found plainly (--no-color: under `color.ui` or
# `color.grep` = always, in the clone's or the user's git config, which the
# in-process selector inherits, git wraps each path in ANSI codes, and the
# escape scan then named no tracked file and recorded no read at all).
# Each runs under LC_ALL=C (in a UTF-8 locale an -E pattern matched no line
# holding a byte that is not UTF-8 before the match) and, where it lists paths,
# with -z (git quotes a non-ASCII path, which then names no tracked file).
# (Until LAND-GATE-EW1-FOLLOWUP-REVIEW-3, -I hid such a file from the escape,
# `../` and source-root scans, only the escape scan set the locale or -z, and
# it alone printed in color.)
GREP_AS_TEXT = ("-a", "--no-textconv", "--no-color")


def _grep_command(g: Graph, args: Sequence[str]) -> List[str]:
    # Git defaults to its own CPU-sized worker pool. Inside a held build slot a
    # query keeps that admission (the incoming macro-read closure's whole-tree
    # grep used about six cores under a two-CPU share: LAND-GREP-ADMISSION-1), and
    # an invalid advertised share refuses before spawning. An unmanaged caller
    # keeps the measured-host behaviour, as every other unmanaged plan does
    # (host_budget; docs/LANDING_GATE.md): `grep.threads=0` is Git's pool of one
    # worker per logical core whatever the clone's or the user's config says, and
    # a caller's CARGO_BUILD_JOBS hint changes nothing. (LAND-GREP-ADMISSION-2,
    # 2026-11-08: a serial unmanaged query made `plan` take about 28 minutes on an
    # 18-CPU host, longer than main stood still, so `run` started no leg in four
    # tries.) This changes only scheduling, never the patterns, file population
    # or failure semantics.
    #
    # Every path a query names is the tree's own spelling, so git must take it
    # as given: with core.precomposeunicode (macOS `git init` sets it) git
    # rewrites its argv to NFC, and a `:(literal)` pathspec naming a decomposed
    # (NFD) tracked path then names nothing and lists nothing, silently
    # (LAND-GATE-DISCOVERY-COST-1 review: a reused listing lost an NFD file's
    # include_str! read). And a query reads the superproject's tree only, as
    # TreeIndex does: submodule.recurse would otherwise add files no index
    # entry holds, or fail on a submodule commit this clone lacks.
    import host_budget
    jobs = host_budget.admitted_jobs()
    return ["git", "-c", f"grep.threads={0 if jobs is None else jobs}", "-c", "core.precomposeunicode=false",
            "-C", g.index.repo, "grep", "--no-recurse-submodules", *args]


def _git_grep(g: Graph, args: Sequence[str], pathspecs: Sequence[str]) -> Optional[bytes]:
    """`git grep <args>` over the commit's `pathspecs` (GREP_AS_TEXT, LC_ALL=C):
    its output, or None when it failed (git's complaint: _grep_complaint)."""
    g._grep_pathspecs.add(tuple(pathspecs))
    proc = subprocess.run(_grep_command(g, [*GREP_AS_TEXT, *args, g.index.rev, "--", *pathspecs]),
                          capture_output=True, env=git_env(LC_ALL="C"))
    if proc.returncode in (0, 1):
        return proc.stdout
    g.__dict__["_grep_complaint"] = proc.stderr.decode("utf-8", "replace").strip()
    return None


def _grep_complaint(g: Graph) -> str:
    """What git said when the last _git_grep of `g` failed (taken once)."""
    return g.__dict__.pop("_grep_complaint", None) or "git grep failed"


def _grep_listed(g: Graph, out: bytes) -> List[str]:
    """The paths a `git grep -l -z` printed, spelled as the index spells them."""
    prefix = g.index.rev + ":"
    return [raw[len(prefix):] if raw.startswith(prefix) else raw
            for raw in out.decode("utf-8", "surrogateescape").split("\0") if raw]


# A whole-tree listing query (`git grep -l -z <args> <rev> -- <positive>
# <literal exclusions>`) answers, per file, a function of that file's blob
# alone: GREP_AS_TEXT reads every file as stored, so no attribute, diff driver
# or neighbour changes it, and the pattern, git and its grep/core config are
# the graph's (graph_store_identity). A later graph therefore takes an earlier
# graph's answer for each file whose path, mode and object id are unchanged
# and that the earlier query examined, and asks git again, by literal path,
# only about the rest. Which files a query examines is git's own pathspec
# matcher's answer for this tree (_pathspec_scope); nothing is guessed from a
# name. (LAND-GATE-DISCOVERY-COST-1: the escape-candidate query alone took
# 150 to 176 s of every discovery on a loaded 14-CPU host, whatever changed.)
# Measured 2026-11-13 on this tree's 49,977-file scope (14-CPU host, load
# about 21), asking a random quarter by :(literal) path in 96 KB batches: the
# escape query 32.86 s against 123.64 s whole, the `mod`-passing query 1.15 s
# against 1.39 s whole. So a quarter is still below the cheapest query's
# break-even; at most a quarter is asked piecewise.
GREP_REUSE_SHARE = 4         # more than a quarter of the scope unknown: one whole query
GREP_PATHSPEC_BYTES = 96 * 1024  # literal pathspecs per git process (ARG_MAX is far above)


def _pathspec_scope(g: Graph, positive: str) -> Optional[FrozenSet[str]]:
    """Every file a `git grep <rev> -- <positive>` reads: what git's tree
    pathspec matcher (the one grep walks a tree with) names when it diffs the
    empty tree against this one, regular files only (grep reads no link or
    gitlink of a tree). None when git cannot say."""
    memo = g.__dict__.setdefault("_pathspec_scopes", {})
    if positive not in memo:
        empty = git(g.index.repo, "hash-object", "-t", "tree", "/dev/null").decode().strip()
        # Argv as given, as every selector grep takes it (_grep_command).
        proc = subprocess.run(["git", "-c", "core.precomposeunicode=false", "-C", g.index.repo,
                               "diff-tree", "-r", "-z", "--name-only", "--no-renames",
                               empty, g.index.tree, "--", positive], capture_output=True, env=git_env(LC_ALL="C"))
        memo[positive] = None if proc.returncode != 0 else frozenset(
            p for p in proc.stdout.decode("utf-8", "surrogateescape").split("\0")
            if p and g.index.entries.get(p, ("",))[0] in REGULAR)
    return memo[positive]


def _prior_listings_usable(previous: Optional[Graph], g: Graph) -> bool:
    """Whether `previous`'s listing answers may stand for `g`'s files: a
    completed scan of the same clone by the same scanner (an in-process graph,
    or a stored one whose identity named this scanner, git and config), and,
    though GREP_AS_TEXT makes them irrelevant, no attributes file changed."""
    if (previous is None or type(previous.index) is not TreeIndex or type(g.index) is not TreeIndex
            or previous.index.repo != g.index.repo or not previous.__dict__.get("_scan_complete", False)):
        return False
    before, after = previous.index.entries, g.index.entries
    return not any(before.get(p) != after.get(p) for p in before.keys() | after.keys()
                   if p.rsplit("/", 1)[-1] == ".gitattributes")


GREP_EXCLUDE_LITERAL = ":(exclude,literal)"


def _listed_by_grep(g: Graph, args: Sequence[str], pathspecs: Sequence[str]) -> Optional[bytes]:
    """_git_grep(g, args, pathspecs), answered per file where it can be.

    A whole-tree listing query (`args` start `-l -z`; `pathspecs` one positive
    and `:(exclude,literal)` exclusions) takes an earlier graph's answer for
    every file it may (_prior_listings) and asks git, by literal path, through
    _git_grep, about the rest; its output is then the listed paths, each
    NUL-terminated, in git's own order (the index's: bytewise by path). Its
    answer is kept (Graph.grep_listings) for the next graph. Any other query,
    or one with nothing to reuse, is _git_grep's, unchanged. None when any git
    grep it ran failed: a refusal, never a partial listing."""
    if (tuple(args[:2]) != ("-l", "-z") or not pathspecs or pathspecs[0].startswith(":(exclude")
            or not all(e.startswith(GREP_EXCLUDE_LITERAL) for e in pathspecs[1:])):
        return _git_grep(g, args, pathspecs)
    positive, exclusions = pathspecs[0], pathspecs[1:]
    key = (tuple(args), positive)
    excluded = frozenset(e[len(GREP_EXCLUDE_LITERAL):] for e in exclusions)
    prior = g.__dict__.get("_prior_listings")
    if prior is not None and key in prior[1]:
        listed = _reused_listing(g, args, positive, excluded, prior[0], prior[1][key])
        if listed is False:
            return None
        if listed is not None:
            # As the whole query would record it (classification reuse reads these).
            g._grep_pathspecs.add(tuple(pathspecs))
            g.grep_listings[key] = (frozenset(listed), excluded)
            return b"".join(p.encode("utf-8", "surrogateescape") + b"\0"
                            for p in sorted(listed, key=lambda q: q.encode("utf-8", "surrogateescape")))
    out = _git_grep(g, args, pathspecs)
    if out is not None:
        g.grep_listings[key] = (frozenset(_grep_listed(g, out)), excluded)
    return out


def _reused_listing(g: Graph, args: Sequence[str], positive: str, excluded: FrozenSet[str],
                    before: Dict[str, Tuple[str, str]],
                    earlier: Tuple[FrozenSet[str], FrozenSet[str]]):
    """The files the listing query lists in `g`'s tree, from the earlier
    graph's answer (`earlier`: listed, excluded; `before`: its tree's entries)
    for each file it examined unchanged, and from git for the rest; None when
    reuse would ask about too many files to pay (the caller asks the whole
    query), False when a git grep failed."""
    scope = _pathspec_scope(g, positive)
    if scope is None:
        return None
    was_listed, was_excluded = earlier
    examined = {p for p in scope if not (excluded and _under_any(p, set(excluded)))}
    after = g.index.entries
    then_out = set(was_excluded)
    unknown = sorted(p for p in examined if before.get(p) != after[p] or (then_out and _under_any(p, then_out)))
    if len(unknown) * GREP_REUSE_SHARE > len(examined):
        return None
    asked = set(unknown)
    listed = {p for p in examined if p in was_listed} - asked
    batch: List[str] = []
    size = 0
    for p in [*unknown, None]:
        spec = None if p is None else ":(literal)" + p
        if batch and (spec is None or size + len(os.fsencode(spec)) > GREP_PATHSPEC_BYTES):
            known = tuple(batch) in g._grep_pathspecs
            out = _git_grep(g, args, batch)
            if not known:
                # Within the positive scope the caller records: no new read.
                g._grep_pathspecs.discard(tuple(batch))
            if out is None:
                return False
            found = set(_grep_listed(g, out))
            # Literal pathspecs name only files of this query's scope.
            if not found <= asked:
                g.__dict__["_grep_complaint"] = f"git grep listed files outside the asked paths: {sorted(found)[:3]}"
                return False
            listed |= found
            batch, size = [], 0
        if spec is not None:
            batch.append(spec)
            size += len(os.fsencode(spec)) + 1
    g.__dict__["_reused_grep_answers"] = g.__dict__.get("_reused_grep_answers", 0) + len(examined) - len(unknown)
    return listed


# ---------------------------------------------------------------------------
# Blob facts: a pure text predicate's answer, per blob.
# ---------------------------------------------------------------------------
#
# The module closure asks the same text predicates of the same files in every
# graph (LAND-GATE-DISCOVERY-COST-1: tokenizing ~23.6k files, the module-macro
# definitions, spelling hints and call sites, module items, path attributes,
# include!s), and each answer is a function of the file's bytes and, for some,
# of one global parameter alone. Graph.blob_facts keeps each answer under
# (kind, the Git object id of the bytes it read, that exact parameter), and a
# later graph takes it for any file holding that blob (_blob_fact), from an
# earlier graph of the same clone under the same terms as its grep listings
# (_prior_listings_usable; a stored one only under an identity that names this
# code, GRAPH-STORE-1). A fact never holds a path, an owner or a context:
# what a package makes of it is computed fresh. Its key is never a path or a
# stat: the object id names the exact bytes, which TreeIndex.read_blobs
# authenticated against it (_blob_id); a tokenization is kept only for its
# blob's own text, taken only for a text equal to the one it holds, and
# every predicate of a text reads that text's tokens, never those of a doctest
# view or link target lexed at the same path (_lexed); a tokenization fact
# holds its fields alone (_bare). An earlier table holding any entry of an
# unknown kind, or of a parameter or value of another shape or type (each
# field of a tokenization's: _is_lexed), gives no fact at all
# (_usable_blob_facts).

def _is_names(value) -> bool:
    return type(value) is tuple and all(type(n) is str for n in value)


# A tokenization's own fields (rust_lex.Lexed); what a scan memoizes on one
# (Lexed.in_comment's _comment_starts, _passes_mod's memo, ..) is never
# part of a fact (_bare).
LEXED_FIELDS = frozenset(("text", "code", "strings", "comments", "test_spans", "test_mod_decls", "mod_decls",
                          "_span_starts", "_spans", "_legacy"))


def _bare(lx):
    """A Lexed holding `lx`'s fields alone (its legacy reading's too), sharing
    their values, which nothing writes after rust_lex.lex: a blob fact, and
    each working copy of one, so that what a scan memoizes on its copy never
    reaches the fact or another graph."""
    from rust_lex import Lexed  # scripts/lib is on sys.path for every caller
    return Lexed(lx.text, code=lx.code, strings=lx.strings, comments=lx.comments, test_spans=lx.test_spans,
                 test_mod_decls=lx.test_mod_decls, mod_decls=lx.mod_decls, _span_starts=lx._span_starts,
                 _spans=lx._spans, _legacy=None if lx._legacy is None else _bare(lx._legacy))


def _are_pairs(value) -> bool:
    """Whether `value` is a list of (int, int)."""
    return (type(value) is list and {type(t) for t in value} <= {tuple} and {len(t) for t in value} <= {2}
            and {type(i) for t in value for i in t} <= {int})


def _lexed_fields_valid(value) -> bool:
    """Whether `value` is a rust_lex.Lexed each of whose fields is of its type:
    a str `code` as long as `text`, `strings` (start, end, value), the spans
    (start, end), the declarations names, and `_legacy` None or another such
    of the same text, with no legacy reading of its own. What else it holds
    is not read here (_is_lexed, _reuse_tokenizations)."""
    from rust_lex import Lexed  # scripts/lib is on sys.path for every caller
    if type(value) is not Lexed:
        return False
    d = vars(value)
    if not LEXED_FIELDS <= d.keys():
        return False
    text, code, strings = d["text"], d["code"], d["strings"]
    legacy = d["_legacy"]
    return (type(text) is str and type(code) is str and len(code) == len(text)
            and type(strings) is list and {type(t) for t in strings} <= {tuple} and {len(t) for t in strings} <= {3}
            and all(type(a) is int and type(b) is int and type(v) is str for a, b, v in strings)
            and _are_pairs(d["comments"]) and _are_pairs(d["test_spans"]) and _are_pairs(d["_spans"])
            and type(d["_span_starts"]) is list and {type(i) for i in d["_span_starts"]} <= {int}
            and all(type(d[k]) is list and {type(n) for n in d[k]} <= {str} for k in ("mod_decls", "test_mod_decls"))
            and (legacy is None or (_lexed_fields_valid(legacy) and vars(legacy)["_legacy"] is None
                                    and vars(legacy)["text"] == text)))


def _is_lexed(value) -> bool:
    """A lex fact: a Lexed of valid fields (_lexed_fields_valid) holding them
    alone, its legacy reading too (_bare): no memo, which a scan would read
    unchecked."""
    return (_lexed_fields_valid(value) and vars(value).keys() == LEXED_FIELDS
            and (value._legacy is None or vars(value._legacy).keys() == LEXED_FIELDS))


def _is_module_items(value) -> bool:
    return type(value) is tuple and all(
        type(item) is tuple and len(item) == 4 and type(item[0]) is int
        and (item[1] is None or type(item[1]) is str)
        and type(item[2]) is tuple and all(a is None or type(a) is str for a in item[2])
        and (item[3] is None or (type(item[3]) is tuple and all(_is_names(c) for c in item[3])))
        for item in value)


def _is_macro_defs(value) -> bool:
    return (type(value) is tuple and len(value) == 2 and _is_names(value[0]) and type(value[1]) is tuple
            and all(type(pair) is tuple and len(pair) == 2 and type(pair[0]) is str
                    and type(pair[1]) is frozenset and all(type(c) is str for c in pair[1]) for pair in value[1]))


def _is_production_param(value) -> bool:
    return (type(value) is tuple and len(value) == 5 and _is_names(value[0]) and _is_names(value[1])
            and all(type(b) is bool for b in value[2:]))


# Each kind: (whether a parameter is of its shape, whether a value is).
BLOB_FACT_KINDS = {
    "lex": (lambda p: p is None, _is_lexed),
    # _macro_module_defs: (the names, what its other macros invoke and its `use`s rename).
    "macro_defs": (lambda p: p is None, _is_macro_defs),
    # _module_macro_spelling's hint, by the frontier it was built from.
    "spelling_hint": (_is_names, lambda v: type(v) is bool),
    # _may_declare_by_macro and _macro_module_sites, by _module_macros (_module_macro_key).
    "may_declare_by_macro": (_is_names, lambda v: type(v) is bool),
    "macro_module_sites": (_is_names, lambda v: type(v) is tuple and all(type(i) is int for i in v)),
    # _may_declare_modules_by_macro's test of one file: (the names it reads,
    # _module_macros, and whether the package defines, compiles from elsewhere
    # or passes `mod` in the file).
    "macro_production": (_is_production_param, lambda v: type(v) is bool),
    "module_items": (lambda p: p is None, _is_module_items),
    "path_attrs": (lambda p: p is None, lambda v: type(v) is tuple and all(
        type(a) is tuple and len(a) == 3 and type(a[0]) is int and (a[1] is None or type(a[1]) is str)
        and type(a[2]) is int for a in v)),
    # _include_calls: (start, end after the opening delimiter, whether it is include!).
    "include_calls": (lambda p: p is None, lambda v: type(v) is tuple and all(
        type(c) is tuple and len(c) == 3 and type(c[0]) is int and type(c[1]) is int and type(c[2]) is bool
        for c in v)),
    "mod_names": (lambda p: p is None, _is_names),
}
_OBJECT_ID = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")


def _usable_blob_facts(table) -> Optional[Dict[Tuple[str, str, object], object]]:
    """An earlier graph's blob facts, or None when any entry is not of its
    kind's shape: one malformed entry discards every fact (fail closed)."""
    if type(table) is not dict:
        return None
    for key, value in table.items():
        if type(key) is not tuple or len(key) != 3 or type(key[0]) is not str or key[0] not in BLOB_FACT_KINDS:
            return None
        kind, oid, param = key
        shaped = BLOB_FACT_KINDS[kind]
        if type(oid) is not str or not _OBJECT_ID.fullmatch(oid) or not shaped[0](param) or not shaped[1](value):
            return None
    return table


def _blob_id(g: Graph, path: str, blob: Optional[bytes]) -> Optional[str]:
    """The object id of `path` when `blob` is the very bytes TreeIndex.read_blobs
    authenticated against it (blob_cache's and read_blobs' are); None
    otherwise, and its facts are then computed and kept nowhere."""
    entry = g.index.entries.get(path)
    held = getattr(g.index, "_blob_bytes", None)
    if entry is None or blob is None or type(held) is not dict or held.get(entry[1]) is not blob:
        return None
    return entry[1]


def _blob_fact(g: Graph, kind: str, oid: Optional[str], param, compute):
    """compute()'s answer for the blob `oid` (None: computed, kept nowhere):
    this graph's, else an earlier graph's (_prior_blob_facts), else computed
    and kept. `param`: the exact global value compute reads beside the bytes."""
    if oid is None:
        return compute()
    key = (kind, oid, param)
    facts = g.blob_facts
    if key in facts:
        return facts[key]
    prior = g.__dict__.get("_prior_blob_facts")
    if prior is not None and key in prior:
        g.__dict__["_reused_blob_facts"] = g.__dict__.get("_reused_blob_facts", 0) + 1
        value = facts[key] = prior[key]
        return value
    value = facts[key] = compute()
    return value


def _blob_fact_held(g: Graph, kind: str, oid: Optional[str], param) -> bool:
    """Whether _blob_fact answers (kind, oid, param) without computing."""
    if oid is None:
        return False
    prior = g.__dict__.get("_prior_blob_facts")
    return (kind, oid, param) in g.blob_facts or (prior is not None and (kind, oid, param) in prior)


def _lexes(lx, text: str) -> bool:
    """Whether `lx` is the tokenization of exactly `text` (_lexed)."""
    return lx.text is text or lx.text == text


def _module_macro_key(g: Graph) -> Tuple[str, ...]:
    """The global parameter of _may_declare_by_macro and _macro_module_sites:
    the module macros indexed so far (_module_macros)."""
    return tuple(sorted(g.__dict__.get("_module_macros", ())))


def _module_items_of(g: Graph, oid: Optional[str], lx, text: str):
    """_module_items, a blob fact (each list a tuple)."""
    return _blob_fact(g, "module_items", oid, None, lambda: tuple(
        (pos, name, tuple(attrs), None if chains is None else tuple(tuple(c) for c in chains))
        for pos, name, attrs, chains in _module_items(lx, text)))


def _path_attrs_of(g: Graph, oid: Optional[str], lx, text: str):
    """_path_attrs, a blob fact."""
    return _blob_fact(g, "path_attrs", oid, None, lambda: tuple(_path_attrs(lx, text)))


def _include_calls_of(g: Graph, oid: Optional[str], lx):
    """_include_calls, a blob fact: (start, end after the opening delimiter,
    _includes_source) of each."""
    return _blob_fact(g, "include_calls", oid, None, lambda: tuple(
        (m.start(), m.end(), _includes_source(m)) for m in _include_calls(lx)))


def _mod_names_of(g: Graph, oid: Optional[str], text: str):
    """MOD_NAME.findall(text), a blob fact."""
    return _blob_fact(g, "mod_names", oid, None, lambda: tuple(MOD_NAME.findall(text)))


def _macro_defs_of(g: Graph, oid: Optional[str], lx) -> Tuple[Tuple[str, ...], Tuple[Tuple[str, FrozenSet[str]], ...]]:
    """_macro_module_defs(lx, calls), a blob fact: (its names, `calls` as
    sorted (name, what it invokes or renames) pairs)."""
    def compute():
        calls: Dict[str, Set[str]] = {}
        names = _macro_module_defs(lx, calls)
        return tuple(names), tuple((n, frozenset(c)) for n, c in sorted(calls.items()))
    return _blob_fact(g, "macro_defs", oid, None, compute)


def _macro_calls(defs) -> Dict[str, FrozenSet[str]]:
    """The `calls` of a _macro_defs_of fact, as _macro_module_defs fills them."""
    return dict(defs[1])


def _reuse_tokenizations(g: Graph, previous: Optional[Graph], blobs: Dict[str, bytes]) -> None:
    """Into g.lex_cache, a completed earlier graph's tokenization of each of
    `blobs` it held for the same entry and exactly its text (a pure
    function of those bytes; module roles and every read context are
    rebuilt), as a working copy of its fields (_bare); the blob's fact
    too (_lexed). None at all when any of them is not of its fields' types
    (_lexed_fields_valid): one malformed entry discards them all."""
    if previous is None or not previous.__dict__.get("_scan_complete", False):
        return
    held = previous.__dict__.get("lex_cache")
    if type(held) is not dict:
        return
    taken = []
    for path, blob in blobs.items():
        cached = held.get(path)
        if cached is not None and previous.index.entries.get(path) == g.index.entries.get(path):
            if not _lexed_fields_valid(cached):
                return
            if cached.text == blob.decode("utf-8", "replace"):
                taken.append((path, cached))
    for path, cached in taken:
        g.lex_cache[path] = _bare(cached)
        g.reused_tokenizations += 1
        g.blob_facts.setdefault(("lex", g.index.entries[path][1], None), _bare(cached))


def scan_escapes(g: Graph, reused: AbstractSet[str] = frozenset(), previous: Optional[Graph] = None,
                 *, progress=None) -> None:
    """Fill each package's reads, unresolved sites and history flags."""
    g.__dict__["_scan_complete"] = False
    _report_discovery(progress, "escape candidates", "start")
    # Every Rust file (_rust_source): `.rs` in any case, since rustc on the
    # landing host's case-insensitive file system compiles `mod helper;` from
    # helper.RS. Under LC_ALL=C, because in a UTF-8 locale git grep matched no
    # line holding a byte that is not UTF-8, while the scan decodes it with
    # replacement and still sees what the line spells. With -z, because git
    # quotes a non-ASCII path, which then named no tracked file. As text
    # (GREP_AS_TEXT): a NUL or a `binary` mark hid a file trustc compiles.
    # And every file with a doc value SCAN_RE cannot see into (DOC_VALUE_SCAN_RE).
    # Answered per file from an earlier graph where its blob is unchanged
    # (_listed_by_grep); git's own answer otherwise.
    out = _listed_by_grep(g, ["-l", "-z", "-E", SCAN_RE + DOC_VALUE_SCAN_RE], [":(icase)*.rs"])
    if out is None:
        why = f"escape scan failed: {_grep_complaint(g)[:200]}"
        for p in g.packages.values():
            p.unresolved.append(Read("compile", why, False, "(scan)"))
        _report_discovery(progress, "escape candidates", "refused", unresolved_packages=len(g.packages))
        return
    prefix = g.index.rev + ":"
    files = []
    for raw in out.decode("utf-8", "surrogateescape").split("\0"):
        path = raw[len(prefix):] if raw.startswith(prefix) else raw
        if path in g.index.entries:
            files.append(path)
    # A name git's ASCII case folding does not take for `.rs` (helper.rſ):
    # scanned whatever it holds.
    files += [p for p in _rust_sources(g) if not p.lower().endswith(".rs")]
    audits = load_audits(g)
    not_paths = load_not_paths(g)
    # A reviewed file can have no syntactic escape at all (for example,
    # metadata-name comparisons). Its declared footprint still applies, and
    # must replace any later package-wide literal harvest of that file.
    files = sorted(set(files) | {p for p in audits if p in g.index.entries})
    _report_discovery(progress, "escape candidates", "complete", candidate_entries=len(files))
    parents = sorted({q for f in files for q in _parent_candidates(f) if q in g.index.entries} - set(files))
    _report_discovery(progress, "source indexing", "start", candidate_entries=len(files))
    blobs = g.index.read_blobs(files + parents)
    g.lex_cache = {}
    _reuse_tokenizations(g, previous, blobs)
    g.blob_cache = blobs
    _index_path_modules(g, files, blobs)
    _report_discovery(progress, "source indexing", "complete", indexed_entries=len(files),
                      reused_tokenizations=g.reused_tokenizations)
    # What each package compiles that the scan above never reads as its own
    # (_compiled_elsewhere); a file found so is indexed too, and the walk
    # repeated, until it finds no new one (what it indexes can only make
    # more modules production, which it reads in).
    own_files: Dict[Optional[str], List[str]] = {}
    for f in files:
        own_files.setdefault(g.owner(f), []).append(f)
    own_links: Dict[Optional[str], List[Tuple[str, Optional[str]]]] = {}
    for link, target in link_targets(g):
        own_links.setdefault(g.owner(link), []).append((link, target))
    nested: Dict[Optional[str], List[str]] = {}  # each package's directly nested ones
    for d in g.packages:
        if d:
            nested.setdefault(g.owner(d), []).append(d)
    targets = g.__dict__.get("_targets_elsewhere", {})
    seeded = sorted(d for d in g.packages if own_links.get(d) or nested.get(d) or targets.get(d) or any(
        PATH_ATTR.search(t) or INCLUDE_HINT.search(t)
        for t in (blobs[f].decode("utf-8", "replace") for f in own_files.get(d, ()))))
    indexed = set(files)
    # The packages, beside its owner, each indexed file was indexed as compiled by.
    indexed_for: Dict[str, Set[str]] = {f: set() for f in files}
    # What each package compiles from elsewhere, as the walk has found it
    # (every round's: it only grows), is what _test_only_file's package rule
    # (_may_declare_modules_by_macro) reads, and the walk reads that rule:
    # each round's walk reads it as the last round left it. It grows only
    # with a file the walk finds new or with a new compiler, which repeats
    # the walk, so the rule the last walk read is the rule after it. (Review
    # 4 of LAND-GATE-EW1-FOLLOWUP-REVIEW-3: the rule read what the walk
    # found only after it, so with its module macro in a file the package
    # compiles from elsewhere (`#[macro_use] #[path = "defs.txt"] mod defs;`)
    # the y.in its mac/x.rs include!s was read test-only.)
    compiled: Dict[str, Set[str]] = {}
    g.__dict__["_compiled_from_elsewhere"] = {}
    closure_round = 0
    while True:
        closure_round += 1
        _report_discovery(progress, "module closure", "start", round=closure_round,
                          packages_examined=0, package_total=len(seeded))
        elsewhere = {}
        for examined, d in enumerate(seeded, 1):
            elsewhere[d] = _compiled_elsewhere(g, g.packages[d], own_files.get(d, []), own_links.get(d, []), blobs,
                                               sorted(nested.get(d, ())), targets.get(d, ()))
            _report_discovery(progress, "module closure", "progress", round=closure_round,
                              packages_examined=examined, package_total=len(seeded))
        _report_discovery(progress, "module closure", "complete", round=closure_round,
                          packages_examined=len(seeded), package_total=len(seeded))
        compilers: Dict[str, Set[str]] = {}
        for d, (found, _edges) in elsewhere.items():
            for _scan, real in found:
                compilers.setdefault(real, set()).add(d)
                compiled.setdefault(d, set()).add(real)
        g.__dict__.update(_compiled_from_elsewhere={d: sorted(c) for d, c in compiled.items()}, _visible_macro_memo={})
        new = sorted(set(compilers) - indexed)
        # A file indexed before a package was known to compile it is indexed
        # again with that package among its compilers: its manifest-dir
        # include! names that package's file too, and a file outside every
        # package defines its module macros for it (`#[macro_use] #[path =
        # "../../shared/defs.rs"] mod defs;`), which the first call leaves out
        # (a ui test's macro is its own). (Review of
        # LAND-GATE-EW1-FOLLOWUP-REVIEW-3: such a file's `macro_rules! m {
        # ($n:ident) => { mod $n; } }` was never indexed, so the module `m!(x);`
        # declares was test-only when a #[cfg(test)] path attribute named it.
        # Review 4: crates/b/src/x.rs's
        # `include!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/gen.rs"))` named
        # only B's gen.rs, and the gen.rs it compiles into A, which A declares
        # only under #[cfg(test)], stayed test-only.)
        regrown = sorted(q for q in compilers if q in indexed and not compilers[q] <= indexed_for.get(q, set()))
        if not new and not regrown:
            break
        if new:
            blobs.update(g.index.read_blobs([q for q in new if q not in blobs]))
            _index_path_modules(g, new, blobs, compilers)
            indexed.update(new)
        if regrown:
            _index_path_modules(g, regrown, blobs, compilers)
        indexed_for.update({q: set(compilers[q]) for q in (*new, *regrown)})
    for d, (_found, edges) in elsewhere.items():
        for real, why, test_only in {(r, t): (r, w, t) for r, w, t in reversed(edges)}.values():
            _foreign_source(g, g.packages[d], real, why, test_only)
    # The harvest reads _compiled_from_elsewhere, set in the loop, too (_harvest_package_literals).
    # Where a macro a package compiles may be called (_package_sources).
    g.__dict__["_sources_elsewhere"] = {d: sorted(found) for d, (found, _edges) in elsewhere.items()}
    _report_discovery(progress, "compiled-source closure", "complete", rounds=closure_round,
                      indexed_entries=len(indexed))
    top = sorted({p.split("/", 1)[0] for p in g.index.entries}, key=len, reverse=True)
    harvest_pkgs: Set[str] = set()
    own_scans = cache_replays = 0
    _report_discovery(progress, "own sources", "start", candidate_total=len(files))
    for examined, path in enumerate(files):
        _report_discovery(progress, "own sources", "progress", candidates_examined=examined,
                          candidate_total=len(files), scan_calls=own_scans, cache_replays=cache_replays)
        owner = g.owner(path)
        if owner is None or owner not in g.packages or owner in reused:
            continue
        pkg = g.packages[owner]
        ckey = cached = None
        if SCAN_CACHE is not None:
            # A source blob's read class also depends on its containing module
            # and Cargo target. Preserve those inputs across historical replay,
            # as well as the audit's value (never its Python object identity).
            audit_key = json.dumps(audits.get(path), sort_keys=True, separators=(",", ":"), default=str)
            test_only = _test_only_file(g, pkg, path)
            # Whether the row holds depends on its premises' blobs in this
            # tree too, not on this file's blob alone (review of EW-1).
            ckey = (path, owner, g.index.entries[path][1], pkg.proc_macro,
                    _build_role(g, pkg, path), test_only, audit_key, audit_holds(g, path, audits.get(path)))
            cached = SCAN_CACHE.get(ckey)
        if cached is not None:
            # The same blob in the same package and scan context scans the same:
            # replay what it recorded (a replay over many commits re-reads few files).
            reads, unresolved, history, walks, walked, foreign = cached
            pkg.reads.extend(reads)
            pkg.unresolved.extend(unresolved)
            pkg.history.extend(history)
            pkg.walks.extend(walks)
            pkg.foreign.extend(foreign)
            pkg.deps.update(foreign)
            if walked:
                harvest_pkgs.add(pkg.dir)
            cache_replays += 1
            continue
        marks = (len(pkg.reads), len(pkg.unresolved), len(pkg.history), len(pkg.walks), len(pkg.foreign))
        g.__dict__["_scan_reads_callers"] = False
        walked = _scan_one(g, pkg, path, blobs, audits, harvest_pkgs)
        own_scans += 1
        # A scan that read a macro's callers (_macro_callers) depends on other
        # files: a caller moved, the same blob scans otherwise.
        if SCAN_CACHE is not None and not g.__dict__["_scan_reads_callers"]:
            SCAN_CACHE[ckey] = (pkg.reads[marks[0]:], pkg.unresolved[marks[1]:], pkg.history[marks[2]:],
                                pkg.walks[marks[3]:], walked, pkg.foreign[marks[4]:])
    _report_discovery(progress, "own sources", "complete", candidates_examined=len(files),
                      candidate_total=len(files), scan_calls=own_scans, cache_replays=cache_replays)
    foreign_scans = 0
    _report_discovery(progress, "foreign sources", "start")
    for d, (found, _edges) in elsewhere.items():
        if d in reused:
            continue
        for (scan, real), contexts in sorted(found.items()):
            # Each context no other subsumes: production over test-only, a
            # run over examples/benches (a build script's is its own class).
            for ctx in sorted((c for c in contexts if not any(
                    o != c and o[0] == c[0] and o[1] <= c[1] and o[2] <= c[2] for o in contexts)),
                    key=lambda c: (c[0] or "", c[1], c[2])):
                # The file is the package's source: an input, as its own files are.
                _record(g, g.packages[d], "compile", real, f"{scan}: compiled by {d or '.'}", ctx[1])
                _scan_one(g, g.packages[d], scan, blobs, audits, harvest_pkgs, ctx, real)
                foreign_scans += 1
                _report_discovery(progress, "foreign sources", "progress", scan_calls=foreign_scans)
    _report_discovery(progress, "foreign sources", "complete", scan_calls=foreign_scans)
    _report_discovery(progress, "package literals", "start", package_total=len(harvest_pkgs))
    for harvested, d in enumerate(sorted(harvest_pkgs), 1):
        _harvest_package_literals(g, g.packages[d], top, audits, not_paths)
        _report_discovery(progress, "package literals", "progress", packages_harvested=harvested,
                          package_total=len(harvest_pkgs))
    _report_discovery(progress, "package literals", "complete", packages_harvested=len(harvest_pkgs),
                      package_total=len(harvest_pkgs))
    g.__dict__["_scan_complete"] = True


def _scan_one(g: Graph, pkg: Package, path: str, blobs: Dict[str, bytes], audits: Dict[str, dict],
              harvest_pkgs: Set[str], ctx: Optional[Tuple[Optional[str], bool, bool]] = None,
              real: Optional[str] = None) -> bool:
    """Scan `path` into `pkg`: its own file, or (`ctx`, _compiled_elsewhere)
    one it compiles from elsewhere, whose text is `real`'s (a link's
    target) and whose sites resolve from `path`."""
    real = real or path
    cache = g.lex_cache
    saved = cache.pop(path, None) if real != path else None  # a link's own text may be lexed there
    try:
        text = blobs[real].decode("utf-8", "replace")
        audit = audits.get(real)
        if audit_holds(g, real, audit):
            test_only = bool(audit.get("test_only", False)) or bool(ctx and ctx[1])
            cls = audit.get("class", "runtime")
            # A file the build script may compile (_build_role "both"): the
            # row's reads count while the package compiles too, never
            # test-only there, as _scan_file records a scanned file's.
            role = ctx[0] if ctx is not None else _build_role(g, pkg, path)
            kinds = [(cls, test_only)] if role is None else \
                [(c, test_only and c != "compile") for c in dict.fromkeys((cls, "compile"))]
            for c, to in kinds:
                for t in audit.get("reads", []):
                    pkg.reads.append(Read(c, t, to, f"{real} (audited)"))
                for t in audit.get("lists", []):
                    pkg.reads.append(Read(c, t, to, f"{real} (audited listing)", listing=True))
            hist = audit.get("history", False)
            if hist is True:
                for c, to in kinds:
                    pkg.history.append(Read(c, f"{real} (audited)", to, real))
            elif hist not in (False, "value-only"):
                pkg.unresolved.append(Read("compile", f"{real}: audit has an unknown history value {hist!r}",
                                           False, real))
            _foreign_edges(g, pkg, path, text)
            walked = _scan_doctests(g, pkg, path, text)
        else:
            walked = _scan_file(g, pkg, path, text) if ctx is None else _scan_file(g, pkg, path, text, ctx)
            walked = _scan_doctests(g, pkg, path, text) or walked
    finally:
        if real != path:
            cache.pop(path, None)
            if saved is not None:
                cache[path] = saved
    if walked:
        harvest_pkgs.add(pkg.dir)
    return walked


def _compiled_elsewhere(g: Graph, pkg: Package, files: Sequence[str], links: Sequence[Tuple[str, Optional[str]]],
                        blobs: Dict[str, bytes], nested: Sequence[str] = (), targets: Sequence[str] = ()
                        ) -> Tuple[Dict[Tuple[str, str], Set[Tuple[Optional[str], bool, bool]]], List[Tuple[str, str, bool]]]:
    """Every file `pkg` compiles that the escape scan never reads as its own:
    {(the path its sites resolve from, the file whose text it is): each
    context (_own_context's) code names it in}. git grep hands the scan
    tracked Rust files by name, each read for its owner alone, so a `#[path]`
    module or include!d file of another name (helper.txt), one outside
    every package, what an in-package link shows (a file link named Rust
    source, read from where the link sits; a directory link's modules), a
    module in a nested package's directory (`mod sub;` with sub/Cargo.toml)
    and a Cargo target's source outside every package or of another name
    were never scanned for the package compiling them
    (LAND-GATE-EW1-FOLLOWUP-REVIEW-3). Walked to a fixed point from the
    path attributes and include!s of the package's scanned files, its links,
    the directories of the packages nested in it (`nested`) and the sources
    of its targets its own scan does not read (`targets`), through
    each module item (_module_items: every path attribute and
    a cfg_attr's default), include! (any delimiter) and, guessed, a literal
    of one that is not a literal, as spelt and as links resolve it. A file
    `pkg` owns, named Rust source and at its own path, is scanned for it
    already: unless its own scan reads it in a narrower context than here
    (test-only, never run, a build script's class), it ends the walk.
    Another package's is walked and scanned for `pkg` too, in `pkg`'s
    context (its CARGO_MANIFEST_DIR), and is an edge (_foreign_source:
    returned as (file, why, test-only), for the caller to add once), but for
    what a scanned file's include! or path attribute outside inline modules
    names, whose edge is the scan's own (_scan_file, _foreign_edges:
    _maybe_foreign). `files`: the package's
    scanned files; `links`: its links and what each resolves to
    (link_targets)."""
    entries, texts = g.index.entries, _link_texts(g)
    found: Dict[Tuple[str, str], Set[Tuple[Optional[str], bool, bool]]] = {}
    edges: List[Tuple[str, str, bool]] = []
    work: List[Tuple[str, str, Tuple[Optional[str], bool, bool], Optional[Tuple[str, ...]], bool]] = []
    again: List[Tuple[str, str, Tuple[Optional[str], bool, bool], Optional[Tuple[str, ...]], bool]] = []

    def regular(q: Optional[str]) -> bool:
        return q is not None and entries.get(q, ("",))[0] in REGULAR

    def consider(scan: str, real: str, ctx: Tuple[Optional[str], bool, bool], why: str, edge: bool = True) -> None:
        owner = g.owner(real)
        if edge and owner is not None and owner != pkg.dir:
            edges.append((real, why, ctx[1]))
        # Only the package's own file is scanned for it already. Another
        # package's is scanned for this one too, in this one's context:
        # CARGO_MANIFEST_DIR is the compiling package's. (Review 4 of
        # LAND-GATE-EW1-FOLLOWUP-REVIEW-3: the walk ended at another package's
        # file its owner read in the same context, so A's `#[path]` module
        # crates/b/src/x.rs read its manifest-dir include_str! under B only.)
        if scan == real and _rust_source(real) and owner == pkg.dir:
            other = g.packages[owner]
            own = _own_context(g, other, real)
            if own[0] == ctx[0] and own[1] <= ctx[1] and own[2] <= ctx[2] and other.proc_macro == pkg.proc_macro:
                return
        if ctx not in found.setdefault((scan, real), set()):
            found[(scan, real)].add(ctx)
            work.append((scan, real, ctx, None, False))

    def reach(base: str, rel: str, ctx: Tuple[Optional[str], bool, bool], why: str, guessed: bool = False,
              edge: bool = True) -> None:
        hits = set()
        spelt = _norm(base, rel)
        if spelt is not None and entries.get(spelt, ("",))[0] == "120000":
            hits.add((spelt, _realpath(g, posixpath.dirname(spelt), texts[spelt])))  # read from the link
        elif regular(spelt):
            hits.add((spelt, spelt))
        elif spelt is not None:  # a miscased name opens the file on the landing host (fold)
            hits.update((q, q) for q in _index_spellings(g).get(fold(spelt), ()) if regular(q))
        resolved = _realpath(g, base, rel)
        # As the file system resolves it: through the links of its
        # directories, read from where it then sits, a file link there
        # from where the link sits (rustc names the file by that path).
        # (Until the review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3 a file link
        # was read from its target's directory too: `#[path = "helper.txt"]`
        # with helper.txt -> ../../../shared/real.txt had real.txt's
        # include_str! leave the repository.)
        head, name = posixpath.split(rel)
        where = _realpath(g, base, head) if head else base
        phys = posixpath.join(where, name) if where is not None and name not in ("", ".", "..") else None
        if phys is not None and entries.get(phys, ("",))[0] == "120000":
            hits.add((phys, resolved))
        else:
            hits.add((resolved, resolved))
        for scan, real in sorted(h for h in hits if h[0] is not None and regular(h[1])):
            if not guessed or _rust_source(real):
                consider(scan, real, ctx, why, edge)

    def children(scan: str, real: str, ctx: Tuple[Optional[str], bool, bool], under: Optional[Tuple[str, ...]],
                 seed: bool) -> None:
        if real not in blobs:
            blobs.update(g.index.read_blobs([real]))
        text = blobs[real].decode("utf-8", "replace")
        oid = _blob_id(g, real, blobs[real])
        if "mod" not in text and "include" not in text and not _may_declare_by_macro(g, text, oid):
            return
        lx = _lexed(g, real, text)
        fdir = posixpath.dirname(scan)
        stem = posixpath.splitext(posixpath.basename(scan))[0]
        bases = (fdir, posixpath.join(fdir, stem))
        guesses = [v for _s, _e, v in lx.strings if _pathlike(v)]

        def follow(pos: int, rels: Iterable[Tuple[str, str]], guessed: bool = False, scanned: bool = False) -> None:
            # What a build script compiles from elsewhere a Cargo target may
            # compile too: both classes (_build_role).
            site = ("both" if ctx[0] else None, ctx[1] or lx.in_test(pos), ctx[2])
            why = f"{scan}:{_line_of(text, pos)} compiles it"
            for base, rel in rels:
                spelt = _norm(base, rel)
                if under is None or (spelt is not None and any(spelt.startswith(u + "/") for u in under)):
                    reach(base, rel, site, why, guessed, edge=not (seed and scanned))
        macro = _macro_module_sites(g, lx, text, oid)
        if macro:
            # A module a macro declares (`mod $name;`, or an invocation of a
            # macro defined elsewhere that declares one) cannot be told:
            # every file one may take below either base, from a site in
            # production code when there is one.
            follow(next((at for at in macro if not lx.in_test(at)), macro[0]),
                   [(b, rel) for b in bases for rel in _module_files_in(g, b)])
        for pos, name, attrs, chains in _module_items_of(g, oid, lx, text):
            if None in attrs or chains is None:
                follow(pos, [(b, v) for v in guesses for b in bases], guessed=True)
            for attr in attrs:  # one outside inline modules names what _maybe_foreign does
                if attr is not None:
                    follow(pos, [(b, rel) for rel in _module_rels(name, [attr], chains or ()) for b in bases],
                           scanned=chains == ((),) and attr != "")
        cxx = _extern_cxx_spans(lx, text) if "C++" in text else []
        for start, end, source in _include_calls_of(g, oid, lx):
            if not source or any(o < start < c for o, c in cxx):
                continue
            kind, value = _include_arg(lx, text, end)
            at, lits = list(bases), guesses
            body = _macro_body_at(lx, start) if kind in ("file", "unknown") else None
            if body is not None:
                # In a macro's body: from each file calling the macro
                # (_macro_callers) the walk knows, a parameter one of their
                # literals; read again once it knows more (`again`). None
                # found, the escape scan leaves the package unresolved. From
                # the defining file too: it may call the macro by a name no
                # search sees (paste's `[<m _x>]!()`, a proc macro's
                # expansion; round 3 of review 4's harvest verifier), as the
                # escape scan (_scan_file) and the walk (_compiled_rust_sources)
                # do (round 4).
                again.append((scan, real, ctx, under, seed))
                via: Set[str] = set()
                callers = sorted(_macro_callers(g, _package_sources(g, pkg) + sorted(found), body[2], blobs, via=via))
                at = list(bases) + [b for c, _r in callers for b in (posixpath.dirname(c), posixpath.splitext(c)[0])]
                lits = guesses + [v for r in sorted({r for _c, r in callers} | via) if r != real for _s, _e, v in
                                  _lexed(g, r, blobs[r].decode("utf-8", "replace")).strings if _pathlike(v)]
            if kind == "file":
                follow(start, [(b, value) for b in at], scanned=True)
            elif kind == "manifest":
                follow(start, [(d, value) for d in sorted({pkg.dir, g.owner(real) or pkg.dir})], scanned=True)
            elif kind == "unknown":
                follow(start, [(b, v) for v in lits for b in dict.fromkeys(at + list(bases))], guessed=True)

    # Seeds: its targets' sources, each compiled from where the manifest names
    # it (build_graph's edge for one outside the package), opened through the
    # links of every component as _opened_files opens it (until review 4 of
    # LAND-GATE-EW1 through a link at its last component only: `build =
    # "ext/build.rs"` with ext a directory link was never scanned); one
    # outside the package in its build role there (a build script's "build",
    # not runtime code) ...
    for t in targets:
        real = t if regular(t) else _realpath(g, "", t)
        # One miscased: each spelling the index holds of what the landing host opens (fold).
        for t, real in [(t, real)] if regular(real) else [(q, r) for q in sorted(_index_spellings(g).get(fold(t), ()))
                                                         for r in [_realpath(g, "", q)] if regular(r)]:
            inside = not pkg.dir or t.startswith(pkg.dir + "/")
            ctx = (_own_context(g, pkg, t) if g.owner(t) == pkg.dir
                   else (_build_role(g, pkg, t), False, False))
            consider(t, real, ctx, f"{pkg.dir or '.'}/Cargo.toml: a target", edge=inside)
    # ... the package's scanned files that name modules or include code ...
    for f in files:
        if regular(f):
            text = blobs[f].decode("utf-8", "replace")
            if PATH_ATTR.search(text) or INCLUDE_HINT.search(text):
                work.append((f, f, _own_context(g, pkg, f), None, True))
    # ... and its links: a file link named Rust source is compiled from where
    # it sits; a directory link, and a nested package's directory, by the
    # modules that the Rust files of its directory and those above it, up to
    # the package's, take there: a file that names the directory's first
    # component below it as a module (or whose stem directory it is), or
    # declares one a macro names.
    through: Dict[str, Tuple[str, Set[str], List[str]]] = {}  # declarer -> (its text's file, dirs, firsts)
    dirs = list(nested)
    for link, target in links:
        if target is None:
            continue  # it leaves the package unresolved (_symlinks_out_of_packages)
        if regular(target):
            if _rust_source(link):
                consider(link, target, _own_context(g, pkg, link), f"{link}: a link")
        else:
            dirs.append(link)
    for link in dirs:
        top = posixpath.dirname(pkg.dir) if pkg.dir else None
        d = posixpath.dirname(link)
        while d != top:
            first = (link[len(d) + 1:] if d else link).split("/", 1)[0]
            for f in _dir_children(g, d):
                real = f if regular(f) else (_realpath(g, d, texts[f]) if f in texts else None)
                if _rust_source(f) and regular(real) and g.owner(f) == pkg.dir:
                    entry = through.setdefault(f, (real, set(), []))
                    entry[1].add(link)
                    entry[2].append(first)
            if not d:
                break
            d = posixpath.dirname(d)
    blobs.update(g.index.read_blobs(sorted({real for real, _l, _n in through.values()} - set(blobs))))
    for f, (real, under, firsts) in sorted(through.items()):
        stem = fold(posixpath.splitext(posixpath.basename(f))[0])
        text = blobs[real].decode("utf-8", "replace")
        oid = _blob_id(g, real, blobs[real])
        names = {fold(n) for n in _mod_names_of(g, oid, text)}
        if any(fold(c) == stem or fold(c) in names for c in firsts) or _may_declare_by_macro(g, text, oid):
            work.append((f, real, _own_context(g, pkg, f), tuple(sorted(under)), False))
    known = -1
    while work:  # a round at a time, each round's texts read in one batch
        batch, work[:] = list(work), []
        blobs.update(g.index.read_blobs(sorted({real for _s, real, *_rest in batch} - set(blobs))))
        for item in batch:
            children(*item)
        if not work and again and len(found) != known:
            known = len(found)  # what calls a macro may lie in a file found since its include! was read
            work.extend(dict.fromkeys(again))
            again.clear()
    return found, edges


def _scan_doctests(g: Graph, pkg: Package, path: str, text: str) -> bool:
    """A file's doctests (doctest_views) are code the test legs compile and
    run (compiler-unit-tests' stage-2 suites): scanned as the file is, every
    record test-only and a doctest's (Read.doctest: compiler-check, which
    builds no doctest, counts none); of a `no_run` or `compile_fail` one,
    rustdoc runs nothing, so only what compiling it reads. An audit row of
    the file declares its code, not its doctests. A doctest's walks are the
    package's test-only walks: the harvest's reads of them are not marked
    (a proc macro's count for compiler-check)."""
    if not _has_doc_text(text):
        return False
    views = doctest_views(g, pkg, path, text, _lexed(g, path, text))
    walked = False
    for compiled_only, by_file in ((False, views.run), (True, views.compile)):
        tag = " (doctest, compiled only)" if compiled_only else " (doctest)"
        for file, view in ((f, v) for f, vs in sorted(by_file.items()) for v in vs):
            walked = _scan_doctest_view(g, pkg, file, view, compiled_only, tag) or walked
            if posixpath.dirname(file) != posixpath.dirname(path) and (
                    INCLUDE_CALL.search(view) or PATH_ATTR.search(view)):
                # A doc file's include! resolves from the doc file in edition
                # 2024 and from the Rust file that includes it before: both.
                _scan_doctest_view(g, pkg, posixpath.join(posixpath.dirname(path), posixpath.basename(file)),
                                   view, True, f" (doctest in {file}, resolved from {path})")
    tag = " (doctest)"
    for file, line, why in views.blind:
        where = f"{file}:{line}"
        pkg.unresolved.append(Read("compile", f"{where}: {why}{tag}", True, where + tag, doctest=True))
    return walked


def _scan_doctest_view(g: Graph, pkg: Package, path: str, view: str, compiled_only: bool, tag: str) -> bool:
    """Scan one doctest view as `path` (a doctest is its own crate: no build
    script, no proc macro) into `pkg`, test-only, each site tagged; of a
    compiled-only one, only the compile-time records (no walk: nothing
    runs)."""
    if not view.strip() or not DOCTEST_SCAN.search(view):
        return False
    probe = Package(dir=pkg.dir, name=pkg.name)
    cache = g.lex_cache
    saved = cache.pop(path, None)
    try:
        walked = _scan_file(g, probe, path, view)
    finally:
        cache.pop(path, None)
        if saved is not None:
            cache[path] = saved

    def kept(r: Read) -> bool:
        return not compiled_only or r.cls == "compile"
    pkg.reads.extend(replace(r, test_only=True, doctest=True, site=r.site + tag) for r in probe.reads if kept(r))
    pkg.unresolved.extend(replace(r, test_only=True, doctest=True, site=r.site + tag, target=r.target + tag)
                          for r in probe.unresolved if kept(r))
    pkg.history.extend(replace(r, test_only=True, doctest=True, site=r.site + tag)
                       for r in probe.history if kept(r))
    pkg.foreign.extend(probe.foreign)
    pkg.deps.update(probe.deps)
    if compiled_only:
        return False
    pkg.walks.extend(replace(w, test_only=True) for w in probe.walks)
    return walked


# The replay (scripts/land_gate.py replay) judges historical trees with TODAY's
# audits: each row still holds only for the blob it names.
AUDITS_OVERRIDE: Optional[bytes] = None


def audit_holds(g: Graph, path: str, audit: Optional[dict]) -> bool:
    """A row holds only while its file is the blob it names and so is every
    premise: a file the row's reasoning rests on beside its own, such as the
    only callers of the function whose reads it declares (review of EW-1).
    A row marked `lapsed` never holds: a landing that moved one of its blobs
    without a fresh review recorded that, and the site is unresolved again
    (LEDGER-PIN-CURRENCY-AT-LANDING-1)."""
    if audit is None or "lapsed" in audit:
        return False
    entries = g.index.entries
    return (path in entries and audit["blob"] == entries[path][1]
            and all(pin["file"] in entries and entries[pin["file"]][1] == pin["blob"]
                    for pin in audit.get("premises", [])))


def _audit_doc(g: Graph) -> dict:
    if tomllib is None:
        return {}
    if AUDITS_OVERRIDE is not None:
        raw = AUDITS_OVERRIDE
    elif AUDITS_FILE in g.index.entries:
        raw = g.index.read_blobs([AUDITS_FILE])[AUDITS_FILE]
    else:
        return {}
    try:
        return tomllib.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError):
        return {}


def _premises_ok(premises) -> bool:
    return isinstance(premises, list) and all(
        isinstance(pin, dict) and set(pin) == {"file", "blob"}
        and isinstance(pin["file"], str) and pin["file"]
        and isinstance(pin["blob"], str)
        and re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", pin["blob"]) is not None
        for pin in premises)


AUDIT_KEYS = frozenset({"file", "blob", "class", "reads", "lists", "history", "test_only", "premises", "reason",
                        "lapsed"})
NOT_PATH_KEYS = frozenset({"file", "blob", "literals", "via", "premises", "reason", "lapsed"})
NOT_PATH_LITERAL = re.compile(r'[^"\\\n]{1,240}')
IDENTIFIER = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')
# `lapsed = "YYYY-MM-DD <commit>: <why>"`: the row's own record that a landing
# moved a blob it pins without renewing it. It keeps the row (and its last
# reviewed pins) in the ledger while granting nothing (audit_holds); the push
# row that requires every moved pin to be renewed or lapsed in the same push
# (scripts/check_ledger_pins.py) and the ledger's currency tests read it.
LAPSED = re.compile(r"(?s)[0-9]{4}-[0-9]{2}-[0-9]{2} \S.*")


def lapse_ok(row: dict) -> bool:
    """A row's `lapsed` marker is absent, or a dated reason (LAPSED)."""
    return "lapsed" not in row or (isinstance(row["lapsed"], str) and LAPSED.fullmatch(row["lapsed"]) is not None)


def audit_row_ok(row: object) -> bool:
    """Whether one [[audit]] row is well formed: load_audits keeps it."""
    if not isinstance(row, dict):
        return False
    path, blob = row.get("file"), row.get("blob")
    reads, history = row.get("reads", []), row.get("history", False)
    lists = row.get("lists", [])
    return not (not set(row) <= AUDIT_KEYS  # a misspelt key (`premise`) would silently drop what it pins
                or not isinstance(path, str) or not path
                or not isinstance(blob, str) or re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", blob) is None
                or row.get("class", "runtime") not in ("compile", "runtime")
                or not isinstance(reads, list)
                or not all(isinstance(target, str) and target for target in reads)
                # A listing names repository paths; a pseudo-input (@stage1) has no listing.
                or not isinstance(lists, list)
                or not all(isinstance(target, str) and target and not target.startswith("@") for target in lists)
                or type(row.get("test_only", False)) is not bool
                or not _premises_ok(row.get("premises", []))
                or not lapse_ok(row)
                or not (history is True or history is False or history == "value-only"))


def load_audits(g: Graph) -> Dict[str, dict]:
    doc = _audit_doc(g)
    out: Dict[str, dict] = {}
    rows = doc.get("audit", [])
    if not isinstance(rows, list):
        return {}
    for row in rows:
        if not audit_row_ok(row):
            continue  # A malformed declaration grants no scan or harvest exemption.
        out[row["file"]] = row
    return out


def load_not_paths(g: Graph) -> Dict[str, dict]:
    """[[not_path]] rows: literal values one file spells that a reviewer traced
    and found never name a checkout path. The file is scanned as any other. The
    harvest skips a lone literal (no `.join` chain) of a listed value in a
    statement naming no path, file-system or process API (_in_path_call), while
    the row holds (not_path_holds): the file and every premise are at their
    pinned blobs, and `via` (the items through which the value leaves the
    file) is empty."""
    doc = _audit_doc(g)
    out: Dict[str, dict] = {}
    rows = doc.get("not_path", [])
    if not isinstance(rows, list):
        return {}
    for row in rows:
        if not not_path_row_ok(row) or row["file"] in out:
            continue  # A malformed or duplicate row exempts nothing.
        out[row["file"]] = row
    return out


def not_path_row_ok(row: object) -> bool:
    """Whether one [[not_path]] row is well formed (load_not_paths keeps the
    first well-formed row of each file)."""
    if not isinstance(row, dict):
        return False
    path, blob, literals = row.get("file"), row.get("blob"), row.get("literals")
    via = row.get("via")
    return not (not set(row) <= NOT_PATH_KEYS
                or not isinstance(path, str) or not path
                or not isinstance(blob, str) or re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", blob) is None
                or not isinstance(literals, list) or not literals
                or not all(isinstance(v, str) and NOT_PATH_LITERAL.fullmatch(v) for v in literals)
                or not isinstance(via, list) or not all(isinstance(v, str) and IDENTIFIER.fullmatch(v) for v in via)
                or not _premises_ok(row.get("premises", []))
                or not lapse_ok(row)
                or not isinstance(row.get("reason"), str) or not row["reason"].strip())


def not_path_holds(g: Graph, path: str, row: Optional[dict]) -> bool:
    """A [[not_path]] row holds at its blobs, and only for a value that stays
    in its file (`via = []`): a value that leaves it through a crate-visible
    item can gain a reader the row cannot see (another package, a `#[path]`
    module, a linked file), so a non-empty `via` exempts nothing."""
    return row is not None and audit_holds(g, path, row) and not row["via"]


def _record(g: Graph, pkg: Package, cls: str, target: Optional[str], why: str, test_only: bool) -> None:
    """Record one read of `target` (repo-relative; None = could not be resolved)."""
    if target is None:
        pkg.unresolved.append(Read(cls, why, test_only, why))
        return
    prefix, is_glob = _cut_glob(target)
    if prefix == "" and not is_glob:
        pkg.unresolved.append(Read(cls, f"{why}: reads the repository root", test_only, why))
        return
    if not is_glob and g.owner(prefix) == pkg.dir and prefix != pkg.dir:
        return  # its own file: already an input of every leg whose closure holds the package
    pkg.reads.append(Read(cls, prefix if prefix else EVERYTHING, test_only, why))


def _record_either(g: Graph, pkg: Package, cls: str, candidates: Sequence[Optional[str]], why: str,
                   test_only: bool) -> None:
    inside = [c for c in candidates if c is not None]
    if not inside:
        _record(g, pkg, cls, None, f"{why}: resolves outside the repository", test_only)
        return
    for c in inside:
        _record(g, pkg, cls, c, why, test_only)


def _maybe_foreign(g: Graph, pkg: Package, target: Optional[str], why: str, test_only: bool,
                   guessed: bool = False) -> None:
    """A `#[path]` module or an `include!`d file owned by another package
    (library/core's `#[path = "../../stdarch/crates/core_arch/src/mod.rs"]`),
    as spelt and as the file system resolves it through links: see
    _foreign_source. rustc compiles what a path attribute or include! names
    as Rust whatever its name (`#[path = "helper.txt"]`, `include!("gen.txt")`):
    a tracked regular file of any name counts, and a name that is Rust
    source (_rust_source: `.rs` in any case) counts even untracked. A
    `guessed` target (a literal of a file whose path attribute or include!
    is not one) counts only by that name. (Until
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only a lower-case `.rs` name did, as
    spelt: helper.RS and helper.txt in another package were no edge.) A
    name is taken in every spelling the landing host opens it by (fold):
    until the review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3,
    `#[path = "../../Other/src/x.rs"]` named no package (the owner of a
    path is case-sensitive), and the walk, which reaches other/src/x.rs and
    leaves a scanned site's edge to this scan, added none."""
    if not target:
        return
    named = {target, _realpath(g, "", target) or target}
    spellings = _index_spellings(g)
    for t in sorted(named | {q for n in named for q in spellings.get(fold(n), ())}):
        regular = g.index.entries.get(t, ("",))[0] in REGULAR
        if (_rust_source(t) or (regular and not guessed)) and g.owner(t) != pkg.dir:
            _foreign_source(g, pkg, t, why, test_only)


def _foreign_edges(g: Graph, pkg: Package, path: str, text: str) -> None:
    """The Rust source of other packages that an audited file compiles (`#[path]`
    modules, `include!`d files). An audit row resolves what the file READS; what
    it compiles is code, whose own escapes reach this package only through
    this edge (bootstrap's tests compile src/tools/targo/build_commit_info.rs by
    `#[path]`), so the edge stands for an audited file too. Taken as reaching
    every leg (never test-only): it can only select more."""
    lx = _lexed(g, path, text)
    fdir = posixpath.dirname(path)
    stem = posixpath.splitext(posixpath.basename(path))[0]
    for m in _include_calls(lx):
        if not _includes_source(m):
            continue
        kind, value = _include_arg(lx, text, m.end())
        where = f"{path}:{_line_of(text, m.start())} include (audited)"
        if kind == "file":
            # From the file, and in a macro's body from each file calling the macro (_macro_callers).
            body = _macro_body_at(lx, m.start())
            callers = _macro_callers(g, _package_sources(g, pkg), body[2], g.blob_cache) if body else set()
            if body is not None and not callers:
                # Whose source it compiles cannot be told (review 4, round 2: the
                # defining file's edge alone stood for it).
                _record(g, pkg, "compile", None, f"{where}: an include! in the body of macro "
                        f"{body[2] or '(of no readable name)'}, whose calls the scan cannot all find", False)
            for d in [fdir] + sorted({posixpath.dirname(scan) for scan, _real in callers}):
                _maybe_foreign(g, pkg, _norm(d, value), where, False)
        elif kind == "manifest":
            _maybe_foreign(g, pkg, _norm(pkg.dir, value), where, False)
    for pos in _lost_inner_paths(lx, text):
        _record(g, pkg, "compile", None, f"{path}:{_line_of(text, pos)}: an inner path attribute that is no "
                "inline module's, whose modules' directory the scan cannot tell", False)
    for pos, value, _end in _path_attrs(lx, text):
        where = f"{path}:{_line_of(text, pos)} #[path] (audited)"
        cands = _path_attr_targets(lx, fdir, stem, value)
        if value is None and not cands:
            # Which source it compiles cannot be told: neither can whose.
            _record(g, pkg, "compile", None, f"{where}: a path attribute that is not a string literal", False)
        for c in cands:
            _maybe_foreign(g, pkg, c, where, False, guessed=value is None)
    # (The default file of a module whose path attribute is a cfg_attr, and
    # what a link or a module of another name compiles, are the walk's:
    # _compiled_elsewhere starts from every scanned file, audited ones too.)


def _path_attr_targets(lx, fdir: str, stem: str, value: Optional[str]) -> List[str]:
    """The files a path attribute may name, beside the file or below its stem:
    its value's; for one that is not a literal (a macro's `#[path = $p]`),
    every path-like literal of the file's, as an include! of a macro
    parameter takes them (an invocation in another file is not seen: none
    resolving leaves the package unresolved)."""
    values = [value] if value is not None else [v for _s, _e, v in lx.strings if _pathlike(v)]
    return [c for v in values for c in (_norm(fdir, v), _norm(posixpath.join(fdir, stem), v)) if c is not None]


def _line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


SQUARE = re.compile(r'[\[\]]')
CURLY = re.compile(r'[{}]')
CONCAT_OPEN = re.compile(r'concat\s*!\s*[(\[{]')
PATH_HEAD = re.compile(r'(?:r#)?path\b')
CFG_ATTR_HEAD = re.compile(r'(?:r#)?cfg_attr\s*\(')
ENV_OPEN = re.compile(r'env\s*!\s*[(\[{]')


def _string_starts(lx) -> Dict[int, Tuple[int, str]]:
    starts = getattr(lx, "_string_starts", None)
    if starts is None:
        starts = lx._string_starts = {s: (e, v) for s, e, v in lx.strings}
    return starts


def _next_token(lx, i: int) -> int:
    """The index of the next token from lx.code[i]: comments are blank there,
    and so is a string literal, which starts a token."""
    starts, code = _string_starts(lx), lx.code
    while i < len(code) and i not in starts and code[i].isspace():
        i += 1
    return i


def _literal_at(lx, text: str, i: int) -> Tuple[Optional[str], int]:
    """The value of the string literal that is the next token from text[i]
    (comments skipped; escapes decoded, raw strings as written) and the index
    after it; (None, index of that token) when the token is anything else."""
    i = _next_token(lx, i)
    hit = _string_starts(lx).get(i)
    if hit is None or text[i] == "'":
        return None, i
    end, body = hit
    raw = text[i] in "rR" or text[i:i + 2] in ("br", "cr")
    return (body if raw else _unescape(body)), end


def _path_attrs(lx, text: str) -> List[Tuple[int, Optional[str], int]]:
    """Each path attribute of a lexed file: `#[path = ..]`, or a `cfg_attr(..)`
    holding `path = ..` at any depth, in any spacing, as (the attribute's
    start, its value, the index after its `]`). The value is None where it
    is not a string literal (`path = $p` in a macro): no scan can tell which
    file that names."""
    code = lx.code
    if "path" not in code or not PATH_ATTR.search(code):
        return []
    out: List[Tuple[int, Optional[str], int]] = []
    for m in ATTR_START.finditer(code):
        depth, close = 0, len(code)
        for b in SQUARE.finditer(code, m.end() - 1):
            depth += 1 if b.group(0) == "[" else -1
            if depth == 0:
                close = b.start()
                break
        head = _next_token(lx, m.end())
        if PATH_HEAD.match(code, head):
            keys = [k for k in (PATH_KEY.match(code, head),) if k is not None]
        elif CFG_ATTR_HEAD.match(code, head):
            keys = list(PATH_KEY.finditer(code, head, close))
        else:
            continue
        for k in keys:
            value, _end = _literal_at(lx, text, k.end())
            out.append((m.start(), value, close + 1))
    return out


MOD_ITEM = re.compile(r'\bmod\s+(?:r#)?(' + IDENT + r')\s*([;{])')  # any identifier (IDENT)
# Each `mod` keyword in a lexed file's code (not `r#mod` or `$mod`): every
# one must be a MOD_ITEM match for the build reach to be complete
# (_build_reach's rule (5)).
MOD_TOKEN = re.compile(r'(?<![\w$#])mod(?!\w)')
MACRO_MOD = re.compile(r'\bmod\s*\$')  # `mod$name;` lexes as `mod $name;`
# The same before lexing (a comment, or Rust whitespace outside ASCII, may stand between).
MACRO_MOD_HINT = re.compile(r'\bmod' + RUST_WS + r'*(?:\$|/[*/])')
# A macro's definition, by its name: `macro_rules! m`, `macro m`.
MACRO_DEF = re.compile(r'\bmacro_rules\s*!\s*(?:r#)?(' + IDENT + r')|\bmacro\s+(?:r#)?(' + IDENT + ')')
# One whose name no identifier spells: `macro_rules! $name` and `macro
# $name(..)` in a macro defining one, `macro_rules! [<a _b>]` in paste!.
# `macro$name(..)` too, which rustc lexes as `macro $name` (review 4, round 3).
MACRO_DEF_UNNAMED = re.compile(r'\bmacro_rules\s*!(?!\s*(?:r#)?' + IDENT + r')|\bmacro\s*(?=\$)')


def _index_module_macros(g: Graph, path: str, text: str) -> None:
    """The macros `path` defines that declare a module (`mod $name` in the
    body of the definition before it), by name, into _module_macros. A
    module a macro declares sits where the macro is INVOKED, not where it is
    defined, so a file invoking one may declare any module of its own
    directory (_macro_module_sites). (Review of
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3: only a file spelling `mod $` itself
    counted, and the src/sub/x.rs that `m!(x);` in src/sub/mod.rs compiles
    was test-only when `m` sat in src/macros.rs and a #[cfg(test)] path
    attribute named it.) The scan reads every file spelling `mod $`
    (SCAN_RE); _index_path_modules hands each a package compiles or owns."""
    if not MACRO_MOD_HINT.search(text):
        return
    lx = _lexed(g, path, text)
    heads = [(m.start(), m.group(1) or m.group(2)) for m in MACRO_DEF.finditer(lx.code)]
    names = g.__dict__.setdefault("_module_macros", set())
    for m in MACRO_MOD.finditer(lx.code):
        before = [name for at, name in heads if at < m.start()]
        if before:
            names.add(before[-1])


def _module_macro_call(g: Graph) -> Optional[Tuple["re.Pattern", "re.Pattern"]]:
    """(in a text, in a lexed code) an invocation of a macro that declares a
    module (_module_macros): its name, then its `!` (not `!=`), whitespace
    or, before lexing, a comment between."""
    names = sorted(g.__dict__.get("_module_macros", ()))
    if not names:
        return None
    cache = g.__dict__.setdefault("_module_macro_rx", {})
    key = tuple(names)
    if key not in cache:
        alt = "|".join(re.escape(n) for n in names)
        cache[key] = (re.compile(r'\b(?:' + alt + r')' + RUST_WS + r'*(?:!|/[*/])'),
                      re.compile(r'\b(?:' + alt + r')\s*!(?!=)'))
    return cache[key]


def _macro_module_sites(g: Graph, lx, text: str, oid: Optional[str] = None) -> Sequence[int]:
    """Where a lexed file may declare a module whose name it does not spell:
    a `mod $name` (a macro defined and invoked here) and each invocation of
    a macro that declares one (_module_macros), in source order. `oid`: the
    blob `text` is, `lx` lexing exactly it (a blob fact then)."""
    def compute() -> Tuple[int, ...]:
        out = [m.start() for m in MACRO_MOD.finditer(lx.code)]
        calls = _module_macro_call(g)
        if calls is not None and calls[0].search(text):
            out += [m.start() for m in calls[1].finditer(lx.code)]
        return tuple(sorted(out))
    return _blob_fact(g, "macro_module_sites", oid, _module_macro_key(g), compute)


def _may_declare_by_macro(g: Graph, text: str, oid: Optional[str] = None) -> bool:
    """Whether a text may hold a site _macro_module_sites finds, before it
    is lexed. `oid`: the blob `text` is (a blob fact then)."""
    def compute() -> bool:
        calls = _module_macro_call(g)
        return bool(MACRO_MOD_HINT.search(text) or (calls is not None and calls[0].search(text)))
    return _blob_fact(g, "may_declare_by_macro", oid, _module_macro_key(g), compute)


BRACKET = re.compile(r'[()\[\]{}]')
# A file that may define a macro holding the `mod` keyword (_macro_module_defs,
# MOD_KEYWORD): a `macro_rules`/`macro` word and a
# `mod` word, each on some line (git grep -w -E; -w, a tenth of the CPU of
# spelling the boundaries out).
MACRO_DEF_GREP = ("macro(_rules)?", "mod")


def _group_end(code: str, i: int) -> int:
    """The index of the bracket closing the one at code[i] (any kind; the
    end of the code when none does)."""
    depth = 0
    for b in BRACKET.finditer(code, i):
        depth += 1 if b.group(0) in "([{" else -1
        if depth == 0:
            return b.start()
    return len(code)


# A macro a macro's body invokes, by its last segment (`inner!`,
# `$crate::inner!`, `d::inner!`), and one its caller names (`$m!`).
BODY_CALL = re.compile(r'(?<![\w$])(?:r#)?(' + IDENT + r')\s*!(?!=)')
PARAM_CALL = re.compile(r'(?<![\w$])\$(?:r#)?' + IDENT + r'\s*!(?!=)')
# A name a `use` gives another (`use d::m as dd;`, `pub use defs::{m as other}`).
USE_RENAME = re.compile(r'(?<![\w$])(?:r#)?(' + IDENT + r')\s+as\s+(?:r#)?(' + IDENT + ')')


def _macro_module_defs(lx, calls: Optional[Dict[str, Set[str]]] = None) -> List[str]:
    """The macros a lexed file defines outside test code whose definition
    holds the `mod` keyword (MOD_KEYWORD) or invokes a macro its caller
    names (`$m!`, which may be one that declares a module): `macro_rules! m
    { .. }`, `macro m(..) { .. }` or `macro m { .. }`, by name. `calls`:
    filled, for each other macro the file defines there, with the macros
    its body invokes (BODY_CALL), and for each name a `use` there gives
    another, with that one: either is a module macro when one of those is
    (_visible_module_macros)."""
    code = lx.code
    out = []
    for m in MACRO_DEF.finditer(code):
        if lx.in_test(m.start()):
            continue
        opening = BRACKET.search(code, m.end())
        if opening is None:
            continue
        end = _group_end(code, opening.start())
        after = BRACKET.match(code, _next_token(lx, end + 1)) if end < len(code) else None
        if m.group(2) and code[opening.start()] == "(" and after is not None and after.group(0) == "{":
            end = _group_end(code, after.start())  # macro m(..) { body }
        # The `mod` keyword in any form (MOD_KEYWORD), not only before an ASCII
        # name or a fragment: passed on as a tt (`$crate::decl!(mod, x)`,
        # `decl2!(mod {x})`) or before a name outside ASCII (`mod ñ;`), it may
        # make a module. (Review 4 of LAND-GATE-EW1-FOLLOWUP-REVIEW-3, round 3:
        # those bodies were no module macro, and the mac/x.rs they compile
        # stayed test-only.)
        if MOD_KEYWORD.search(code, m.end(), end) or PARAM_CALL.search(code, m.end(), end):
            out.append(m.group(1) or m.group(2))
        elif calls is not None:
            calls.setdefault(m.group(1) or m.group(2), set()).update(
                c.group(1) for c in BODY_CALL.finditer(code, m.end(), end))
    for u in USE_DECL.finditer(code) if calls is not None else ():
        if not lx.in_test(u.start()):
            for r in USE_RENAME.finditer(code, u.start(), u.end()):
                calls.setdefault(r.group(2), set()).add(r.group(1))
    return out


def _macro_module_names(g: Graph) -> Optional[Tuple[Dict[Optional[str], List[str]], Dict[str, List[str]]]]:
    """(every tracked Rust file that may define a macro holding the `mod`
    keyword (MACRO_DEF_GREP, and each a name git's ASCII case folding does not take
    for `.rs`: helper.rſ) or invoking one its caller names (a `macro` and a
    `$`, git grep -F), by its owner; the names of those macros
    (_macro_module_defs) each defines, by file). None when git grep
    failed."""
    if "_macro_module_names" in g.__dict__:
        return g.__dict__["_macro_module_names"]
    out = None
    found = _listed_by_grep(g, ["-l", "-z", "-w", "--all-match", "-E", "-e", MACRO_DEF_GREP[0], "-e",
                                MACRO_DEF_GREP[1]], [":(icase)*.rs"])
    params = _listed_by_grep(g, ["-l", "-z", "--all-match", "-F", "-e", "macro", "-e", "$"], [":(icase)*.rs"])
    if found is not None and params is not None:
        odd = [p for p in _rust_sources(g) if not p.lower().endswith(".rs")]
        paths = sorted(p for p in {*_grep_listed(g, found), *odd} if g.index.entries.get(p, ("",))[0] in REGULAR)
        more = sorted(p for p in set(_grep_listed(g, params)) - set(paths)
                      if g.index.entries.get(p, ("",))[0] in REGULAR)
        cache = g.blob_cache
        cache.update(g.index.read_blobs(sorted(p for p in paths if p not in cache)))
        by_owner: Dict[Optional[str], List[str]] = {}
        by_file: Dict[str, List[str]] = {}
        for p in paths:
            by_owner.setdefault(g.owner(p), []).append(p)
            by_file[p] = list(_blob_macro_defs(g, p, cache[p])[0])
        texts = {p: g.blob_cache.get(p) for p in more}
        texts.update(g.index.read_blobs(sorted(p for p, t in texts.items() if t is None)))
        for p in more:
            text = texts[p].decode("utf-8", "replace")
            if PARAM_CALL.search(text):  # before lexing: a superset
                defined = list(_blob_macro_defs(g, p, texts[p], text)[0])
                if defined:
                    by_owner.setdefault(g.owner(p), []).append(p)
                    by_file[p] = defined
        out = (by_owner, by_file)
    g.__dict__["_macro_module_names"] = out
    return out


def _blob_macro_defs(g: Graph, path: str, blob: bytes, text: Optional[str] = None):
    """_macro_defs_of `path`'s blob, `blob` (`text`: its text, decoded),
    lexed only when no graph holds the fact."""
    oid = _blob_id(g, path, blob)
    if _blob_fact_held(g, "macro_defs", oid, None):
        return _blob_fact(g, "macro_defs", oid, None, None)
    text = blob.decode("utf-8", "replace") if text is None else text
    return _macro_defs_of(g, oid, _lexed(g, path, text))


def _macro_spelling_hint(names: Sequence[str]) -> "re.Pattern":
    """In a text before lexing, a call of one of `names` or a renaming `use`
    of one: the name, then its `!` or `as`, with Rust whitespace (RUST_WS)
    or a comment's start between (`m/**/!(x)`, `m // c` then `!(x)`,
    `m/**/as n`). A superset of each such token pair's lexed reading."""
    alt = "|".join(re.escape(n) for n in names)
    return re.compile(r'\b(?:' + alt + r')(?:' + RUST_WS + r'*(?:!|/[*/])|' + RUST_WS + r'+as\b)')


def _wrapped(names: Set[str], calls: Iterable[Dict[str, Set[str]]]) -> Set[str]:
    """`names` and, to a fixed point, each macro of `calls` whose body
    invokes one of them, and each name a `use` gives one of them
    (_macro_module_defs's `calls`)."""
    out = set(names)
    pending = [(n, c) for cs in calls for n, c in cs.items() if n not in out]
    while True:
        grown = {n for n, c in pending if n not in out and not c.isdisjoint(out)}
        if not grown:
            return out
        out |= grown


def _macro_spelling_exclusions(g: Graph, state: dict, *, byte_limit: int = 16 * 1024) -> List[str]:
    """Skip a bounded subset already parsed completely for its current owner.

    Calls hold every body/rename, independently of the frontier; spelt already
    holds this file for that owner. A word-only match is not yet parsed and
    must remain eligible. Prefer large cached files; a safe subset suffices.
    Literal pathspecs prevent a filename from excluding other source files.
    """
    eligible = [path for path in state["calls"]
                if path in state["spelt"].get(g.owner(path), ())]
    result: List[str] = []
    used = 0
    for path in sorted(eligible, key=lambda p: (-len(g.blob_cache.get(p, b"")), p)):
        literal = ":(exclude,literal)" + path
        size = len(os.fsencode(literal)) + 1
        if size <= byte_limit - used:
            result.append(literal)
            used += size
    return result


def _macro_word_patterns(names: Sequence[str], *, byte_limit: int = 16 * 1024) -> List[str]:
    """One literal identifier union, or the original fixed-pattern query.

    Git applies the same -w predicate to the union. ASCII identifiers contain
    no ERE metacharacters, so its matches are exactly the union of the fixed
    words. Other spellings and oversized unions keep the original query.
    """
    if names and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) for name in names):
        union = "|".join(names)
        if len(union) + 1 <= byte_limit:
            return ["-E", "-e", union]
    return ["-F", *(a for name in names for a in ("-e", name))]


def _module_macro_spelling(g: Graph, by_file: Dict[str, List[str]]
                           ) -> Optional[Tuple[Dict[Optional[str], Set[str]], Dict[str, Dict[str, Set[str]]]]]:
    """(every file spelling as a word a macro that may declare a module, by
    owner; what the macros of each such file that may call or rename one
    invoke, and what its `use`s rename: _macro_module_defs's `calls`, by
    file). Such a macro, to a fixed point over the tree: one holding the
    `mod` keyword (`by_file`) or declaring one (_module_macros), and one whose
    body invokes such a macro, or a name a `use` gives one (_wrapped); a
    file does either only by spelling its name, so each round greps the
    names the last one added (-w with a literal identifier union where safe;
    no call syntax or whitespace pattern), and reads each a name git's ASCII case folding
    does not take for `.rs` (helper.rſ). Which a package sees:
    _visible_module_macros.
    None when git grep failed. (Review 4 of LAND-GATE-EW1-FOLLOWUP-REVIEW-3:
    `macro_rules! outer { () => { $crate::inner!(); } }` beside inner's
    `mod x;` was no module macro, so the mac/x.rs `d::outer!();` compiles
    stayed test-only.)"""
    st = _spelling_state(g)
    while not st["failed"]:
        seeds = frozenset({n for ns in by_file.values() for n in ns} | set(g.__dict__.get("_module_macros", ())))
        # _wrapped of exactly these seeds over exactly these calls (each
        # write to them moves the generation, _record_calls), once.
        if st["wrapped"] is None or st["wrapped"][:2] != (st["generation"], seeds):
            st["wrapped"] = (st["generation"], seeds, frozenset(_wrapped(seeds, st["calls"].values())))
        frontier = sorted(st["wrapped"][2] - st["grepped"])
        if not frontier:
            return st["spelt"], st["calls"]
        found = _listed_by_grep(g, ["-l", "-z", "-w", *_macro_word_patterns(frontier)],
                                [":(icase)*.rs", *_macro_spelling_exclusions(g, st)])
        if found is None:
            st["failed"] = True
            break
        st["grepped"].update(frontier)
        odd = [p for p in _rust_sources(g) if not p.lower().endswith(".rs")]
        listed = [p for p in dict.fromkeys([*_grep_listed(g, found), *odd])
                  if g.index.entries.get(p, ("",))[0] in REGULAR]
        hint = _macro_spelling_hint(frontier)
        hinted = tuple(frontier)  # the hint's parameter: it is built from these alone
        unread = [p for p in listed if p not in st["calls"]]
        texts = {p: g.blob_cache[p] for p in unread if p in g.blob_cache}
        texts.update(g.index.read_blobs(sorted(p for p in unread if p not in texts)))
        for p in listed:
            st["spelt"].setdefault(g.owner(p), set()).add(p)
            if p in texts:
                blob = texts[p]
                # A call or a renaming `use` of one, before lexing.
                if _blob_fact(g, "spelling_hint", _blob_id(g, p, blob), hinted,
                              lambda: hint.search(blob.decode("utf-8", "replace")) is not None):
                    _record_calls(st, p, _macro_calls(_blob_macro_defs(g, p, blob)))
    return None


def _spelling_state(g: Graph) -> dict:
    """_module_macro_spelling's state: the names grepped, the files spelling
    them by owner, each read file's `calls`, and _wrapped's last answer
    over them with the generation of `calls` it read."""
    return g.__dict__.setdefault("_macro_spelling", {"grepped": set(), "spelt": {}, "calls": {}, "failed": False,
                                                     "generation": 0, "wrapped": None})


def _record_calls(st: dict, path: str, calls: Dict[str, FrozenSet[str]]) -> None:
    """Every write to the spelling state's `calls`: a new generation."""
    st["calls"][path] = calls
    st["generation"] += 1


# The sysroot's crates, which every crate may use without declaring them.
SYSROOT = ("library/std", "library/proc_macro", "library/test")
# A `use` declaration, up to its `;` (in lexed code: no comment or string).
USE_DECL = re.compile(r'\buse\b[^;]*')


def _visible_module_macros(g: Graph, pkg: Package, by_file: Dict[str, List[str]]) -> Optional[List[str]]:
    """The macros that may declare a module that `pkg` may invoke: those
    holding the `mod` keyword (_macro_module_defs), and to a fixed point those
    invoking or renaming one (_wrapped), each defined in a file that a
    package of its dependency closure, or of the sysroot's (SYSROOT), owns
    or compiles from elsewhere. A `macro_rules!` or `macro` macro is seen
    only by its own crate and, exported or re-exported, by the crates
    depending on it, and invokes only what the crate defining it sees or
    its caller does, so what a wrapper invokes is one of these: the
    tree-wide names of _module_macros, which _may_declare_modules_by_macro
    adds, make no wrapper (`use crate::linker::tests as fixture;` beside
    another package's `macro_rules! tests { .. mod $n; .. }` made every
    `fixture!` a module macro). A file a crate compiles resolves its paths
    in that crate, so the edges _foreign_source adds later add none. None
    when git grep failed."""
    compiled = g.__dict__.get("_compiled_from_elsewhere")
    indexed = set(g.__dict__.get("_module_macros", ()))
    st = g.__dict__.get("_macro_spelling", {})
    memo = g.__dict__.setdefault("_visible_macro_memo", {})
    key = (pkg.dir, compiled is not None, tuple(sorted(indexed)), len(st.get("grepped", ())), len(st.get("calls", ())))
    if key in memo:
        return memo[key]
    by_owner = g.__dict__.get("_macro_names_by_owner")
    if by_owner is None or by_owner[0] != len(by_file):
        by_owner = (len(by_file), {})
        for p, defined in by_file.items():
            by_owner[1].setdefault(g.owner(p), set()).update(defined)
        g.__dict__["_macro_names_by_owner"] = by_owner
    seen = g.closure([pkg.dir, *SYSROOT])
    names = {n for d in seen for n in by_owner[1].get(d, ())}
    by_compiled = sorted({p for d in seen for p in (compiled or {}).get(d, ())})
    for p in by_compiled:
        if p not in by_file:  # a file the definers' search does not read (helper.txt)
            if g.index.entries.get(p, ("",))[0] not in REGULAR:
                continue
            if p not in g.blob_cache:
                g.blob_cache.update(g.index.read_blobs([p]))
            defs = _blob_macro_defs(g, p, g.blob_cache[p])
            by_file[p] = list(defs[0])
            spelling_state = _spelling_state(g)
            if p not in spelling_state["calls"]:
                _record_calls(spelling_state, p, _macro_calls(defs))
        names.update(by_file[p])
    by_compiled = set(by_compiled)
    spelling = _module_macro_spelling(g, by_file)
    if spelling is None:
        return None
    owners = g.__dict__.setdefault("_macro_spelling_owner", {})
    for p in spelling[1].keys() - owners.keys():
        owners[p] = g.owner(p)
    out = sorted(_wrapped(names, (c for p, c in spelling[1].items() if owners[p] in seen or p in by_compiled)))
    st = g.__dict__["_macro_spelling"]
    memo[(pkg.dir, compiled is not None, tuple(sorted(indexed)), len(st["grepped"]), len(st["calls"]))] = out
    return out


# A macro invocation's opening: its name, `!` and a delimiter (not
# `macro_rules! m {`); and the `mod` keyword (not `$mod`, `r#mod`, `module`).
INVOCATION = re.compile(r'(?<![\w$])(?:r#)?' + IDENT + r'\s*!\s*[(\[{]')
MOD_KEYWORD = re.compile(r'(?<![\w$#])mod(?!\w)')


def _passes_mod(lx) -> bool:
    """Whether a lexed file passes the `mod` keyword to a macro outside test
    code (`decl!(mod x)`, `cfg_if! { .. mod imp; .. }`): what the macro
    makes of it (`($k:tt $n:ident) => { $k $n; }`) may be a module no
    declaration the gate reads names."""
    # Lexed objects survive exact-byte tokenization reuse. Retain one pure
    # lexical answer with them, keyed by values so mutations of code or span
    # boundaries invalidate it. Graph/module roles are evaluated separately.
    key = (lx.code, tuple(tuple(span) for span in lx.test_spans))
    memo = lx.__dict__.get("_passes_mod_memo")
    if memo is not None and memo[0] == key:
        return memo[1]
    result = _passes_mod_inputs(*key)
    lx._passes_mod_memo = (key, result)
    return result


def _passes_mod_inputs(code: str, test_spans: Tuple[Tuple[int, int], ...]) -> bool:
    """The module-keyword predicate on an immutable lexical snapshot."""
    at = [k.start() for k in MOD_KEYWORD.finditer(code)
          if not any(start <= k.start() < end for start, end in test_spans)]
    if not at:
        return False
    for m in INVOCATION.finditer(code):
        close = _group_end(code, m.end() - 1)
        i = bisect.bisect_right(at, m.end() - 1)
        if i < len(at) and at[i] < close:
            return True
    return False


def _mod_passing_files(g: Graph) -> Optional[Dict[Optional[str], Set[str]]]:
    """Every tracked Rust file that may pass the `mod` keyword to a macro (a
    `!` and `mod`, git grep -F), and each a name git's ASCII case folding
    does not take for `.rs`, by owner. None when git grep failed."""
    if "_mod_passing_files" not in g.__dict__:
        found = _listed_by_grep(g, ["-l", "-z", "--all-match", "-F", "-e", "!", "-e", "mod"], [":(icase)*.rs"])
        out: Optional[Dict[Optional[str], Set[str]]] = None
        if found is not None:
            out = {}
            for p in [*_grep_listed(g, found), *(p for p in _rust_sources(g) if not p.lower().endswith(".rs"))]:
                out.setdefault(g.owner(p), set()).add(p)
        g.__dict__["_mod_passing_files"] = out
    return g.__dict__["_mod_passing_files"]


def _may_declare_modules_by_macro(g: Graph, pkg: Package) -> bool:
    """Whether a file `pkg` compiles (its own Rust files, and what it compiles
    from elsewhere) may declare a module by a macro outside test code: it
    defines a macro holding the `mod` keyword (_macro_module_defs: `mod x;`,
    `mod $n;`, `decl!(mod, x)`, or one invoking `$m!`), holds a site
    _macro_module_sites finds, invokes, or imports under another name in a
    `use` (`m!`, `use d::m as dd;`), a macro that may declare one that it
    may see (_visible_module_macros: holding one, declaring one
    (_module_macros), or invoking or renaming such a macro), or passes the
    `mod` keyword to a macro (_passes_mod). Such a module's name or file
    may be one no declaration the gate reads spells (a literal `mod x;` in
    a macro body invoked from another directory, a renamed macro), so none
    of the package's modules is test-only by its declarations
    (_test_only_file). True when git grep failed. The escape scan's walk
    reads it as what it found the package compiles from elsewhere so far
    makes it (scan_escapes)."""
    defs = _macro_module_names(g)
    if defs is None:
        return True
    definers, by_file = defs
    indexed = set(g.__dict__.get("_module_macros", ()))
    visible = _visible_module_macros(g, pkg, by_file)
    spelling = _module_macro_spelling(g, by_file)
    passing = _mod_passing_files(g)
    if visible is None or spelling is None or passing is None:
        return True
    names = sorted(set(visible) | indexed)
    elsewhere = tuple(g.__dict__.get("_compiled_from_elsewhere", {}).get(pkg.dir, ()))
    memo = g.__dict__.setdefault("_by_macro_memo", {})
    key = (pkg.dir, tuple(names), elsewhere)
    if key in memo:
        return memo[key]
    spelt = spelling[0]
    alt = "|".join(re.escape(n) for n in names)
    # Rust whitespace outside ASCII between the tokens (RUST_WS; review 4,
    # round 2: `m<U+200E>!(x)` was no call).
    named = re.compile(r'\b(?:' + alt + r')' + RUST_WS + r'*!(?!=)') if names else None
    renamed = re.compile(r'\b(?:' + alt + r')' + RUST_WS + r'+as\b') if names else None
    # Before lexing, a comment may sit between the name and its `!` or `as`
    # (`z::m/**/!();` was no call, and the package's #[cfg(test)] modules
    # stayed test-only); named and renamed read the lexed code.
    spoken = _macro_spelling_hint(names) if names else None
    defining = set(definers.get(pkg.dir, ()))
    passes = passing.get(pkg.dir, set())
    files = [p for p in sorted(defining | spelt.get(pkg.dir, set()) | passes | set(elsewhere))
             if g.index.entries.get(p, ("",))[0] in REGULAR]
    texts = {p: g.blob_cache[p] for p in files if p in g.blob_cache}
    texts.update(g.index.read_blobs([p for p in files if p not in texts]))
    result = False
    names_key, indexed_key = tuple(names), _module_macro_key(g)

    def declares(p: str, blob: bytes, oid: Optional[str]) -> bool:
        # A function of the file's bytes and of everything in its blob fact's
        # parameter: `names` (named, renamed), _module_macros (indexed_key,
        # _may_declare_by_macro, _macro_module_sites) and whether the package
        # defines, compiles from elsewhere or passes `mod` in it. Those three
        # only open the test to its lexed reading, which a file that reading
        # finds true for is opened to in any package listing it (its owner
        # greps it into `defining` or `passes`, another compiles it from
        # elsewhere), so no answer is known to turn on them; they are in the
        # key because the test reads them. So is indexed_key: `names` holds
        # every _module_macros name, and spoken and named take each text and
        # code _module_macro_call's patterns take, so no answer is known to
        # turn on it beside `names` either.
        text = blob.decode("utf-8", "replace")
        if not (p in defining or p in elsewhere or _may_declare_by_macro(g, text, oid)
                or (spoken is not None and spoken.search(text))
                or (p in passes and MOD_KEYWORD.search(text))):
            return False
        lx = _lexed(g, p, text)
        uses = USE_DECL.finditer(lx.code) if renamed is not None else ()
        return bool(_macro_defs_of(g, oid, lx)[0]
                    or any(not lx.in_test(at) for at in _macro_module_sites(g, lx, text, oid))
                    or (named is not None and any(not lx.in_test(c.start()) for c in named.finditer(lx.code)))
                    or any(renamed.search(lx.code, u.start(), u.end()) and not lx.in_test(u.start()) for u in uses)
                    or _passes_mod(lx))
    for p in files:
        blob, oid = texts[p], _blob_id(g, p, texts[p])
        if _blob_fact(g, "macro_production", oid,
                      (names_key, indexed_key, p in defining, p in elsewhere, p in passes),
                      lambda: declares(p, blob, oid)):
            result = True
            break
    memo[key] = result
    return result


VISIBILITY = re.compile(r'pub\s*(?:\([^)]*\))?\s*')
EXTERN_CXX = re.compile(r'\bextern\s*$')


def _pairs(code: str, pattern: "re.Pattern") -> Dict[int, int]:
    """Each opening bracket `pattern` finds in code, mapped to its closing one."""
    out: Dict[int, int] = {}
    stack: List[int] = []
    for b in pattern.finditer(code):
        if b.group(0) in "([{":
            stack.append(b.start())
        elif stack:
            out[stack.pop()] = b.start()
    return out


def _conditional_attr(lx, pos: int) -> bool:
    """Whether the attribute starting at lx.code[pos] (`#`) is a `cfg_attr`,
    whose predicate may not hold on the landing host."""
    m = ATTR_START.match(lx.code, pos)
    return m is not None and CFG_ATTR_HEAD.match(lx.code, _next_token(lx, m.end())) is not None


def _module_items(lx, text: str) -> List[Tuple[int, Optional[str], List[Optional[str]], Optional[List[List[str]]]]]:
    """Each file module a lexed Rust file declares (`mod x;`): (its position,
    its name, the file names it may take, and the directory chains of the
    inline modules around it). The names: every path attribute's value
    (None for one that is not a literal), and "" for the default `x.rs` or
    `x/mod.rs`, without a path attribute or with a `cfg_attr` one, whose
    predicate may not hold on this host. The chains: `mod a { mod x; }` is
    [["a"]], each path attribute of an inline module standing for its name
    (one chain per choice); None when one is not a literal. rustc looks for
    the file in that directory below the file's own, or below the file's
    stem for a file that is not mod.rs, lib.rs or main.rs.
    (LAND-GATE-EW1-FOLLOWUP-REVIEW-3: until then an item kept only its last
    path attribute and never its default, so `#[cfg_attr(unix, path = "a.rs")]
    #[cfg_attr(windows, path = "b.rs")] mod m;` named b.rs alone and
    `#[cfg_attr(windows, path = "w.rs")] mod m;` never the m.rs this host
    compiles.)
    An inline module's inner path attribute (`mod a { #![path = "zzz"] .. }`)
    is its own as an outer one is: rustc merges inner attributes into the
    item's, so `mod x;` there compiles zzz/x.rs. Only one among the inner
    attributes at the head of that module's body is (_inner_attr_head); one
    anywhere else names no module's file here and leaves every default
    standing (_lost_inner_paths: a lost site). (Review 4, round 2: every inner path
    attribute inside the module's braces was its own, a fn's
    `fn f() { #![path = "zzz"] }` too, which rustc ignores, and its
    default a/x.rs was dropped for the decoy zzz/x.rs.) A path attribute whose item
    no MOD_ITEM match takes (`#[path = ".."] mod $n;` in a macro) is an
    item of its own, its name None: its file is the attribute's still.
    (Review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3: the inner attribute was
    read as the next item's, or no one's, and the harvest followed a/x.rs;
    an item of a name the regexes did not read, `mod ñ;`, named nothing.)"""
    code = lx.code
    if "mod" not in code and "path" not in code:
        return []
    square = _pairs(code, SQUARE)
    curly = _pairs(code, CURLY)
    mods = list(MOD_ITEM.finditer(code))
    bodies = [(m.end() - 1, curly.get(m.end() - 1, len(code))) for m in mods if m.group(2) == "{"]
    attrs_of: Dict[int, List[Optional[str]]] = {}
    inner_of: Dict[int, List[Optional[str]]] = {}  # an inline module's `{` -> its inner path attributes
    unread: Dict[int, List[Optional[str]]] = {}  # an item no MOD_ITEM match takes -> its path attributes
    inline_opens = {o for o, _c in bodies}
    for pos, value, end in _path_attrs(lx, text):
        if code.startswith("!", _next_token(lx, pos + 1)):
            # `#![path = ..]`: an inline module's at the head of its body;
            # anywhere else no module's (_lost_inner_paths).
            head = _inner_attr_head(lx, pos, curly, square)
            if head in inline_opens:
                inner = inner_of.setdefault(head, [])
                inner.append(value)
                if _conditional_attr(lx, pos) and "" not in inner:
                    inner.append("")
            continue
        j = end
        while True:  # further attributes and a visibility, up to the item
            j = _next_token(lx, j)
            if code.startswith("#", j):
                k = _next_token(lx, j + 1)
                k = _next_token(lx, k + 1) if code.startswith("!", k) else k
                if k not in square:
                    break
                j = square[k] + 1
                continue
            vis = VISIBILITY.match(code, j)
            j = vis.end() if vis and vis.end() > j else j
            break
        if MOD_ITEM.match(code, j):
            alts = attrs_of.setdefault(j, [])
            alts.append(value)
            if _conditional_attr(lx, pos) and "" not in alts:
                alts.append("")
        else:
            unread.setdefault(j, []).append(value)
    inline = []  # (open, close, the directories it may stand for, None for one that is not a literal)
    items: List[Tuple[int, Optional[str], List[Optional[str]]]] = [(j, None, v) for j, v in unread.items()]
    for m in mods:
        alts = attrs_of.get(m.start(), [""])
        if m.group(2) == "{":
            close = curly.get(m.end() - 1, len(code))
            if m.end() - 1 in inner_of:  # outer and inner, the default where none is or one is a cfg_attr
                alts = list(dict.fromkeys(attrs_of.get(m.start(), []) + inner_of[m.end() - 1]))
            inline.append((m.end() - 1, close, [m.group(1) if attr == "" else attr for attr in alts]))
        else:
            items.append((m.start(), m.group(1), alts))
    out = []
    for pos, name, alts in sorted(items, key=lambda item: item[0]):
        chains: Optional[List[List[str]]] = [[]]
        for _o, _c, dirs in (x for x in inline if x[0] < pos < x[1]):  # outermost first
            if None in dirs:
                chains = None
                break
            chains = [chain + [d] for chain in chains for d in dirs]
        out.append((pos, name, alts, chains))
    return out


def _inner_attr_head(lx, pos: int, curly: Dict[int, int], square: Dict[int, int]) -> Optional[int]:
    """The `{` opening the body at whose head the inner attribute starting
    at lx.code[pos] (`#![..]`) stands, only inner attributes before it;
    None when it stands anywhere else: after an item or a statement, or
    outside every brace (a file's own). `curly` and `square`: _pairs'."""
    code = lx.code
    around = [o for o, c in curly.items() if o < pos < c]
    if not around:
        return None
    j = _next_token(lx, max(around) + 1)
    while j < pos:  # only inner attributes before it
        if not code.startswith("#", j):
            return None
        k = _next_token(lx, j + 1)
        if not code.startswith("!", k):
            return None
        k = _next_token(lx, k + 1)
        if k not in square:
            return None
        j = _next_token(lx, square[k] + 1)
    return max(around) if j == pos else None


def _lost_inner_paths(lx, text: str) -> List[int]:
    """Where a lexed file holds an inner path attribute (`#![path = ..]`, a
    `cfg_attr` one too) that is no inline module's (_module_items): one in
    a fn's, a block's, an impl's or another item's body, which rustc
    ignores, and one at a file's head, from whose parent directory rustc
    then takes that file's `mod x;` children (mod_dir_path, Inline::No;
    `#![path = "sub/zzz"]` in foo.rs compiles sub/x.rs, not foo/x.rs).
    Neither is followed, nor guessed at: a lost site, which leaves the
    package unresolved. (Review 4, round 2: the first named its inline module's
    directory, the second nothing, and both left the package resolved.)"""
    code = lx.code
    if "path" not in code:
        return []
    inner = {pos for pos, _value, _end in _path_attrs(lx, text)
             if code.startswith("!", _next_token(lx, pos + 1))}
    if not inner:
        return []
    curly, square = _pairs(code, CURLY), _pairs(code, SQUARE)
    inline_opens = {m.end() - 1 for m in MOD_ITEM.finditer(code) if m.group(2) == "{"}
    return sorted(pos for pos in inner
                  if _inner_attr_head(lx, pos, curly, square) not in inline_opens)


def _module_rels(name: Optional[str], attrs: Sequence[Optional[str]], chains: Sequence[Sequence[str]]) -> List[str]:
    """The files a module item of _module_items may take, relative to its
    file's directory (or that file's stem directory): each chain of inline
    directories, then each path attribute's value, or the default `name.rs`
    and `name/mod.rs` for "" (none for an item whose name is not read).
    (No None among `attrs`.)"""
    out = []
    for chain in chains:
        inner = "".join(d + "/" for d in chain)
        for attr in attrs:
            out += [inner + attr] if attr else [inner + name + tail for tail in (".rs", "/mod.rs") if name is not None]
    return out


def _extern_cxx_spans(lx, text: str) -> List[Tuple[int, int]]:
    """The `extern "C++" { .. }` blocks written in a lexed file itself: rustc
    compiles none (it knows no such ABI); cxx's bridge macro reads them, and
    an `include!` there names a C++ header, not Rust source. One among a
    macro's tokens (its definition's, or a call's: `strip! { unsafe extern
    "C++" { include!("gen.rs"); } }`) is not one: the macro may take the
    block apart, and rustc then compiles gen.rs. (Review of
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3: it was, and nothing read gen.rs.)"""
    spans = []
    curly = None
    for s, e, v in lx.strings:
        if v == "C++" and EXTERN_CXX.search(lx.code, max(0, s - 40), s) and not _among_macro_tokens(lx, s):
            j = _next_token(lx, e)
            if lx.code.startswith("{", j):
                curly = curly if curly is not None else _pairs(lx.code, CURLY)
                spans.append((j, curly.get(j, len(lx.code))))
    return spans


def _macro_bodies(lx) -> List[Tuple[int, int, Optional[str], int]]:
    """Each macro a lexed file defines (MACRO_DEF): (its body's opening
    bracket, the closing one, its name, where its name stands), the body
    of `macro_rules! m { .. }` (or `( .. );`, `[ .. ];`), `macro m { .. }`
    and `macro m(..) { .. }` (its parameters and body). One whose name no
    identifier spells (MACRO_DEF_UNNAMED: `macro_rules! $name { .. }`)
    is a body too, its name None: the bracket groups after `$name`, or
    after `macro_rules!`, the first and one right after it (a pasted
    name's `[<..>]`, or a `macro`'s parameters), or where none stands
    there, the rest of the brackets around it. (Review 4, round 2: it was none, and
    an include! in it was resolved from the callers of the macro around
    it, which only defines it; rustc resolves it from the file calling
    the macro it defines.)"""
    out = getattr(lx, "_macro_bodies", None)
    if out is None:
        out, code, pairs = [], lx.code, None
        for m in MACRO_DEF.finditer(code) if "macro" in code else ():
            j = _next_token(lx, m.end())
            if code[j:j + 1] not in ("(", "[", "{"):
                continue
            pairs = pairs if pairs is not None else _pairs(code, BRACKET)
            close = pairs.get(j, len(code))
            if m.group(2) is not None and code[j] == "(":
                k = _next_token(lx, close + 1)
                close = pairs.get(k, len(code)) if code.startswith("{", k) else close
            out.append((j, close, m.group(1) or m.group(2), m.start(1) if m.group(1) is not None else m.start(2)))
        for m in MACRO_DEF_UNNAMED.finditer(code) if "macro" in code else ():
            pairs = pairs if pairs is not None else _pairs(code, BRACKET)
            j = _next_token(lx, m.end())
            if code.startswith("$", j):  # `$name`: a name a macro parameter gives
                k = _next_token(lx, j + 1)
                name = re.compile(IDENT).match(code, k)
                j = _next_token(lx, name.end()) if name else k
            if j in pairs:
                close = pairs[j]
                k = _next_token(lx, close + 1)
                close = pairs[k] if k in pairs else close
            else:
                j, close = m.start(), min((c for o, c in pairs.items() if o < m.start() < c), default=len(code))
            out.append((j, close, None, m.start()))
        lx._macro_bodies = out
    return out


def _nested_macro_body(lx, body: Tuple[int, int, Optional[str], int]) -> bool:
    """Whether the macro body (_macro_bodies) sits inside another's."""
    return any(b[0] < body[0] and body[1] <= b[1] for b in _macro_bodies(lx) if b is not body)


def _include_names_parameter(lx, m: "re.Match") -> bool:
    """Whether the include! call `m` (its match ends at its opening bracket)
    names a macro parameter (`$`) among its tokens; one whose close is not
    found, too."""
    pairs = lx.__dict__.get("_bracket_pairs")
    if pairs is None:
        pairs = lx.__dict__["_bracket_pairs"] = _pairs(lx.code, BRACKET)
    close = pairs.get(m.end() - 1)
    return close is None or "$" in lx.code[m.end():close]


def _macro_body_at(lx, pos: int) -> Optional[Tuple[int, int, Optional[str], int]]:
    """The innermost macro definition (_macro_bodies) whose body holds `pos`."""
    inside = [b for b in _macro_bodies(lx) if b[0] < pos < b[1]]
    return max(inside, key=lambda b: b[0]) if inside else None


def _among_macro_tokens(lx, pos: int) -> bool:
    """Whether `pos` lies in a macro's definition (_macro_bodies) or among a
    macro call's tokens (`m!(..)`, `m! [..]`, `m! { .. }`)."""
    if _macro_body_at(lx, pos) is not None:
        return True
    code = lx.code
    pairs = _pairs(code, BRACKET)
    return any(m.end() - 1 < pos < pairs.get(m.end() - 1, len(code)) for m in MACRO_ARGS.finditer(code, 0, pos))


def _package_sources(g: Graph, pkg: Package) -> List[Tuple[str, str]]:
    """Every Rust file `pkg` owns, and (once the escape scan's walk has run)
    every file it compiles from elsewhere (_compiled_elsewhere), as (the
    path its sites resolve from, the file whose text it is): where a macro
    the package compiles may be called (_macro_callers)."""
    own = g.__dict__.setdefault("_owned_sources", {})
    if pkg.dir not in own:
        own[pkg.dir] = [q for q in _entries_under(g, pkg.dir) if g.index.entries[q][0] in REGULAR
                        and _rust_source(q) and g.owner(q) == pkg.dir]
    return [(q, q) for q in own[pkg.dir]] + list(g.__dict__.get("_sources_elsewhere", {}).get(pkg.dir, ()))


USE_ITEM = re.compile(r'(?<![\w$])use\b[^;]*')
# What starts a `use` item's path after the keyword: a name (its word kept,
# that `move` and `async` may be told apart), `::`, `{` or `*`.
USE_PATH_START = re.compile(r'\s+(?:r#)?(' + IDENT + r')|\s*(?:::|\{|\*)')  # a `use` item, to its `;` (literals and comments blank)
# include!($p), after its opener; rustc reads `$ p` and `$/* c */p` as `$p`
# (round 6 of review 4: those were none, and the include! stayed unresolved).
BARE_PARAM_ARG = re.compile(r'\s*\$\s*(?:r#)?' + IDENT + r'\s*(?:,\s*)?[)\]}]')
CALL_AFTER_NAME = re.compile(r'\s*!\s*[(\[{]')
ONLY_SEPARATORS = re.compile(r'[\s,]*')
# A macro call's token tree, or a `macro_rules! name {..}` body: `use` among
# its tokens is a token, no item (round 7 of review 4).
MACRO_TOKENS = re.compile(r'(?<![\w$])(?:r#)?' + IDENT + r'\s*!\s*(?:(?:r#)?' + IDENT + r'\s*)?[(\[{]')
PUB_BEFORE = re.compile(r'(?<![\w$])pub\s*$')


class _MentionFacts(NamedTuple):
    use_starts: List[int]
    use_ends: List[int]
    use_certain: List[bool]  # each `use` match, whether it is certainly a `use` item (_use_is_an_item)
    pairs: Dict[int, int]
    lit_starts: List[int]
    macro_starts: List[int]  # the outermost macro token trees, (opener, close]
    macro_ends: List[int]


def _mention_facts(g: Graph, real: str, lx) -> _MentionFacts:
    """What _macro_callers asks of each mention in the file `real`, found
    once per file: its `use` items (USE_ITEM) and whether each is certainly
    one, its bracket pairs, the starts of its literals (lx.strings, in order)
    and its outermost macro token trees. (Round 6 of review 4: each mention
    searched from its statement's start, quadratic in a long statement
    naming the macro many times.)"""
    cache = g.__dict__.setdefault("_mention_facts", {})
    facts = cache.get(real)
    if facts is None:
        code = lx.code
        pairs = _pairs(code, BRACKET)
        spans: List[Tuple[int, int]] = []
        trees = [(t.end() - 1, pairs.get(t.end() - 1)) for t in MACRO_TOKENS.finditer(code)]
        # A `macro m(..) { .. }` body is a macro's tokens too, which no `m!`
        # opens (round 8 of review 4: its `use .. as $a;` was a certain item).
        trees += [(b[0], b[1]) for b in _macro_bodies(lx)]
        for opener, close in sorted(t for t in trees if t[1] is not None):
            if not spans or opener > spans[-1][1]:
                spans.append((opener, close))
        macro_starts, macro_ends = [a for a, _b in spans], [b for _a, b in spans]
        opener_of = {c: o for o, c in pairs.items()}
        uses = [(u.start(), u.end()) for u in USE_ITEM.finditer(code)]
        certain = [_use_is_an_item(code, a, opener_of, macro_starts, macro_ends) for a, _b in uses]
        facts = cache[real] = _MentionFacts([a for a, _b in uses], [b for _a, b in uses], certain, pairs,
                                            [a for a, _b, _v in lx.strings], macro_starts, macro_ends)
    return facts


def _use_is_an_item(code: str, at: int, opener_of: Dict[int, int], macro_starts: List[int],
                    macro_ends: List[int]) -> bool:
    """Whether the `use` keyword at code[at] certainly starts a `use` item:
    not among a macro's tokens (`with_path!(use inner)`, a `macro_rules!`
    body, where `use ... as $a;` is a fragment's), and where an item
    starts: the file's start, or after `;`, `{`, `}`, an attribute's `]`,
    `pub` or `pub(..)`, and followed by a path: a name, `::`, `{` or `*`. A
    raw identifier (`r#use`, after a `#`), a precise capture bound
    (`impl Sized + use<>`) and a `use` closure (`use || ..`,
    `use move || ..`) are none. (Round 7 of review 4: any `use` keyword
    began an item, and a callback mention after it handed nothing; round 8:
    a `use` closure, and a `macro m(..) { .. }` body, were items.)"""
    i = bisect.bisect_left(macro_starts, at)
    if i > 0 and at < macro_ends[i - 1]:
        return False
    after = USE_PATH_START.match(code, at + 3)
    if after is None or after.group(1) in ("move", "async", "static"):
        return False
    j = at
    while True:
        j -= 1
        while j >= 0 and code[j].isspace():
            j -= 1
        if j < 0 or code[j] in ";{}]":
            return True
        if code[j] == ")" and j in opener_of:
            o = opener_of[j]
            m = PUB_BEFORE.search(code, max(0, o - 16), o)
            if m is None:
                return False
            j = m.start()
            continue
        m = PUB_BEFORE.search(code, max(0, j - 15), j + 1)
        if m is None:
            return False
        j = m.start()


def _in_use_item(g: Graph, real: str, lx, pos: int) -> bool:
    """Whether `pos` lies in a `use` match (USE_ITEM), certain or not."""
    facts = _mention_facts(g, real, lx)
    i = bisect.bisect_left(facts.use_starts, pos)
    return i > 0 and pos < facts.use_ends[i - 1]


def _in_certain_use_item(g: Graph, real: str, lx, pos: int) -> bool:
    """Whether `pos` lies in a `use` item that is certainly one (_use_is_an_item)."""
    facts = _mention_facts(g, real, lx)
    i = bisect.bisect_left(facts.use_starts, pos)
    return i > 0 and pos < facts.use_ends[i - 1] and facts.use_certain[i - 1]


def _handed_by(g: Graph, real: str, lx, m: "re.Match", name: str) -> List[Optional[str]]:
    """What the mention `m` of the macro `name` hands it: each literal of a
    call (`name!(..)`, any delimiter) whose tokens are literals and commas
    only, decoded (_decoded_literal), nothing for a call of no tokens or a
    name in what is certainly a `use` item (_use_is_an_item), and [None]
    otherwise: a computed argument (`concat!(..)`, `$p`, a constant's name,
    a doc comment, which rustc makes a `#[doc = ".."]` attribute), or the
    name handed to another macro (`with_path!(inner)`, whose body may call
    it with a literal of its own). (Round 7 of review 4: a doc comment
    among a call's tokens was a separator, a `use` token anywhere began an
    item, and a literal's escapes were its value.)"""
    end = m.start() + m.group(0).find(name) + len(name)
    call = CALL_AFTER_NAME.match(lx.code, end) if m.group(1) is None else None
    if call is None:
        return [] if _in_certain_use_item(g, real, lx, m.start()) else [None]
    facts = _mention_facts(g, real, lx)
    opener = call.end() - 1
    close = facts.pairs.get(opener)
    if close is None or not ONLY_SEPARATORS.fullmatch(lx.code, opener + 1, close):
        return [None]
    docs = lx.doc_comment_starts()
    d = bisect.bisect_right(docs, opener)
    if d < len(docs) and docs[d] < close:
        return [None]
    i = bisect.bisect_right(facts.lit_starts, opener)
    out: List[Optional[str]] = []
    while i < len(facts.lit_starts) and facts.lit_starts[i] < close:
        s, _e, v = lx.strings[i]
        out.append(_decoded_literal(lx, s, v))
        i += 1
    return out


class _UntoldCaller(Exception):
    """A file calling a macro that _macro_callers cannot find."""


def _macro_callers(g: Graph, sources: Sequence[Tuple[str, str]], name: Optional[str], blobs: Dict[str, bytes],
                   _seen: Optional[Set[Tuple[str, bool]]] = None, via: Optional[Set[str]] = None,
                   handed: Optional[List[Optional[str]]] = None) -> Set[Tuple[str, str]]:
    """The files of `sources` ((the path its sites resolve from, the file
    whose text it is), _package_sources) from whose directory an include!
    in the body of the macro `name` resolves, as such pairs. rustc resolves an include!'s
    relative path from the file of its outermost macro call
    (rustc_expand's resolve_path takes span.source_callsite()), not from
    the macro's definition: so each file that names the macro outside its
    definition's head, calling it (`m!(..)`) or handing it to another macro
    (`error_codes!(m)`); a name in another macro's body stands for that
    macro's own callers, and a `use` renaming it (`use m as n;`) for the new
    name's too. Empty: no file names it (a macro exported to other crates),
    and the include! cannot be resolved. (Review of
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3: it was resolved from the defining
    file, and a file of that name there stood for the one rustc compiles.)
    Empty too when a caller cannot be found: the macro's name is none an
    identifier spells (None: `macro_rules! $name`, _macro_bodies), or a
    file names it in the body of such a macro, which may be called from
    anywhere. (Review 4, round 2: such a body was no macro's, and the include! was
    resolved from the callers of the macro around it.) `via` gains each file
    (its text's) that names the macro in another macro's body or renames it:
    a literal there may be what a parameter of the macro is handed
    (`outer!` calling `inner!("../x.md")`), though rustc resolves it from
    the outer macro's callers. (Round 5 of review 4: such a file's literals
    were none a parameter could be, and an unrelated literal of a caller
    stood for it.) `handed` gains what each mention of the macro or of a
    rename of it hands the macro (_handed_by): the literals of a call
    handing only literals, and None for any other (a computed argument, a
    name, the macro handed on as another's callback); a `use` hands
    nothing. (Round 6 of review 4: any literal of a file naming the macro
    stood for a bare parameter's argument, `inner!(concat!(..))` beside one
    included.) A name is visited once in each role: as a name of the macro,
    collecting `handed`, and as a macro whose body names it, collecting
    callers only; the first stands in for the second. (Round 7 of review 4:
    a name first visited as an outer macro was not visited again as a
    rename, and the rename's calls handed nothing.)"""
    # What the scan of a file reading this records is not its blob's alone:
    # scan_escapes caches none of it (SCAN_CACHE).
    g.__dict__["_scan_reads_callers"] = True
    g.global_scan_packages.update(owner for _scan, real in sources
                                  if (owner := g.owner(real)) is not None)
    if _seen is None:
        try:
            return _macro_callers(g, sources, name, blobs, set(), via, handed)
        except _UntoldCaller:
            return set()
    if name is None:
        raise _UntoldCaller(name)
    seen = _seen
    tracked = handed is not None
    if (name, True) in seen or (name, tracked) in seen:
        return set()
    seen.add((name, tracked))
    blobs.update(g.index.read_blobs(sorted({real for _scan, real in sources} - set(blobs))))
    named = re.compile(r'(?<![\w$])(?:r#)?' + re.escape(name) + r'(?![\w$])(?:\s+as\s+(?:r#)?(' + IDENT + r'))?')
    out: Set[Tuple[str, str]] = set()
    for scan, real in sources:
        text = blobs[real].decode("utf-8", "replace")
        if name not in text:
            continue
        lx = _lexed(g, real, text)
        heads = {at for _o, _c, n, at in _macro_bodies(lx) if n == name}
        for m in named.finditer(lx.code):
            if m.start() + m.group(0).find(name) in heads:
                continue  # its own definition
            # In a `use` item, however far its keyword stands (_mention_facts).
            # (Round 5 of review 4: a window of 2000 characters missed a long
            # `use` group's rename; round 6: from the statement's start, each
            # name searched a long statement again.)
            in_use = _in_use_item(g, real, lx, m.start())
            if m.group(1) is not None and in_use:
                if via is not None:
                    via.add(real)
                out |= _macro_callers(g, sources, m.group(1), blobs, seen, via, handed)
            if handed is not None:
                handed.extend(_handed_by(g, real, lx, m, name))
            body = _macro_body_at(lx, m.start())
            if body is None:
                out.add((scan, real))
            else:
                if via is not None:
                    via.add(real)
                out |= _macro_callers(g, sources, body[2], blobs, seen, via)
    return out


def _include_arg(lx, text: str, i: int) -> Tuple[str, Optional[str]]:
    """What the include! whose opening delimiter (any of `(`, `[`, `{`) ends
    before text[i] names: ("file", value) for a string literal or a concat!
    of literals, ("manifest", rest) for a concat! of
    env!("CARGO_MANIFEST_DIR") and literals, ("generated", None) for one
    built from another env! (OUT_DIR: a file outside the tree), and
    ("unknown", None) for anything else (a macro parameter, a call). concat!
    and env! take any delimiter too, each closed by its own (MACRO_CLOSE)."""
    code = lx.code
    value, j = _literal_at(lx, text, i)
    if value is not None:
        return "file", value
    concat = CONCAT_OPEN.match(code, j)
    env = ENV_OPEN.match(code, j)
    if env is not None:
        return "generated", None
    if concat is None:
        return "unknown", None
    close = MACRO_CLOSE[code[concat.end() - 1]]
    parts: List[str] = []
    manifest = False
    k = concat.end()
    while True:
        value, k = _literal_at(lx, text, k)
        if value is not None:
            parts.append(value)
        else:
            env = ENV_OPEN.match(code, k)
            if env is None:
                return "unknown", None
            name, k = _literal_at(lx, text, env.end())
            k = _next_token(lx, k)
            if name is None or code[k:k + 1] != MACRO_CLOSE[code[env.end() - 1]]:
                return "unknown", None
            if name != "CARGO_MANIFEST_DIR":
                return "generated", None
            if parts or manifest:
                return "unknown", None
            manifest, k = True, k + 1
        k = _next_token(lx, k)
        if code[k:k + 1] == ",":
            k = _next_token(lx, k + 1)
        if code[k:k + 1] == close:
            break
        if k >= len(code) or code[k] in ")]};":
            return "unknown", None
    joined = "".join(parts)
    return ("manifest", joined.lstrip("/")) if manifest else ("file", joined)


DOC_COMMENT_MARKS = ("///", "//!", "/**", "/*!")
# A `doc = ...` attribute value (`#[doc = ".."]`, `#![doc = include_str!(..)]`,
# `#[cfg_attr(unix, doc = "```no_run")]`), matched in a lexed file's code,
# where a comment is blank (`#[doc /* c */ = ..]`): a doc fragment rustdoc
# joins, in source order, to the doc comments and other fragments of the same
# item.
DOC_ATTR_VALUE = re.compile(r'\bdoc\s*=(?!=)')
# Whether a file may hold one at all, in its raw text: the attribute's name.
# A comment may stand before its `=`, so `doc =` is no prefilter (review 4: a
# file whose only doc text was `#[doc /* example */ = r#"..."#]` was never read).
DOC_WORD = re.compile(r'\bdoc\b')
DOC_CFG_ATTR = re.compile(r'\s*(?:r#)?cfg_attr\s*\(')
# The path of an attribute that may hold a doc value (_doc_attr_values): doc
# (`r#doc` too), or a cfg_attr, whose payload may.
DOC_ATTR_PATH = re.compile(r'\s*(?:r#)?(doc|cfg_attr)\b')
# A macro call in a doc value: the path before its name, and its name.
DOC_MACRO_CALL = re.compile(r'((?:(?:r#)?\w+\s*::\s*)*)(?:r#)?(\w+)\s*!\s*[(\[{]')
# The paths that name the standard library's macros (`std::concat!`); any
# other (`crate::concat!`) names a macro of the program's.
STD_MACRO_PATHS = ("", "std::", "core::")
# A doc file a value includes, in every spelling rustc expands: any delimiter,
# whitespace (in lexed code, a comment too) before and after the `!`, and a
# path through std or core (until review 4 only `include_str!(`: the doc
# files of `include_str![..]`, `include_str !(..)` and `std::include_str!(..)`
# were never read).
DOC_INCLUDE = re.compile(r'(?:(?:::\s*)?(?:std|core)\s*::\s*)?include_str\s*!\s*[(\[{]')
ARG_DELIM = re.compile(r'[()\[\]{},]')
# The prefilter over a doctest view, line by line as git grep reads a file. A
# view blanks the rest of its file to whitespace, and with `\s` the line-start
# alternative ran from every line over all the blank lines after it: 87 s on
# trust-ir-bridge's lower.rs, 1332 s of a 1357 s scan (measured 2026-11-06).
DOCTEST_SCAN = re.compile(SCAN_RE.replace("[[:space:]]", r"[ \t\r\f\v]"), re.M)
# The editions rustdoc's LangString::parse takes after `rust` in a token
# (Edition::from_str): `rust2021` and `rustfuture` are no language, only a lint.
RUST_EDITIONS = ("2015", "2018", "2021", "2024", "future")


def _info_tokens(info: str) -> Optional[List[Tuple[str, str]]]:
    """rustdoc's TagIterator over a fence's info string: ("lang", token),
    ("class", name) and ("kv", key) items, or None where it reports an error
    (an unclosed quote, comment or attribute block, a stray character)."""
    def leading(c: str) -> bool:
        return c in "_-:" or (c.isascii() and c.isalnum())

    def bare(c: str) -> bool:
        return leading(c) or c in ".!#$%&*+/;<>?@^|~"

    sep = " ,\t"
    out: List[Tuple[str, str]] = []
    n, i, in_attr = len(info), 0, False

    def after_ok(j: int) -> bool:
        return j >= n or info[j] == "}" or info[j] in sep or info[j] == "("

    while True:
        while i < n and info[i] in sep:
            i += 1
        if i >= n:
            return None if in_attr else out
        start, c = i, info[i]
        i += 1
        if in_attr:
            if c == "}":
                in_attr = False
            elif c == ".":
                while i < n and bare(info[i]):
                    i += 1
                if i == start + 1 or not after_ok(i):
                    return None
                out.append(("class", info[start + 1:i]))
            elif c == '"' or leading(c):
                if c == '"':
                    end = info.find('"', i)
                    if end < 0 or end == i:
                        return None
                    key, i = info[i:end], end + 1
                else:
                    while i < n and bare(info[i]):
                        i += 1
                    if i >= n:
                        return None
                    key = info[start:i]
                if i >= n or info[i] != "=":
                    return None
                i += 1
                if i >= n:
                    return None
                if info[i] == '"':
                    end = info.find('"', i + 1)
                    if end < 0 or end == i + 1:
                        return None
                    i = end + 1
                elif bare(info[i]):
                    while i < n and bare(info[i]):
                        i += 1
                    if i >= n:
                        return None
                else:
                    return None
                if not after_ok(i):
                    return None
                out.append(("kv", key))
            else:
                return None
            continue
        if c == '"':
            end = info.find('"', i)
            if end < 0:
                return None
            i = end + 1
            if i < n and info[i] != "{" and info[i] not in sep and info[i] != "(":
                return None
            out.append(("lang", info[start + 1:end]))
            continue
        j = start
        while True:
            if j >= n:
                if j > start:
                    out.append(("lang", info[start:j]))
                i = j
                break
            c = info[j]
            if c == "{":
                in_attr, i = True, j + 1  # rustdoc drops a token run straight into `{`
                break
            if c in sep:
                if j > start:
                    out.append(("lang", info[start:j]))
                i = j + 1
                break
            if c == "(":
                close = info.find(")", j + 1)
                if close < 0:
                    return None
                if j > start:
                    out.append(("lang", info[start:j]))
                i = close + 1
                break
            if c == '"' and j > start:
                return None
            if (j == start and leading(c)) or (j > start and bare(c)):
                j += 1
                continue
            return None


def _rustdoc_block(info: str) -> Optional[str]:
    """What rustdoc's doctest collector does with a fenced block whose info
    string is `info` (LangString::parse, after pulldown-cmark decoded it:
    _md_info): "run", "compile" (no_run, compile_fail: compiled, never run)
    or None (not Rust, or ignored on every target). An empty info string is
    Rust. A token rustdoc reads as a Rust tag only with its error-code check
    on (`E0277`, and `E+123`, whose four characters parse as a u32) is read as
    one; `edition*` and `rust` + an edition (`rust2021`, `rustfuture`) are no
    language; an info string the port cannot tokenize counts as Rust that
    runs: each keeps more code than rustdoc may test (until review 4
    `rustfuture` and `E+123` were a language that is not Rust)."""
    info = info.strip()
    if not info:
        return "run"
    tokens = _info_tokens(info)
    if tokens is None:
        return "run"
    seen_rust = seen_other = custom = no_run = ignore_all = False
    ignores = False
    for kind, t in tokens:
        if kind != "lang":
            continue
        if t in ("should_panic", "no_run", "ignore"):
            seen_rust = not seen_other
            no_run = no_run or t == "no_run"
            ignore_all = ignore_all or t == "ignore"
        elif t.startswith("ignore-"):
            ignores, seen_rust = True, not seen_other
        elif t == "rust":
            seen_rust = True
        elif t == "custom":
            custom = True
        elif t in ("test_harness", "standalone_crate", "compile_fail"):
            seen_rust = not seen_other or seen_rust
            no_run = no_run or t == "compile_fail"
        elif t.startswith("edition") or (t.startswith("rust") and t[4:] in RUST_EDITIONS):
            pass
        elif t.startswith("E") and len(t[1:].encode()) == 4 and re.fullmatch(r"\+?[0-9]+", t[1:]):
            seen_rust = not seen_other or seen_rust
        else:
            seen_other = True
    if custom or (seen_other and not seen_rust) or (ignore_all and not ignores):
        return None
    return "compile" if no_run else "run"


def _has_doc_text(text: str) -> bool:
    """Whether a Rust file can hold a doctest: a doc comment, or a doc
    attribute (a string, or a doc file it includes)."""
    return any(mark in text for mark in DOC_COMMENT_MARKS) or DOC_WORD.search(text) is not None


# rustdoc reads a doc as Markdown with pulldown-cmark 0.11.3 (Cargo.lock) and
# main_body_opts: tables, footnotes (GFM's: a definition is a container its
# lines continue at four columns), strikethrough, task lists, smart
# punctuation. What follows ports its first pass (firstpass.rs, scanners.rs)
# line by line, as far as it decides which lines are code: the containers
# (block quotes, list items, footnote definitions; a tab to the next stop of
# four), and the leaves (paragraphs and their lazy lines, tables, headings,
# rules, HTML blocks of types 1 to 7, fenced and indented code). A fence opens
# and closes only at three columns or fewer past its containers, and closes
# with them: a container that a line does not continue ends the block, and
# the line is read again outside it. Where the port does not follow a
# construct to its end (an HTML block of type 7, whose tag it does not scan; a
# table, whose columns it does not count; a link reference definition, whose
# title may run over lines) it reads the line both ways and keeps every
# reading: more code, never less. (Until review 4 a fence was a fence at any
# indent, in a container that had ended, or inside an HTML block.)
#
# A reading's state: (containers, leaf, begin_list_item, last_line_blank).
# A container is ("L", marker, tight) a list, ("I", indent) a list item, ("Q",)
# a block quote, ("N",) a footnote definition. A leaf is None, ("P", may be a
# link reference definition) a paragraph, ("TH",) a paragraph's first line
# that the next may make a table head, ("T",) a table, ("F", character,
# length, indent, rustdoc's mode, first line) a fenced block, ("C", first
# line) an indented one, ("H", end tag) an HTML block of type 1 to 5, ("H6",)
# one of type 6 or 7.
_MD_WS = " \t\x0b\x0c"                      # is_ascii_whitespace_no_nl
_MD_ASCII_WS = " \t\n\x0b\x0c\r"            # is_ascii_whitespace
# Rust's char::is_whitespace (Unicode White_Space), which rustdoc's unindent
# and beautify_doc_string test: not Python's str.isspace, which takes
# U+001C..U+001F too (review 4: a doc line of U+001C set the least indent).
_RUST_WS = ("\t\n\x0b\x0c\r \x85\xa0            "
            "    　")
_MD_PUNCT = frozenset('!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~')
_MD_ENTITY = re.compile(r'&(?:#[xX]([0-9A-Fa-f]{1,6})|#([0-9]{1,7})|([A-Za-z0-9]+));')
_MD_HTML_TAGS = frozenset(
    "address article aside base basefont blockquote body caption center col colgroup dd details dialog dir "
    "div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html "
    "iframe legend li link main menu menuitem nav noframes ol optgroup option p param search section summary "
    "table tbody td tfoot th thead title tr track ul".split())
_MD_HTML7 = re.compile(r'</?[A-Za-z][A-Za-z0-9-]*(?:[ \t\x0b\x0c/>]|$)')
_MD_FRESH = ((), None, False, False)
# The states a module's outer doc this scan does not see may leave its file's
# doc in: none open, or a paragraph (doctest_views blinds a module whose outer
# doc may leave any other).
_MD_JOINABLE = (_MD_FRESH, ((), ("P", True), False, False), ((), ("TH",), False, False))


def _md_blank(s: str) -> bool:
    return not s.strip(_MD_WS)


class _MdLine:
    """pulldown-cmark's LineStart over one line (its ending removed)."""
    __slots__ = ("s", "ix", "tab", "rem")

    def __init__(self, s: str, ix: int = 0) -> None:
        self.s, self.ix, self.tab, self.rem = s, ix, ix, 0

    def copy(self) -> "_MdLine":
        c = _MdLine(self.s, self.ix)
        c.tab, c.rem = self.tab, self.rem
        return c

    def restore(self, other: "_MdLine") -> None:
        self.ix, self.tab, self.rem = other.ix, other.tab, other.rem

    def _space(self, n: int) -> int:
        k = min(self.rem, n)
        self.rem -= k
        n -= k
        s = self.s
        while n > 0 and self.ix < len(s):
            c = s[self.ix]
            if c == " ":
                self.ix += 1
                n -= 1
            elif c == "\t":
                spaces = 4 - (self.ix - self.tab) % 4
                self.ix += 1
                self.tab = self.ix
                k = min(spaces, n)
                n -= k
                self.rem = spaces - k
            else:
                break
        return n

    def space(self, n: int) -> bool:
        return self._space(n) == 0

    def upto(self, n: int) -> int:
        return n - self._space(n)

    def all_space(self) -> None:
        self.rem = 0
        while self.ix < len(self.s) and self.s[self.ix] in " \t":
            self.ix += 1

    def eol(self) -> bool:
        return self.ix >= len(self.s)

    def quote(self) -> bool:
        save = self.copy()
        self.space(3)
        if self.s.startswith(">", self.ix):
            self.ix += 1
            self.space(1)
            return True
        self.restore(save)
        return False

    def list_marker(self) -> Optional[Tuple[str, int, int]]:
        save = self.copy()
        indent = self.upto(4)
        s = self.s
        if indent < 4 and self.ix < len(s):
            c = s[self.ix]
            if c in "-+*":
                if _md_hrule(s[self.ix:]):
                    self.restore(save)
                    return None
                self.ix += 1
                if self.space(1) or self.eol():
                    return self._finish_marker(c, 0, indent + 2)
            elif "0" <= c <= "9":
                start, j, val = self.ix, self.ix + 1, int(c)
                while j < len(s) and j - start < 10:
                    d = s[j]
                    j += 1
                    if "0" <= d <= "9":
                        val = val * 10 + int(d)
                    elif d in ".)":
                        self.ix = j
                        if self.space(1) or self.eol():
                            return self._finish_marker(d, val, indent + 1 + j - start)
                        break
                    else:
                        break
        self.restore(save)
        return None

    def _finish_marker(self, c: str, start: int, indent: int) -> Tuple[str, int, int]:
        save = self.copy()
        if _md_blank(self.s[self.ix:]):
            return c, start, indent
        post = self.upto(4)
        if post < 4:
            indent += post
        else:
            self.restore(save)
        return c, start, indent

    def task(self) -> bool:
        save = self.copy()
        self.upto(3)
        s, i = self.s, self.ix
        if (s[i:i + 1] == "[" and s[i + 1:i + 2] != "" and (s[i + 1] in _MD_WS or s[i + 1] in "xX")
                and s[i + 2:i + 3] == "]" and s[i + 3:i + 4] != "" and s[i + 3] in _MD_WS):
            self.ix = i + 3
            return True
        self.restore(save)
        return False


def _md_indent(s: str, most: int) -> Tuple[int, int]:
    """calc_indent: where the indent of `s` stops (the index of the character
    it stops at) and how many columns it is, up to `most`."""
    spaces = off = 0
    for off, b in enumerate(s):
        if b == " ":
            spaces += 1
            if spaces == most:
                break
        elif b == "\t":
            new = spaces + 4 - (spaces & 3)
            if new > most:
                break
            spaces = new
        else:
            break
    return off, spaces


def _md_hrule(s: str) -> bool:
    if len(s) < 3 or s[0] not in "*-_":
        return False
    n = 0
    for ch in s:
        if ch == s[0]:
            n += 1
        elif ch not in " \t":
            return False
    return n >= 3


def _md_atx(s: str) -> bool:
    n = len(s) - len(s.lstrip("#"))
    return 1 <= n <= 6 and (n == len(s) or s[n] in _MD_ASCII_WS)


def _md_setext(s: str) -> bool:
    return s[:1] in ("=", "-") and _md_blank(s.lstrip(s[0]))


def _md_fence(s: str) -> Optional[Tuple[str, int]]:
    """scan_code_fence: the character and length of the fence `s` opens with."""
    if s[:1] not in ("`", "~"):
        return None
    n = len(s) - len(s.lstrip(s[0]))
    if n < 3 or (s[0] == "`" and "`" in s[n:]):
        return None
    return s[0], n


def _md_closes(s: str, ch: str, n: int) -> bool:
    """scan_closing_code_fence: at least as long, then only spaces (a tab
    keeps the block open)."""
    k = len(s) - len(s.lstrip(ch))
    return k >= n and not s[k:].strip(" ")


def _md_table_head(s: str) -> bool:
    """scan_table_head: whether `s` is a table's delimiter row."""
    off, spaces = _md_indent(s, 4)
    if spaces > 3 or off == len(s):
        return False
    pipe = hyphen = in_col = False
    i = off
    if s[i] == "|":
        i, pipe = i + 1, True
    for c in s[i:]:
        if c == "-":
            hyphen = in_col = True
        elif c == "|":
            if not in_col:
                return False
            pipe, in_col = True, False
        elif c not in " :":
            return False
    return pipe and hyphen


def _md_listitem(s: str) -> Optional[Tuple[int, str, int]]:
    """scan_listitem: (where the item's text starts, its delimiter, its start
    number)."""
    if not s:
        return None
    if s[0] in "-+*":
        w, c, start = 1, s[0], 0
    elif "0" <= s[0] <= "9":
        k = 0
        while k < 9 and k < len(s) and "0" <= s[k] <= "9":
            k += 1
        if k >= len(s) or s[k] not in ".)":
            return None
        w, c, start = k + 1, s[k], int(s[:k])
    else:
        return None
    postn, post = _md_indent(s[w:], 5)
    if post == 0:
        if s[w:]:
            return None
    elif post > 4:
        postn = 1
    if _md_blank(s[w:]):
        postn = 0
    return w + postn, c, start


def _md_html_end(t: str) -> Optional[str]:
    """get_html_end_tag, `t` after the `<`: the text that ends an HTML block
    of type 1 to 5."""
    for tag, end in (("pre", "</pre>"), ("style", "</style>"), ("script", "</script>"),
                     ("textarea", "</textarea>")):
        k = len(tag)
        if len(t) < k:
            break
        if t[:k].isascii() and t[:k].lower() == tag and (len(t) == k or t[k] in _MD_ASCII_WS or t[k] == ">"):
            return end
    for begin, end in (("!--", "-->"), ("?", "?>"), ("![CDATA[", "]]>")):
        if t.startswith(begin):
            return end
    return ">" if len(t) > 1 and t[0] == "!" and t[1].isascii() and t[1].isalpha() else None


def _md_html6(t: str) -> bool:
    """starts_html_block_type_6, `t` after the `<`."""
    i = 1 if t.startswith("/") else 0
    j = i
    while j < len(t) and t[j].isascii() and t[j].isalnum():
        j += 1
    tail = t[j:]
    return t[i:j].lower() in _MD_HTML_TAGS and (tail == "" or tail[0] in " \t>" or tail.startswith("/>"))


def _md_footnote(s: str, i: int) -> Optional[int]:
    """parse_footnote at s[i:] (GFM: a label on one line): where the
    definition's text starts, or None."""
    if not s.startswith("[^", i):
        return None
    j, only_ws, n = i + 2, True, 0
    while True:
        if n >= 1000 or j >= len(s):
            return None
        c = s[j]
        if c == "[":
            return None
        if c == "]":
            break
        if c == "\\" and j + 1 < len(s) and s[j + 1] in _MD_PUNCT:
            j, n, only_ws = j + 2, n + 2, False
        elif c in _MD_ASCII_WS:
            k, weight = j, 0
            while k < len(s) and s[k] in _MD_ASCII_WS:
                weight += 1 if s[k] == " " else 2
                k += 1
            n += k - j if weight > 1 else 1
            j = k
        else:
            only_ws = False
            n += 0 if c.isascii() else len(c.encode())
            j += 1
    if only_ws or s[j + 1:j + 2] != ":":
        return None
    j += 2
    while j < len(s) and s[j] in _MD_WS:
        j += 1
    return j


def _md_info(s: str) -> str:
    """A fence's info string as pulldown-cmark hands it to rustdoc: from the
    first character after the fence and its blanks, without trailing
    whitespace, a backslash before ASCII punctuation dropped and each entity
    decoded (unescape, scan_entity: `r&#117;st` is `rust`, `text&#44;rust`
    two tokens; until review 4 the source text was read)."""
    from html.entities import html5
    s = s.lstrip(_MD_WS).rstrip(_MD_ASCII_WS)
    if "\\" not in s and "&" not in s and "\r" not in s:
        return s
    out: List[str] = []
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s) and s[i + 1] in _MD_PUNCT:
            out.append(s[i + 1])
            i += 2
            continue
        if c == "&":
            m = _MD_ENTITY.match(s, i)
            if m and m.group(3) is not None:
                value = html5.get(m.group(3) + ";")
                if value is not None:
                    out.append(value)
                    i = m.end()
                    continue
            elif m:
                cp = int(m.group(1), 16) if m.group(1) else int(m.group(2))
                out.append(chr(cp) if 0 < cp <= 0x10FFFF and not 0xD800 <= cp <= 0xDFFF else "�")
                i = m.end()
                continue
        if c != "\r":
            out.append(c)
        i += 1
    return "".join(out)


def _md_match(spine: tuple, ls: _MdLine) -> int:
    """scan_containers: how many of the open containers the line continues."""
    i = 0
    for c in spine:
        if c[0] == "Q":
            if not ls.quote():
                break
        elif c[0] in "IN":
            save = ls.copy()
            if not ls.space(c[1] if c[0] == "I" else 4) and not ls.eol():
                ls.restore(save)
                break
        i += 1
    return i


def _md_interrupts(s: str, cur: bool, table: bool):
    """scan_paragraph_interrupt (`table`: scan_paragraph_interrupt_no_table in
    a table) for a line's text `s` after its containers and indent: True,
    False, or "table" for a line that opens a heavy table, which interrupts
    only when the next line is a table head (read both ways)."""
    if s == "" or _md_hrule(s) or _md_atx(s) or _md_fence(s) or s.startswith(">"):
        return True
    item = _md_listitem(s)
    if item is not None and (not cur or table or ((item[1] in "*-+" or item[2] == 1)
                                                   and not _md_blank(s[item[0]:]))):
        return True
    if s.startswith("<") and (_md_html_end(s[1:]) is not None or _md_html6(s[1:])):
        return True
    if s.startswith("[^") and _md_footnote(s, 0) is not None:
        return True
    return "table" if not table and s.startswith("|") else False


class _MdBuild:
    """The open containers and list flags while one line is read (the tree
    operations of FirstPass: pop, finish_list, continue_list)."""
    __slots__ = ("sp", "blk", "llb")

    def __init__(self, spine: tuple, blk: bool, llb: bool) -> None:
        self.sp, self.blk, self.llb = list(spine), blk, llb

    def state(self, leaf) -> tuple:
        return tuple(self.sp), leaf, self.blk, self.llb

    def pop(self) -> None:
        c = self.sp.pop()
        if c[0] == "L" and c[2]:
            self.blk = False

    def finish_empty(self) -> None:
        if self.blk and self.llb and self.sp and self.sp[-1][0] == "I":
            self.pop()
        self.blk = False

    def finish_list(self) -> None:
        self.finish_empty()
        if self.sp and self.sp[-1][0] == "L":
            self.pop()
        if self.llb:
            if len(self.sp) >= 2 and self.sp[-2][0] == "L":
                self.sp[-2] = ("L", self.sp[-2][1], False)
            self.llb = False

    def continue_list(self, ch: str) -> None:
        self.finish_empty()
        if self.sp:
            top = self.sp[-1]
            if top[0] == "L" and top[1] == ch:
                if self.llb:
                    self.sp[-1] = ("L", ch, False)
                    self.llb = False
                return
            self.finish_list()
        self.sp.append(("L", ch, True))
        self.llb = False


def _md_start(spine: tuple, blk: bool, llb: bool, line: str, lid) -> list:
    """parse_block: a line read where no leaf is open, as [(state, code)];
    code is (the column its code starts at, rustdoc's mode) or None."""
    st = _MdBuild(spine, blk, llb)
    ls = _MdLine(line)
    i = _md_match(spine, ls)
    while len(st.sp) > i:
        st.pop()
    while True:
        save = ls.copy()
        if ls.upto(4) < 4:
            j = _md_footnote(line, ls.ix)
            if j is not None:
                st.finish_list()
                if st.sp and st.sp[-1][0] == "N":
                    st.pop()
                st.sp.append(("N",))
                ls = _MdLine(line, j)
                continue
        ls.restore(save)
        marker = ls.list_marker()
        if marker is not None:
            st.continue_list(marker[0])
            st.sp.append(("I", marker[2]))
            if _md_blank(line[ls.ix:]) or (ls.task() and _md_blank(line[ls.ix:])):
                st.blk = True
                return [(st.state(None), None)]
            continue
        if ls.quote():
            st.finish_list()
            st.sp.append(("Q",))
            continue
        break
    if _md_blank(line[ls.ix:]):
        if st.sp:
            top = st.sp[-1]
            if top[0] == "I" and st.blk:
                st.llb = True
                st.sp[-1] = ("I", 0)
            elif top[0] != "Q":
                st.llb = True
        return [(st.state(None), None)]
    st.finish_list()
    indent = ls.upto(4)
    if indent == 4:
        st.llb = False
        return [(st.state(("C", lid)), (ls.ix, "run"))]
    s = line[ls.ix:]
    out = []
    if s.startswith("<"):
        end = _md_html_end(s[1:])
        if end is not None:
            return [(st.state(None if end in s else ("H", end)), None)]
        if _md_html6(s[1:]):
            return [(st.state(("H6",)), None)]
        if _MD_HTML7.match(s) and s.rstrip(_MD_WS).endswith(">"):
            out.append((st.state(("H6",)), None))  # type 7 when its tag scans: both
    if _md_hrule(s) or _md_atx(s):
        return [(st.state(None), None)]
    fence = _md_fence(s)
    if fence is not None:
        mode = _rustdoc_block(_md_info(s[fence[1]:]))
        return [(st.state(("F", fence[0], fence[1], indent, mode, lid)), None)]
    out.append((st.state(("P", s.startswith("["))), None))
    if "|" in s:
        out.append((st.state(("TH",)), None))
    return out


def _md_step(md: tuple, line: str, lid) -> list:
    """Read one line of a doc from the state `md`: every state it may leave,
    with the column its code starts at and rustdoc's mode, or None."""
    spine, leaf, blk, llb = md
    if leaf is None:
        return _md_start(spine, blk, llb, line, lid)
    kind = leaf[0]
    ls = _MdLine(line)
    n = _md_match(spine, ls)
    if kind == "F":
        if n < len(spine):
            return _md_start(spine, blk, llb, line, lid)
        ls.space(leaf[3])
        close = ls.copy()
        if not close.space(4 - leaf[3]) and _md_closes(line[close.ix:], leaf[1], leaf[2]):
            return [((spine, None, blk, llb), None)]
        return [(md, (ls.ix, leaf[4]))]
    if kind == "C":
        if n < len(spine) or not (ls.space(4) or ls.eol()):
            return _md_start(spine, blk, llb, line, lid)
        return [((spine, leaf, blk, _md_blank(line[ls.ix:])), (ls.ix, "run"))]
    if kind == "H":
        if n < len(spine):
            return _md_start(spine, blk, llb, line, lid)
        return [((spine, None if leaf[1] in line[ls.ix:] else leaf, blk, llb), None)]
    if kind == "H6":
        if n < len(spine) or _md_blank(line[ls.ix:]):
            return _md_start(spine, blk, llb, line, lid)
        return [(md, None)]
    if kind == "TH":
        if n < len(spine) or not _md_table_head(line[ls.ix:]):
            return []  # no table: the paragraph's own reading goes on
        return [((spine, ("T",), blk, llb), None)]
    if kind == "T":
        if n < len(spine):
            return _md_start(spine, blk, llb, line, lid)
        ls.all_space()
        s = line[ls.ix:]
        if _md_interrupts(s, True, True) or _md_blank(s[1:] if s.startswith("|") else s):
            return _md_start(spine, blk, llb, line, lid)
        return [(md, None)]
    # A paragraph (parse_paragraph): a setext underline or an interrupting
    # line ends it, a blank line too; any other line is its text, lazily when
    # its containers do not all go on. One that may be a link reference
    # definition may also go on through either (its title spans lines).
    out: list = []
    again = False
    if not ls.space(4):
        s = line[ls.ix:]
        if n == len(spine) and _md_setext(s):
            out.append(((spine, None, blk, llb), None))
            if not leaf[1]:
                return out
        else:
            cut = _md_interrupts(s, n == len(spine), False)
            if cut:
                out += _md_start(spine, blk, llb, line, lid)
                again = True
                if cut is True and not leaf[1]:
                    return out
    ls.all_space()
    if ls.eol():
        return out if again else out + _md_start(spine, blk, llb, line, lid)
    return out + [(md, None)]


@dataclass
class DoctestViews:
    """The doctests of one Rust file, by the file their code sits in (the file
    itself, a doc file a `doc = include_str!(..)` attribute pulls in, or the
    file whose outer doc of a module its file's doc goes on): `run` is the
    code of those rustdoc compiles and runs, `compile` that of `no_run` and
    `compile_fail` ones, each as views of that file's text with everything
    else blanked (line numbers are the file's own, and offsets but where a
    view opens with the rest of a literal or comment, _doc_views). A file
    has more than one view where the row spans of two blocks overlap, where
    a block's code does not close lexically (an open string or comment would
    hide the code after it), or where it crosses into another file or row
    inside a literal or comment. `blind` (file, line, why): doctest code no
    view can place."""
    run: Dict[str, List[str]]
    compile: Dict[str, List[str]]
    blind: List[Tuple[str, int, str]]


def _attr_close(code: str, open_bracket: int) -> int:
    """The end of the attribute whose `[` is at `open_bracket` in a lexed
    file's code (literals and comments blanked): after its `]`, or the file's
    end."""
    depth = 0
    for m in BRACKET.finditer(code, open_bracket):
        if m.group(0) in "([{":
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                return m.end()
    return len(code)


def _arg_end(code: str, start: int, stop: int) -> int:
    """Where the macro or attribute argument starting at `start` ends: the
    next `,` or closing bracket at its own depth, or `stop`."""
    depth = 0
    for m in ARG_DELIM.finditer(code, start, stop):
        c = m.group(0)
        if c in "([{":
            depth += 1
        elif depth == 0:
            return m.start()
        elif c != ",":
            depth -= 1
    return stop


def _literal_value(text: str, s: int, body: str) -> Tuple[str, Optional[int]]:
    """A string literal's value, and where its body starts in `text` when each
    character of the value is that character of the source (a raw string, or
    a plain one without escapes); None otherwise."""
    if text[s] == '"':
        return (_unescape(body), None) if "\\" in body else (body, s + 1)
    if text[s] == "r" or text[s:s + 2] in ("br", "cr"):
        return body, text.index('"', s) + 1
    return _unescape(body), None


def _doc_include_targets(g: "Graph", pkg: "Package", path: str, text: str, lx, start: int, stop: int
                         ) -> Optional[List[str]]:
    """The tracked regular files a `doc = include_str!(..)` value at
    text[start:stop] may name (any delimiter, DOC_INCLUDE): one for a literal
    (or a manifest-dir concat!), every file a concat! pattern matches (each
    argument that is not a literal a wildcard), and for any other argument (a
    macro parameter) each path-like literal of the file that names one, as
    _scan_file resolves an include. None when it names none."""
    fdir = posixpath.dirname(path)
    opened = DOC_INCLUDE.match(lx.code, start, stop)
    open_paren = opened.end() - 1 if opened else lx.code.index("(", start)
    tail = text[open_paren + 1: open_paren + 401]
    lit = ARG_LIT.match(tail)
    man = ARG_MANIFEST.match(tail)
    cands: List[Optional[str]] = []
    if lit:
        cands = [_norm(fdir, _unescape(lit.group(1)))]
    elif man and man.group(2) != ",":
        cands = [_norm(pkg.dir, _unescape(man.group(1)).lstrip("/"))]
    elif re.match(r'\s*concat\s*!\s*[(\[{]', tail):
        inner = re.compile(r'[(\[{]').search(lx.code, open_paren + 1 + tail.index("concat")).end()
        end = _arg_end(lx.code, inner, stop)
        while end < stop and lx.code[end] == ",":
            end = _arg_end(lx.code, end + 1, stop)
        strings = {s: b for s, e, b in lx.strings if inner <= s < end}
        ends = {s: e for s, e, b in lx.strings if inner <= s < end}
        pattern: List[str] = []
        base, pos = fdir, inner
        while pos < end:
            arg_end = _arg_end(lx.code, pos, end)
            raw = text[pos:arg_end]
            lead = pos + len(raw) - len(raw.lstrip())
            if lead in strings and not lx.code[ends[lead]:arg_end].strip():
                pattern.append(_literal_value(text, lead, strings[lead])[0])
            elif not pattern and re.fullmatch(r'env\s*!\s*[(\[{]\s*"CARGO_MANIFEST_DIR"\s*[)\]}]', raw.strip()):
                base = pkg.dir
            elif raw.strip():
                pattern.append("*")
            pos = arg_end + 1
        joined = "".join(pattern)
        glob = _norm(base, joined.lstrip("/") if base == pkg.dir else joined)
        if glob is not None and "*" not in glob.split("/", 1)[0] and glob:
            cands = [p for p, (mode, _) in g.index.entries.items()
                     if mode in ("100644", "100755") and fnmatch.fnmatchcase(p, glob)]
    else:
        for s, e, v in lx.strings:
            v = _unescape(v)
            if _pathlike(v):
                cands += [_norm(fdir, v), _norm(pkg.dir, v)]
    found = sorted({c for c in cands if c is not None and g.index.entries.get(c, ("",))[0] in ("100644", "100755")})
    return found or None


def _rust_lines(data: str, off: Optional[int]) -> List[Tuple[Optional[int], str]]:
    """str::lines with each line's offset (off + its index in data, or None):
    split at "\\n", a "\\r" before it dropped, no line after a final one."""
    out: List[Tuple[Optional[int], str]] = []
    pos = 0
    while pos < len(data):
        j = data.find("\n", pos)
        line = data[pos:] if j < 0 else data[pos:j].removesuffix("\r")
        out.append((None if off is None else off + pos, line))
        pos = len(data) if j < 0 else j + 1
    return out


def _horizontal_trim(lines: List[str], block: bool) -> Optional[str]:
    """beautify_doc_string's get_horizontal_trim: the `[ \\t]*` before a `*`
    that stands in one column on every line (a block comment's first line,
    and its blank lines at either end, aside), or None."""
    if block:
        i = 0 if not lines or lines[0].lstrip(_RUST_WS).startswith("*") else 1
        j = len(lines)
        while i < j and not lines[i].strip(_RUST_WS):
            i += 1
        while j > i and not lines[j - 1].strip(_RUST_WS):
            j -= 1
        lines = lines[i:j]
    col: Optional[int] = None
    for line in lines:
        for j, c in enumerate(line):
            if (col is not None and j > col) or c not in "* \t":
                return None
            if c == "*":
                if col is None:
                    col = j
                elif col != j:
                    return None
                break
        if col is None or col >= len(line.encode()):
            return None
    return lines[0][:col] if lines else None


def _doc_lines(data: str, file: str, off: Optional[int], at: int, block: bool
               ) -> Tuple[Tuple[str, Optional[int], str, int], ...]:
    """A doc fragment's lines as rustdoc's add_doc_fragment reads them, after
    beautify_doc_string (`block`: a `/** */` or `/*! */` comment; a raw value
    is read as a line comment): a first line of stars, and a last, dropped;
    a `[ \\t]*\\*` decoration in one column stripped, and of a block comment
    one more `*` where `* ` or `**` follows it, the rest of the line's text
    kept as written (until review 4 every starred line lost its `*` and the
    blank after it). Each (file, offset of the text in file or None, text,
    `at`: where the fragment stands in its own file)."""
    lines = _rust_lines(data, off)
    if "\n" in data:
        changed = False
        i, j = 0, len(lines)
        if lines and all(c == "*" for c in lines[0][1]):
            i = 1
        if j > i and lines[j - 1][1] and all(c == "*" for c in lines[j - 1][1]):
            j -= 1
        if i or j != len(lines):
            changed, lines = True, lines[i:j]
        prefix = _horizontal_trim([t for _o, t in lines], block)
        if prefix is not None:
            changed = True
            trimmed = []
            for o, t in lines:
                if t.startswith(prefix):
                    k = len(prefix)
                    if block and (t[k:] == "*" or t[k:].startswith(("* ", "**"))):
                        k += 1
                    t, o = t[k:], None if o is None else o + k
                trimmed.append((o, t))
            lines = trimmed
        if changed and len(lines) > 1 and lines[-1][1] == "":
            lines = lines[:-1]  # joined and split again: no line after a final newline
    if not lines:
        return ((file, off, "", at),)  # an empty fragment is one empty line
    return tuple((file, o, t, at) for o, t in lines)


class _DocUnit:
    """One item's doc as rustdoc assembles it: `items` in source order, each
    (optional, fragments): a cfg_attr's values are optional, together; a
    fragment is (sugared, alternatives), each alternative its lines
    (_doc_lines), more than one for a doc file an include may name.
    `leading`: the inner doc a file opens with, which a module's outer doc
    elsewhere may go before; `mod_pos`: where the `mod` keyword of the file
    module this outer doc is on stands."""
    __slots__ = ("kind", "items", "start", "leading", "mod_pos")

    def __init__(self, kind: str, items: list, start: int, leading: bool = False) -> None:
        self.kind, self.items, self.start, self.leading, self.mod_pos = kind, items, start, leading, None


# What follows an outer doc: a file module (`mod x;`, a macro's `mod $x;`), or
# an item header whose block opens with the item's inner doc (`mod m {`, a
# function body, an impl, a trait, an extern block): rustdoc reads the outer
# doc and the inner one as one (HIR attributes: the outer, then the inner).
DOC_FILE_MOD = re.compile(r'\s*(?:pub\s*(?:\([^)]*\))?\s*)?(?:unsafe\s+)?(mod)\s+(?:r#)?(?:\w+|\$\w*)\s*;')
DOC_BLOCK_ITEM = re.compile(r'\b(?:mod|fn|impl|trait|extern)\b')


def _doc_blob_text(g: "Graph", path: str) -> str:
    cache = g.__dict__.setdefault("blob_cache", {})
    if path not in cache:
        cache.update(g.index.read_blobs([path]))
    return cache[path].decode("utf-8", "replace")


def _doc_attr_values(code: str, start: int, stop: int) -> List[int]:
    """Where each doc value of the attribute whose contents start at
    code[start] (a lexed file's; `stop` after its `]`) begins, after its `=`:
    the attribute's own where its path is `doc`, and each of a cfg_attr's
    payload after its predicate, nested ones too. A `doc =` among another
    attribute's arguments is none, as rustdoc reads it (until review 4 round
    2 `#[rustfmt::skip(doc = "```")]` was a doc fragment, which closed the
    doctest it stood in)."""
    m = DOC_ATTR_PATH.match(code, start, stop)
    if m is None:
        return []
    if m.group(1) == "doc":
        value = DOC_ATTR_VALUE.match(code, m.start(1), stop)
        return [value.end()] if value else []
    args = re.compile(r"\s*\(").match(code, m.end(), stop)
    if args is None:
        return []
    out: List[int] = []
    k = _arg_end(code, args.end(), stop)  # the predicate's end
    while k < stop and code[k] == ",":
        nxt = _arg_end(code, k + 1, stop)
        out += _doc_attr_values(code, k + 1, nxt)
        k = nxt
    return out


# The width rustc's pretty printer (rustc_ast_pretty::pp, MARGIN) fits on a
# line; stringify!'s text wraps past it (measured: 78 bytes stay one line).
_PP_MARGIN = 78
# Pattern_White_Space: what rustc's lexer skips between tokens.
_LEX_WS = "\t\n\x0b\x0c\r \x85\u200e\u200f\u2028\u2029"


def _is_doc_comment(body: str) -> bool:
    """Whether a comment's text is a doc comment to rustc."""
    return (body.startswith(("///", "//!", "/**", "/*!"))
            and not body.startswith(("////", "/***", "/**/")))


def _strung_lines_unknown(text: str, lx, a: int, b: int) -> bool:
    """Whether the text of the stringify! whose tokens are text[a:b] may not
    be the one line this scan makes of it: rustc keeps a literal's line
    breaks, drops a plain comment, prints a doc comment as a `#[doc = ..]`
    attribute (a `/** */` one with its line breaks), and wraps a text wider
    than _PP_MARGIN. Its text is never wider than its tokens as written, one
    blank between each two (review 4 round 3: `stringify!(r#"` with fence
    lines in it, a `/** */` with them, and `~~~ rust include_str!(..); ~~~`
    wider than the margin were read as one line, and their doctests missed)."""
    if len(text[a:b].encode("utf-8", "surrogatepass")) > _PP_MARGIN:
        return True
    if any(a <= s < b for s, _e in lx.comments):
        return True
    return any(a <= s < b and ("\n" in text[s:e] or "\r" in text[s:e]) for s, e, _v in lx.strings)


def _shebang_attr(text: str, lx, at: int) -> bool:
    """rustc's strip_shebang: whether the next token from text[at] (after a
    `#!`), past whitespace and comments that are no doc, however far, is `[`,
    so that the `#!` opens an inner attribute and no shebang line."""
    while True:
        while at < len(text) and text[at] in _LEX_WS:
            at += 1
        i = bisect.bisect_left(lx.comments, (at,))
        if not (i < len(lx.comments) and lx.comments[i][0] == at) or _is_doc_comment(text[at:lx.comments[i][1]]):
            return text.startswith("[", at)
        at = lx.comments[i][1]


def _doc_units(g: "Graph", pkg: "Package", path: str, text: str, lx
               ) -> Tuple[List[_DocUnit], Set[Tuple[str, int, str]]]:
    """Each item's doc in a lexed file (_DocUnit), and the blind rows of doc
    files an include names that the scan cannot and of values a macro it does
    not expand computes. An item's doc is its `///`
    or `//!` lines, `/** */` and `/*! */` blocks and `doc = ` attribute values
    in source order (an attribute between two doc comments, or in the item's
    header, does not end it; code between them, or a switch between inner
    and outer docs, starts another), and an outer doc goes on into the inner
    doc its item's block opens with. A leading U+FEFF and a shebang line are
    no code. The doc file a `doc = include_str!(..)` names is read in
    place; a computed or escaped value (concat!, stringify!, `\\"`) has no
    place in the file: its lines carry no offset; one any other macro
    computes is blind."""
    memo = g.__dict__.setdefault("_doc_units_memo", {})
    key = (pkg.dir, path, len(text), hash(text))
    if key in memo:
        return memo[key]
    blind: Set[Tuple[str, int, str]] = set()
    units: List[_DocUnit] = []
    frags: List[Tuple[int, int, str]] = [(s, e, "comment") for s, e in lx.comments]
    frags += [(m.start(), _attr_close(lx.code, m.end() - 1), "attr") for m in ATTR_OPEN.finditer(lx.code)]
    frags.sort()
    ordered = sorted(lx.strings)
    starts = [s for s, _e, _b in ordered]
    cur: List[_DocUnit] = []  # the units this fragment joins (an item header with `=` in it: both ways)
    after: List[_DocUnit] = []  # an outer doc before an item header `{`, which its inner doc joins
    held: List[_DocUnit] = []  # an outer doc whose item header an attribute stands in, and that header so far
    held_head = ""
    seen_code = False
    # rustc reads a file from after a leading U+FEFF, and after a shebang line
    # (`#!` with no `[` next): neither is code before the file's leading doc
    # (review 4 round 2: a module file opening with a BOM had none, so its doc
    # was read apart from the outer doc on its `mod x;`). The `[` is looked
    # for as rustc does, past any comment (round 3: only 4096 characters
    # were, so a longer comment before `[doc = ..]` made the inner doc the
    # shebang's line) but no doc comment (`#!/** x */[..]` is a shebang).
    skip = 1 if text.startswith("\ufeff") else 0
    if text.startswith("#!", skip) and not _shebang_attr(text, lx, skip + 2):
        line_end = text.find("\n", skip)
        skip = len(text) if line_end < 0 else line_end
    prev, covered = skip, skip

    def code_after(at: int, upto: int, attr: bool) -> None:
        """Code between docs: a file module or an item header after an outer
        doc, and the end of the current doc. `attr`: an attribute that is no
        doc follows, which may stand inside the header."""
        nonlocal cur, after, seen_code, held, held_head
        between = lx.code[at:upto]
        if not between.strip():
            return
        seen_code = True
        outer = [u for u in cur if u.kind == "outer"]
        head, split = between.strip(), False
        if not outer and held:
            outer, head, split = held, held_head + " " + head, True
        after, held = [], []
        if outer:
            m = DOC_FILE_MOD.match(between)
            if m and not split:
                for u in outer:
                    u.mod_pos = at + m.start(1)
            if head.endswith("{") and DOC_BLOCK_ITEM.search(head):
                # A header this cannot read for certain (`fn f(x: [u8; 4]) {`,
                # `impl X<{ N }> {`, a `=`, an attribute in it): the inner doc
                # joins it, and not.
                plain = not split and head.count("{") == 1 and not any(c in head for c in ";}=")
                after = [(u, not plain) for u in outer]
            elif attr and not head.endswith(("{", ";", "}")):
                # An attribute in the header (a parameter's, a generic
                # parameter's: `fn f(#[a] x: u8) {`): the header goes on after
                # it (until review 4 round 2 the inner doc was read alone).
                held, held_head = outer, head
        cur = []

    for start, end, kind in frags:
        if start < covered:
            continue  # inside an attribute already read
        if kind == "comment":
            body = text[start:end]
            if body.startswith(("///", "//!")) and not body.startswith("////"):
                found = [(False, [(True, (_doc_lines(body[3:].removesuffix("\r"), path, start + 3, start, False),))])]
            elif body.startswith(("/**", "/*!")) and not body.startswith(("/***", "/**/")):
                data = body[3:-2] if len(body) >= 5 and body.endswith("*/") else body[3:]
                found = [(False, [(True, (_doc_lines(data, path, start + 3, start, True),))])]
            else:
                continue  # a plain comment is no doc text, and no code
            style = "inner" if text[start + 2] == "!" else "outer"
        else:
            covered = end
            open_bracket = lx.code.index("[", start)
            style = "inner" if "!" in lx.code[start:open_bracket] else "outer"
            values: List[tuple] = []
            for value_at in _doc_attr_values(lx.code, open_bracket + 1, end):
                v0 = _next_token(lx, value_at)
                i = bisect.bisect_left(starts, v0)
                lit = ordered[i] if i < len(ordered) and starts[i] == v0 else None
                if lit is not None and not lx.code[lit[1]:_arg_end(lx.code, lit[1], end)].strip():
                    value, body_start = _literal_value(text, v0, lit[2])
                    values.append((False, (_doc_lines(value, path, body_start, v0, False),)))
                    continue
                stop = _arg_end(lx.code, v0, end)
                if DOC_INCLUDE.match(lx.code, v0, stop):
                    targets = _doc_include_targets(g, pkg, path, text, lx, v0, stop)
                    if targets is None:
                        blind.add((path, _line_of(text, v0), "the doctests of a doc file this scan cannot name"))
                        continue
                    values.append((False, tuple(_doc_lines(_doc_blob_text(g, t), t, 0, v0, False)
                                                for t in targets)))
                    continue
                # The text: its literals' values, and a stringify!'s tokens as
                # written, on one line (until review 4 round 2 only the
                # literals in them: `stringify!(std::env::current_dir())` was
                # an empty doc).
                strung: List[Tuple[int, int]] = []
                called: Set[str] = set()
                for m in DOC_MACRO_CALL.finditer(lx.code, v0, stop):
                    if strung and m.start() < strung[-1][1]:
                        continue  # a stringify!'s tokens
                    prefix = re.sub(r"\s|r#", "", m.group(1))
                    name = m.group(2) if prefix in STD_MACRO_PATHS else prefix + m.group(2)
                    if name == "stringify":
                        strung.append((m.end(), _attr_close(lx.code, m.end() - 1) - 1))
                    called.add(name)
                if called - {"concat", "stringify"}:
                    # A macro this scan does not expand (`readme!()`, `env!`,
                    # an include_str! in a concat!): its text is unknown
                    # (review 4 round 2: `#[doc = readme!()]` was an empty doc).
                    blind.add((path, _line_of(text, v0), "the doctests of a doc value a macro this scan does not "
                                                         "expand computes"))
                    continue
                if any(_strung_lines_unknown(text, lx, a, b) for a, b in strung):
                    blind.add((path, _line_of(text, v0), "the doctests of a stringify! doc value whose lines this "
                                                         "scan cannot tell"))
                    continue
                pieces = [(a, " ".join(text[a:b].split())) for a, b in strung]
                j = bisect.bisect_left(starts, v0)
                while j < len(ordered) and ordered[j][0] < stop:
                    if not any(a <= ordered[j][0] < b for a, b in strung):
                        pieces.append((ordered[j][0], _literal_value(text, ordered[j][0], ordered[j][2])[0]))
                    j += 1
                values.append((False, (_doc_lines("".join(t for _a, t in sorted(pieces)), path, None, v0, False),)))
            if DOC_CFG_ATTR.match(lx.code, open_bracket + 1):
                # On a predicate this scan does not evaluate: present or not,
                # its values together (each alone under a nested cfg_attr).
                nested = lx.code.count("cfg_attr", open_bracket, end) > 1
                found = [(True, [v]) for v in values] if nested else ([(True, values)] if values else [])
            else:
                found = [(False, [v]) for v in values]
        code_after(prev, start, kind == "attr" and not found)
        prev = max(prev, end)
        if not found:
            continue  # an attribute that is no doc ends no doc
        if not cur or cur[0].kind != style:
            if style == "inner" and after and not cur:
                cur = []
                for u, both in after:
                    if both:
                        cur.append(_DocUnit("inner", [], start))
                        units.append(cur[-1])
                        u = _DocUnit("inner", list(u.items), u.start)
                        units.append(u)
                    u.kind = "inner"
                    cur.append(u)
            else:
                cur = [_DocUnit(style, [], start, leading=style == "inner" and not seen_code and not units)]
                units.append(cur[0])
            after = []
        for u in cur:
            u.items.extend(found)
    code_after(prev, len(lx.code), False)
    memo[key] = (units, blind)
    return units, blind


_MD_MAX = 1 << 30
_DOC_READINGS = 512  # readings of one doc at once; past them every line is code


class _DocTooMany(Exception):
    pass


def _doc_variants(items: list, loose: bool) -> List[Tuple[int, int]]:
    """unindent_doc_fragments: the (least indent, add) pairs a reading of the
    fragments may take. The least indent is that of every line holding a
    character that is not whitespace (Rust's char::is_whitespace), in spaces
    and tabs, a raw value's one more (`add`) when the doc mixes sugared and
    raw fragments; each fragment loses it (a raw one, `add` less). With
    cfg_attr values each subset the predicates may leave is a doc: each least
    indent one may have. `loose`: a doc this scan does not see may join this
    one (a module's outer doc): every least indent up to its own."""
    frags = [(optional, f) for optional, fs in items for f in fs]
    sugared = {f[0] for _o, f in frags}
    required = {f[0] for o, f in frags if not o}
    if loose:
        adds = (0, 1)
    elif sugared == {True, False}:
        adds = (1,) if required == {True, False} else (0, 1)
    else:
        adds = (0,)
    out: Set[Tuple[int, int]] = set()
    for add in adds:
        cands: Set[int] = set()
        bound = _MD_MAX
        for optional, (is_sugared, alts) in frags:
            least = [min((len(t) - len(t.lstrip(" \t")) + (0 if is_sugared else add)
                          for _f, _o, t, _a in alt if t.strip(_RUST_WS)), default=_MD_MAX) for alt in alts]
            cands.update(least)
            if not optional:
                bound = min(bound, max(least))
        levels = {c for c in cands if c <= bound} | {bound}
        if loose:
            top = bound if bound < _MD_MAX else max((c for c in cands if c < _MD_MAX), default=0)
            levels |= set(range(top + 1))
        out.update((level, add) for level in levels)
    return sorted(out)


def _read_doc(items: list, starts: Iterable[tuple], variants: List[Tuple[int, int]],
              blocks: Set[tuple], blind: Set[Tuple[str, int, str]], text_of: Callable[[str], str]) -> Set:
    """Read one doc (a _DocUnit's items) as rustdoc does, from each start
    state, under each (least indent, add) variant, each cfg_attr item present
    and not: the code blocks every reading finds go to `blocks` as (mode,
    ((file, offset, code), ...)); a line of a computed value read as code that
    the scan's prefilter matches, to `blind`. Returns the states the readings
    end in (None: this port read every line as code)."""
    lines = [ln for _o, fs in items for f in fs for alt in f[1] for ln in alt]

    def every_line() -> None:
        for ln in lines:
            _doc_code(("C", ln), ((ln[0], ln[1], ln[2], ln[3]),), blocks, blind, text_of)
            if DOCTEST_SCAN.search(ln[2]):
                # Each line is lexed alone, without the literals and comments
                # the lines around it open: blind where the prefilter matches
                # (review 4 round 3: `let s = "` hid the next line's include).
                blind.add((ln[0], _line_of(text_of(ln[0]), ln[3]), "doctest code in a doc read with every line code"))

    if any("\r" in ln[2] for ln in lines):
        # A lone carriage return (a doc file's): pulldown-cmark ends a line
        # there except in a code block. Every line is code.
        every_line()
        return {None}
    ends: Set = set()
    for least, add in variants:
        readings: Dict[tuple, tuple] = {(s, None): ((),) for s in starts}
        try:
            for optional, frs in items:
                fed = readings
                for is_sugared, alts in frs:
                    cut = least - add if (not is_sugared and least > 0) else least
                    out: Dict[tuple, tuple] = {}
                    for alt in alts:
                        cur = fed
                        for file, off, t, at in alt:
                            if t.strip(_RUST_WS):
                                k = min(cut, len(t) - len(t.lstrip(" \t")))
                                t, off = t[k:], None if off is None else off + k
                            cur = _doc_feed(cur, (file, off, t, at), blocks, blind, text_of)
                        _doc_merge(out, cur)
                    fed = out
                if optional:
                    readings = dict(readings)
                    _doc_merge(readings, fed)
                else:
                    readings = fed
        except _DocTooMany:
            every_line()
            ends.add(None)
            continue
        for (md, key), codes in readings.items():
            for code in codes:
                _doc_code(key, code, blocks, blind, text_of)
            ends.add(md)
    return ends


def _doc_merge(into: Dict[tuple, tuple], readings: Dict[tuple, tuple]) -> None:
    """Add readings to `into`: one entry per (state, open block), each with
    the lines that block may hold so far, one tuple per reading."""
    for k, codes in readings.items():
        have = into.get(k)
        if have is None:
            into[k] = codes
        elif have is not codes:
            into[k] = have + tuple(c for c in codes if c not in have)


def _doc_feed(readings: Dict[tuple, tuple], line: tuple, blocks: Set[tuple], blind: Set[Tuple[str, int, str]],
              text_of: Callable[[str], str]) -> Dict[tuple, tuple]:
    """Each reading (state, its open code block's leaf: the lines that block
    holds so far) after one more line of the doc."""
    file, off, t, at = line
    out: Dict[tuple, tuple] = {}
    for (md, key), codes in readings.items():
        for md2, hit in _md_step(md, t, (file, off, at, t)):
            leaf = md2[1]
            key2 = leaf if leaf is not None and (leaf[0] == "C" or (leaf[0] == "F" and leaf[4])) else None
            now = codes
            if key2 != key:
                for code in codes:
                    _doc_code(key, code, blocks, blind, text_of)
                now = ((),)
            if hit is not None and key2 is not None and t[hit[0]:].strip():
                ln = (file, off, t[hit[0]:], at) if off is None else (file, off + hit[0], t[hit[0]:], at)
                now = tuple(code + (ln,) for code in now)
            _doc_merge(out, {(md2, key2): now})
    if len(out) > _DOC_READINGS:
        raise _DocTooMany
    return out


# What may open or close a literal or comment in a doctest's line.
_DOC_TOKEN_CHARS = ('"', "'", "/*", "*/", "#")


def _doc_code(key, code: tuple, blocks: Set[tuple], blind: Set[Tuple[str, int, str]],
              text_of: Callable[[str], str]) -> None:
    """A finished code block: its placed lines to `blocks` (each at its first
    character that is not a blank, so that readings that cut a line
    differently place the same code), its computed ones to `blind` where the
    scan's prefilter matches them or a literal or comment crosses them."""
    if key is None or not code:
        return
    mode = "run" if key[0] == "C" else key[4]
    placed = []
    crossing = False  # a computed line holds what may open or close a literal or comment
    for file, off, c, at in code:
        if off is None:
            if DOCTEST_SCAN.search(c):
                blind.add((file, _line_of(text_of(file), at), "doctest code in a computed or escaped #[doc] value"))
            crossing = crossing or any(q in c for q in _DOC_TOKEN_CHARS)
            continue
        lead = len(c) - len(c.lstrip(" \t"))
        placed.append((file, off + lead, c[lead:]))
    if placed and crossing:
        # The views leave a computed line out, so a literal or comment that
        # crosses into or out of it in the block's text (rustdoc's: every
        # line joined) is lexed wrong across the placed lines: blind (review
        # 4 round 3: `let s = "`, then `#[doc = "\";"]`, hid the include_str!
        # line after it in a string). One whose literals and comments all
        # close on it changes nothing.
        from rust_lex import lex
        lines = [_doctest_line(c)[1] for _f, _o, c, _a in code]
        lx = lex("\n".join(lines) + "\n;x")
        tokens = [(s, e) for s, e, _v in lx.strings] + lx.comments
        pos = 0
        for (file, off, _c, at), c in zip(code, lines):
            end = pos + len(c)
            if off is None and any(q in c for q in _DOC_TOKEN_CHARS) and any(
                    s < pos < e or s < end < e for s, e in tokens):
                blind.add((file, _line_of(text_of(file), at),
                           "doctest code a computed or escaped #[doc] value may open or close a literal or comment in"))
                break
            pos = end + 1
    if placed:
        blocks.add((mode, tuple(placed)))


def _doctest_line(c: str) -> Tuple[int, str]:
    """The code rustdoc compiles for one line of a doctest (map_line): `# x`
    is x (hidden on the page), `#` alone nothing, `##x` is `#x`; as (where in
    the line it starts, its text)."""
    trimmed = c.strip(_RUST_WS)
    lead = len(c) - len(c.lstrip(_RUST_WS))
    if trimmed.startswith("##"):
        return lead + 1, c[lead + 1:]
    if trimmed.startswith("# "):
        return lead + 2, c[lead + 2:]
    if trimmed == "#":
        return 0, ""
    return 0, c


def _doc_views(blocks: Set[tuple], text_of: Callable[[str], str]
               ) -> Tuple[Dict[str, List[str]], Dict[str, List[str]]]:
    """Place each code block in views of the files its lines sit in, each
    view lexing as rustdoc's text of every block in it. A block is lexed as
    one text (rustdoc's: its lines joined) and cut into runs where a line is
    in another file or stands no lower in it than the line before (two doc
    fragments on one row are two lines). A run that starts or ends inside a
    literal or comment of that text has a view of its own, the rest of that
    token before it (at the view's start) and after it (at its end), its
    newlines blanks: a string a module's outer doc opens closes in its file's
    doc as in the doctest. A block's other runs in one file are a part, put
    in the first view of the file where its row span [first, last] overlaps
    no other part's and both close lexically, or a new one. (Until review 4
    round 2 each file's part was lexed alone, two fragments on one row were
    one line, and parts shared a view where only their rows differed: a
    block whose `/*` and `*/` rows enclosed another block's row hid it.)"""
    from rust_lex import lex
    views: Dict[Tuple[str, str], List[list]] = {}
    newlines: Dict[str, List[int]] = {}
    blank: Dict[str, str] = {}

    def row(file: str, off: int) -> int:
        if file not in newlines:
            newlines[file] = [i for i, ch in enumerate(text_of(file)) if ch == "\n"]
        return bisect.bisect_left(newlines[file], off)

    def place(mode: str, file: str, part: List[Tuple[int, str]], closed: bool, ends: Tuple[str, str]) -> None:
        """Put a part in a view: [text, span starts, span ends, open to others, (prefix, suffix)]."""
        lo, hi = row(file, part[0][0]), row(file, part[-1][0])
        mine = views.setdefault((mode, file), [])
        for view in mine:
            i = bisect.bisect_right(view[1], hi)
            if closed and view[3] and not (i and view[2][i - 1] >= lo):
                break
        else:
            if file not in blank:
                blank[file] = re.sub(r"[^\n]", " ", text_of(file))
            view = [list(blank[file]), [], [], closed and ends == ("", ""), ends]
            mine.append(view)
        i = bisect.bisect_right(view[1], hi)
        view[1].insert(i, lo)
        view[2].insert(i, hi)
        for off, c in part:
            view[0][off:off + len(c)] = c

    for mode, code in sorted(blocks):
        lines = []
        for file, off, c in code:
            k, c = _doctest_line(c)
            if c.strip():
                lines.append((file, off + k, c))
        if not lines:
            continue
        joined = "\n".join(c for _f, _o, c in lines)
        if any(q in joined for q in ('"', "'", "/*")):
            lx = lex(joined + "\n;x")
            tokens = sorted([(s, e) for s, e, _v in lx.strings] + list(lx.comments))
            whole = lx.code.endswith(";x")
        else:
            tokens, whole = [], True  # no token here holds a newline
        token_starts = [s for s, _e in tokens]

        def token_at(b: int) -> Optional[Tuple[int, int]]:
            i = bisect.bisect_right(token_starts, b) - 1
            return tokens[i] if i >= 0 and tokens[i][1] > b else None

        runs: List[list] = []  # [file, lines, start in joined]
        pos, last = 0, -1
        for file, off, c in lines:
            r = row(file, off)
            if not runs or runs[-1][0] != file or r <= last:
                runs.append([file, [], pos])
            runs[-1][1].append((off, c))
            pos, last = pos + len(c) + 1, r
        parts: Dict[str, List[list]] = {}
        for i, (file, run_lines, start) in enumerate(runs):
            before = token_at(start - 1) if i else None
            end = runs[i + 1][2] - 1 if i + 1 < len(runs) else len(joined)
            after = token_at(end) if i + 1 < len(runs) else None
            closed = whole if i + 1 == len(runs) else after is None
            if before or after:
                ends = (joined[before[0]:start].replace("\n", " ") if before else "",
                        joined[end:min(after[1], len(joined))].replace("\n", " ") if after else "")
                place(mode, file, run_lines, False, ends)
                continue
            mine = parts.setdefault(file, [])
            if mine and row(file, mine[-1][0][-1][0]) < row(file, run_lines[0][0]):
                mine[-1][0] += run_lines
                mine[-1][1] = mine[-1][1] and closed
            else:
                mine.append([list(run_lines), closed])
        for file, mine in sorted(parts.items()):
            for part, closed in mine:
                place(mode, file, part, closed, ("", ""))
    run: Dict[str, List[str]] = {}
    compiled: Dict[str, List[str]] = {}
    for (mode, file), mine in sorted(views.items()):
        (run if mode == "run" else compiled)[file] = [v[4][0] + "".join(v[0]) + v[4][1] for v in mine]
    return run, compiled


def _md_joinable(end) -> bool:
    """Whether a module's outer doc that ends in state `end` leaves its file's
    doc as one of _MD_JOINABLE does."""
    return end is not None and end[0] == () and (end[1] is None or end[1][0] in ("P", "TH"))


def _leading_doc(g: "Graph", pkg: "Package", path: str) -> Optional[_DocUnit]:
    """The inner doc the file `path` opens with, if any."""
    text = _doc_blob_text(g, path)
    units = _doc_units(g, pkg, path, text, _lexed(g, path, text))[0]
    return units[0] if units and units[0].leading else None


def _module_doc_files(g: "Graph", path: str, text: str, lx, pos: int) -> Optional[List[str]]:
    """The tracked files the file module whose `mod` keyword stands at `pos`
    may take (_module_items, from the file's directory or its stem's, a link
    read through), or None when this scan cannot tell them."""
    fdir = posixpath.dirname(path)
    bases = (fdir, posixpath.join(fdir, posixpath.splitext(posixpath.basename(path))[0]))
    for at, name, attrs, chains in _module_items(lx, text):
        if at != pos:
            continue
        if None in attrs or chains is None:
            return None
        found = {t for rel in _module_rels(name, attrs, chains) for b in bases
                 for t in (_norm(b, rel), _realpath(g, b, rel)) if t and g.index.entries.get(t, ("",))[0] in REGULAR}
        return sorted(found) or None
    return None


def _module_declarers(pkg: "Package", path: str) -> List[str]:
    """The files that may hold the `mod` item of the module file `path`
    (_module_items, read through inline modules): each mod.rs, lib.rs and
    main.rs from its directory up to its package's, and each `<dir>.rs` in
    between. (_parent_candidates, the direct ones alone, misses `mod a { mod
    x; }`.)"""
    d, base = posixpath.split(path)
    if base == "mod.rs":
        d = posixpath.dirname(d)
    parts = d.split("/") if d else []
    top = len(pkg.dir.split("/")) if pkg.dir else 0
    out: List[str] = []
    for i in range(len(parts), min(top, len(parts)) - 1, -1):
        pre = "/".join(parts[:i])
        out += [posixpath.join(pre, n) for n in ("mod.rs", "lib.rs", "main.rs")]
        if i > top:
            out.append(pre + ".rs")
    return [p for p in out if p != path]


def _module_decl_docs(g: "Graph", pkg: "Package", path: str) -> Tuple[List[Tuple[str, _DocUnit]], bool]:
    """The outer docs on the `mod` items that may declare the module file
    `path`, in each file that may hold one (_module_declarers, in any
    spelling the landing host opens one by, a link read through) and each
    file such a file include!s, to a fixed point: an item whose file this
    scan cannot tell may take this one. And whether one of those files
    include!s a file this scan cannot name, whose `mod` item may be this
    module's. A module a path attribute names from elsewhere is read there
    (that file is scanned: it spells `path`)."""
    d, base = posixpath.split(path)
    stem = posixpath.basename(d) if base == "mod.rs" else posixpath.splitext(base)[0]
    spellings = _index_spellings(g)
    entries = g.index.entries
    links = _link_texts(g)

    def regular(spelt: str) -> Optional[str]:
        real: Optional[str] = spelt
        if entries.get(spelt, ("",))[0] == "120000":
            real = _realpath(g, posixpath.dirname(spelt), links[spelt])
        return real if real is not None and entries.get(real, ("",))[0] in REGULAR else None

    def bases_of(spelt: str) -> Tuple[str, str]:
        pdir = posixpath.dirname(spelt)
        return pdir, posixpath.join(pdir, posixpath.splitext(posixpath.basename(spelt))[0])

    todo = [(q, bases_of(q)) for q in sorted({q for c in _module_declarers(pkg, path)
                                               for q in spellings.get(fold(c), ()) if q in entries})]
    missing = [r for r in {regular(q) for q, _b in todo} if r and r not in g.blob_cache]
    g.blob_cache.update(g.index.read_blobs(sorted(missing)))
    out: List[Tuple[str, _DocUnit]] = []
    unsure = False
    seen: Set[Tuple[str, Tuple[str, ...]]] = set()
    while todo:
        p, bases = todo.pop()
        real = regular(p)
        if real is None or (real, bases) in seen:
            continue
        seen.add((real, bases))
        ptext = _doc_blob_text(g, real)
        if "mod" not in ptext and "include" not in ptext:
            continue
        plx = _lexed(g, real, ptext)
        for m in _include_calls(plx):
            if not _includes_source(m):
                continue
            kind, value = _include_arg(plx, ptext, m.end())
            if kind == "file" and value is not None:
                named = {t for t in (_norm(posixpath.dirname(p), value), _realpath(g, posixpath.dirname(p), value))
                         if t and regular(t)}
            elif kind == "manifest" and value is not None:
                named = {t for t in (_norm(pkg.dir, value),) if t and regular(t)}
            else:
                named = set()
            if not named:
                unsure = True
            # An included file's `mod` items resolve from the including module
            # (or, read wide, from the included file).
            todo += [(t, b) for t in sorted(named) for b in (bases, bases_of(t))]
        units = {u.mod_pos: u for u in _doc_units(g, pkg, real, ptext, plx)[0] if u.mod_pos is not None}
        if not units:
            continue
        for at, name, attrs, chains in _module_items(plx, ptext):
            u = units.get(at)
            if u is None:
                continue
            if None in attrs or chains is None:
                out.append((real, u))
                continue
            if fold(name) != fold(stem) and all(a == "" for a in attrs):
                continue
            taken = {fold(t) for rel in _module_rels(name, attrs, chains) for b in bases
                     for t in (_norm(b, rel), _realpath(g, b, rel)) if t}
            if fold(path) in taken:
                out.append((real, u))
    return out, unsure


def doctest_views(g: "Graph", pkg: "Package", path: str, text: str, lx) -> DoctestViews:
    """The code of the doctests rustdoc compiles from `path`, item by item
    (_doc_units), each doc read as rustdoc reads it (_read_doc: unindented,
    then Markdown, then each fenced block's info string by rustdoc's rules).
    A module's doc is its outer doc and its file's inner doc in one: an outer
    doc on `mod x;` is read with the inner doc of each file the module may
    take; the inner doc a file opens with, with the outer doc of each `mod`
    item that may declare it, and alone from every state an outer doc this
    scan does not see may leave it in (_MD_JOINABLE: none open, or a
    paragraph), and with any least indent up to its own. An outer doc on a
    module whose file this scan cannot tell, that may leave another state,
    is blind, and so is a module file's doc the prefilter matches where an
    include! this scan cannot name may hold its declaration. (Until review 4
    each was read alone.)"""
    memo = g.__dict__.setdefault("_doctest_views_memo", {})
    key = (pkg.dir, path, len(text), hash(text))
    if key in memo:
        return memo[key]
    texts = {path: text}

    def text_of(file: str) -> str:
        if file not in texts:
            texts[file] = _doc_blob_text(g, file)
        return texts[file]

    units, unit_blind = _doc_units(g, pkg, path, text, lx)
    blind = set(unit_blind)
    blocks: Set[tuple] = set()
    files = {u.mod_pos: _module_doc_files(g, path, text, lx, u.mod_pos) for u in units if u.mod_pos is not None}
    cache = g.__dict__.setdefault("blob_cache", {})
    cache.update(g.index.read_blobs(sorted({t for ts in files.values() for t in ts or () if t not in cache})))
    for u in units:
        if u.mod_pos is not None:
            targets = files[u.mod_pos]
            if targets:
                for t in targets:
                    lead = _leading_doc(g, pkg, t)
                    items = u.items + (lead.items if lead else [])
                    _read_doc(items, [_MD_FRESH], _doc_variants(items, False), blocks, blind, text_of)
                continue
            ends = _read_doc(u.items, [_MD_FRESH], _doc_variants(u.items, True), blocks, blind, text_of)
            if not all(_md_joinable(e) for e in ends):
                blind.add((path, _line_of(text, u.start),
                           "the doc of a module whose file this scan cannot name, which that file's doc goes on"))
            continue
        if u.leading:
            decls, unsure = _module_decl_docs(g, pkg, path)
            for _p, outer in decls:
                items = outer.items + u.items
                _read_doc(items, [_MD_FRESH], _doc_variants(items, False), blocks, blind, text_of)
            _read_doc(u.items, _MD_JOINABLE, _doc_variants(u.items, True), blocks, blind, text_of)
            if unsure and any(DOCTEST_SCAN.search(ln[2]) for _o, fs in u.items for f in fs for alt in f[1] for ln in alt):
                blind.add((path, _line_of(text, u.start), "the doc of a module file whose declaration may stand in "
                                                          "a file an include! this scan cannot name"))
            continue
        _read_doc(u.items, [_MD_FRESH], _doc_variants(u.items, False), blocks, blind, text_of)
    run, compiled = _doc_views(blocks, text_of)
    views = DoctestViews(run=run, compile=compiled, blind=sorted(blind))
    memo[key] = views
    return views


def _is_build_script(pkg: Package, path: str) -> bool:
    """Whether `path` is the package's build script (Cargo's default
    <pkg>/build.rs, or the manifest's `build = ...`), compared as the landing
    host's file system compares names (fold): Cargo there runs <pkg>/build.RS
    or Build.rs as the default build script, and `build = "Build.rs"` opens
    build.rs. A test file that happens to be named build.rs
    (src/tools/targo/tests/testsuite/build.rs) is not one. (Until
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3 the names compared exactly, and such a
    script's reads were runtime only: compiler-check skipped them.)"""
    folded = fold(path)
    return any(fold(b) == folded for b in pkg.build_scripts)


# What the build reach (_build_reach) understands in a file it reaches; any
# other construct in code position may compile a file it never sees, so the
# reach is then incomplete (review 4 of LAND-GATE-EW1). The std macros that
# cannot compile another file: each expands to a format, a write, a panic or
# an assertion, a vector, or a compile-time constant (env!, concat!,
# stringify!, cfg!, line!, ...), never to an item, a module or a file read;
# include!, include_str! and include_bytes! are read on their own.
BUILD_MACROS = frozenset("""
    println print eprintln eprint format format_args write writeln panic assert assert_eq assert_ne
    debug_assert debug_assert_eq debug_assert_ne unreachable unimplemented todo vec env option_env concat
    stringify cfg matches line column file module_path dbg compile_error
    """.split())
INCLUDE_MACROS = frozenset(("include", "include_str", "include_bytes"))
# Attributes that are no macro: rustc's own cfg, lint, doc and codegen
# attributes (not a tool's such as rustfmt::skip, whose first segment a
# module or build-dependency named rustfmt can take); and std's
# `test`, a built-in attribute macro whose expansion is the function itself
# (with --test, also a test descriptor naming it) and never another file,
# and `ignore`, an inert attribute the test harness reads. (Measured on the
# real tree: the test modules the build scripts of rustc_llvm, bootstrap,
# targo and trust-thir-lower reach hold #[test] and #[ignore], and nothing
# else outside this set.)
BUILD_ATTRS = frozenset("""
    cfg allow warn deny forbid expect doc inline cold must_use deprecated non_exhaustive repr track_caller
    test ignore
    """.split())
STD_DERIVES = frozenset("Debug Clone Copy PartialEq Eq PartialOrd Ord Hash Default".split())
STD_ROOTS = frozenset(("std", "core", "alloc"))
# Every name above, and the crates whose paths name them: an item of the
# build script's crate that binds one (`use other::println;`, `use pm::Debug;`,
# `use other as std;`) makes the name another crate's macro (trustc compiles
# the file such a macro include!s: dep-info `build.rs gen.rs`).
BUILD_NAMES = BUILD_MACROS | INCLUDE_MACROS | BUILD_ATTRS | STD_DERIVES | STD_ROOTS | {
    "derive", "cfg_attr", "path", "rustfmt"}
# Rust 2015's strict and reserved keywords, which no edition takes for a
# name: a `!` after one is an operator (`if !x`, `impl !Send`), never a call.
BANG_KEYWORDS = frozenset("""
    as break const continue crate else enum extern false fn for if impl in let loop match mod move mut pub ref
    return self Self static struct super trait true type unsafe use where while abstract become box do final
    macro override priv typeof unsized virtual yield
    """.split())
# The tokens of a lexed file's code (comments, strings and chars blank there).
BUILD_TOKEN = re.compile(r'r#[A-Za-z_][A-Za-z0-9_]*|[A-Za-z_][A-Za-z0-9_]*|[0-9][A-Za-z0-9_]*|::|\S')
NON_ASCII = re.compile(r'[^\x00-\x7f]')


def _build_unread(lx, text: str, dep_macro: Optional[Callable[[str, str], Optional[str]]] = None) -> Optional[str]:
    """Where and why the build reach does not understand a lexed file it
    reaches (_build_reach's rules (1) to (4)), or None. In code position:
    (1) a character that is not ASCII (U+200E and U+200F are whitespace to
    rustc, so `include<U+200E>!` is an include!, and a name may look like
    another); (2) a macro call (a path, then `!`) other than a BUILD_MACROS
    one or an include call INCLUDE_CALL reads, bare or under std::, core:: or
    alloc::; `macro_rules!` and a `macro` item too; (3) an item that can make
    such a name another crate's (a `use` binding one of BUILD_NAMES from
    outside std, core and alloc or renamed, one naming an include macro at
    all, a glob from outside std, core, alloc and the crate, an `extern
    crate`, a module named std, core or alloc); (4) an attribute other than
    BUILD_ATTRS, a derive of STD_DERIVES, a cfg_attr of them and an outer
    path attribute on a module item (an inner `#![path]`, a cfg_attr's
    path, `#[macro_use]`, `#[rustfmt::skip]` and every procedural macro are
    not); and where rust_lex reads other than rustc does: a shebang, a char
    literal it leaves open, a frontmatter. `dep_macro(dep, name)`: why the
    call `dep::name!` is not understood (_dep_macro_unread), None when it
    is; without it every such call is not."""
    if not text.isascii():
        for m in NON_ASCII.finditer(text):
            if lx.in_code(m.start()):
                return f"{_line_of(text, m.start())}: U+{ord(m.group(0)):04X}, not ASCII, in code"
    code = lx.code
    toks = [(m.start(), m.group(0)) for m in BUILD_TOKEN.finditer(code)]
    words = [t for _p, t in toks]
    n = len(words)

    def named(t: str) -> bool:
        return t.startswith("r#") or t[0].isalpha() or t[0] == "_"

    def plain(t: str) -> str:
        return t[2:] if t.startswith("r#") else t

    def close_of(j: int) -> Optional[int]:
        # The index of the bracket closing words[j] ("(", "[" or "{").
        depth = 0
        for k in range(j, n):
            if words[k] in "([{" and len(words[k]) == 1:
                depth += 1
            elif words[k] in ")]}" and len(words[k]) == 1:
                depth -= 1
                if depth == 0:
                    return k
        return None

    def at(i: int) -> str:
        return f"{_line_of(text, toks[i][0])}: "

    for i, (pos, t) in enumerate(toks):
        if t == "!" and i and not code.startswith("=", pos + 1) and named(words[i - 1]) \
                and words[i - 1] not in BANG_KEYWORDS:
            segs, k = [plain(words[i - 1])], i - 1
            while k >= 2 and words[k - 1] == "::" and named(words[k - 2]):
                segs.insert(0, plain(words[k - 2]))
                k -= 2
            lead = words[k - 1] if k else None
            ok = segs[-1] in BUILD_MACROS | INCLUDE_MACROS and (
                (len(segs) == 1 and lead not in ("::", "$")) or (len(segs) == 2 and segs[0] in STD_ROOTS))
            held = None
            if not ok and dep_macro is not None and len(segs) == 2 and lead not in ("::", "$"):
                # `dep::name!`: its one definition, held to these rules
                # (review 4 of LAND-GATE-EW1, round 3: tippy's
                # rustc_tools_util::setup_version_info!).
                held = dep_macro(segs[0], segs[1])
                ok = held is None
            if not ok:
                return at(i) + f"the macro call {'::'.join(segs)}!, which may compile another file" + (
                    f" ({held})" if held else "")
            # An include call so spelt is one INCLUDE_CALL reads (rule (1)
            # leaves it no whitespace but ASCII's, which the lexer's comment
            # blanking keeps), and _build_reach follows each include!.
        elif t == "macro":
            return at(i) + "a macro definition"
        elif t == "'" and code.startswith("\\", pos + 1):
            # rust_lex gave up on an escaped char literal (`'\u{4___________1}'`)
            # and reads on from its quote, where rustc does not (round 3).
            return at(i) + "a char literal the lexer leaves open"
        elif t == "-" and i == 0:
            # A frontmatter (`---` first), which rust_lex reads as code (round 3).
            return at(i) + "a `-` first, a frontmatter the lexer does not read"
        elif t == "extern" and i + 1 < n and words[i + 1] == "crate":
            return at(i) + "an extern crate, which may bring macros in"
        elif t == "mod" and i + 1 < n and plain(words[i + 1]) in STD_ROOTS:
            return at(i) + f"a module named {plain(words[i + 1])}"
        elif t == "use" and not (i + 1 < n and words[i + 1] == "<"):  # not `use<'a>`, which captures
            depth, end = 0, None
            for k in range(i + 1, n):
                depth += {"{": 1, "}": -1}.get(words[k], 0)
                if words[k] == ";" and depth == 0:
                    end = k
                    break
            leaves = _use_leaves(words[i + 1:end] if end is not None else [])
            if leaves is None:
                return at(i) + "a use the reach does not parse"
            for segs, bound, glob in leaves:
                root = next((s for s in segs if s), None)
                if INCLUDE_MACROS & {*segs, bound}:
                    return at(i) + "a use naming an include macro"
                if glob and root not in STD_ROOTS | {"crate", "self", "super"}:
                    return at(i) + f"a glob use of {'::'.join(segs)}, which may bring macros in"
                last = segs[-2] if segs[-1] == "self" and len(segs) > 1 else segs[-1] if segs else None
                if not glob and bound in BUILD_NAMES and not (root in STD_ROOTS and bound == last):
                    return at(i) + f"a use binding {bound}, which may make it another crate's macro"
        elif t == "#":
            j = i + 1 + (i + 1 < n and words[i + 1] == "!")
            inner = j > i + 1
            if j >= n or words[j] != "[":
                # A shebang too: rustc drops its line, rust_lex reads it as
                # code (`#!/usr/bin/env x /*` hides what follows; round 3).
                return at(i) + "a `#` that opens no attribute"
            close = close_of(j)
            if close is None:
                return at(i) + "an attribute that does not close"
            why = _attr_unread(words[j + 1:close], inner, False, lambda: _on_module_item(words, close + 1))
            if why:
                return at(i) + why
    return None


def _use_leaves(ts: Sequence[str]) -> Optional[List[Tuple[List[str], Optional[str], bool]]]:
    """Each leaf of a `use` tree's tokens (BUILD_TOKEN, without `use` and
    `;`): (its path's segments, "" for a leading `::`; the name it binds, its
    rename or its last segment, None for a glob; whether it is a glob); None
    for a tree this does not parse."""
    out: List[Tuple[List[str], Optional[str], bool]] = []

    def tree(i: int, prefix: List[str]) -> int:
        segs = list(prefix)
        if ts[i] == "::":
            segs.append("")
            i += 1
        while True:
            t = ts[i]
            if t == "*":
                out.append((segs, None, True))
                return i + 1
            if t == "{":
                i += 1
                while ts[i] != "}":
                    i = tree(i, segs)
                    if ts[i] == ",":
                        i += 1
                    elif ts[i] != "}":
                        raise ValueError(t)
                return i + 1
            if not (t.startswith("r#") or t[0].isalpha() or t[0] == "_"):
                raise ValueError(t)
            segs = segs + [t[2:] if t.startswith("r#") else t]
            i += 1
            if i < len(ts) and ts[i] == "::":
                i += 1
                continue
            last = segs[-2] if segs[-1] == "self" and len(segs) > 1 else segs[-1]
            if i < len(ts) and ts[i] == "as":
                rename = ts[i + 1]
                out.append((segs, rename[2:] if rename.startswith("r#") else rename, False))
                return i + 2
            out.append((segs, last, False))
            return i

    try:
        end = tree(0, [])
    except (IndexError, ValueError):
        return None
    return out if end == len(ts) else None


def _attr_unread(ts: Sequence[str], inner: bool, nested: bool, on_module: Callable[[], bool]) -> Optional[str]:
    """Why the build reach does not take an attribute (its tokens inside
    `#[..]`), or None (_build_unread's rule (4)). `nested`: in a cfg_attr;
    `on_module`: whether the item it stands on is a module item."""
    segs, k = [], 0
    while k < len(ts) and (ts[k].startswith("r#") or ts[k][0].isalpha() or ts[k][0] == "_"):
        segs.append(ts[k][2:] if ts[k].startswith("r#") else ts[k])
        k += 1
        if k < len(ts) and ts[k] == "::":
            k += 1
            continue
        break
    path, rest = "::".join(segs), list(ts[k:])
    if path == "path":
        if inner:
            return "an inner #![path], which may place a module anywhere"
        if nested:
            return "a cfg_attr's path attribute"
        return None if on_module() else "a path attribute on no module item"
    if path in ("cfg_attr", "derive"):
        if not rest or rest[0] != "(" or rest[-1] != ")":
            return f"a {path} the reach does not parse"
        parts: List[List[str]] = [[]]
        depth = 0
        for t in rest[1:-1]:
            depth += {"(": 1, "[": 1, "{": 1, ")": -1, "]": -1, "}": -1}.get(t, 0)
            if t == "," and depth == 0:
                parts.append([])
            else:
                parts[-1].append(t)
        if path == "derive":
            bad = [" ".join(p) for p in parts if p and (len(p) != 1 or p[0] not in STD_DERIVES)]
            return f"a derive of {bad[0]}, which may be a procedural macro" if bad else None
        for part in parts[1:]:  # after the predicate
            why = _attr_unread(part, inner, True, on_module) if part else None
            if why:
                return why
        return None
    # Not rustfmt::skip: a module or build-dependency named rustfmt makes it
    # another crate's attribute macro (review 4 of LAND-GATE-EW1, round 3).
    if path in BUILD_ATTRS:
        return None
    return f"the attribute #[{path}], which may be a procedural macro"


def _on_module_item(words: Sequence[str], i: int) -> bool:
    """Whether the item at words[i] (BUILD_TOKEN tokens), after further
    outer attributes and a visibility, is a module item."""
    n = len(words)
    while i < n and words[i] == "#" and i + 1 < n and words[i + 1] == "[":
        depth = 0
        for k in range(i + 1, n):
            depth += {"[": 1, "]": -1}.get(words[k], 0)
            if depth == 0:
                i = k + 1
                break
        else:
            return False
    if i < n and words[i] == "pub":
        i += 1
        if i < n and words[i] == "(":
            while i < n and words[i] != ")":
                i += 1
            i += 1
    return i < n and words[i] == "mod"


# What a build-dependency's macro may carry beside `#[macro_export]` and keep
# its expansion (_dep_macro_unread): doc and lint attributes.
DEP_MACRO_ATTRS = frozenset(("doc", "allow", "warn", "deny", "forbid", "expect"))


def _dep_macro_unread(g: Graph, dep: str, name: str) -> Optional[str]:
    """Why the build reach does not understand the call `<dep>::<name>!` of
    the tracked path build-dependency at `dep` (None when it does; review 4
    of LAND-GATE-EW1, round 3). It does where the dependency's one
    definition of that name (MACRO_DEF, over every Rust file it owns) is a
    `macro_rules!` at the top of its library's root, which is a tracked
    regular file at its spelling that rust_lex reads as rustc does
    (_root_lex_unread) with no inner attribute rule (4) refuses (no
    `#![feature]` for a custom inner attribute), the definition carrying
    `#[macro_export]` (not local_inner_macros) and only DEP_MACRO_ATTRS
    beside it (no cfg); and where its body, patterns and transcribers, keeps
    _build_unread's rules with no `mod` and no include call (the reach
    follows neither from there; a `$crate::m!` is no std macro, so is not
    understood), spelling no path and no walk (a build script's harvest
    reads its own file's). Compiled wherever the dependency is, so any other export of
    the name is E0428 (trustc: a macro-expanded one too). A `$fragment` is
    the call's tokens, held to the rules where the call stands; the body's
    `$crate::f()` calls the dependency, which runs, and is compiled, as that
    package's code."""
    memo = g.__dict__.setdefault("_dep_macro_memo", {})
    if (dep, name) in memo:
        return memo[(dep, name)]

    def why() -> Optional[str]:
        pkg = g.packages[dep]
        if pkg.proc_macro:
            return f"{dep} is a procedural macro crate"
        manifest = posixpath.join(dep, "Cargo.toml") if dep else "Cargo.toml"
        try:
            lib = tomllib.loads(g.index.read_blobs([manifest])[manifest].decode("utf-8")).get("lib")
        except (KeyError, RuntimeError, ValueError, UnicodeDecodeError):
            return f"{manifest} does not parse"
        spelled = lib.get("path", "src/lib.rs") if isinstance(lib, dict) else "src/lib.rs"
        root = _norm(dep, spelled) if isinstance(spelled, str) else None
        if root is None or g.index.entries.get(root, ("",))[0] not in REGULAR or _realpath(g, dep, spelled) != root:
            return f"{dep}'s library root {spelled!r} is no tracked regular file at its spelling"
        defs = []
        for q in sorted({real for _q, real in _package_sources(g, pkg)} | {root}):
            lx = _lexed(g, q)
            defs += [(q, lx, m) for m in MACRO_DEF.finditer(lx.code) if (m.group(1) or m.group(2)) == name]
        if len(defs) != 1:
            return f"{len(defs)} definitions of {name} in {dep}"
        q, lx, m = defs[0]
        text, code = lx.text, lx.code
        where = f"{q}:{_line_of(text, m.start())}"
        if q != root or m.group(1) is None:
            return f"{where}: {name} is no macro_rules! of the library's root"
        unread = _root_lex_unread(lx, text)
        if unread:
            return f"{root}:{unread}"
        pairs = _pairs(code, BRACKET)
        if any(o < m.start() < c for o, c in pairs.items()):
            return f"{where}: {name} is not at the top of the root"
        toks = [(t.start(), t.group(0)) for t in BUILD_TOKEN.finditer(code)]
        words = [t for _p, t in toks]
        for i, (pos, t) in enumerate(toks):  # the root's inner attributes, rule (4)
            if t == "#" and words[i + 1:i + 3] == ["!", "["] and not any(o < pos < c for o, c in pairs.items()):
                close = pairs.get(toks[i + 2][0])
                inner = _attr_unread([w for p, w in toks[i + 3:] if p < close], True, False, lambda: False) \
                    if close is not None else "an attribute that does not close"
                if inner:
                    return f"{root}:{_line_of(text, pos)}: {inner}"
        k = next((i for i, (p, _t) in enumerate(toks) if p == m.start()), None)
        if k is None:
            return f"{where}: a definition the lexer cannot read"
        attrs: List[List[str]] = []  # its outer attributes, back to the item before it
        while k >= 3 and words[k - 1] == "]":
            o = max((i for i, (p, _t) in enumerate(toks[:k]) if pairs.get(p) == toks[k - 1][0]), default=None)
            if o is None or o < 1 or words[o - 1] != "#":
                break
            attrs.append(words[o + 1:k - 1])
            k = o - 1
        if attrs.count(["macro_export"]) != 1 or any(
                a != ["macro_export"] and (not a or a[0] not in DEP_MACRO_ATTRS) for a in attrs):
            return f"{where}: {name} carries {[' '.join(a) for a in attrs]}, not #[macro_export] alone"
        j = _next_token(lx, m.end())
        if code[j:j + 1] not in ("(", "[", "{") or j not in pairs:
            return f"{where}: a definition the lexer cannot read"
        from rust_lex import lex  # scripts/lib is on sys.path for every caller
        body = text[j:pairs[j] + 1]
        blx = lex(body)
        held = _build_unread(blx, body)
        if held is None and MOD_TOKEN.search(blx.code):
            held = "a `mod`, whose file the reach does not follow from there"
        if held is None and _include_calls(blx):
            held = "an include call, whose file the reach does not follow from there"
        # Expanded in the build script, its literals and walks are the build
        # script's, but _scan_file harvests a build script's from its own
        # file: a body that spells a path (as that harvest takes one) or walks
        # is not followed.
        spellings = _index_spellings(g)
        if held is None and any(_pathlike(v) or fold(v) in spellings or v in ANCHOR_LITERALS or v == ".."
                                for _s, _e, v in blx.strings):
            held = "a path literal, which the build script's harvest reads from its own file only"
        if held is None and any(p.search(blx.code) for p in (FILE_ANCHOR_CODE, CWD_ANCHOR_CODE, CLIMB_CODE, POP_CODE)):
            held = "a walk, which the build script's harvest reads from its own file only"
        return f"{where}: the body of {name}: {held}" if held else None

    memo[(dep, name)] = why()
    return memo[(dep, name)]


def _root_lex_unread(lx, text: str) -> Optional[str]:
    """Where rust_lex may read a file other than rustc does, as
    _build_unread's rule (1) and its lexer checks find it (a character
    outside ASCII in code, a `'` left in code before a `\\`, a `-` first)
    and a shebang (`#!` first, opening no attribute), for a file the build
    reach reads only for one definition (_dep_macro_unread)."""
    if not text.isascii():
        for m in NON_ASCII.finditer(text):
            if lx.in_code(m.start()):
                return f"{_line_of(text, m.start())}: U+{ord(m.group(0)):04X}, not ASCII, in code"
    toks = [(m.start(), m.group(0)) for m in BUILD_TOKEN.finditer(lx.code)]
    for pos, t in toks:
        if t == "'" and lx.code.startswith("\\", pos + 1):
            return f"{_line_of(text, pos)}: a char literal the lexer leaves open"
    if toks[:1] and toks[0][1] == "-":
        return f"{_line_of(text, toks[0][0])}: a `-` first, a frontmatter the lexer does not read"
    first = [t for _p, t in toks[:3]]
    if first[:2] == ["#", "!"] and first[2:] != ["["]:
        return f"{_line_of(text, toks[0][0])}: a shebang, which the lexer reads as code"
    return None


def _spelt_unread(lx, text: str, names: Set[str]) -> Optional[str]:
    """Where a lexed file spells one of `names` other than as a path's head
    (`dep::`, after no `::`): an item, import or binding of the name, to
    which rustc resolves `dep::m!` instead of the build-dependency
    (_build_reach)."""
    toks = [(m.start(), m.group(0)) for m in BUILD_TOKEN.finditer(lx.code)]
    for i, (pos, t) in enumerate(toks):
        if (t[2:] if t.startswith("r#") else t) in names and not (
                i + 1 < len(toks) and toks[i + 1][1] == "::" and (i == 0 or toks[i - 1][1] != "::")):
            return f"{_line_of(text, pos)}: {t}, a build-dependency whose macro it reads, spelt other than as a path's head"
    return None


def _build_reach(g: Graph, pkg: Package) -> Tuple[FrozenSet[str], bool]:
    """The tracked Rust files the package's build script compiles: the script
    (_build_script_files) and, to a fixed point, what a file names as a module
    (`mod x;`, with or without a path attribute in any spelling) or include!s
    (a literal, raw or not, or a manifest-dir concat!); and whether that is
    all of them, which it is by construction only when the reach understands
    every token of every file it reaches. Review 4 of LAND-GATE-EW1 found it
    called itself complete while the script compiled a module a macro of
    another crate declares, one after a U+200E, one an inner `#![path]`
    places, a module behind a file link, a renamed include! and an include!
    a macro strips of `extern "C++"`. It is incomplete, in a file it reaches,
    on (1) a character that is not ASCII in code, (2) a macro call that is
    not a std macro that cannot compile another file, an include! it
    resolves, or a path build-dependency's macro whose one definition keeps
    these rules (_dep_macro_unread; the file then spells that dependency
    only as a path's head, _spelt_unread), (3) an item that can shadow such
    a name, or a build-dependency named std, core, alloc or rustfmt
    (_find_build_scripts), (4) an attribute that is not inert (_build_unread
    has each, and where rust_lex misreads), (5) a `mod` that is no module item
    it parses (MOD_TOKEN), and (6) a file it reaches that is a link or lies
    under a directory link, the build script included; and, as before, a
    module item or include! naming no tracked regular file at its spelling
    (rustc opens `mod Gen;` as gen.rs here, and reads an untracked file) or
    no literal (a macro's `mod $n;`, `#[path = $p]`, include! of a computed
    path). Why it is incomplete goes into the cache beside it
    (build_reach_cache: its first reasons). (Review of
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3: a miss then left the file runtime code
    only, and compiler-check skipped what it reads.)"""
    cached = g.build_reach_cache.get(pkg.dir)
    if cached is not None:
        return cached[0], cached[1]
    entries = g.index.entries
    why: List[str] = []

    def regular(q: Optional[str]) -> bool:
        return q is not None and entries.get(q, ("", ""))[0] in ("100644", "100755")

    seen = set(_build_script_files(g, pkg))
    spellings = _index_spellings(g)
    for b in sorted(pkg.build_scripts):  # as named, and where a link takes it (_find_build_scripts)
        opened = sorted(q for q in spellings.get(fold(b), ()) if q in entries)
        if not all(regular(q) for q in opened) or not opened:
            why.append(f"the build script {b} is a link, lies under a directory link, or is missing")
    # A build-dependency named std, core, alloc or rustfmt (_find_build_scripts).
    crates, shadowing = g.__dict__.get("_build_crates", {}).get(pkg.dir, ({}, []))
    why.extend(shadowing)
    used: Set[str] = set()  # the build-dependencies whose macro a reached file calls
    reached: Dict[str, Tuple[object, str]] = {}

    def dep_macro(dep: str, name: str) -> Optional[str]:
        # `dep::name!` of a tracked path build-dependency (round 3).
        if crates.get(dep) is None:
            return f"{dep} names no one tracked path build-dependency"
        held = _dep_macro_unread(g, crates[dep], name)
        if held is None:
            used.add(dep)
        return held

    frontier = sorted(q for q in seen if regular(q))
    while frontier:
        known = g.blob_cache
        blobs = g.index.read_blobs([q for q in frontier if q not in known])
        following: Set[str] = set()
        for path in frontier:
            text = (known[path] if path in known else blobs[path]).decode("utf-8", "replace")
            lx = _lexed(g, path, text)
            unread = _build_unread(lx, text, dep_macro)
            reached[path] = (lx, text)
            if unread:
                why.append(f"{path}:{unread}")
            fdir = posixpath.dirname(path)
            stem = posixpath.splitext(posixpath.basename(path))[0]
            if MACRO_MOD.search(lx.code):
                why.append(f"{path}: a macro names a module")
            cxx = _extern_cxx_spans(lx, text) if "C++" in text else []
            sites: List[Tuple[int, List[Tuple[str, str]]]] = []  # each site's candidate files
            for m in _include_calls(lx):
                if not _includes_source(m) or any(o < m.start() < c for o, c in cxx):
                    continue
                kind, value = _include_arg(lx, text, m.end())
                if kind == "file":
                    sites.append((m.start(), [(fdir, value), (posixpath.join(fdir, stem), value)]))
                elif kind == "manifest":
                    sites.append((m.start(), [(d, value) for d in sorted({pkg.dir, g.owner(path) or pkg.dir})]))
                else:
                    why.append(f"{path}:{_line_of(text, m.start())}: an include! of no literal path")
            items = _module_items(lx, text)
            parsed = {m.start() for m in MOD_ITEM.finditer(lx.code)}
            for m in MOD_TOKEN.finditer(lx.code):
                if m.start() not in parsed:
                    why.append(f"{path}:{_line_of(text, m.start())}: a `mod` that is no module item it parses")
            for pos, name, attrs, around in items:
                if None in attrs or around is None:
                    why.append(f"{path}:{_line_of(text, pos)}: a module whose path is no literal")
                    continue
                sites.append((pos, [(fdir, pre + rel) for pre in ("", stem + "/")
                                    for rel in _module_rels(name, attrs, around)]))
            for pos, cands in sites:
                where = f"{path}:{_line_of(text, pos)}"
                hits = set()
                for base, rel in cands:
                    spelt, real = _norm(base, rel), _realpath(g, base, rel)
                    hits.update(q for q in (spelt, real) if regular(q))
                    # rustc compiles a link, or a file under a directory
                    # link, as its own path: the escape scan reads that path
                    # as the link's owner reads it, not as the build script's.
                    if spelt is not None and (entries.get(spelt, ("",))[0] == "120000"
                                              or (regular(real) and real != spelt)):
                        why.append(f"{where}: {spelt} is a link or lies under a directory link")
                if not hits:
                    why.append(f"{where}: names no tracked regular file at its spelling")
                following.update(hits - seen)
        seen |= following
        frontier = sorted(following)
    # rustc resolves `dep::name!` to an item or import named dep where one
    # stands: a reached file may spell a dependency whose macro it read only
    # as a path's head (`mod rustc_tools_util { pub use other::m; }`; round 3).
    for path in sorted(reached) if used else ():
        spelt = _spelt_unread(reached[path][0], reached[path][1], used)
        if spelt:
            why.append(f"{path}:{spelt}")
    g.build_reach_cache[pkg.dir] = (frozenset(seen), not why, "; ".join(why[:3]) or None)
    return frozenset(seen), not why


# The roots Cargo finds for a package's targets with no manifest key, relative
# to the package and folded (_build_role).
DEFAULT_TARGET_ROOT = re.compile(r"src/(?:lib|main)\.rs|(?:src/bin|tests|benches|examples)/[^/]+(?:\.rs|/main\.rs)")


def _build_role(g: Graph, pkg: Package, path: str) -> Optional[str]:
    """What builds `path`, a file of `pkg`: "build" for the build script
    itself (_is_build_script), whose reads happen while the package compiles;
    "both" for a file the build script compiles too (_build_reach: `mod gen;`
    beside build.rs, `include!("src/shared.rs")`), which a Cargo target may
    also compile, so its reads count at compile time and at run time, and for
    every file of a package whose build reach is incomplete (it does not
    understand every token of every file it reaches: _build_reach's rules;
    build_reach_cache keeps why); None for runtime code. (Until LAND-GATE-EW1-FOLLOWUP-REVIEW-3 a guess stood
    in for the reach: every file under <pkg>/build/ was the build script's
    alone, in any case once names folded, so a library rooted there lost its
    runtime reads and its package-wide harvest, while a module the script
    loaded beside it read nothing at compile time.)"""
    if not pkg.build_scripts:
        return None
    if _is_build_script(pkg, path):
        # A build script a module item also takes (build.rs -> src/shared.rs,
        # or `build = "src/shared.rs"`, beside lib.rs's `mod shared;`) is a
        # target's code too: "both", or its run-time reads and walk are lost
        # (review 4 of LAND-GATE-EW1, round 3). A production module item as
        # _production_name finds one (_declared_in, in its directory and
        # every one above), or any module item, a test one too (`#[cfg(test)]
        # mod shared;`, which the unit tests compile), in a file that may
        # declare it, in any spelling and through a link (one that does not
        # resolve may declare it), in the lexer's reading (`#[cfg(test)]
        # mod<U+200E>shared;` too, which _declared_only_under_test's legacy
        # reading leaves production). A path attribute or include! naming it
        # is scanned for the file naming it already (_compiled_elsewhere).
        # The declaring files are listed here, not by _parent_candidates,
        # which lists none for a file named build.rs, lib.rs or main.rs: a
        # build script is one (`#[cfg(test)] mod build;` beside build.rs ->
        # src/build.rs; round 3's verifier).
        d, base = posixpath.split(path)
        stem = posixpath.basename(d) if fold(base) == "mod.rs" else posixpath.splitext(base)[0]
        for a in [d, *reversed(_proper_ancestors(d)), ""] if d else [""]:
            declared = _declared_in(g, a, fold(stem))
            if None in declared or fold(path) in declared:
                return "both"
        spellings = _index_spellings(g)
        pd = posixpath.dirname(d) if fold(base) == "mod.rs" else d
        declarers = [posixpath.join(pd, "mod.rs"), posixpath.join(pd, "lib.rs"), posixpath.join(pd, "main.rs"), pd + ".rs"]
        for p in sorted({q for c in declarers for q in spellings.get(fold(c), ())
                         if q in g.index.entries}):
            if g.index.entries[p][0] == "120000":
                p = _realpath(g, posixpath.dirname(p), _link_texts(g)[p])
                if p is None or g.index.entries.get(p, ("",))[0] not in REGULAR:
                    return "both"
            if g.index.entries[p][0] in REGULAR and fold(stem) in {fold(m) for m in _lexed(g, p).mod_decls}:
                return "both"
        # So is one that is a Cargo target's root (`build = "src/main.rs"`,
        # Cargo's default binary, or `[lib] path = "build.rs"`; round 3): a
        # default root whatever the auto keys say, or a manifest's target path.
        rel = path if not pkg.dir else path[len(pkg.dir) + 1:] if path.startswith(pkg.dir + "/") else None
        if rel is not None and DEFAULT_TARGET_ROOT.fullmatch(fold(rel)):
            return "both"
        if fold(path) in g.__dict__.get("_build_target_roots", {}).get(pkg.dir, ()):
            return "both"
        return "build"
    reach, complete = _build_reach(g, pkg)
    # A file under <pkg>/build/ stays "both" whatever the reach finds: the
    # guess the reach replaced read it at compile time, and a reach that
    # misses a shape it does not parse must not take that away (review of
    # LAND-GATE-EW1-FOLLOWUP-REVIEW-3).
    under_build = fold(path).startswith(fold(pkg.dir + "/" if pkg.dir else "") + "build/")
    return "both" if path in reach or not complete or under_build else None


def _build_script_files(g: Graph, pkg: Package) -> List[str]:
    """The tracked files that are the package's build script on the landing
    host (_is_build_script): every spelling the index holds of each name."""
    spellings = _index_spellings(g)
    return sorted({q for b in pkg.build_scripts for q in spellings.get(fold(b), ()) if q in g.index.entries})


def _scan_file(g: Graph, pkg: Package, path: str, text: str,
               ctx: Optional[Tuple[Optional[str], bool, bool]] = None) -> bool:
    """Scan one file. Returns True when the file reaches above its package
    (a CARGO_MANIFEST_DIR walk, a repo-root variable, git): the package's
    literals are then harvested (_harvest_package_literals). `ctx`, for a
    file the package compiles from elsewhere (_compiled_elsewhere): whether
    it is part of a build script, test-only, never run, as the code that
    names it is; otherwise the package's own file's (_own_context)."""
    lx = _lexed(g, path, text)
    fdir = posixpath.dirname(path)
    base = posixpath.basename(path)
    # The package's build script, or a file it compiles that a Cargo target
    # may compile too, whose reads then count in both classes (_build_role);
    # for a file compiled from elsewhere, as the code naming it is (`ctx`).
    role, file_test_only, never_runs = ctx if ctx is not None else _own_context(g, pkg, path, lazy=True)
    is_build = role is not None
    runtime_cls = "compile" if (role == "build" or pkg.proc_macro) else "runtime"
    _file_test: List[bool] = [] if file_test_only is None else [file_test_only]
    if never_runs and runtime_cls == "runtime":
        runtime_cls = "never"  # recorded under a class no leg reads
    run_classes = [runtime_cls] + (["compile"] if runtime_cls != "compile" and is_build else [])
    marks = (len(pkg.reads), len(pkg.unresolved), len(pkg.history))  # what this file records (below)

    def file_test() -> bool:
        if not _file_test:
            _file_test.append(_test_only_file(g, pkg, path))
        return _file_test[0]

    def t_only(pos: int) -> bool:
        return lx.in_test(pos) or file_test()

    calls = _include_calls(lx)
    plain = lx.without_comments() if calls else text  # what the ARG_* regexes read
    # What every regex matching tokens across the text reads: its comments
    # blank and Rust whitespace outside ASCII a space, its literals as
    # written, at the same offsets (Lexed.without_comments). (Review 4, round 2:
    # BARE_UP_BEFORE, JOIN_BEFORE and MACRO_CALL read the text, and
    # `.join<U+200E>("..")`, which rustc compiles, climbed nowhere. GIT_SPAWN
    # still reads the text: _git_literal_sites, which reads the lexed
    # tokens, finds every "git" it does, a `show-toplevel` is a literal's.)
    view = lx.without_comments()

    def include_site(m: "re.Match", fdir: str, lits: Sequence[str], decide: Optional[Sequence[str]] = None) -> None:
        # One include!, a relative path resolved from `fdir`; `lits`: the
        # path-like literals a path that is not one may be, each read;
        # `decide` (default `lits`): those whose resolving leaves it resolved.
        where = f"{path}:{_line_of(text, m.start())}"
        tail = plain[m.end(): m.end() + 400]
        to = t_only(m.start())
        source = _includes_source(m)  # compiled as source; include_str!/_bytes! read data
        lit = ARG_LIT.match(tail)
        man = ARG_MANIFEST.match(tail)
        cat = ARG_CONCAT_LIT.match(tail)
        kind, value = _include_arg(lx, text, m.end())
        if lit or (kind == "file" and not man and not cat):
            # A literal, raw (`include!(r"..")`) or not, or a concat! of them.
            target = _norm(fdir, _unescape(lit.group(1)) if lit else value)
            _record(g, pkg, "compile", target, f"{where} include", to)
            if source:
                _maybe_foreign(g, pkg, target, f"{where} include", to)
        elif man:
            # Each piece by its decoded value, as rustc reads it (round 8 of
            # review 4: a concat! prefix spelled with escapes, `"..\u{2f}.."`,
            # read the including file's own directory).
            rel = _unescape(man.group(1)).lstrip("/")
            target = _norm(pkg.dir, rel) if man.group(2) in ")]}" else _norm(pkg.dir, posixpath.dirname(rel) or ".")
            _record(g, pkg, "compile", target, f"{where} include", to)
            if source and kind == "manifest":  # the whole file, when every piece is a literal
                _maybe_foreign(g, pkg, _norm(pkg.dir, value), f"{where} include", to)
        elif cat:
            rel = _unescape(cat.group(1))
            target = _norm(fdir, rel) if cat.group(2) in ")]}" else _norm(fdir, posixpath.dirname(rel) or ".")
            _record(g, pkg, "compile", target, f"{where} include (concat prefix)", to)
            if source and kind == "file":  # the whole file, when every piece is a literal
                # (Until the review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3 no edge:
                # `include!(concat!("../../other/src/", "x.rs"))` compiled
                # another package's file with no edge to it, and the walk,
                # which leaves a scanned site's edge to this scan, added none.)
                _maybe_foreign(g, pkg, _norm(fdir, value), f"{where} include", to)
        elif ARG_OUT_DIR.match(tail):
            pass  # generated into OUT_DIR, or a Cargo artifact dependency: not a tree read
        else:
            # A macro parameter or a computed path: every path-like literal of the file.
            resolved = [t for v in lits for t in (_norm(fdir, v), _norm(pkg.dir, v)) if t is not None]
            decided = resolved if decide is None else [v for v in decide if _norm(fdir, v) or _norm(pkg.dir, v)]
            if not decided:
                _record(g, pkg, "compile", None, f"{where}: include! of a computed path", to)
            # A literal that resolves outside the repository is not a tree read
            # (an include of a file outside the checkout is an untracked input
            # no git selector sees; docs/LANDING_GATE.md lists it as a hazard).
            for t in resolved:
                _record(g, pkg, "compile", t, f"{where} include (file literal)", to)

    own_lits = [v for v in _literal_values(lx) if _pathlike(v)]
    for m in calls:
        body = _macro_body_at(lx, m.start())
        if body is None or ARG_MANIFEST.match(plain, m.end()) or ARG_OUT_DIR.match(plain, m.end()):
            include_site(m, fdir, own_lits)
            continue
        # In a macro's body a relative path resolves from each file calling
        # the macro (_macro_callers), and a macro parameter is a literal of
        # one: none found, the file it names cannot be told. From the
        # defining file too, as before review 4: it may call the macro by a
        # name no search sees (paste's `[<m _x>]!()`), and a path that leaves
        # the tree from there stays unresolved (round 4 of review 4: read
        # from the callers only, an include_str! of a literal continued on
        # the next line, which only include_site decodes, called by paste in
        # the defining file read nothing).
        via: Set[str] = set()
        handed: List[Optional[str]] = []
        callers = sorted(_macro_callers(g, _package_sources(g, pkg), body[2], g.blob_cache, via=via, handed=handed))
        if not callers:
            _record(g, pkg, "compile", None, f"{path}:{_line_of(text, m.start())}: an include! in the body of "
                    f"macro {body[2] or '(of no readable name)'}, whose calls the scan cannot all find in "
                    f"{pkg.dir or '.'} (rustc resolves it from the file calling the macro)", t_only(m.start()))
        given = [v for v in handed if v is not None]
        lits = list(dict.fromkeys(own_lits + given + [
            v for real in sorted({r for _scan, r in callers} | via) if real != path
            for v in _literal_values(_lexed(g, real, g.blob_cache[real].decode("utf-8", "replace"))) if _pathlike(v)]))
        # A bare parameter (`include!($p)`) is what the macro's calls hand it
        # (_handed_by): while each hands literals only, those decide. A path
        # computed from a parameter (`concat!($d, "/x")`), and a parameter one
        # call hands anything else (`inner!(concat!(..))` in another macro's
        # body, a constant's name, the macro handed on as a callback), is none
        # of them: the defining file's own literals decide it, as before review
        # 4. Every literal of the files naming the macro is still read. (Round 5
        # of review 4: an unrelated literal of a caller stood for a computed
        # path; round 6: any literal of a caller or `via` file stood for a bare
        # parameter, whatever the calls handed.)
        bare = BARE_PARAM_ARG.match(plain, m.end()) is not None
        decide = given if bare and handed and None not in handed else own_lits
        # In a macro defined in another macro's body, a parameter the include
        # names may be the outer macro's (`$q` of `make!`), substituted by
        # make!'s calls, which name no inner macro: neither those calls nor
        # the defining file's literals can tell what it reads (round 8 of
        # review 4: the inner macro's calls decided it).
        if _nested_macro_body(lx, body) and _include_names_parameter(lx, m):
            _record(g, pkg, "compile", None, f"{path}:{_line_of(text, m.start())}: an include! naming a "
                    f"parameter in macro {body[2] or '(of no readable name)'}, defined in another macro's body, "
                    "which may bind it", t_only(m.start()))
        for d in sorted({fdir} | {posixpath.dirname(scan) for scan, _real in callers}):
            include_site(m, d, lits, decide)
    # A `use` renaming an include macro: its calls are include!s of files no
    # scan can tell (INCLUDE_RENAME).
    for m in INCLUDE_RENAME.finditer(lx.code) if "include" in text else ():
        _record(g, pkg, "compile", None, f"{path}:{_line_of(text, m.start())}: a `use` renaming an include "
                "macro, whose calls the scan cannot see", t_only(m.start()))
    # An inner path attribute that is no inline module's: which directory
    # the file's modules take cannot be told (_lost_inner_paths).
    for pos in _lost_inner_paths(lx, text):
        _record(g, pkg, "compile", None, f"{path}:{_line_of(text, pos)}: an inner path attribute that is no "
                "inline module's, whose modules' directory the scan cannot tell", t_only(pos))
    for pos, value, _end in _path_attrs(lx, text):
        where = f"{path}:{_line_of(text, pos)}"
        stem = posixpath.splitext(base)[0]
        if value is None:
            cands = _path_attr_targets(lx, fdir, stem, None)
            if not cands:
                _record(g, pkg, "compile", None, f"{where}: a path attribute that is not a string literal",
                        t_only(pos))
            for c in cands:
                _record(g, pkg, "compile", c, f"{where} #[path] (file literal)", t_only(pos))
                _maybe_foreign(g, pkg, c, f"{where} #[path] (file literal)", t_only(pos), guessed=True)
            continue
        cands = [_norm(fdir, value), _norm(posixpath.join(fdir, stem), value)]
        _record_either(g, pkg, "compile", cands, f"{where} #[path]", t_only(pos))
        for c in cands:
            _maybe_foreign(g, pkg, c, f"{where} #[path]", t_only(pos))
    if is_build:
        # A build script names its inputs with literals (rerun-if-changed={CONST}
        # included): every path-like literal, relative to the package, but an
        # include!'s or a path attribute's own, which rustc reads relative to
        # the file, as recorded above. (Until review 4 of LAND-GATE-EW1 they
        # were read relative to the package too: `build = "tools/build.rs"`
        # with `include_str!("../../../docs/x")` then left the repository, and
        # every leg compiling the package was unresolved.)
        spans = _include_arg_spans(lx, calls) + [(at, end) for at, _v, end in _path_attrs(lx, text)]
        for s, e, v in lx.strings:
            if not _pathlike(v) or any(a <= s < b for a, b in spans):
                continue
            v = PLACEHOLDER.sub("", v.replace("cargo:rerun-if-changed=", "").replace("cargo::rerun-if-changed=", ""))
            if not v or v.startswith("/"):
                continue
            _record_either(g, pkg, "compile", [_norm(pkg.dir, v)], f"{path}:{_line_of(text, s)} build literal",
                           False)
    walk_sites: List[bool] = []
    for s, e, v in lx.strings:
        if not v.startswith("../") and (("../" not in v and not v.endswith("/..")) or not PATHISH.match(v)):
            # Not a climbing literal here; a bare ".." is a walk (see below).
            continue
        to = t_only(s)
        where = f"{path}:{_line_of(text, s)} literal"
        rel = v
        if not v.startswith("../"):
            # "/../../docs/x" after concat!(env!("CARGO_MANIFEST_DIR"), ..), or
            # "{}/../../docs/x" in a format!: relative to a base this scan cannot
            # see (most often the manifest dir). Resolve it against the package and
            # the file, and treat the package as walking (the harvest adds every
            # repository path it spells).
            rel = PLACEHOLDER.sub("", v).lstrip("/")
            if not rel.startswith("../"):
                rel = posixpath.normpath(rel) if rel else ""
                if not (rel.startswith("../") or rel == ".."):
                    continue  # "a/../b": stays inside wherever it is rooted
            walk_sites.append(to)
        if rel.replace("../", "").strip(".") == "":
            walk_sites.append(to)
            continue  # "../..": a walk to a parent; resolved by the harvest
        cands = [_norm(pkg.dir, rel), _norm(fdir, rel)]
        for cls in run_classes:
            _record_either(g, pkg, cls, cands, where, to)
        # Inside an attribute or a macro's arguments a literal can be a
        # compile-time read: a proc macro reads it while the crate compiles
        # (rust-embed's #[folder], include_dir!). Recorded in that class too, for
        # every resolution inside the repository (the runtime record above keeps
        # the fail-closed answer for one that resolves nowhere).
        if runtime_cls != "compile" and (_in_macro_or_attribute(view, s) or _among_reading_brackets(lx, s)):
            for c in cands:
                if c is not None and _cut_glob(c)[0]:  # not the repository root itself
                    _record(g, pkg, "compile", c, where, to)
    for s, e, v in lx.strings:
        if STAGE_LITERAL.search(fold(v)) or v in ENV_PSEUDO:
            target = ENV_PSEUDO.get(v, STAGE1)
            for cls in run_classes:
                pkg.reads.append(Read(cls, target, t_only(s), f"{path}:{_line_of(text, s)} {v!r}"))
    spawns = [m.start() for m in GIT_SPAWN.finditer(text)] + _git_literal_sites(lx, text)
    for start in sorted(set(spawns)):
        if not lx.in_comment(start):  # `show-toplevel` sits inside a string literal
            to = t_only(start)
            where = f"{path}:{_line_of(text, start)}"
            for cls in run_classes:
                _record(g, pkg, cls, None, f"{where}: runs git (reads history and the worktree)", to)
                pkg.history.append(Read(cls, where, to, where))
    for m in REPO_ROOT_ENV.finditer(lx.without_comments()):
        if not lx.in_comment(m.start()):
            walk_sites.append(t_only(m.start()))
    # An anchor and a climb anywhere in the file (see ANCHOR_LITERALS). The walk
    # is test-only when every anchor, or every climb, is: production code walks
    # only with both. A walk anchored only at the working directory or the
    # executable is a `cwd` walk when it is production code outside a build
    # script (a build script runs in its package directory: there it is an
    # ordinary walk); a `..` handed to a path constructor is such a walk by itself.
    dir_anchors = [s for s, _e, v in lx.strings if v in ANCHOR_LITERALS] + \
                  [m.start() for m in FILE_ANCHOR_CODE.finditer(lx.code)]
    cwd_anchors = [m.start() for m in CWD_ANCHOR_CODE.finditer(lx.code)]
    bare_up = [s for s, _e, v in lx.strings if v == ".." and BARE_UP_BEFORE.search(view, max(0, s - 80), s)]
    climbs = [m.start() for m in CLIMB_CODE.finditer(lx.code)] + bare_up + \
             [s for s, _e, v in lx.strings if v == ".." and JOIN_BEFORE.search(view, max(0, s - 80), s)] + \
             [s for s, _e, v in lx.strings if v != ".." and _climbing_literal(v)]
    # PathBuf::pop climbs, Vec::pop does not, and a large file has hundreds of
    # the latter: a `.pop()` counts within POP_WINDOW characters after an anchor
    # (`let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR")); p.pop(); p.pop();`).
    starts = sorted(dir_anchors + cwd_anchors)
    climbs += [m.start() for m in POP_CODE.finditer(lx.code)
               if any(0 < m.start() - a <= POP_WINDOW for a in starts)]
    cwd_sites: List[bool] = []
    if climbs and dir_anchors:
        walk_sites.append(all(t_only(p) for p in dir_anchors) or all(t_only(p) for p in climbs))
    if climbs and cwd_anchors:
        cwd_sites.append(all(t_only(p) for p in cwd_anchors) or all(t_only(p) for p in climbs))
    cwd_sites.extend(t_only(p) for p in bare_up)
    if is_build:
        # A build script runs in its package directory: a walk from the
        # working directory is an ordinary walk there. A file the build script
        # compiles that a Cargo target may compile too ("both") walks for that
        # target as well (below), which harvests the whole package.
        if walk_sites or cwd_sites:
            # A build script that walks reads, while the crate compiles, the
            # repository paths IT spells: harvested from this file alone (not
            # the whole package, whose literals are runtime data), anchored at a
            # top-level entry. One that spells none, and resolves no `../`
            # literal either, is unresolved.
            # (Folded, as the harvest anchors: "Docs/x" opens docs/x.)
            spellings = _index_spellings(g)
            spelled = [v for _s, _e, v in lx.strings if _pathlike(v) or fold(v) in spellings]
            anchored = 0
            for v in spelled:
                cand = re.sub(r"^(?:\.\.?/)+", "", PLACEHOLDER.sub("", v)).lstrip("/")
                head = cand.split("/", 1)[0]
                if fold(head) in spellings and head not in ("", ".", ".."):
                    _record(g, pkg, "compile", cand.rstrip("/"), f"{path} (build-script walk literal)", False)
                    anchored += 1
            if not anchored and not any(v.startswith("../") or "/../" in v for v in spelled):
                _record(g, pkg, "compile", None, f"{path}: a build script walks above its package and "
                                                 "names no repository path", False)
        if role == "build":
            return False
    if role == "both":
        # The build script may compile this file, a test file or a test-only
        # module too (_build_role): what the file reads while the package
        # compiles is never test-only, its compile copy of a run-time read
        # included (review 4 of LAND-GATE-EW1: ui-trust, which runs no test
        # code, skipped a git run in tests/common/gen.rs the script compiles).
        for recorded, mark in zip((pkg.reads, pkg.unresolved, pkg.history), marks):
            recorded[mark:] = [replace(r, test_only=False) if r.cls == "compile" else r for r in recorded[mark:]]
    if walk_sites or cwd_sites:
        pkg.walks.append(Walk(path, all(walk_sites + cwd_sites), cwd=not walk_sites,
                              cls="compile" if runtime_cls == "compile" else "runtime"))
    return bool(walk_sites or cwd_sites)


# A macro call, whitespace between its name and `!` too (`m !(..)`, which
# rustc takes), read on the code view (_scan_file's `view`), where Rust
# whitespace outside ASCII is a space; a keyword a negation may follow is
# no name (`if !(..)`, NOT_AFTER).
MACRO_CALL = re.compile(r'([A-Za-z_][A-Za-z0-9_]*)\s*!\s*[(\[{]')
NOT_AFTER = frozenset(("if", "while", "match", "return", "break", "in", "yield"))
ATTR_OPEN = re.compile(r'#!?\s*\[')
# Macros that cannot read a file while a crate compiles (std's and core's own;
# include*! is scanned on its own). A macro_rules! macro expands to code, whose
# own include*! the scan sees in the definition.
NON_READING_MACROS = frozenset("""
    assert assert_eq assert_ne debug_assert debug_assert_eq debug_assert_ne panic unreachable todo
    unimplemented format format_args write writeln print println eprint eprintln vec concat stringify
    matches env option_env cfg line column file module_path dbg compile_error thread_local
    """.split())


def _in_macro_or_attribute(text: str, pos: int) -> bool:
    """Whether the literal at `pos` may be read by a proc macro while the crate
    compiles: it sits after an attribute opened on its line, or after a call of
    a macro that is neither std's nor a macro_rules! of this file (a line-local
    test, conservative toward yes for any other macro)."""
    line_start = text.rfind("\n", 0, pos) + 1
    if ATTR_OPEN.search(text, line_start, pos):
        return True
    for m in MACRO_CALL.finditer(text, line_start, pos):
        name = m.group(1)
        if name in NON_READING_MACROS or name in NOT_AFTER:
            continue
        if re.search(r'macro_rules!\s*%s\b' % re.escape(name), text):
            continue
        return True
    return False


# `$m!(..)` too: a macro a parameter names (review 4, round 3), which may be any.
READING_OPEN = re.compile(r'#\s*(?:!\s*)?\[|(?<![\w$])(r#|\$\s*)?([^\W\d]\w*)\s*!\s*[(\[{]')


def _among_reading_brackets(lx, pos: int) -> bool:
    """Whether `pos` lies inside an attribute's brackets (`#[..]`, `#![..]`)
    or among the tokens of a call of a macro that is neither std's nor a
    macro_rules! of the file (_in_macro_or_attribute's), wherever a line
    breaks: Rust whitespace, a line break too, may stand between the
    name, the `!`, the bracket and the literal. (Review 4, round 2:
    _in_macro_or_attribute reads the literal's own line, and
    `include_dir!(\n    "../x"\n)` was no compile-time read.)"""
    opens = lx.__dict__.get("_reading_opens")
    if opens is None:
        code = lx.code
        pairs = _pairs(code, BRACKET)
        local = set(re.findall(r'\bmacro_rules\s*!\s*(?:r#)?(\w+)', code)) if "macro_rules" in code else set()
        opens = []
        for m in READING_OPEN.finditer(code):
            name = None if (m.group(1) or "").startswith("$") else m.group(2)  # `$m!`: no name skips it
            if name is not None and (name in NON_READING_MACROS or name in local
                                     or (name in NOT_AFTER and not m.group(1))):
                continue
            opens.append((m.end() - 1, pairs.get(m.end() - 1, len(code))))
        lx._reading_opens = opens
    return any(o < pos < c for o, c in opens)


def _climbing_literal(v: str) -> bool:
    """A path literal with a `..` component: "..", "../x", "a/../../b", "{}/../x"."""
    if not v or len(v) > 300 or "\n" in v:
        return False
    return v == ".." or v.startswith("../") or v.endswith("/..") or ("/../" in v and PATHISH.match(v) is not None)


def _pathlike(v: str) -> bool:
    return bool(v) and len(v) < 300 and "\n" not in v and (
        "/" in v or re.search(r"\.(rs|json|toml|md|txt|lean|olean|bin|ll|s|c|h|cpp|yaml|yml|tsv|csv)$", v) is not None)


def _rust_source(path: str) -> bool:
    """Whether a tracked file is Rust source by its name: `.rs` as the landing
    host's file system compares names (fold). rustc there compiles `mod
    helper;` from helper.RS, which a case-sensitive test never scanned or
    harvested (review of LAND-GATE-EW1-FOLLOWUP-REVIEW-2)."""
    return path.endswith(".rs") or fold(path).endswith(".rs")


def _rust_sources(g: Graph) -> List[str]:
    """Every tracked regular file that is Rust source (_rust_source), sorted."""
    out = getattr(g, "_rust_sources", None)
    if out is None:
        out = sorted(p for p, (mode, _) in g.index.entries.items()
                     if mode in ("100644", "100755") and _rust_source(p))
        g._rust_sources = out  # type: ignore[attr-defined]
    return out


def _entries_under(g: Graph, d: str) -> List[str]:
    """The index's paths under the directory `d` ("" is the root), in order."""
    keys = getattr(g, "_sorted_entries", None)
    if keys is None:
        keys = g._sorted_entries = sorted(g.index.entries)  # type: ignore[attr-defined]
    if not d:
        return keys
    return keys[bisect.bisect_left(keys, d + "/"):bisect.bisect_left(keys, d + "0")]  # "0" follows "/"


# Cargo's auto-discovered targets, relative to the package.
AUTO_TARGET = re.compile(r'(?:src/(?:lib|main)\.rs|src/bin/[^/]+\.rs|src/bin/[^/]+/main\.rs'
                         r'|(?:tests|benches|examples)/[^/]+\.rs|(?:tests|benches|examples)/[^/]+/main\.rs)')


def _crate_roots(g: Graph, pkg: Package) -> Optional[List[str]]:
    """The source file of every Cargo target of `pkg`: auto-discovered (more
    than `autobins = false` and the like leave), declared in its manifest
    (wherever that points), its build scripts. A package nested in it is
    its own (a fixture's, a test's), whose files the harvest still reads.
    None when the manifest cannot be read."""
    manifest = posixpath.join(pkg.dir, "Cargo.toml") if pkg.dir else "Cargo.toml"
    try:
        doc = tomllib.loads(g.index.read_blobs([manifest])[manifest].decode("utf-8"))
    except (KeyError, RuntimeError, ValueError, UnicodeDecodeError):
        return None
    roots: Set[str] = set()
    for spelled in _target_paths(doc):
        target = _norm(pkg.dir, spelled)
        if target is None:
            return None
        roots.add(target)
    roots.update(_build_script_files(g, pkg))  # build.rs in any spelling, when there is one
    for q in _entries_under(g, pkg.dir):
        # As the landing host compares names (fold): Cargo there compiles
        # src/Lib.rs as src/lib.rs (until the review of
        # LAND-GATE-EW1-FOLLOWUP-REVIEW-3 no root, so its lost sites never
        # blinded the package).
        if AUTO_TARGET.fullmatch(fold(q[len(pkg.dir) + 1:] if pkg.dir else q)):
            roots.add(q)
    return sorted(roots)


def _compiled_rust_sources(g: Graph, pkg: Package, paths: List[str], blobs: Dict[str, bytes]) -> List[str]:
    """`paths` (the package's regular Rust files) and every other Rust file the
    package compiles: the target of an in-package link named `.rs` in any case
    (_rust_source), a Cargo target's
    source wherever the manifest puts it, and, to a fixed point, what a file
    names as a module (`mod x;` with or without a path attribute in any
    spelling, through directory links too) or includes (`include!` of a
    literal, raw or not, or of a manifest-dir concat!). `blobs` gains each
    added file.
    What a compiled file names but the index does not hold (a file inside a
    gitlink, a missing or generated one, a path that is not a literal) leaves
    the package unresolved: the harvest cannot read that code's literals. A
    file is compiled when the walk from the Cargo targets reaches it (a fixture
    or a ui test is not), or when the walk cannot be told complete (a module
    a macro names, `mod $name;`, or a manifest it cannot read). A `.rs` link
    that cannot be resolved leaves it unresolved wherever it is. (Until
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3 only that link did, and a directory link,
    a `cfg_attr`, raw-string or spaced path attribute, an include! of a raw
    string or of a manifest-dir concat!, and the modules of a module outside
    the package were never read.)"""
    entries = g.index.entries
    classes = ["compile"] if pkg.proc_macro else ["runtime"]  # the harvest's
    kinds = sorted({(w.test_only, w.cwd) for w in pkg.walks}) or [(False, False)]

    def regular(q: Optional[str]) -> bool:
        return q is not None and entries.get(q, ("", ""))[0] in ("100644", "100755")

    def inside(q: str) -> bool:
        return not pkg.dir or q.startswith(pkg.dir + "/")

    def blind(site: str, why: str, test_only: bool = False) -> None:
        for cls in classes:
            for walk_test_only, cwd in kinds:
                pkg.unresolved.append(Read(cls, f"{site}: {why}", walk_test_only or test_only, site, cwd))

    texts = _link_texts(g)
    # Every file the escape scan's walk found the package compiles from
    # elsewhere (_compiled_elsewhere), compiled as its targets' files are: a
    # module a macro declares through a directory link (`mod $name;`) was the
    # walk's alone until the review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3, and
    # its literals were never harvested.
    found = [q for q in g.__dict__.get("_compiled_from_elsewhere", {}).get(pkg.dir, ()) if regular(q)]
    start = list(paths) + found
    for link in sorted(texts):
        if _rust_source(link) and inside(link):
            target = _realpath(g, posixpath.dirname(link), texts[link])
            if regular(target):
                start.append(target)
            else:
                pkg.unresolved.append(Read("runtime", f"{link}: a linked Rust file that cannot be resolved",
                                           False, link))
    # Every file reached from `start`: its edges, its sites that name nothing
    # the index holds (site, why, test-only), and whether a macro names a module.
    edges: Dict[str, List[str]] = {}
    lost: Dict[str, List[Tuple[str, str, bool]]] = {}
    macro_modules: Set[str] = set()
    roots = _crate_roots(g, pkg)
    if roots is not None:  # each as the file system opens it (a target may be a link)
        named, roots = roots, []
        for r in named:
            q = r if regular(r) else _realpath(g, posixpath.dirname(r), posixpath.basename(r))
            # A declared one miscased (`path = "src/Main.rs"`): what the
            # landing host opens, each spelling the index holds (fold).
            folded = [] if regular(q) else sorted(s for s in _index_spellings(g).get(fold(r), ()) if regular(s))
            if regular(q):
                roots.append(q)
            elif folded:
                roots += folded
            else:
                roots.append(r)
                lost.setdefault(r, []).append((r, "a Cargo target whose source the index does not hold", False))
        start += [r for r in roots if regular(r)]
    frontier = sorted(set(start))
    seen = set(frontier)
    # Where a macro the package compiles may be called (_macro_callers).
    sources = [(q, q) for q in sorted(set(paths) | set(found))]
    while frontier:
        blobs.update(g.index.read_blobs([q for q in frontier if q not in blobs]))
        following: List[str] = []
        for path in frontier:
            text = blobs[path].decode("utf-8", "replace")
            out_edges = edges.setdefault(path, [])
            sites = lost.setdefault(path, [])
            if "include" not in text and "mod" not in text and not _may_declare_by_macro(g, text):
                continue
            lx = _lexed(g, path, text)
            fdir = posixpath.dirname(path)
            stem = posixpath.splitext(posixpath.basename(path))[0]
            prefixes = ("", stem + "/")
            if _macro_module_sites(g, lx, text):
                macro_modules.add(path)

            def lose(pos: int, why: str) -> None:
                test_only = lx.in_test(pos) or (inside(path) and _test_only_file(g, pkg, path))
                sites.append((f"{path}:{_line_of(text, pos)}", why, test_only))

            def follow(rels: Iterable[Tuple[str, str]], pos: int, what: str, blind: bool = True) -> None:
                hits = sorted({q for base, rel in rels for q in (_norm(base, rel), _realpath(g, base, rel))
                               if regular(q)})
                if not hits and not blind:
                    return  # a default beside a cfg_attr path attribute: one more candidate
                if not hits:
                    lose(pos, f"{what} that is not a tracked regular file")
                out_edges.extend(hits)
            cxx = _extern_cxx_spans(lx, text) if "C++" in text else []
            for m in _include_calls(lx):
                if not _includes_source(m) or any(o < m.start() < c for o, c in cxx):
                    continue  # include_str!/_bytes! read data (the escape scan's); cxx's names a header
                kind, value = _include_arg(lx, text, m.end())
                body = _macro_body_at(lx, m.start())
                if kind == "file" and body is not None:
                    # In a macro's body: from each file calling the macro
                    # (_macro_callers); none, and the file cannot be told.
                    callers = sorted(_macro_callers(g, sources, body[2], blobs))
                    if not callers:
                        lose(m.start(), f"an include! in the body of macro {body[2] or '(of no readable name)'}, "
                                        "whose calls the walk cannot all find in the files the package compiles")
                    # From each caller's directory, each on its own: rustc
                    # resolves an include! from the directory of the file it
                    # opened, never its stem directory, and one caller's file
                    # stands for no other's (round 5 of review 4: a tracked
                    # file at a stem directory, or at one caller's, left the
                    # untracked one nothing unresolved).
                    for scan in sorted({scan for scan, _real in callers}):
                        follow([(posixpath.dirname(scan), value)], m.start(), "an include!d file")
                    # From the defining file too, as before review 4, and a
                    # file that is not tracked there leaves the package
                    # unresolved: it may call the macro by a name no search
                    # sees (paste's `[<m _x>]!()`). Round 4 of review 4: from
                    # the callers only, `include!("gen.rs")` of a src/gen.rs
                    # including OUT_DIR's file, or of an untracked gen.in,
                    # left nothing unresolved; and a file of the callers' that
                    # names the macro only by chance (`fn m_y`) dropped the
                    # blind of a macro no search sees called.
                    follow([(fdir, value)], m.start(), "an include!d file")
                elif kind == "file":
                    follow([(fdir, value)], m.start(), "an include!d file")
                elif kind == "manifest":
                    # CARGO_MANIFEST_DIR: the package compiling the file, or the nested one owning it.
                    dirs = {pkg.dir, (g.owner(path) or pkg.dir) if inside(path) else pkg.dir}
                    follow([(d, value) for d in sorted(dirs)], m.start(), "an include!d file")
                elif kind == "generated":
                    lose(m.start(), "an include! of a file outside the tree (OUT_DIR), whose code the harvest "
                                    "cannot read")
                else:
                    lose(m.start(), "an include! of a path that is not a literal")
            for m in INCLUDE_RENAME.finditer(lx.code) if "include" in text else ():
                lose(m.start(), "a `use` renaming an include macro, whose calls the walk cannot follow")
            for pos in _lost_inner_paths(lx, text):
                lose(pos, "an inner path attribute that is no inline module's, whose modules' directory the walk "
                          "cannot tell")
            for pos, name, attr, around in _module_items(lx, text):
                if None in attr or around is None:
                    lose(pos, "a path attribute that is not a string literal")
                    continue
                # Every file it may take (_module_items). Each path attribute's,
                # cfg_attr or not, blinds the harvest when the index holds none
                # of its candidates: the landing host may take that one. The
                # default (`x.rs`, `x/mod.rs`) beside a cfg_attr one is one more
                # candidate, and blinds only an item with no path attribute.
                # (Review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3: all were followed
                # as one, so `#[cfg_attr(unix, path = "gen/imp.rs")] mod imp;`
                # with gen/imp.rs untracked resolved through src/imp.rs.)
                for alt in attr:
                    rels = _module_rels(name, [alt], around)
                    follow([(fdir, pre + rel) for pre in prefixes for rel in rels], pos, f"module {name or '(unread)'}",
                           blind=alt != "" or attr == [""])
            for q in out_edges:
                if q not in seen:
                    seen.add(q)
                    following.append(q)
        frontier = following
    # The files the Cargo targets compile: a site of one that names nothing
    # leaves the package unresolved. A module a macro may declare anywhere in
    # the package makes every file count: the walk cannot follow a module a
    # macro declares (a renamed one, `use defs::declare as dd; dd!(gen);`),
    # so a file it does not reach may still be compiled. (The review of
    # LAND-GATE-EW1-FOLLOWUP-REVIEW-3 narrowed this to a macro site the walk
    # reaches, and a package compiling such a gen.rs with a missing module
    # resolved; it stays wide, at the price of blinding a package whose
    # fixtures, trustfmt's tests/source, invoke one.)
    if roots is None or macro_modules:
        compiled = set(edges) | set(lost)
    else:
        compiled = set()
        stack = [r for r in roots] + found
        while stack:
            q = stack.pop()
            if q not in compiled:
                compiled.add(q)
                stack.extend(edges.get(q, ()))
                if q in macro_modules:
                    compiled = set(edges) | set(lost)
                    break
    for q in sorted(compiled):
        for site, why, test_only in lost.get(q, ()):
            blind(site, why, test_only)
    return sorted(set(paths) | set(edges))


def _harvest_package_literals(g: Graph, pkg: Package, top: Sequence[str], audits: Dict[str, dict],
                              not_paths: Optional[Dict[str, dict]] = None) -> None:
    """A package that walks above itself reads repo paths it spells with
    literals: harvest every literal of the package anchored at a top-level
    entry ("docs/TCB.md", "compiler", "/scripts/x"), as a read in the class of
    the walk (runtime, or compile in a build script or proc macro), test-only
    when every walking file is test-only, and always for a doctest's literal.
    A walking package that spells no anchored literal in its code is
    unresolved."""
    # A literal, or a chain of them joined (`.join("tests").join("js262")`),
    # which spells one path: "tests/js262", not all of tests/. Every Rust file
    # under the package (_rust_source: helper.RS too; nested packages' included,
    # as before), from the lexer's tokens (_string_chains).
    # One read per KIND of walk the package has (test-only or not, through the
    # working directory or not): a production working-directory walk and a
    # test-only manifest walk (compiletest's lib.rs and directives/tests.rs) are
    # two contexts, and neither reaches the stage-1 suites; folding them into one
    # production, manifest-anchored read made every docs change select those suites.
    kinds = sorted({(w.test_only, w.cwd) for w in pkg.walks}) or [(False, False)]
    # The class of the walk: a proc macro's reads while the crate compiles (a
    # build script's walk is harvested from that file alone, in _scan_file).
    classes = ["compile"] if pkg.proc_macro else ["runtime"]
    found = 0
    paths = [p for p in _rust_sources(g) if not pkg.dir or p.startswith(pkg.dir + "/")]
    missing = [p for p in paths if p not in g.blob_cache]
    blobs = dict(g.blob_cache)
    blobs.update(g.index.read_blobs(missing))
    paths = _compiled_rust_sources(g, pkg, paths, blobs)
    from rust_lex import formatting_label_starts
    standard = "library/std" in g.packages and g.packages["library/std"].name == "std"
    # Unrelated test workspaces may also contain a package named std. What
    # matters is whether THIS package overrides the implicit sysroot name.
    manifest_path = posixpath.join(pkg.dir, "Cargo.toml")
    try:
        manifest = tomllib.loads(g.index.read_blobs([manifest_path])[manifest_path].decode())
        def overrides_std(table):
            return any((key.endswith("dependencies") and isinstance(value, dict) and "std" in value)
                       or (isinstance(value, dict) and overrides_std(value))
                       for key, value in table.items())
        standard = standard and not overrides_std(manifest)
    except (KeyError, ValueError, UnicodeDecodeError):
        standard = False
    # Namespace aliases need not themselves contain a path literal or belong
    # to one of Cargo's entry-point files. Inspect all tracked Rust source in
    # the package before crediting the standard-library binding, and every
    # other file it compiles (`paths`: a #[path] module or include!d file
    # outside the package or of another name, a link's target), whose
    # binding is the package's as much (until LAND-GATE-EW1-FOLLOWUP-REVIEW-3
    # only the files under the package directory counted).
    namespace_files = [p for p in g.index.entries
                       if p.startswith(pkg.dir + "/") and _rust_source(p)]
    blobs.update(g.index.read_blobs([p for p in namespace_files if p not in blobs]))
    checked = [p for p in paths if not (p.startswith(pkg.dir + "/") and _rust_source(p))]
    for path, blob in blobs.items():
        if path.startswith(pkg.dir + "/") and _rust_source(path):
            checked.append(path)
    # A local std binding can replace the external-prelude name. Refuse the
    # formatting optimization for the entire package when one is present.
    for path in checked:
        code = _lexed(g, path, blobs[path].decode("utf-8", "replace")).code
        if re.search(r"\b(?:mod|struct|enum|trait|type)\s+(?:r#)?std\b|\bas\s+(?:r#)?std\b|"
                     r"#!\s*\[\s*no_std\b|\buse\s+[^;]*::\s*(?:r#)?std\s*;|"
                     r"\buse\s+[^;]*\{[^}]*\bstd\b", code):
            standard = False
            break
    harvested: List[Tuple[List[str], bool]] = []  # (values, read only by a doctest)
    package_aliases: List[Tuple[Set[str], bool]] = []  # every compiled file's (_package_path_aliases), once

    def package_aliased(code: str) -> bool:
        # Identifiers compare NFC-normalized, as rustc compares them.
        if not package_aliases:
            package_aliases.append(_package_path_aliases(
                [unicodedata.normalize("NFC", _lexed(g, p, blobs[p].decode("utf-8", "replace")).code)
                 for p in paths]))
        names, unknown = package_aliases[0]
        return unknown or (bool(names) and re.search(r'(?<![\w$])(?:%s)(?![\w$])' % "|".join(
            sorted(map(re.escape, names))), unicodedata.normalize("NFC", code)) is not None)

    for path in paths:
        if audit_holds(g, path, audits.get(path)):
            continue  # scan_escapes already recorded this exact declared footprint
        text = blobs[path].decode("utf-8", "replace")
        lx = _lexed(g, path, text)
        labels = formatting_label_starts(text, standard_library=standard)
        row = (not_paths or {}).get(path)
        exempt = (set(row["literals"]) if not_path_holds(g, path, row) and not _path_api_aliased(lx.code)
                  and not package_aliased(lx.code) else set())
        calls: Dict[object, object] = {}  # _in_value_call's scopes and bindings of this file
        for start, end, values in _string_chains(lx, text):
            if len(values) == 1:
                if start in labels:
                    continue
                if (values[0] in exempt and not _in_path_call(lx.code, start, end)
                        and not _in_value_call(lx.code, start, calls)):
                    continue  # a reviewed non-path value of this exact blob ([[not_path]])
            harvested.append((values, False))
    # Doctests compile against the package and run in its test legs: their
    # literals are the package's too, an audited file's included (a row
    # declares the file's code, not its doctests).
    for path in paths:
        text = blobs[path].decode("utf-8", "replace")
        if _has_doc_text(text):
            from rust_lex import lex
            for view in (v for vs in doctest_views(g, pkg, path, text, _lexed(g, path, text)).run.values() for v in vs):
                if view.strip():
                    harvested.extend((values, True) for _s, _e, values in _string_chains(lex(view), view))
    spellings = _index_spellings(g)
    for parts, doctest in harvested:
        if not parts:
            continue
        v = "/".join(p.strip("/") for p in parts if p.strip("/")) if len(parts) > 1 else parts[0]
        v = PLACEHOLDER.sub("", v)
        v = re.sub(r"^(?:\.\.?/)+", "", v)  # the walk itself ("../..") is not part of the path
        cand = v.lstrip("/")
        if cand.startswith("./"):
            cand = cand[2:]
        head = cand.split("/", 1)[0]
        if fold(head) == "build":  # the untracked build tree: the stage-1 compiler and sysroot
            for cls in classes:
                for test_only, cwd in kinds:
                    pkg.reads.append(Read(cls, STAGE1, test_only or doctest,
                                          f"{pkg.dir} (harvested build-tree literal)", cwd))
            found += not doctest  # a doctest's path does not name a walk's
            continue
        if head in ("", ".", ".."):
            continue
        # Anchored at the top level, or at an ancestor of the package where its
        # first component exists: a walk may stop there (`.parent()` of
        # `crates/x`'s manifest dir is `crates/`, and `.join("y/js/d.mjs")`
        # reads `crates/y/js/d.mjs`). Until LAND-GATE-EW1-FOLLOWUP-REVIEW-2 only
        # the top level counted; a chain glued `.expect("crates")` onto the
        # join, which caught this by accident. Both compare as the landing
        # host's file system does (fold): APFS opens "Docs/x.md" as docs/x.md
        # (until LAND-GATE-EW1-FOLLOWUP-REVIEW-3 the top level was exact).
        anchors = [""] if fold(head) in spellings else []
        anchors += [a for a in _proper_ancestors(pkg.dir) if fold(f"{a}/{head}") in spellings]
        for anchor in anchors:
            target = (f"{anchor}/{cand}" if anchor else cand).rstrip("/")
            prefix, _ = _cut_glob(target)
            if prefix:
                if g.owner(prefix) != pkg.dir or prefix == pkg.dir:
                    for cls in classes:
                        for test_only, cwd in kinds:
                            pkg.reads.append(Read(cls, prefix, test_only or doctest,
                                                  f"{pkg.dir} (harvested literal)", cwd))
                found += not doctest  # a doctest's path does not name a walk's
    if not found:
        for cls in classes:
            for test_only, cwd in kinds:
                pkg.unresolved.append(Read(cls, f"{pkg.dir}: walks above its package and names no repository path",
                                           test_only, pkg.dir, cwd))


def _proper_ancestors(d: str) -> List[str]:
    """The directories strictly between the repository root and `d`."""
    parts = d.split("/") if d else []
    return ["/".join(parts[:i]) for i in range(1, len(parts))]


def _parent_candidates(path: str) -> List[str]:
    """The files that may declare the module file `path` (`mod <stem>;`)."""
    d, base = posixpath.split(path)
    if base in ("lib.rs", "main.rs", "build.rs"):
        return []
    if base == "mod.rs":
        d = posixpath.dirname(d)
    return [posixpath.join(d, "mod.rs"), posixpath.join(d, "lib.rs"), posixpath.join(d, "main.rs"), d + ".rs"]


def _lexed(g: Graph, path: str, text: Optional[str] = None):
    """`text` tokenized (`text`: `path`'s blob's own when not given), never
    another text's: lex_cache's `path` when it holds exactly `text`, else
    the blob's tokenization (a blob fact) when its text is exactly `text`,
    else lexed. Cached at `path` only when `path` holds nothing: a doctest
    view or a link target's text is lexed at the path while that is scanned
    (_scan_doctest_view, _scan_one), and a predicate of the file's own text
    read meanwhile reads its own tokens (until this, _macro_module_names'
    first run inside a doctest view's scan took the view's for its file's).
    Without `text`, lex_cache's `path` is taken as it stands: a scan of a
    view reads the view there."""
    cache = getattr(g, "lex_cache", None)
    if cache is None:
        cache = g.lex_cache = {}
    held = cache.get(path)
    if held is not None and (text is None or held.text is text or held.text == text):
        return held
    blob = None
    if text is None:
        blob = getattr(g, "blob_cache", {}).get(path)
        if blob is None:
            blob = g.index.read_blobs([path])[path]
        text = blob.decode("utf-8", "replace")
    lx = _tokenization(g, path, text, blob)
    if held is None:
        cache[path] = lx
    return lx


def _tokenization(g: Graph, path: str, text: str, blob: Optional[bytes]):
    """`text` tokenized, for _lexed: from `path`'s blob's tokenization (a blob
    fact; an earlier graph's counts as reused) when that is of exactly
    `text`, else lexed; kept as the blob's only when `text` is the blob's
    own (`blob`, when given, is the bytes it was decoded from). What it
    returns is a working copy (_bare): what a scan memoizes on it never
    reaches the fact."""
    from rust_lex import lex  # scripts/lib is on sys.path for every caller
    entry = g.index.entries.get(path) if isinstance(getattr(g, "index", None), TreeIndex) else None
    facts = g.__dict__.setdefault("blob_facts", {})
    key = None if entry is None else ("lex", entry[1], None)
    fact = facts.get(key) if key is not None else None
    if fact is None and key is not None:
        prior = g.__dict__.get("_prior_blob_facts")
        fact = None if prior is None else prior.get(key)
        if fact is not None and _lexes(fact, text):
            g.__dict__["_reused_blob_facts"] = g.__dict__.get("_reused_blob_facts", 0) + 1
            facts[key] = fact
    if fact is not None and _lexes(fact, text):
        return _bare(fact)
    lx = lex(text)
    if key is not None and key not in facts:
        own = g.index._blob_bytes.get(entry[1])
        if own is not None and (blob is own or text == own.decode("utf-8", "replace")):
            facts[key] = _bare(lx)
    return lx


def _declared_only_under_test(g: Graph, pkg: Package, path: str) -> bool:
    """True when the module file `path` is declared only by `#[cfg(test)] mod
    <stem>;` in the files that may declare it. Errs toward production: no
    declaring file found, or any declaration without cfg(test), is production.
    A declaring file is found in any spelling the landing host opens it by
    (fold: src/Lib.rs), and a link is read through to what it shows (until
    LAND-GATE-EW1-FOLLOWUP-REVIEW-3 a link's own text, its target's path, was
    lexed: a production `mod helper;` behind src/lib.rs -> ../lib_real.rs did
    not count against main.rs's `#[cfg(test)] mod helper;`); one that cannot
    be resolved may declare it in production. What is found only so, through
    a link or in another spelling, may keep the file production but never
    makes it test-only: _named_in_production cannot see every production
    declaration (a literal `mod x;` in a macro body, a renamed module macro:
    docs/KNOWN_HAZARDS.md), so a test-only reading stays where it stood
    before (review of LAND-GATE-EW1-FOLLOWUP-REVIEW-3: rustc-main's
    src/lib.rs -> ../real/lib_real.rs, or src/Lib.rs, holding
    `#[cfg(test)] mod x;` turned the x.rs main.rs's `lit!();` compiles
    test-only)."""
    d, base = posixpath.split(path)
    stem = posixpath.basename(d) if base == "mod.rs" else posixpath.splitext(base)[0]
    spellings = _index_spellings(g)
    exact = [p for p in _parent_candidates(path) if p in g.index.entries]
    parents = sorted({q for p in _parent_candidates(path) for q in spellings.get(fold(p), ())
                      if q in g.index.entries})
    if not parents:
        return False
    any_test, any_prod = False, False
    for p in parents:
        widened = p not in exact
        if g.index.entries[p][0] == "120000":
            real = _realpath(g, posixpath.dirname(p), _link_texts(g)[p])
            if real is None or g.index.entries.get(real, ("",))[0] not in REGULAR:
                return False
            p, widened = real, True
        lx = _lexed(g, p)
        n_all = lx.mod_decls.count(stem)
        n_test = lx.test_mod_decls.count(stem)
        if n_all:
            if n_test >= n_all and not widened:
                # Test-only evidence only where the lexer's reading before
                # LAND-GATE-EW1-FOLLOWUP-REVIEW-3 takes every declaration it
                # sees for a test one too (Lexed.legacy): `#[cfg(test)]
                # mod<U+200E>x;` and `#[cfg(test<U+200E>)] mod x;`, first read
                # since, are none, and the second a production one. (Review 4
                # of that review: as the path attributes it first read, they
                # turned a module production code compiles test-only.)
                old = lx.legacy()
                n_old = old.mod_decls.count(stem)
                if n_old and old.test_mod_decls.count(stem) >= n_old:
                    any_test = True
                elif n_old:
                    any_prod = True
            else:
                any_prod = True
    return any_test and not any_prod


# ---------------------------------------------------------------------------
# Legs.
# ---------------------------------------------------------------------------


@dataclass
class LegSpec:
    id: str
    title: str
    roots: Callable[[Graph], Set[str]]
    classes: Tuple[str, ...]                         # ("compile",) or ("compile", "runtime")
    extra: Callable[[Graph], Set[str]]               # non-package input prefixes
    partial: Optional[Callable[[Graph, List[str]], Optional[List[str]]]] = None
    include_test: bool = True                        # False: only production code runs (a stage-1 suite)
    cwd: bool = True                                 # False: reads through the cwd/executable do not reach the checkout
    doctests: bool = True                            # False: the leg builds no doctest (Read.doctest)


def _pkgs_under(g: Graph, prefixes: Sequence[str]) -> Set[str]:
    out: Set[str] = set()
    for d in g.packages:
        for p in prefixes:
            if p.endswith("/") and d.startswith(p):
                out.add(d)
            elif not p.endswith("/") and (d == p or d.startswith(p + "/")):
                out.add(d)
    return out


def _members(g: Graph, root: str) -> Set[str]:
    return {m for m in g.workspace_members.get(root, set()) if m in g.packages}


def roots_compiler_check(g: Graph) -> Set[str]:
    """Bootstrap checks compiler/tool roots and their dependency closure.

    Workspace membership alone does not select a product for x.py: the Rustc
    step starts at rustc-main (`in_tree_crates`), and tool steps select tools.
    Developer-only root members are covered by the default-members test leg.
    """
    compiler_tools = {m for m in _members(g, "") if m.startswith(("compiler/", "src/"))}
    return (compiler_tools | _members(g, "library") | _members(g, "src/tools/rust-analyzer")
            | _pkgs_under(g, ["compiler/", "src/bootstrap"]))


def roots_stage1(g: Graph) -> Set[str]:
    """What a stage-1 test run executes: every compiler/ crate (rustc-main's
    closure and every codegen backend), the standard library, and the tools
    that drive the suites (compiletest, run-make-support)."""
    return (_pkgs_under(g, ["compiler/", "src/tools/compiletest", "src/tools/run-make-support",
                            "src/build_helper"]) | _members(g, "library"))


def roots_run_make(g: Graph) -> Set[str]:
    """What the trust run-make tests execute: the stage-1 roots, and rustdoc
    (src/librustdoc and its binary, src/tools/trustdoc), which run-make-support's
    `rustdoc()` runs (tests/run-make/trust-deauthorized-frontend-effective-posture)."""
    return roots_stage1(g) | _pkgs_under(g, ["src/librustdoc", "src/tools/trustdoc"])


def roots_olean(g: Graph) -> Set[str]:
    """scripts/regen-trustir-oleans.sh --check computes the bridge closure by
    running trust-bridge-closure's binary. Its shared BRIDGE_ROOT_MODULES and
    actual loader dependencies can move the audited closure; the unrelated
    solvers and elaborator behind trust-clean cannot."""
    return {d for d in g.packages if d == "crates/trust-bridge-closure"}


def roots_bootstrap_tests(g: Graph) -> Set[str]:
    """x.py test src/bootstrap: bootstrap's own unit tests and their inline
    snapshots of the step graph, which count the crates of rustc-main's closure
    (Inc 6, 368d75f732: T11 deleted crates/trust-hmac and five snapshots went
    red with no leg to see them). Their code is bootstrap and build_helper; the
    graph they snapshot is every manifest, which selects every leg anyway
    (EVERYTHING_RULES)."""
    return _pkgs_under(g, ["src/bootstrap", "src/build_helper"])


def roots_targo_trust(g: Graph) -> Set[str]:
    """targo-trust's own workspace, tests included. x.py check builds no target
    of it (bootstrap has no check step for targo-trust), so compiler-check
    cannot cover its test targets: Inc 6's E0308 in
    targo-trust's bin test target (407bef184ef) landed past every leg."""
    return {d for d in g.packages if d == "targo-trust"}


def roots_native_targo_tests(g: Graph) -> Set[str]:
    """Native Cargo's workspace tests and the compiler/std/rustdoc they run.

    Bootstrap's Cargo test step builds the tool with the previous stage and
    exercises the next-stage compiler, including its fixture-specific shims.
    These tests are separate from the targo-trust subcommand's workspace.
    """
    return (_members(g, "src/tools/targo") | _pkgs_under(g, ["src/tools/targo"])
            | roots_run_make(g) | roots_bootstrap_tests(g))


def _extra_native_targo_tests(g: Graph) -> Set[str]:
    # Cargo's Rust tests read snapshots, manifests and scripts that are not
    # Rust package sources. Keep the complete test/fixture tree in the key.
    return {"src/tools/targo"}


def _no_extra(g: Graph) -> Set[str]:
    return set()


def _extra_compiler_check(g: Graph) -> Set[str]:
    # The non-package inputs scoped.compiler-check's IN_SCOPE_RE names that no
    # EVERYTHING rule already covers.
    return {"tests/fixtures/binary_decomp"}


def _escaping_refs(g: Graph, root: str) -> Set[str]:
    """Every path a file under `root` names with `../` that leaves `root`
    (an aux-build, an include!, a #[path], a run-make source): resolved from the
    file's directory, cut at a glob. Such a file is an input of the suite as
    much as the suite's own tree. One that leaves the repository is a path no
    tree selector sees: it widens to the whole suite root's parent tree."""
    out = _relative_refs(g, root)
    return {EVERYTHING} if out is None else out | _symlink_escapes(g, root)


# One record of `git grep -n -o -z`: <rev>:<path> NUL <line> NUL <match> LF. A
# path holds no NUL and a match no LF, so a record reads unambiguously.
GREP_MATCH_RECORD = re.compile(rb'([^\0]*)\0([0-9]+)\0([^\n]*)\n')
# A `../` reference, as the ../ scan's git grep pattern spells it.
RELATIVE_REF = re.compile(r"(?:\.\./)+[^\] \"'),;>`]*")


def _ref_spellings(ref: str) -> Set[str]:
    """A `../` reference as the ../ scan matched it (to a space, quote or
    bracket), and as a reader that ends it at whitespace or a line break takes
    it (compiletest reads a directive's line without its CRLF's CR, a token
    ends at a tab): cut at its first line break, cut at its first whitespace
    or NUL, and each `../` path after one. Each is a read, so the scan only
    adds paths. (LAND-GATE-EW1-FOLLOWUP-REVIEW-3: a match runs to the end of
    its line, so in a CRLF file a reference that ends its line kept the CR and
    named no file; reading lines split at every line break had dropped it.)"""
    out = {ref}
    lines = ref.splitlines()
    if lines:
        out.add(lines[0])
    for part in re.split(r"[\s\0]+", ref):
        out.update(m.group(0) for m in RELATIVE_REF.finditer(part))
    return out


def _relative_refs(g: Graph, root: str) -> Optional[Set[str]]:
    # POSIX ERE: a `]` is literal only first in a bracket; the quote is a real quote.
    # Every file as text, bytes, paths as stored (_git_grep; -z): a ui test
    # with a NUL, a byte that is not UTF-8 or a non-ASCII name was never read.
    found = _git_grep(g, ["-n", "-o", "-z", "--no-column", "-E", "(\\.\\./)+[^] \"'),;>`]*"], [root])
    out: Set[str] = set()
    if found is None:
        return None
    prefix = (g.index.rev + ":").encode()
    pos = 0
    while pos < len(found):
        record = GREP_MATCH_RECORD.match(found, pos)
        if record is None or not record.group(1).startswith(prefix):
            return None  # output this cannot read: the caller reads everything
        pos = record.end()
        path = record.group(1)[len(prefix):].decode("utf-8", "surrogateescape")
        for ref in sorted(_ref_spellings(record.group(3).decode("utf-8", "surrogateescape"))):
            target = _norm(posixpath.dirname(path), ref)
            if target is None:
                out.add(EVERYTHING)
                continue
            target, _ = _cut_glob(target)
            if target and not (target == root or target.startswith(root + "/")):
                out.add(target)
    return out


def _symlink_escapes(g: Graph, root: str, symlinks: Optional[Dict[str, bytes]] = None) -> Set[str]:
    """What a symbolic link under `root` points at outside `root` (a file read
    through a link is that file): its target, resolved from the link's
    directory; EVERYTHING when the link leaves the repository."""
    if symlinks is None:
        links = [p for p, (mode, _) in g.index.entries.items()
                 if mode == "120000" and (p == root or p.startswith(root + "/"))]
        symlinks = g.index.read_blobs(links)
    out: Set[str] = set()
    for p, blob in symlinks.items():
        text = blob.decode("utf-8", "surrogateescape")
        for target in {_norm(posixpath.dirname(p), text), _realpath(g, posixpath.dirname(p), text)}:
            if target is None:
                out.add(EVERYTHING)
            elif not (target == root or target.startswith(root + "/")):
                out.add(target if target else EVERYTHING)
    return out


# What compiletest reads from a whole suite before any filter applies: it walks
# the suite root, honours `compiletest-ignore-dir` markers, parses the
# directives of EVERY test file (src/tools/compiletest/src/lib.rs,
# collect_and_make_tests: "This always inspects _all_ test files in the suite
# ... regardless of whether any filters/tests were specified"), panics on a bad
# directive or an overlapping test stem, and only then filters. So one broken
# tests/ui/<anything>.rs fails `x.py test tests/ui/trust`, and one broken
# tests/run-make/<dir>/rmake.rs fails the trust run-make tests.
UI_COLLECTION = ("tests/ui/*.rs", "tests/ui/*compiletest-ignore-dir")
RUN_MAKE_COLLECTION = ("tests/run-make/*rmake.rs", "tests/run-make/*compiletest-ignore-dir")


def _extra_ui(g: Graph) -> Set[str]:
    return {"tests/ui/trust"} | _escaping_refs(g, "tests/ui/trust") | set(UI_COLLECTION)


def run_make_trust_dirs(g: Graph) -> Set[str]:
    """`x.py test tests/run-make --test-args trust` runs every run-make test
    whose path contains `trust`: a run-make test is a directory holding an
    `rmake.rs` (compiletest does not look inside one for more), at any depth
    under tests/run-make, and the filter is a substring of its path."""
    if g.run_make_dirs_cache is None:
        # compiletest asks whether `dir.join("rmake.rs")` exists, which on the
        # landing host's file system is true of Rmake.rs too, and rustc then
        # compiles that file (LAND-GATE-EW1-FOLLOWUP-REVIEW-3: an exact name
        # left such a test, and every path it reads, out of the leg).
        rmake = sorted(posixpath.dirname(p) for p in g.index.entries
                       if p.startswith("tests/run-make/") and fold(posixpath.basename(p)) == "rmake.rs")
        tests: Set[str] = set()
        for d in rmake:
            if not any(d.startswith(t + "/") for t in tests):
                tests.add(d)
        g.run_make_dirs_cache = tuple(sorted(d for d in tests if "trust" in d[len("tests/run-make/"):]))
    return set(g.run_make_dirs_cache)


# A run-make recipe reaches the source tree through run-make-support's
# `source_root()` (the SOURCE_ROOT compiletest exports), with no `../` in sight:
# tests/run-make/trust-ir-fndef-declaration-signatures compiles
# `source_root().join("tests/ui/trust").join(..)`, and
# trust-instance-census-cache hands `source_root()` to its own validate.py.
SOURCE_ROOT_RE = re.compile(r'source_root|SOURCE_ROOT')


def run_make_reads(g: Graph) -> Dict[str, Set[str]]:
    """For each trust run-make test directory, what it reads outside itself:
    every `../` reference and symbolic link (_escaping_refs), and, for a recipe
    that names the source root, every repository path any file of the
    directory spells anchored at a top-level entry (the recipe's literals and
    those of the scripts it hands the root to). A directory that names the
    source root and spells no repository path reads EVERYTHING."""
    if g.run_make_reads_cache is None:
        discovered = _discover_run_make_reads(g)
        g.run_make_reads_cache = tuple((d, frozenset(reads)) for d, reads in sorted(discovered.items()))
    return {d: set(reads) for d, reads in g.run_make_reads_cache}


def _discover_run_make_reads(g: Graph) -> Dict[str, Set[str]]:
    dirs = sorted(run_make_trust_dirs(g))
    if not dirs:
        return {}
    # These directories never overlap: compiletest stops at the first rmake.rs.
    # Inventory their regular files and symlinks once, rather than walking the
    # full tree separately for every directory and every source-root reader.
    files: Dict[str, List[str]] = {d: [] for d in dirs}
    links: Dict[str, List[str]] = {d: [] for d in dirs}
    for path, (mode, _) in g.index.entries.items():
        if not path.startswith("tests/run-make/"):
            continue
        d = path
        while d and d not in files:
            d = posixpath.dirname(d)
        if d:
            if mode == "120000":
                links[d].append(path)
            elif path != d and mode in ("100644", "100755"):
                files[d].append(path)
    relative = {d: _relative_refs(g, d) for d in dirs}
    # A failed relative scan already reads EVERYTHING and historically never
    # opened that directory's symlinks. Keep that error boundary unchanged.
    link_blobs = g.index.read_blobs([p for d in dirs if relative[d] is not None for p in links[d]])
    out: Dict[str, Set[str]] = {}
    for d, refs in relative.items():
        out[d] = ({EVERYTHING} if refs is None else refs | _symlink_escapes(
            g, d, {p: link_blobs[p] for p in links[d]}))
    # Every file as text, bytes, paths as stored (_git_grep; -z): a recipe
    # with a NUL, a byte that is not UTF-8 or a non-ASCII name named nothing.
    listed = _git_grep(g, ["-l", "-z", "-E", SOURCE_ROOT_RE.pattern], dirs)
    if listed is None:
        return {d: {EVERYTHING} for d in dirs}
    named = set()
    for path in _grep_listed(g, listed):
        named.update(d for d in dirs if path.startswith(d + "/"))
    top = {p.split("/", 1)[0] for p in g.index.entries}
    blobs = g.index.read_blobs([p for d in sorted(named) for p in files[d]])
    for d in sorted(named):
        found = _anchored_paths(g, files[d], top, blobs)
        out[d] |= {t for t in found if not (t == d or t.startswith(d + "/"))} if found else {EVERYTHING}
    return out


def _anchored_paths(g: Graph, files: Sequence[str], top: Set[str],
                    blobs: Optional[Dict[str, bytes]] = None) -> Set[str]:
    """Every repository path the text of `files` spells anchored at a top-level
    entry of the tree ("tests/ui/trust", "scripts/x.py", a `.join("a").join("b")`
    chain as a/b), cut at a glob or a format placeholder."""
    found: Set[str] = set()
    if blobs is None:
        blobs = g.index.read_blobs(list(files))
    # The first component compares as the landing host compares names (fold):
    # `source_root().join("Tests/ui/trust/b.rs")` opens tests/ui/trust/b.rs, a
    # read the selector then folds too. Until LAND-GATE-EW1-FOLLOWUP-REVIEW-3
    # it was exact here, as it was in the harvest (_harvest_package_literals).
    ftop = {fold(t) for t in top if t not in ("", ".", "..")}
    for path in files:
        blob = blobs[path]
        # Binary data (a NUL in its first 8 KiB) spells no path the directory
        # reads; Rust source does whatever its bytes, since trustc compiles a
        # NUL in a comment or a string (until LAND-GATE-EW1-FOLLOWUP-REVIEW-3
        # such a file was skipped too).
        if b"\0" in blob[:8192] and not _rust_source(path):
            continue  # binary
        text = blob.decode("utf-8", "replace")
        # Rust source by its name as the landing host compares it (_rust_source):
        # a recipe spelt RMAKE.RS is compiled, so its escapes are decoded and
        # its comments spell nothing (LAND-GATE-EW1-FOLLOWUP-REVIEW-3: an exact
        # `.rs` read it as text, and a computed path it named only in a comment
        # read that one path instead of EVERYTHING).
        lx = _lexed(g, path, text) if _rust_source(path) else None
        if lx is not None:
            chains = [values for _s, _e, values in _string_chains(lx, text)]
            text = lx.without_comments()
        else:
            chains = [re.findall(r'"([^"\\]*)"', m.group(0))
                      for m in re.finditer(HARVEST_RE.replace("[[:space:]]", r"\s"), text)]
        for parts in chains:
            if not parts:
                continue
            v = "/".join(x.strip("/") for x in parts if x.strip("/")) if len(parts) > 1 else parts[0]
            v = re.sub(r"^(?:\.\.?/)+", "", PLACEHOLDER.sub("", v)).lstrip("/")
            head = v.split("/", 1)[0]
            if fold(head) in ftop and head not in ("", ".", ".."):
                cut, _ = _cut_glob(v.rstrip("/"))
                if cut:
                    found.add(cut)
        for start, spelt in _top_anchored(text, ftop):
            if lx is not None and lx.in_comment(start):
                continue
            cut, _ = _cut_glob(PLACEHOLDER.sub("", spelt).rstrip("/."))
            if cut:
                found.add(cut)
    return found


PATH_TAIL = re.compile(r"[\w./+-]*")
NOT_PATH_START = re.compile(r"[\w./-]")


def _top_anchored(text: str, ftop: Set[str]) -> Iterable[Tuple[int, str]]:
    """Each path `text` spells from a top-level entry, compared as the landing
    host compares names (`ftop`, the entries folded): a first component
    preceded by no word character, `.`, `/` or `-` whose fold is an entry,
    then `/` and the rest of the path, leftmost first and not overlapping, as
    a regex of the entries would find them spelt exactly. A component never
    folds shorter than it is spelt, so it is at most the longest entry long."""
    longest = max(map(len, ftop), default=0)
    after = 0  # a first component starts here or later: past the last `/` or path
    for slash in (m.start() for m in re.finditer("/", text)):
        if slash < after:
            continue  # inside the path found last
        start = after
        after = slash + 1
        for i in range(max(start, slash - longest), slash):
            if (i == 0 or not NOT_PATH_START.match(text, i - 1)) and fold(text[i:slash]) in ftop:
                after = PATH_TAIL.match(text, slash + 1).end()
                yield i, text[i:after]
                break


def _extra_run_make(g: Graph) -> Set[str]:
    out = set(run_make_trust_dirs(g)) | set(RUN_MAKE_COLLECTION)
    for reads in run_make_reads(g).values():
        out |= reads
    return out


def _extra_olean(g: Graph) -> Set[str]:
    return {"crates/trust-clean/fixtures/trustir-oleans"}


def _ui_partial(g: Graph, paths: List[str]) -> Optional[List[str]]:
    """Fixture-only change under tests/ui/trust: the test files to run, or None
    for the whole suite. A sibling output (.stderr, .stdout, .fixed, a
    revision's .<rev>.stderr, ...) names the .rs of the same stem. An
    auxiliary/ file, a file with no .rs of its stem, or a file another test
    names, runs the whole suite."""
    root = "tests/ui/trust/"
    targets: Set[str] = set()
    stems: Dict[str, str] = {}
    for p in paths:
        if not p.startswith(root):
            return None
        rel = p[len(root):]
        if rel.startswith("auxiliary/") or "/auxiliary/" in rel:
            return None
        # The searches below fold ASCII case only (git grep -i), and the landing
        # host folds names fully (fold(): NFD and Unicode case folding, so
        # `Données.rs` opens données.rs): a changed path that is not ASCII runs
        # the whole suite. The whole path, as a mod.rs is named by its
        # directory (LAND-GATE-EW1-FOLLOWUP-REVIEW-3).
        if not rel.isascii():
            return None
        d, base = posixpath.split(p)
        stem = base.split(".", 1)[0]
        test = posixpath.join(d, stem + ".rs")
        if base.endswith(".rs") and base != stem + ".rs":
            return None  # foo.bar.rs: not a test file of the usual shape
        if test not in g.index.entries and not base.endswith(".rs"):
            return None  # an output whose test is gone, or a non-test file (.lean, data): whole suite
        if test in g.index.entries:
            targets.add(test)  # a deleted test runs nowhere; its references are checked below
        stems[posixpath.join(d, stem)] = base
    # Is any changed file named by a test that is not itself selected? Named as
    # the landing host compares names: rustc opens include_str!("A.rs"),
    # #[path = "A.rs"] and `mod Helper;` as a.rs and helper.rs, so the search
    # ignores case (-i; until LAND-GATE-EW1-FOLLOWUP-REVIEW-3 it was exact,
    # and a miscased reader ran only the changed fixture, or nothing once it
    # was deleted). git folds only ASCII, so a non-ASCII name (é, or NFD
    # against NFC) runs the whole suite: the changed path's check above, as
    # each name is part of its path. Every file as text, paths as stored.
    names = sorted({posixpath.basename(p) for p in paths})
    if names:
        argv = ["-l", "-z", "-i", "-w", "-F"]
        for n in names:
            argv += ["-e", n]
        listed = _git_grep(g, argv, [root])
        if listed is None:
            return None
        for hit in _grep_listed(g, listed):
            d, base = posixpath.split(hit)
            if posixpath.join(d, base.split(".", 1)[0]) in stems:
                continue  # the test's own file or one of its own outputs
            return None
    if _ui_mod_named(g, root, paths) or _ui_folds_into_ascii(g, root):
        return None
    return sorted(targets)


def _ui_mod_named(g: Graph, root: str, paths: List[str]) -> bool:
    """A module file is loaded by name, not by file name: `mod helper;` in
    tests/ui/trust/a.rs compiles tests/ui/trust/helper.rs (`mod sub;`,
    sub/mod.rs). True when some `mod <name>;` under `root` names a changed .rs
    file's stem (for a mod.rs, its directory too), or the search fails: the
    whole suite then runs. Every file as text, in bytes (_git_grep: in a
    UTF-8 locale a line holding a byte that is not UTF-8 matched nothing).
    (Until LAND-GATE-EW1-FOLLOWUP-REVIEW-3 the search was exact and in the
    caller's locale.)"""
    # Names compare as the landing host compares them: `mod Helper;` compiles
    # helper.rs, and `mod sub;` sub/MOD.rs, so the file names fold and the
    # search ignores case (LAND-GATE-EW1-FOLLOWUP-REVIEW-3; _ui_partial runs
    # the whole suite for a name that is not ASCII, which git grep -i does
    # not fold). A mod.rs is still named by its own stem as well: a crate root
    # beside sub/MOD.rs loads it by `mod MOD;`, and one beside sub/mod.rs by
    # `mod r#mod;` (LAND-GATE-EW1-FOLLOWUP-REVIEW-3: searching only the
    # directory's name for a MOD.rs ran the changed file alone).
    mods = sorted({posixpath.basename(p)[:-3] for p in paths if fold(p).endswith(".rs")}
                  | {posixpath.basename(posixpath.dirname(p)) for p in paths
                     if fold(posixpath.basename(p)) == "mod.rs"})
    if not mods:
        return False
    if not all(m.isascii() for m in mods):
        return True
    pattern = r"(^|[^[:alnum:]_])mod[[:space:]]+(r#)?(%s)[[:space:]]*;" % "|".join(re.escape(m) for m in mods)
    listed = _git_grep(g, ["-l", "-z", "-i", "-E", pattern], [root])
    return listed is None or bool(listed.strip(b"\0\n"))


def _folds_into_ascii() -> Tuple[str, ...]:
    """The characters that are not ASCII but fold (fold()) to ASCII: KELVIN
    SIGN to k, LONG S to s, SHARP S to ss, the fi ligature to fi, ... On the
    landing host a name spelt with one opens an ASCII-named file (APFS opens
    `helper.rſ` as helper.rs), which no ASCII case folding finds. Memoized
    per fold function."""
    chars = _FOLDS_INTO_ASCII.get(fold)
    if chars is None:
        chars = _FOLDS_INTO_ASCII[fold] = tuple(chr(c) for c in range(0x80, 0x110000)
                                                if not 0xD800 <= c < 0xE000 and fold(chr(c)).isascii())
    return chars


_FOLDS_INTO_ASCII: Dict[Callable[[str], str], Tuple[str, ...]] = {}


def _ui_folds_into_ascii(g: Graph, root: str) -> bool:
    """True when some file under `root` holds a character that folds into
    ASCII (_folds_into_ascii), or the search fails: such a file may name any
    changed file, as `include_str!("a.rſ")` names a.rs, past the
    case-insensitive searches, so the whole suite runs
    (LAND-GATE-EW1-FOLLOWUP-REVIEW-3)."""
    chars = _folds_into_ascii()
    if not chars:
        return False
    argv = _grep_command(g, ["-l", "-F"])
    for c in chars:
        argv += ["-e", c]
    proc = subprocess.run(argv + [g.index.rev, "--", root], capture_output=True, env=git_env())
    return proc.returncode not in (0, 1) or bool(proc.stdout.strip())


def _run_make_partial(g: Graph, paths: List[str]) -> Optional[List[str]]:
    """A change that reaches the trust run-make tests only through their own
    files and what they read outside themselves: the test dirs whose files
    changed, and the dirs that read a changed path. A path no single dir
    accounts for (a collection input: another run-make recipe) runs them all."""
    reads = {d: _InputSet(r) for d, r in run_make_reads(g).items()}
    targets: Set[str] = set()
    for p in paths:
        own = [d for d in reads if p == d or p.startswith(d + "/")]
        readers = _run_make_readers(g, p, reads)
        if not own and not readers:
            return None
        targets.update(own)
        targets.update(readers)
    return sorted(targets)


def _run_make_readers(g: Graph, path: str, reads: Dict[str, "_InputSet"]) -> List[str]:
    """The trust run-make dirs that read `path`, by the selector's own test
    (_reads): through a link or a miscased name too, or a dir that reads it so
    is left out of a run that another dir's exact read narrowed to."""
    return [d for d, r in reads.items() if _reads(g, path, r)]


LEGS: Tuple[LegSpec, ...] = (
    # `cargo check --all-targets` checks the test targets and builds no doctest.
    LegSpec("compiler-check", "x.py check --stage 1 --all-targets", roots_compiler_check, ("compile",),
            _extra_compiler_check, doctests=False),
    LegSpec("ui-trust", "x.py test --stage 1 tests/ui/trust", roots_stage1, ("compile", "runtime"),
            _extra_ui, _ui_partial, include_test=False, cwd=False),
    LegSpec("run-make-trust", "x.py test --stage 1 tests/run-make --test-args trust", roots_run_make,
            ("compile", "runtime"), _extra_run_make, _run_make_partial, include_test=False, cwd=False),
    # The example the audit runs is compiled and RUN: its runtime reads count
    # (class "never" is the one examples/ and benches/ are recorded under).
    LegSpec("olean-audit", "scripts/regen-trustir-oleans.sh --check", roots_olean, ("compile", "runtime", "never"),
            _extra_olean, include_test=False),
    LegSpec("bootstrap-tests", "x.py test src/bootstrap", roots_bootstrap_tests, ("compile", "runtime"),
            _no_extra),
    LegSpec("targo-trust", "targo --unverified test --manifest-path targo-trust/Cargo.toml", roots_targo_trust,
            ("compile", "runtime"), _no_extra),
    LegSpec("native-targo-tests", "x.py test --stage 1 src/tools/targo", roots_native_targo_tests,
            ("compile", "runtime"), _extra_native_targo_tests),
)


def unit_test_crates(g: Graph) -> Set[str]:
    """The compiler crates with a #[test], and the three rustc_private crates
    the compiler sysroot requires (scripts/check_compiler_unit_tests.sh's
    RUSTC_PRIVATE_CRATES), as check_compiler_unit_tests.sh would run them."""
    candidates = _pkgs_under(g, ["compiler/"]) | {d for d in ("crates/trust-mir-extract", "crates/trust-thir-lower",
                                                              "crates/trust-witness") if d in g.packages}
    # Paths as stored (-z; _git_grep): a #[test] only in a file whose name git
    # quotes (données.rs) named no package until LAND-GATE-EW1-FOLLOWUP-REVIEW-3.
    listed = _git_grep(g, ["-l", "-z", "-F", "#[test]"], sorted(candidates))
    if listed is None:
        return candidates  # cannot tell: every candidate (the script re-checks)
    with_tests: Set[str] = set()
    for path in _grep_listed(g, listed):
        o = g.owner(path)
        if o in candidates:
            with_tests.add(o)
    return with_tests


def crates_lane_sets(g: Graph) -> Tuple[Set[str], Set[str]]:
    """(developer default-members, own-workspace roots): the two kinds of crate
    scripts/check_crates_tests_scoped.py tests, at the selected commit, each a
    package of this graph. The default-members come from the root Cargo.toml's
    `default-members`, which is Cargo's inventory too (the lane reads it from
    `targo metadata`). The own-workspace roots come from the lane's own rule,
    scripts/lib/crates_lane_members.py: `crates/<dir>`, one level deep, with a
    `[workspace]` line. Before LAND-GATE-HOOKLESS-1 round 5 (D1) this took
    every `[workspace]` under crates/ at any depth. The lane could attribute
    none of the six nested ones and ran without them, and the gate stored a
    PASS for each one anyway."""
    import crates_lane_members  # scripts/lib is on sys.path for every caller
    # Read the single authority at the selected commit, not a duplicate list.
    root = tomllib.loads(g.index.read_blobs(["Cargo.toml"])["Cargo.toml"].decode())
    defaults = root.get("workspace", {}).get("default-members")
    if not isinstance(defaults, list) or not defaults:
        raise RuntimeError("canonical workspace has no developer default-members")
    members = {m for m in _expand_members(g.index, "", defaults, set(g.packages)) if m in g.packages}
    manifests = sorted(p for p, (mode, _) in g.index.entries.items()
                       if mode != "160000" and crates_lane_members.own_workspace_manifest(p))
    blobs = g.index.read_blobs(manifests)
    roots: Set[str] = set()
    for m in manifests:
        try:
            text = blobs[m].decode("utf-8")
        except UnicodeDecodeError:
            continue  # the lane's read_text fails on it too and skips it
        r = crates_lane_members.own_workspace_root(m, text)
        if r is not None and r in g.packages:
            roots.add(r)
    return members, roots


def crates_members(g: Graph) -> Set[str]:
    """The crates the crates lane tests: its developer default-members and its
    own-workspace crates (crates_lane_sets). It is the lane's set, so the land
    gate never hands the lane a member the lane cannot attribute (round 5, D1)."""
    defaults, roots = crates_lane_sets(g)
    return defaults | roots


# Selection.per_crate's family for nested_workspace_crates: decided as the
# crates members are, so the crates leg can name the ones a change reaches.
NESTED_CRATES = "crates-tests-not-covered"


def nested_workspace_crates(g: Graph) -> Set[str]:
    """Packages under crates/ that declare their own `[workspace]` and are no
    crate of the crates lane (crates_members): a harness or fixture crate
    nested inside a member (crates/trust-disasm/harness/native-invariant,
    crates/trust-clean/fixtures/.../extract-foldmemo). No leg here tests one as
    a crate. The crates leg names each one the change touches or reaches as NOT
    COVERED, never as tested (round 5, D1)."""
    lane = crates_members(g)
    return {d for d in g.workspace_members
            if d.startswith("crates/") and d in g.packages and d not in lane}


# ---------------------------------------------------------------------------
# Selection.
# ---------------------------------------------------------------------------


@dataclass
class Decision:
    leg: str
    selected: bool
    targets: Optional[List[str]]       # None = the whole leg; a list = only these
    reasons: List[str]
    inputs: List[str]                  # input prefixes (EVERYTHING possible), for the cache key
    history: List[str] = field(default_factory=list)  # sites that read git history (cache keys add HEAD)


@dataclass
class Selection:
    base: str
    head: str
    changed: List[str]
    everything: List[str]
    decisions: Dict[str, Decision] = field(default_factory=dict)
    # The changed paths a regular file before and after (changed_in_place):
    # the only changes a listing read (Read.listing) does not see. Empty
    # unless the caller read the diff's statuses.
    in_place: Set[str] = field(default_factory=set)
    per_crate: Dict[str, Dict[str, Decision]] = field(default_factory=dict)
    # Proven semantic Cargo deltas, derived from both committed trees. These
    # add actual owning/feature-activation readers without inventing paths in
    # the changed set or weakening raw-file reads and unresolved inputs.
    cargo_impacts: Dict[str, Set[str]] = field(default_factory=dict)

    def as_json(self) -> dict:
        def dec(d: Decision) -> dict:
            return {"selected": d.selected, "targets": d.targets, "reasons": d.reasons}
        return {
            "base": self.base, "head": self.head, "changed": len(self.changed),
            "everything": self.everything,
            "cargo_impacts": {p: sorted(owners) for p, owners in sorted(self.cargo_impacts.items())},
            "legs": {k: dec(v) for k, v in self.decisions.items()},
            "per_crate": {fam: sorted(k for k, v in per.items() if v.selected)
                          for fam, per in self.per_crate.items()},
        }


def global_inputs(g: Graph) -> List[str]:
    """The paths that are inputs of EVERY leg: the ones a change to selects
    everything (EVERYTHING_RULES, an unparsable manifest's tree, a submodule pin,
    and every path no package owns and no rule classifies). A cache key over a
    leg's own inputs alone would let a change to one of these hit (the selector
    runs the leg, the cache would skip it), so every key holds them too."""
    out: List[str] = []
    for path in g.index.entries:
        kind, _ = classify(g, path)
        if kind in ("everything", "unmapped"):
            out.append(path)
    return sorted(out)


def changed_paths(repo: str, base: str, head: str) -> List[str]:
    """Tree diff base..head: every path whose bytes differ, deletions and both
    sides of a move included (--no-renames), gitlinks included (whatever
    diff.ignoreSubmodules or .gitmodules says)."""
    out = git(repo, "-c", "diff.renames=false", "diff", "--no-renames", "--ignore-submodules=none",
              "--name-only", "-z", base, head)
    return sorted(p for p in out.decode("utf-8", "surrogateescape").split("\0") if p)


def changed_in_place(repo: str, base: str, head: str) -> Set[str]:
    """The paths of base..head that are a regular file (100644 or 100755) on
    both sides with different bytes or mode: a change no listing read sees.
    An addition, a deletion, a type change, a symlink or a gitlink is not.
    Raises when git cannot answer: a caller then passes no statuses."""
    out = git(repo, "-c", "diff.renames=false", "diff", "--raw", "--no-renames", "--no-abbrev",
              "--ignore-submodules=none", "-z", base, head)
    fields = out.decode("utf-8", "surrogateescape").split("\0")
    regular = ("100644", "100755")
    found: Set[str] = set()
    i = 0
    while i + 1 < len(fields):
        meta, path = fields[i], fields[i + 1]
        i += 2
        parts = meta.lstrip(":").split()
        if len(parts) != 5:
            raise ValueError(f"unexpected `git diff --raw` record {meta!r}")
        old_mode, new_mode, _old, _new, status = parts
        if status == "M" and old_mode in regular and new_mode in regular:
            found.add(path)
    return found


def leg_inputs(g: Graph, roots: Set[str], classes: Tuple[str, ...], include_test: bool = True,
               test_roots: Optional[Set[str]] = None, _expanding: Tuple[str, ...] = (),
               cwd: bool = True, listed: Optional[Set[str]] = None,
               doctests: bool = True) -> Tuple[Set[str], List[str], List[str]]:
    """The input prefixes of the code of a leg: its closure's package dirs (and
    gitlinks) and the files they read outside themselves, in the leg's classes.
    Test-only reads count for a package whose test code the leg runs: every
    package when include_test and test_roots is None, only test_roots when it
    is given, none when not include_test. Pseudo-inputs (@stage1,
    @targo-trust) expand to that leg's inputs. Returns (inputs, unresolved
    reasons, history sites); ({EVERYTHING}, reasons, ...) when a package in the
    closure is unresolved for the leg, or the graph holds a path dependency on
    an unparsable manifest. `cwd`: whether reads through the working directory
    or the executable (Read.cwd) count: they do where the leg runs tests or
    tools from the checkout, not for the stage-1 suites (see Read.cwd).
    `listed`: when given, listing reads (Read.listing) go there instead of
    into the inputs; without it they are inputs like any read. `doctests`:
    whether a doctest's records (Read.doctest) count where test code does;
    not for a leg that builds no doctest."""
    closure = g.closure(roots)
    inputs: Set[str] = set(closure)
    reasons: List[str] = []
    history: List[str] = []
    pseudo: Set[str] = set()

    def counts(d: str, r: "Read") -> bool:
        if r.cls not in classes:
            return False
        if r.cwd and not cwd and r.cls == "runtime":
            return False  # compile-time reads run under Cargo in the checkout: they always count
        if not r.test_only:
            return True
        if not include_test or (r.doctest and not doctests):
            return False
        return test_roots is None or d in test_roots

    for d in sorted(closure):
        pkg = g.packages.get(d)
        if pkg is None:
            continue
        for r in pkg.reads:
            if counts(d, r):
                if r.target.startswith("@"):
                    pseudo.add(r.target)
                elif r.listing and listed is not None:
                    listed.add(r.target)
                else:
                    inputs.add(r.target)
        for r in pkg.unresolved:
            if counts(d, r):
                reasons.append(f"{d}: {r.target}")
        for r in pkg.history:
            if counts(d, r):
                history.append(r.target)
        if d in g.opaque:
            reasons.append(f"{d}: {g.opaque[d]}")
    for p in sorted(pseudo):
        if p in _expanding:
            continue
        if p == STAGE1:
            sub_roots, sub_classes, sub_cwd = roots_stage1(g), ("compile", "runtime"), False
        elif p == TARGO_TRUST:
            sub_roots, sub_classes, sub_cwd = {d for d in g.packages if d == "targo-trust"}, ("compile", "runtime"), True
        else:
            reasons.append(f"unknown pseudo-input {p}")
            continue
        sub, sub_reasons, sub_hist = leg_inputs(g, sub_roots, sub_classes, False, None, _expanding + (p,), sub_cwd,
                                                listed)
        inputs |= sub
        reasons.extend(sub_reasons)
        history.extend(sub_hist)
    if "" in g.opaque:
        reasons.append(g.opaque[""])
    if reasons:
        return {EVERYTHING}, reasons, history
    return inputs, [], history


def reaches(path: str, inputs: Set[str]) -> bool:
    if isinstance(inputs, _InputSet):
        return inputs.reach(path)  # the same test, indexed once per decision
    if EVERYTHING in inputs:
        return True
    if _under_any(path, inputs):
        return True
    prefix = path + "/"
    for i in inputs:
        if i.startswith(prefix):
            return True  # a changed directory entry (a gitlink) holds an input
        if any(ch in i for ch in "*?[") and fnmatch.fnmatchcase(path, i):
            return True
    return False


GLOB_FIXED = re.compile(r"[^*?\[]*")


def _slashes(path: str) -> Iterable[int]:
    i = path.find("/")
    while i != -1:
        yield i
        i = path.find("/", i + 1)


class _Reach:
    """An input set indexed once for the many paths a decision tests against
    it: `index(path)` is `reaches(path, inputs)`, and `index.touches(link)`
    is _touches' test of one spelling. A path is looked up among the inputs
    and their directories, and matched against the globs whose fixed text it
    starts with, instead of being compared with every input."""

    def __init__(self, inputs: Iterable[str]) -> None:
        names = frozenset(inputs)
        self.everything = EVERYTHING in names
        self.names = names
        self.longest = max((len(n) for n in names), default=0)
        # An input at, above or below a path shares its first component.
        self.heads = {n.partition("/")[0] for n in names}
        # The directories strictly above an input: reaches' `i.startswith(path + "/")`.
        self.above = {n[:i] for n in names for i in _slashes(n)}
        # fnmatch matches a glob's text before its first wildcard literally.
        self.globs = [(GLOB_FIXED.match(n).group(0), n) for n in names if any(c in n for c in "*?[")]
        self._touch: Optional[Tuple[Set[str], Set[str]]] = None
        self._roots: Dict[str, tuple] = {}

    def __call__(self, path: str) -> bool:
        return self.everything or self.named(path) or any(
            path.startswith(fixed) and fnmatch.fnmatchcase(path, glob) for fixed, glob in self.globs)

    def named(self, path: str) -> bool:
        """An input at or above `path`, or below it (a changed directory
        entry, a gitlink, holds an input); globs aside."""
        if path.partition("/")[0] not in self.heads:
            return False
        if path in self.names or path in self.above:
            return True
        for i in _slashes(path):
            if i > self.longest:
                break  # no input is that long
            if path[:i] in self.names:
                return True
        return False

    def touches(self, link: str) -> bool:
        """An input at, above or under `link`, or a glob whose fixed
        directory (_cut_glob) is at or above it."""
        if self(link):
            return True
        if self._touch is None:
            cut = {n: _cut_glob(n) for n in self.names}
            fixed = {c for c, _glob in cut.values()}
            self._touch = (fixed | {c[:i] for c in fixed for i in _slashes(c)},
                           {c for c, glob in cut.values() if glob})
        at_or_below, glob_dirs = self._touch
        if link in at_or_below or "" in glob_dirs:
            return True
        return any(link[:i] in glob_dirs for i in _slashes(link))

    def through_root(self, root: str, path: str, depth: int) -> bool:
        """Whether `root`/`path`, `root`/`root`/`path`, ... (k copies, k at
        most LINK_DEPTH - depth) reaches these inputs, for `root` a link onto
        the repository root and `path` an alias `depth` links deep: what
        link_aliases would spell out, tested by the prefix instead. An input
        at or above root^k reads every path; one below it reads what it
        names there (the inputs under root^k/, re-rooted); a glob that can
        match a spelling starting with `root/` is matched against each."""
        budget = LINK_DEPTH - depth
        if budget < 1:
            return False
        if self.everything:
            return True
        prof = self._roots.get(root)
        if prof is None:
            prof = self._roots[root] = self._root_profile(root)
        covered, below, globs = prof
        if covered is not None and covered <= budget:
            return True
        for k, under in below:
            if k > budget:
                break
            if under.named(path):
                return True
        for fixed, glob in globs:
            if glob.startswith("*"):
                # A leading `*` also matches one more `root/` in front: if
                # root^k/path matches, so does root^(k+1)/path.
                if fnmatch.fnmatchcase("/".join([root] * budget + [path]), glob):
                    return True
                continue
            spelt = path
            for _k in range(budget):
                spelt = f"{root}/{spelt}"
                if spelt.startswith(fixed) and fnmatch.fnmatchcase(spelt, glob):
                    return True
        return False

    def _root_profile(self, root: str) -> tuple:
        """(the least k with an input at or above root^k, or None; for each k
        with inputs below root^k, those inputs re-rooted there; the globs
        that can match a spelling starting with `root/`)."""
        covered: Optional[int] = None
        below: List[Tuple[int, _Reach]] = []
        under_root = [n for n in self.names if n.startswith(root + "/")]
        spelt = root
        for k in range(1, LINK_DEPTH + 1):
            if spelt in self.names or any(spelt[:i] in self.names for i in _slashes(spelt)):
                covered = k  # a deeper k reads no more than every path
                break
            under = [n[len(spelt) + 1:] for n in under_root if n.startswith(spelt + "/")]
            if under:
                below.append((k, _Reach(under)))
            if not under_root or len(spelt) >= self.longest:
                break  # no input is at, above or below a deeper spelling
            spelt = f"{spelt}/{root}"
        globs = [(fixed, glob) for fixed, glob in self.globs
                 if (root + "/").startswith(fixed) or fixed.startswith(root + "/")]
        return covered, below, globs


class _InputSet(frozenset):
    """A decision's input set, keeping what the selector derives from the set
    alone: its reach index, its folded spelling and the link verdicts that do
    not depend on the changed path. Each is then computed once per decision,
    not once per changed path."""

    def __init__(self, names: Iterable[str] = ()) -> None:
        super().__init__()
        self._reach: Optional[_Reach] = None
        self._folded: Optional[_InputSet] = None
        self.verdicts: Dict[str, bool] = {}

    @property
    def reach(self) -> _Reach:
        if self._reach is None:
            self._reach = _Reach(self)
        return self._reach

    @property
    def folded(self) -> "_InputSet":
        if self._folded is None:
            self._folded = _InputSet(fold(i) for i in self if i != EVERYTHING)
        return self._folded


def _reach_index(inputs: Iterable[str]) -> _Reach:
    return inputs.reach if isinstance(inputs, _InputSet) else _Reach(inputs)


def _folded_inputs(inputs: Iterable[str]) -> Set[str]:
    """`inputs` as the landing host's file system compares names (fold)."""
    if isinstance(inputs, _InputSet):
        return inputs.folded
    return {fold(i) for i in inputs if i != EVERYTHING}


def _input_verdict(g: Graph, inputs: Iterable[str], what: str, decide: Callable[[], bool]) -> bool:
    """A verdict that depends on the input set and the graph alone, kept on an
    _InputSet so the decision computes it once."""
    memo = getattr(inputs, "verdicts", None)
    if memo is None:
        return decide()
    key = f"{what} {id(g)}"
    if key not in memo:
        memo[key] = decide()
    return memo[key]


def classify(g: Graph, path: str) -> Tuple[str, str]:
    """('everything', why) | ('package', dir) | ('validation', why) | ('prose', '') | ('suite', '') |
    ('unmapped', why)."""
    why = everything_reason(path)
    if why:
        return "everything", why
    opaque = g.opaque_owner(path)
    if opaque:
        return "everything", opaque
    owner = g.owner(path)
    if owner is not None and owner != "":
        if owner in g.gitlinks:
            return "everything", f"{owner} is a submodule pin"
        return "package", owner
    if is_validation_program(path):
        return "validation", "validation program; its own tests and actual input readers run"
    if is_prose(path):
        return "prose", ""
    if is_suite_path(path):
        return "suite", ""
    return "unmapped", f"{path}: no package owns it and no rule classifies it"


def _decide(g: Graph, sel: Selection, leg_id: str, roots: Set[str], classes: Tuple[str, ...],
            extra: Set[str], partial, include_test: bool = True,
            test_roots: Optional[Set[str]] = None, cwd: bool = True, doctests: bool = True) -> Decision:
    listed: Set[str] = set()
    content, unresolved, history = leg_inputs(g, roots, classes, include_test, test_roots, cwd=cwd, listed=listed,
                                              doctests=doctests)
    if EVERYTHING in content:
        closure_inputs, inputs, listing_only = content, content, set()
    else:
        # A listing read is an input like any other (the key, the partial
        # check); only the reach of an in-place change skips it, and only
        # where no content read covers the same target.
        closure_inputs = content | listed
        inputs = closure_inputs | extra
        listing_only = listed - content - extra
    d = _decide_inputs(sel, leg_id, inputs, closure_inputs, unresolved, partial, g, listing_only)
    d.history = sorted(set(history))
    return d


UNRESOLVED_LINK = None  # a link that leaves the repository, loops, runs out of hops, or is miscased


def _link_texts(g: Graph) -> Dict[str, str]:
    texts = getattr(g, "_link_texts", None)
    if texts is None:
        links = sorted(p for p, (mode, _) in g.index.entries.items() if mode == "120000")
        texts = {p: b.decode("utf-8", "surrogateescape") for p, b in g.index.read_blobs(links).items()}
        g._link_texts = texts  # type: ignore[attr-defined]
    return texts


def fold(path: str) -> str:
    """A path as the landing host's file system compares it: APFS (and NTFS)
    ignore case, and APFS Unicode normalization too."""
    return unicodedata.normalize("NFD", path).casefold()


def _index_spellings(g: Graph) -> Dict[str, Set[str]]:
    """Each folded spelling of a tracked path or directory, and its exact spellings."""
    m = getattr(g, "_index_spellings", None)
    if m is None:
        m = {}
        for p in g.index.entries:
            parts = p.split("/")
            for i in range(1, len(parts) + 1):
                q = "/".join(parts[:i])
                m.setdefault(fold(q), set()).add(q)
        g._index_spellings = m  # type: ignore[attr-defined]
    return m


def _index_realpath(texts: Dict[str, str], start_dir: str, rel: str,
                    spellings: Optional[Dict[str, Set[str]]] = None) -> Optional[str]:
    """`rel` resolved from `start_dir` the way the file system resolves it,
    over the tracked links: one component at a time, a component that is a
    tracked link replaced by what it names, `..` applied after that (so
    `first-party/trust/docs/x` is `docs/x`). None: it leaves the repository,
    is absolute, takes more than 40 link hops, or names a tracked path only up
    to case or Unicode normalization (`DOCS/x.md`, which a case-insensitive
    file system opens as `docs/x.md`)."""
    if rel.startswith("/"):
        return UNRESOLVED_LINK
    cur: List[str] = [c for c in start_dir.split("/") if c] if start_dir else []
    pending = list(reversed(rel.split("/")))
    hops = 0
    while pending:
        c = pending.pop()
        if c in ("", "."):
            continue
        if c == "..":
            if not cur:
                return UNRESOLVED_LINK
            cur.pop()
            continue
        cur.append(c)
        here = "/".join(cur)
        if spellings is not None:
            exact = spellings.get(fold(here))
            if exact is not None and here not in exact:
                return UNRESOLVED_LINK
        if here in texts:
            hops += 1
            if hops > 40:
                return UNRESOLVED_LINK
            target = texts[here]
            cur.pop()
            if target.startswith("/"):
                return UNRESOLVED_LINK
            pending.extend(reversed(target.split("/")))
    return "/".join(cur)


def _realpath(g: Graph, start_dir: str, rel: str) -> Optional[str]:
    return _index_realpath(_link_texts(g), start_dir, rel, _index_spellings(g))


def link_targets(g: Graph) -> Tuple[Tuple[str, Optional[str]], ...]:
    """Every tracked symbolic link and the repository path it resolves to over
    the index (_index_realpath; None: unresolvable)."""
    if g.link_targets_cache is None:
        texts = _link_texts(g)
        g.link_targets_cache = tuple((link, _realpath(g, posixpath.dirname(link), texts[link]))
                                     for link in sorted(texts))
    return g.link_targets_cache


def _touches(link: str, content: Set[str]) -> bool:
    """Whether a reader of `content` can open anything at or under `link`: an
    input at or above it, under it, or a glob whose fixed prefix is at or above
    it, with names compared as the landing host's file system compares them
    (`Crates/linker/src/N.rs` opens the link `crates/linker/src/n.rs`). Only
    for a link that cannot be resolved, which may expose anything, and for
    every link past LINK_ALIAS_LIMIT."""
    return _reach_index(content).touches(link) or _reach_index(_folded_inputs(content)).touches(fold(link))


LINK_ALIAS_LIMIT = 4096
LINK_DEPTH = 40  # the most links the kernel follows in one lookup


class _Aliases(collections.abc.Set):
    """link_aliases' answer where at most one tracked link resolves onto the
    repository root and no other link resolves to a directory above it
    (_link_shape): the aliases through the other links, each with the number
    of links it takes, and that root link. The root link shows every path
    again under itself, so each of those aliases (and the path) is also
    root/q, root/root/q, ... up to LINK_DEPTH links in all: about 40 deep
    spellings per path, which _Reach.through_root tests by their prefix
    instead of having them spelt out. Iterating yields every alias."""

    def __init__(self, path: str, plain: Dict[str, int], root: Optional[str]) -> None:
        self.path = path
        self.plain = plain  # alias -> the links it takes
        self.root = root
        self._folded: Optional[Tuple[str, Dict[str, str], Optional[str]]] = None

    def _bases(self) -> List[Tuple[str, int]]:
        return [(self.path, 0), *self.plain.items()]

    def __iter__(self):
        yield from self.plain
        if self.root is not None:
            for q, depth in self._bases():
                for _k in range(LINK_DEPTH - depth):
                    q = f"{self.root}/{q}"
                    yield q

    def __len__(self) -> int:
        return len(self.plain) + (sum(LINK_DEPTH - d for _q, d in self._bases()) if self.root is not None else 0)

    def __contains__(self, alias: object) -> bool:
        # Exactly what __iter__ yields: a plain alias, or k root links then the
        # path or a plain alias. Every k is tried, not only the most root/
        # prefixes that strip: a path can itself lie under the root link (a
        # base-side path, deleted when a directory became the link), and
        # root/<path> was then not in the set (LAND-GATE-EW1-FOLLOWUP-REVIEW-3).
        if not isinstance(alias, str):
            return False
        if alias in self.plain:
            return True
        if self.root is None:
            return False
        prefix, k = self.root + "/", 0
        while alias.startswith(prefix):
            alias, k = alias[len(prefix):], k + 1
            depth = 0 if alias == self.path else self.plain.get(alias)
            if depth is not None and k <= LINK_DEPTH - depth:
                return True
        return False

    def reach(self, inputs: Set[str], folded: Set[str]) -> bool:
        """Whether some alias reaches `inputs` (reaches), as spelt or as the
        landing host compares names (`folded`, the inputs folded)."""
        if self._folded is None:
            self._folded = (fold(self.path), {a: fold(a) for a in self.plain},
                            None if self.root is None else fold(self.root))
        fpath, fplain, froot = self._folded
        for a in self.plain:
            if reaches(a, inputs) or reaches(fplain[a], folded):
                return True
        if self.root is not None:
            index, folded_index = _reach_index(inputs), _reach_index(folded)
            for q, depth in self._bases():
                fq = fpath if q == self.path else fplain[q]
                if index.through_root(self.root, q, depth) or folded_index.through_root(froot, fq, depth):
                    return True
        return False


def _link_shape(g: Graph) -> Tuple[bool, List[str], Dict[str, List[str]], int]:
    """(whether link_aliases can leave the root links' nesting unspelt, the
    links onto the repository root, the other resolved links by the target
    they resolve to, the longest such target). Unspelt only when no other
    link resolves to a directory above a root link: then an alias through a
    root link starts with that link (nothing else leads into it), so its
    nesting is a prefix. Memoized per graph."""
    shape = getattr(g, "_link_shape", None)
    if shape is None:
        resolved = link_targets(g)
        roots = [link for link, target in resolved if target == ""]
        by_target: Dict[str, List[str]] = {}
        for link, target in resolved:
            if target:
                by_target.setdefault(target, []).append(link)
        above_roots = {a for r in roots for a in _proper_ancestors(r)}
        shape = (not (above_roots & set(by_target)), roots, by_target,
                 max((len(t) for t in by_target), default=0))
        g._link_shape = shape  # type: ignore[attr-defined]
    return shape


def link_aliases(g: Graph, path: str) -> Optional[AbstractSet[str]]:
    """Every other repository path at which `path` can be opened through
    tracked links: a link resolving onto `path` or a directory above it
    (_index_realpath) shows it at the link's own path, and a link onto (or
    above) such an alias shows it again, up to LINK_DEPTH links deep (the
    most the kernel follows in one lookup). None when there are more than
    LINK_ALIAS_LIMIT: the caller then judges by the links themselves. Links
    that cannot be resolved are _read_through_a_link's. Where _link_shape
    allows, the aliases come as _Aliases, which leaves the root link's
    nesting unspelt (the same set, counted alike). Memoized per graph."""
    cache = g.__dict__.setdefault("_link_alias_cache", {})
    if path in cache:
        return cache[path]
    unspelt, roots, by_target, longest = _link_shape(g)
    result = _spelt_aliases(g, path) if not unspelt else _unspelt_aliases(g, path, roots, by_target, longest)
    cache[path] = result
    return result


def _unspelt_aliases(g: Graph, path: str, roots: List[str], by_target: Dict[str, List[str]],
                     longest: int) -> Optional[AbstractSet[str]]:
    """link_aliases through the links not onto the root, breadth first, each
    with the links it takes; the root links' nested spellings are counted,
    not spelt (_Aliases)."""
    plain: Dict[str, int] = {}
    frontier = [path]
    for depth in range(1, LINK_DEPTH + 1):
        following: List[str] = []
        for q in frontier:
            # Each link resolving to q or a directory above it shows q again.
            for end in [*itertools.takewhile(lambda i: i <= longest, _slashes(q)), len(q)]:
                for link in by_target.get(q[:end], ()):
                    alias = link + q[end:]
                    if alias != path and alias not in plain:
                        plain[alias] = depth
                        following.append(alias)
        if len(plain) + 1 > LINK_ALIAS_LIMIT:
            return None
        if not following:
            break
        frontier = following
    # Each alias q (and the path) is also every word of k root links, then
    # q, for k up to the links q leaves: r**1 + ... + r**(LINK_DEPTH - depth).
    r = len(roots)
    nested = sum(sum(r ** k for k in range(1, LINK_DEPTH - d + 1)) for d in (0, *plain.values())) if r else 0
    if len(plain) + nested + 1 > LINK_ALIAS_LIMIT:
        return None
    if r > 1:
        return _spelt_aliases(g, path)  # only under a limit above 2**40: spelt as words of root links
    return _Aliases(path, plain, roots[0] if roots else None)


def _spelt_aliases(g: Graph, path: str) -> Optional[Set[str]]:
    """link_aliases with every alias spelt out, breadth first over every link."""
    resolved = link_targets(g)
    seen = {path}
    frontier = [path]
    result: Optional[Set[str]] = None
    for _depth in range(LINK_DEPTH):
        following: List[str] = []
        for q in frontier:
            for link, target in resolved:
                if target is UNRESOLVED_LINK:
                    continue
                if target == "":
                    alias = f"{link}/{q}"
                elif q == target:
                    alias = link
                elif q.startswith(target + "/"):
                    alias = link + q[len(target):]
                else:
                    continue
                if alias not in seen:
                    seen.add(alias)
                    following.append(alias)
        if len(seen) > LINK_ALIAS_LIMIT:
            break
        if not following:
            seen.discard(path)
            result = seen
            break
        frontier = following
    else:
        seen.discard(path)
        result = seen
    return result


def _reaches_folded(path: str, inputs: Set[str], folded: Set[str]) -> bool:
    """reaches(), also as a case-insensitive file system compares names: a
    read spelt `DOCS/x.md` opens `docs/x.md` on the landing host."""
    return reaches(path, inputs) or reaches(fold(path), folded)


def _read_through_a_link(g: Graph, path: str, inputs: Set[str], folded: Optional[Set[str]] = None) -> bool:
    """Whether an input reaches `path` at another path that tracked links show
    it at (link_aliases), by the same test a direct read gets: a `*.rs` glob
    reads `src/notes.rs -> ../docs/notes.md`, not `src/all/other.md` through
    `src/all -> ../docs`; an input under a directory link reads only what it
    names there. A link that cannot be resolved may show anything: it counts
    wherever an input touches it or any path that other links show it at.
    Past LINK_ALIAS_LIMIT, every link an input touches counts. Names compare
    as the landing host compares them throughout (fold, _touches). The two
    link verdicts do not depend on `path`: an _InputSet keeps them."""
    if folded is None:
        folded = _folded_inputs(inputs)
    aliases = link_aliases(g, path)
    if aliases is None:
        return _input_verdict(g, inputs, "a link is touched",
                              lambda: any(_touches(link, inputs) for link, _target in link_targets(g)))
    if isinstance(aliases, _Aliases):
        if aliases.reach(inputs, folded):
            return True
    elif any(_reaches_folded(alias, inputs, folded) for alias in aliases):
        return True
    return _input_verdict(g, inputs, "an unresolved link is touched", lambda: _unresolved_link_touched(g, inputs))


def _unresolved_link_touched(g: Graph, inputs: Set[str]) -> bool:
    for link, target in link_targets(g):
        if target is not UNRESOLVED_LINK:
            continue
        shown = link_aliases(g, link)
        if shown is None or _touches(link, inputs) or any(_touches(a, inputs) for a in shown):
            return True
    return False


def _reads(g: Graph, path: str, inputs: "_InputSet") -> bool:
    """Whether `inputs` read `path`, by hit()'s own test (_decide_inputs):
    named as the landing host compares names, or at a path tracked links
    show it at."""
    folded = inputs.folded
    return _reaches_folded(path, inputs, folded) or _read_through_a_link(g, path, inputs, folded)


def _decide_inputs(sel: Selection, leg_id: str, inputs: Set[str], closure_inputs: Set[str],
                   unresolved: List[str], partial, g: Graph, listing_only: Set[str] = frozenset()) -> Decision:
    if sel.everything:
        return Decision(leg_id, True, None, ["selects everything: " + r for r in sel.everything[:5]], sorted(inputs))
    content = inputs - listing_only if listing_only else inputs
    # Indexed once: every changed path is tested against these sets.
    inputs = _InputSet(inputs)
    content = _InputSet(content) if listing_only else inputs

    def hit(p: str) -> bool:
        # A changed path is read where an input names it, as the landing host's
        # file system compares names, or names a path that tracked links show
        # it at. An in-place edit changes only bytes, which a listing never
        # reads: only content inputs count for it.
        within = content if p in sel.in_place else inputs
        folded = within.folded
        return _reaches_folded(p, within, folded) or _read_through_a_link(g, p, within, folded)
    def impacted(p: str) -> List[str]:
        return [owner + "/Cargo.toml" for owner in sel.cargo_impacts.get(p, ())]

    hits = [p for p in sel.changed if hit(p) or any(hit(q) for q in impacted(p))]
    if not hits:
        return Decision(leg_id, False, [], [f"no changed path reaches its inputs ({len(sel.changed)} changed)"],
                        sorted(inputs))
    targets = None
    # A partial run is for a change no code of the leg reads. The leg's code
    # reads a hit by the test that made it one (_reads): through a link or a
    # miscased name too, or a fixture the compiler reads that way would run
    # alone, or not at all once deleted.
    closure = _InputSet(closure_inputs)
    if partial is not None and not any(_reads(g, q, closure) for p in hits for q in [p, *impacted(p)]):
        targets = partial(g, hits)
        if targets == []:
            return Decision(leg_id, False, [], ["only deleted fixtures changed, and no other fixture names them"],
                            sorted(inputs))
    why = ([f"inputs unresolved: {r}" for r in unresolved[:2]] +
           [f"{p} reaches it" for p in hits[:5]] + ([f"... {len(hits) - 5} more"] if len(hits) > 5 else []))
    return Decision(leg_id, True, targets, why, sorted(inputs))


def select(g: Graph, base: str, changed: List[str], extra_everything: Sequence[str] = (),
           in_place: Optional[Set[str]] = None) -> Selection:
    from land_manifest import scoped_inputs

    sel = Selection(base=base, head=g.index.rev, changed=list(changed), everything=list(extra_everything),
                    in_place=set(in_place or ()) & set(changed), cargo_impacts=scoped_inputs(g, base, changed))
    for p in changed:
        if p in sel.cargo_impacts:
            continue
        kind, why = classify(g, p)
        if kind == "everything":
            sel.everything.append(f"{p}: {why}")
        elif kind == "unmapped":
            sel.everything.append(why)
    for leg in LEGS:
        sel.decisions[leg.id] = _decide(g, sel, leg.id, leg.roots(g), leg.classes, leg.extra(g), leg.partial,
                                        leg.include_test, cwd=leg.cwd, doctests=leg.doctests)
    for family, members in (("compiler-unit-tests", unit_test_crates(g)), ("crates-tests", crates_members(g)),
                            # Decided like members, but tested by no leg: the
                            # crates leg names the ones selected NOT COVERED.
                            (NESTED_CRATES, nested_workspace_crates(g))):
        sel.per_crate[family] = {m: _decide(g, sel, m, {m}, ("compile", "runtime"), set(), None, True, {m})
                                 for m in sorted(members)}
    return sel
