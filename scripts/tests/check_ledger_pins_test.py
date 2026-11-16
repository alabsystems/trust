"""Tests for scripts/check_ledger_pins.py (LEDGER-PIN-CURRENCY-AT-LANDING-1).

The row refuses a pushed tree in which a blob pinned by the escape-audit
ledger (an [[audit]] or [[not_path]] row's file or premise) or by the IR read
set (a reader) moved, unless the entry pinning it says, in the same tree, that
it lapsed. Each case is a fixture repository and the row's own reading of a
commit's tree from git objects: red when a premise, a file or a reader moved
with neither a renewal nor a lapse, green with either; a lapse on another row,
a malformed or misspelt lapse, and a duplicate row do not excuse it; the keys
name the entry and its pinned blob, never the tree's blob, so a red main
already carries is INHERITED by push-rows. The CLI contract (TRUST_PUSHED_REFS,
`FINDINGS: complete`, SKIPPED, exit 2) runs in-process and as a program.

    python3 -B scripts/tests/check_ledger_pins_test.py             # the tests
    python3 -B scripts/tests/check_ledger_pins_test.py --mutants   # each MUTANT must be killed

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""
from __future__ import annotations

import contextlib
import hashlib
import inspect
import io
import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple
from unittest import mock

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "check_ledger_pins.py"
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(REPO / "scripts" / "lib"))

import check_ledger_pins as clp  # noqa: E402
import land_select as ls  # noqa: E402

ISOLATED = {"GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_NOSYSTEM": "1"}
FIXTURE_ENV = {**ISOLATED, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t", "GIT_COMMITTER_NAME": "t",
               "GIT_COMMITTER_EMAIL": "t@t", "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "maintenance.auto",
               "GIT_CONFIG_VALUE_0": "false"}
LAPSE = "2026-11-10 0123456789: a premise moved; not renewed in this push"

AUDITED = "crates/a/src/lib.rs"
PREMISE = "crates/a/src/caller.rs"
OTHER = "crates/c/src/lib.rs"
NAMES = "crates/b/src/names.rs"
NAMES_PREMISE = "crates/b/src/lib.rs"
READER = "scripts/reader.py"
READER2 = "scripts/lib/reader2.py"
BASE = {
    AUDITED: "fn a() { std::process::Command::new(\"git\"); }\n",
    PREMISE: "fn caller() { a(); }\n",
    OTHER: "fn c() {}\n",
    NAMES: "fn kind(n: &str) -> bool { n == \"docs\" }\n",
    NAMES_PREMISE: "mod names;\n",
    READER: "# the IR-only run's entry\n",
    READER2: "# a module it imports\n",
}


def blob(text: str) -> str:
    data = text.encode()
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def toml(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, list):
        return "[" + ", ".join(toml(v) for v in value) + "]"
    if isinstance(value, dict):
        return "{ " + ", ".join(f"{k} = {toml(v)}" for k, v in value.items()) + " }"
    return json.dumps(value)


def audit_row(file: str, pins: Dict[str, str], premises: Sequence[str] = (), **extra) -> str:
    row = {"file": file, "blob": blob(pins[file]), "class": "runtime", "reads": [], "history": False}
    if premises:
        row["premises"] = [{"file": p, "blob": blob(pins[p])} for p in premises]
    row["reason"] = "reviewed"
    row.update(extra)
    return "[[audit]]\n" + "".join(f"{k} = {toml(v)}\n" for k, v in row.items() if v is not None)


def not_path_row(pins: Dict[str, str], **extra) -> str:
    row = {"file": NAMES, "blob": blob(pins[NAMES]), "literals": ["docs"], "via": [],
           "premises": [{"file": NAMES_PREMISE, "blob": blob(pins[NAMES_PREMISE])}], "reason": "a match arm"}
    row.update(extra)
    return "[[not_path]]\n" + "".join(f"{k} = {toml(v)}\n" for k, v in row.items() if v is not None)


def ledger(pins: Dict[str, str], *, audit: Optional[dict] = None, other: Optional[dict] = None,
           not_path: Optional[dict] = None, extra_rows: str = "") -> str:
    """The escape-audit ledger pinning `pins` (the reviewed bytes): the
    audited file with its premise, a second row, and a not_path row; each
    dict adds or overrides that row's keys (None drops one)."""
    return "\n".join((
        "# fixture ledger\n",
        audit_row(AUDITED, pins, [PREMISE], **(audit or {})),
        audit_row(OTHER, pins, **(other or {})),
        not_path_row(pins, **(not_path or {})),
    )) + extra_rows


def read_set(pins: Dict[str, str], lapsed: Optional[dict] = None, **extra) -> str:
    doc = {"readers": {READER: blob(pins[READER]), READER2: blob(pins[READER2])},
           "schema": "trust.land-gate.ir-cohort-read-set.v1"}
    if lapsed is not None:
        doc["lapsed"] = lapsed
    doc.update(extra)
    return json.dumps(doc, indent=2, sort_keys=True) + "\n"


def clean_env(extra: Optional[Dict[str, str]] = None) -> Dict[str, str]:
    env = {k: v for k, v in os.environ.items() if k not in ls.GIT_ENV_DROPPED and k != "TRUST_PUSHED_REFS"}
    env.update(extra or {})
    return env


class Fixture:
    """A git repository whose commits are the trees the row judges."""

    def __init__(self, test: unittest.TestCase):
        tmp = tempfile.TemporaryDirectory(prefix="ledger-pins.")
        test.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve() / "repo"
        self.root.mkdir()
        self.git("init", "-q", "-b", "main")

    def git(self, *args: str) -> str:
        proc = subprocess.run(["git", "-C", str(self.root), *args], capture_output=True, env=clean_env(FIXTURE_ENV))
        if proc.returncode != 0:
            raise AssertionError(f"git {args}: {proc.stderr.decode('utf-8', 'replace')}")
        return proc.stdout.decode().strip()

    def commit(self, files: Dict[str, Optional[str]], message: str = "case") -> str:
        for rel, text in files.items():
            path = self.root / rel
            if text is None:
                if path.is_dir():
                    raise AssertionError(rel)
                path.unlink(missing_ok=True)
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def reviewed(self, **overrides) -> str:
        """A tree whose every pin holds: the base files and ledgers pinning them."""
        files: Dict[str, Optional[str]] = dict(BASE)
        files[clp.AUDITS] = ledger(BASE)
        files[clp.READ_SET] = read_set(BASE)
        files.update(overrides)
        return self.commit(files)


def run(root: Path, rev: str) -> Tuple[int, str]:
    out = io.StringIO()
    with mock.patch.dict(os.environ, ISOLATED), contextlib.redirect_stdout(out):
        rc = clp.judge_subjects(root, [("case", rev)], "SUBJECT: case")
    return rc, out.getvalue()


def keys(text: str) -> List[str]:
    return [line[len("FINDING: "):] for line in text.splitlines() if line.startswith("FINDING: ")]


def moved(table: str, row_file: str, path: str, pinned_text: str) -> str:
    return f"escape-audits {table} {row_file} MOVED {path} {blob(pinned_text)}"


class LedgerPinTests(unittest.TestCase):
    def setUp(self):
        self.repo = Fixture(self)
        self.base = self.repo.reviewed()

    def judge(self, files: Dict[str, Optional[str]]) -> Tuple[int, str]:
        return run(self.repo.root, self.repo.commit(files))

    def assertRed(self, files: Dict[str, Optional[str]], expected: Sequence[str]) -> str:
        rc, out = self.judge(files)
        self.assertEqual(rc, 1, out)
        self.assertEqual(keys(out), sorted(expected), out)
        self.assertIn("FINDINGS: complete", out)
        return out

    def assertGreen(self, files: Dict[str, Optional[str]]) -> str:
        rc, out = self.judge(files)
        self.assertEqual(rc, 0, out)
        self.assertEqual(keys(out), [], out)
        self.assertIn("PASS:", out)
        return out

    # -- every pin holds ----------------------------------------------------

    def test_a_reviewed_tree_is_green(self):
        rc, out = run(self.repo.root, self.base)
        self.assertEqual(rc, 0, out)
        self.assertIn("3 loaded row(s): 3 hold, 0 lapsed, 0 with a moved pin", out)
        self.assertIn("2 reader(s): 2 hold, 0 lapsed, 0 moved", out)

    def test_an_unpinned_file_moves_freely(self):
        self.assertGreen({"crates/a/src/unrelated.rs": "fn u() {}\n", "README.md": "prose\n"})

    # -- a moved pin: red, unless renewed or lapsed in the same tree --------

    def test_a_premise_moved_without_renewal_or_lapse_is_red(self):
        out = self.assertRed({PREMISE: "fn caller() { a(); a(); }\n"},
                             [moved("audit", AUDITED, PREMISE, BASE[PREMISE])])
        self.assertIn(f"(the tree holds {blob('fn caller() { a(); a(); }' + chr(10))})", out)
        for text in ("RENEW", "LAPSE", 'lapsed = "YYYY-MM-DD', "LEDGER-PIN-CURRENCY-AT-LANDING-1"):
            self.assertIn(text, out)
        self.assertNotIn("a reader:", out, "the repair text names only the ledger that moved")

    def test_the_audited_file_moved_is_red(self):
        self.assertRed({AUDITED: BASE[AUDITED] + "// edited\n"}, [moved("audit", AUDITED, AUDITED, BASE[AUDITED])])

    def test_a_renewal_in_the_same_tree_is_green(self):
        pins = dict(BASE, **{PREMISE: "fn caller() { a(); a(); }\n"})
        self.assertGreen({PREMISE: pins[PREMISE], clp.AUDITS: ledger(pins)})

    def test_a_lapse_in_the_same_tree_is_green(self):
        out = self.assertGreen({PREMISE: "fn caller() { a(); a(); }\n",
                                clp.AUDITS: ledger(BASE, audit={"lapsed": LAPSE})})
        self.assertIn("3 loaded row(s): 2 hold, 1 lapsed, 0 with a moved pin", out)
        self.assertNotIn("NOTE:", out)

    def test_a_lapse_on_another_row_excuses_nothing(self):
        self.assertRed({PREMISE: "fn caller() { a(); a(); }\n",
                        clp.AUDITS: ledger(BASE, other={"lapsed": LAPSE}, not_path={"lapsed": LAPSE})},
                       [moved("audit", AUDITED, PREMISE, BASE[PREMISE])])

    def test_a_lapse_whose_pins_hold_again_is_a_note(self):
        out = self.assertGreen({clp.AUDITS: ledger(BASE, other={"lapsed": LAPSE})})
        self.assertIn(f"NOTE: [[audit]] {OTHER} is lapsed but every pin it holds is current", out)

    def test_a_deleted_premise_is_absent(self):
        self.assertRed({PREMISE: None}, [f"escape-audits audit {AUDITED} ABSENT {PREMISE}"])

    def test_a_pinned_path_that_became_a_directory_is_absent(self):
        self.repo.git("rm", "-q", PREMISE)
        self.assertRed({PREMISE + "/inner.rs": "fn x() {}\n"}, [f"escape-audits audit {AUDITED} ABSENT {PREMISE}"])

    def test_a_not_path_premise_moved_is_red_and_its_lapse_is_green(self):
        self.assertRed({NAMES_PREMISE: "mod names;\nmod more;\n"},
                       [moved("not_path", NAMES, NAMES_PREMISE, BASE[NAMES_PREMISE])])
        self.assertGreen({clp.AUDITS: ledger(BASE, not_path={"lapsed": LAPSE})})

    def test_every_moved_pin_of_a_row_is_named(self):
        self.assertRed({AUDITED: "fn a2() {}\n", PREMISE: None, NAMES: "fn kind() {}\n"},
                       [moved("audit", AUDITED, AUDITED, BASE[AUDITED]),
                        f"escape-audits audit {AUDITED} ABSENT {PREMISE}",
                        moved("not_path", NAMES, NAMES, BASE[NAMES])])

    def test_keys_name_the_pinned_blob_never_the_trees(self):
        # INHERITED: a red main already carries keeps its key when a later
        # landing moves the same pin again.
        _rc, first = self.judge({PREMISE: "fn caller() { 1 }\n"})
        _rc, second = self.judge({PREMISE: "fn caller() { 2 }\n"})
        self.assertEqual(keys(first), keys(second))
        self.assertTrue(keys(first))

    # -- an entry the product would silently drop ---------------------------

    def test_a_malformed_or_misspelt_lapse_is_refused_even_where_every_pin_holds(self):
        for override in ({"lapsed": ""}, {"lapsed": "soon"}, {"lapsed": "2026-11-10"}, {"lapsed": 3},
                         {"lapse": LAPSE}, {"lapsed": None, "laps": LAPSE}):
            with self.subTest(override=override):
                self.assertRed({clp.AUDITS: ledger(BASE, audit=override)},
                               [f"escape-audits audit {AUDITED} MALFORMED"])
        self.assertRed({clp.AUDITS: ledger(BASE, not_path={"lapsed": "later"})},
                       [f"escape-audits not_path {NAMES} MALFORMED"])

    def test_a_malformed_lapse_is_explained(self):
        _rc, out = self.judge({clp.AUDITS: ledger(BASE, audit={"lapsed": "soon"})})
        self.assertIn('`lapsed` must read "YYYY-MM-DD <commit>: <why>"', out)
        self.assertIn("Neither clears the other finding(s)", out)

    def test_a_malformed_row_is_refused_by_its_file_or_position(self):
        self.assertRed({clp.AUDITS: ledger(BASE, other={"class": "neither"})},
                       [f"escape-audits audit {OTHER} MALFORMED"])
        self.assertRed({clp.AUDITS: ledger(BASE) + "\n[[audit]]\nblob = \"x\"\n"}, ["escape-audits audit #3 MALFORMED"])
        self.assertRed({clp.AUDITS: "audit = 3\n"}, ["escape-audits audit #0 MALFORMED"])

    def test_a_duplicate_row_is_refused(self):
        self.assertRed({clp.AUDITS: ledger(BASE, extra_rows="\n" + audit_row(OTHER, BASE))},
                       [f"escape-audits audit {OTHER} DUPLICATE"])
        self.assertRed({clp.AUDITS: ledger(BASE, extra_rows="\n" + not_path_row(BASE))},
                       [f"escape-audits not_path {NAMES} DUPLICATE"])

    def test_an_absent_or_unreadable_ledger_is_red(self):
        self.assertRed({clp.AUDITS: None}, ["escape-audits LEDGER-ABSENT"])
        self.assertRed({clp.AUDITS: "[[audit]\n"}, ["escape-audits LEDGER-UNREADABLE"])

    def test_the_row_rules_are_land_selects(self):
        # A row the checker accepts is one load_audits keeps, and a lapsed one
        # never holds in the product.
        lapsed = ls.tomllib.loads(ledger(BASE, audit={"lapsed": LAPSE}))["audit"][0]
        self.assertTrue(ls.audit_row_ok(lapsed))
        entries = {path: ("100644", blob(text)) for path, text in BASE.items()}
        graph = ls.Graph(ls.TreeIndex(str(self.repo.root), "fixture", "fixture", entries), {}, {}, [], {}, {})
        self.assertFalse(ls.audit_holds(graph, AUDITED, lapsed))
        self.assertTrue(ls.audit_holds(graph, AUDITED, {k: v for k, v in lapsed.items() if k != "lapsed"}))

    # -- the IR read set ----------------------------------------------------

    def test_a_reader_moved_is_red_renewed_or_lapsed_is_green(self):
        out = self.assertRed({READER: "# a new read\n"}, [f"ir-read-set {READER} MOVED {blob(BASE[READER])}"])
        self.assertIn("a reader:", out)
        self.assertIn("does any change add or alter a physical read on the IR-only cohort run's path?", out)
        self.assertNotIn("a row:", out)
        self.assertGreen({clp.READ_SET: read_set(dict(BASE, **{READER: "# a new read\n"}))})
        out = self.assertGreen({clp.READ_SET: read_set(BASE, lapsed={READER: LAPSE})})
        self.assertIn("1 hold, 1 lapsed, 0 moved; IR-only narrowing off", out)

    def test_a_lapse_of_one_reader_excuses_no_other(self):
        self.assertRed({READER: "# a new read\n", clp.READ_SET: read_set(BASE, lapsed={READER2: LAPSE})},
                       [f"ir-read-set {READER} MOVED {blob(BASE[READER])}"])

    def test_a_deleted_reader_is_absent(self):
        self.assertRed({READER2: None}, [f"ir-read-set {READER2} ABSENT"])

    def test_a_reader_lapse_whose_pin_holds_is_a_note(self):
        out = self.assertGreen({clp.READ_SET: read_set(BASE, lapsed={READER: LAPSE})})
        self.assertIn(f"NOTE: reader {READER} is lapsed but its pin is current", out)

    def test_a_lapse_naming_no_reader_is_refused(self):
        self.assertRed({clp.READ_SET: read_set(BASE, lapsed={"scripts/other.py": LAPSE})},
                       ["ir-read-set LAPSE-NAMES-NO-READER scripts/other.py"])

    def test_a_malformed_read_set_is_refused(self):
        for text in (read_set(BASE, lapsed={}), read_set(BASE, lapsed={READER: "soon"}),
                     read_set(BASE, lapsed=[READER]), read_set(BASE, extra="x"),
                     read_set(BASE, schema="wrong"), read_set(BASE, readers={READER: "HEAD"}),
                     '{"schema": "a", "schema": "trust.land-gate.ir-cohort-read-set.v1", "readers": {}}',
                     "not json", "[]"):
            with self.subTest(text=text[:60]):
                self.assertRed({clp.READ_SET: text}, ["ir-read-set MALFORMED"])

    def test_an_absent_read_set_is_red(self):
        self.assertRed({clp.READ_SET: None}, ["ir-read-set LEDGER-ABSENT"])


class SubjectTests(unittest.TestCase):
    """Which tree is judged, and the push contract."""

    def setUp(self):
        self.repo = Fixture(self)
        self.base = self.repo.reviewed()
        self.red = self.repo.commit({PREMISE: "fn caller() { moved(); }\n"})

    def main(self, argv: Sequence[str] = (), refs: Optional[str] = None) -> Tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        env = dict(ISOLATED)
        with mock.patch.dict(os.environ, env), mock.patch.object(clp, "ROOT", self.repo.root), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            os.environ.pop("TRUST_PUSHED_REFS", None)
            if refs is not None:
                os.environ["TRUST_PUSHED_REFS"] = refs
            rc = clp.main(list(argv))
        return rc, out.getvalue(), err.getvalue()

    def test_head_is_judged_without_a_push(self):
        rc, out, _ = self.main()
        self.assertEqual(rc, 1, out)
        self.assertIn("SUBJECT: HEAD's tree", out)

    def test_the_pushed_sha_is_judged_not_head_nor_the_worktree(self):
        (self.repo.root / PREMISE).write_text(BASE[PREMISE])  # the worktree is green again
        rc, out, _ = self.main(refs=f"refs/heads/main {self.base} refs/heads/main {'0' * 40}\n")
        self.assertEqual(rc, 0, out)
        rc, out, _ = self.main(refs=f"refs/heads/main {self.red} refs/heads/main {self.base}\n")
        self.assertEqual(rc, 1, out)
        self.assertIn(moved("audit", AUDITED, PREMISE, BASE[PREMISE]), keys(out))
        rc, out, _ = self.main(["--rev", self.base], refs=f"refs/heads/main {self.red} refs/heads/main {self.base}")
        self.assertEqual(rc, 0, "--rev ignores the push")

    def test_every_pushed_tree_is_judged(self):
        refs = f"refs/heads/a {self.base} refs/heads/a {'0' * 40}\nrefs/heads/b {self.red} refs/heads/b {'0' * 40}\n"
        rc, out, _ = self.main(refs=refs)
        self.assertEqual(rc, 1, out)

    def test_a_deletion_only_push_is_skipped(self):
        rc, out, _ = self.main(refs=f"(delete) {'0' * 40} refs/heads/gone {self.base}\n")
        self.assertEqual(rc, 0)
        self.assertIn("SKIPPED:", out)

    def test_a_malformed_push_line_exits_2(self):
        for refs in ("refs/heads/main HEAD refs/heads/main 0\n", "one two three\n"):
            with self.subTest(refs=refs):
                rc, _out, err = self.main(refs=refs)
                self.assertEqual(rc, 2)
                self.assertIn("LEDGER PINS INVALID", err)

    def test_a_sha_this_clone_cannot_read_is_an_unkeyed_red(self):
        rc, out, _ = self.main(refs=f"refs/heads/main {'1' * 40} refs/heads/main {self.base}\n")
        self.assertEqual(rc, 1, out)
        self.assertIn("LEDGER PINS UNREADABLE", out)
        self.assertNotIn("FINDINGS: complete", out)
        both = f"refs/heads/a {'1' * 40} refs/heads/a {'0' * 40}\nrefs/heads/b {self.red} refs/heads/b {'0' * 40}\n"
        rc, out, _ = self.main(refs=both)
        self.assertEqual(rc, 1, out)
        self.assertTrue(keys(out))
        self.assertNotIn("FINDINGS: complete", out, "a tree it could not read leaves the keys incomplete")

    def test_the_program_runs_as_the_push_row_spells_it(self):
        env = clean_env(dict(ISOLATED, TRUST_PUSHED_REFS=f"(delete) {'0' * 40} refs/heads/x {'1' * 40}\n"))
        proc = subprocess.run([sys.executable, "-B", str(SCRIPT)], capture_output=True, text=True, env=env)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("SKIPPED:", proc.stdout)
        env["TRUST_PUSHED_REFS"] = "garbage\n"
        proc = subprocess.run([sys.executable, "-B", str(SCRIPT)], capture_output=True, text=True, env=env)
        self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)


def old_interpreter() -> Optional[str]:
    """A Python older than 3.11 on this machine (plain `python3` is 3.9 under
    macOS CommandLineTools), or None."""
    for name in ("/usr/bin/python3", "python3.10", "python3.9", "python3"):
        path = (name if os.access(name, os.X_OK) else None) if "/" in name else shutil.which(name)
        if path and subprocess.run([path, "-c", "import sys; raise SystemExit(sys.version_info >= (3, 11))"],
                                   capture_output=True).returncode == 0:
            return path
    return None


@unittest.skipUnless(os.name == "posix", "the re-exec is POSIX")
class InterpreterFloorTests(unittest.TestCase):
    """The push row is spelt `python3 scripts/check_ledger_pins.py`, and plain
    python3 can be older than 3.11. land_select refuses to import there (its
    row table gates/land.toml is TOML), so the script must reach a Python that
    has tomllib BEFORE that import. When the floor ran after the import
    (2026-11-14, the row table's first day) the row died with a traceback
    under an old python3 where it had judged before; no test started it there."""

    @classmethod
    def setUpClass(cls):
        cls.old = old_interpreter()
        if cls.old is None:
            raise unittest.SkipTest("no Python older than 3.11 on this machine: nothing can start below the floor")

    def start(self, newer: bool) -> Tuple[subprocess.CompletedProcess, List[str]]:
        """The script started under the old interpreter, as a deletion-only
        push; PATH offers only a logging `python3.14` that runs this test's
        interpreter (`newer`), or nothing at all."""
        with tempfile.TemporaryDirectory() as tmp:
            bin_dir, log = Path(tmp) / "bin", Path(tmp) / "started"
            bin_dir.mkdir()
            if newer:
                wrapper = bin_dir / "python3.14"
                wrapper.write_text(f"#!/bin/sh\nprintf 'newer\\n' >> {shlex.quote(str(log))}\n"
                                   f"exec {shlex.quote(sys.executable)} \"$@\"\n", encoding="utf-8")
                wrapper.chmod(0o755)
            env = clean_env(dict(ISOLATED, PATH=str(bin_dir),
                                 TRUST_PUSHED_REFS=f"(delete) {'0' * 40} refs/heads/x {'1' * 40}\n"))
            proc = subprocess.run([self.old, "-B", str(SCRIPT)], capture_output=True, text=True, env=env,
                                  stdin=subprocess.DEVNULL, timeout=300)
            return proc, (log.read_text().split() if log.exists() else [])

    def test_an_old_python3_reaches_the_judgment_under_a_newer_one(self):
        self.assertGreaterEqual(sys.version_info, (3, 11), "this test's own interpreter is the newer one")
        proc, started = self.start(newer=True)
        self.assertEqual(started, ["newer"], proc.stdout + proc.stderr)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("SKIPPED:", proc.stdout)
        self.assertNotIn("Traceback", proc.stderr)

    def test_no_newer_python_is_the_unreadable_red_not_a_traceback(self):
        proc, started = self.start(newer=False)
        self.assertEqual(started, [])
        self.assertEqual(proc.returncode, 1, proc.stdout + proc.stderr)
        self.assertIn("LEDGER PINS UNREADABLE", proc.stdout)
        self.assertNotIn("Traceback", proc.stderr)
        self.assertNotIn("PASS", proc.stdout)


# ---------------------------------------------------------------------------
# Mutants: each reopens a hole one test above exists to close.
# ---------------------------------------------------------------------------

@contextlib.contextmanager
def patched(obj, name, value):
    old = getattr(obj, name)
    setattr(obj, name, value)
    try:
        yield
    finally:
        setattr(obj, name, old)


def _m_source(name: str, old: str, new: str):
    src = textwrap.dedent(inspect.getsource(getattr(clp, name)))
    assert src.count(old) == 1, (name, old)
    local: dict = {}
    exec(compile(src.replace(old, new), clp.__file__, "exec"), clp.__dict__, local)
    return patched(clp, name, local[name])


MUTANTS = [
    ("a lapse on any row excuses every row",
     lambda: _m_source("judge_audits", '        if "lapsed" in row:\n',
                       '        if any("lapsed" in r for _t, r in valid):\n')),
    ("a lapsed row's moved pins are refused anyway",
     lambda: _m_source("judge_audits", '        if "lapsed" in row:\n', "        if False:\n")),
    ("premises are not judged", lambda: patched(clp, "row_pins", lambda row: [(row["file"], row["blob"])])),
    ("the row's own file is not judged",
     lambda: patched(clp, "row_pins", lambda row: [(p["file"], p["blob"]) for p in row.get("premises", [])])),
    ("an absent pinned path holds",
     lambda: _m_source("pin_state", "return actual == blob, actual", "return actual in (blob, None), actual")),
    ("a malformed row is dropped silently",
     lambda: _m_source("judge_audits", '                v.findings.append(f"escape-audits {table} {name} MALFORMED")\n',
                       "")),
    ("a duplicate row is not refused",
     lambda: _m_source("judge_audits", '                v.findings.append(f"escape-audits {table} {name} DUPLICATE")\n',
                       "")),
    ("not_path rows are not judged",
     lambda: _m_source("judge_audits", 'for table in ("audit", "not_path"):', 'for table in ("audit",):')),
    ("land_select's row rule is not applied", lambda: patched(ls, "audit_row_ok", lambda row: isinstance(row, dict))),
    ("a lapse of any reader excuses every reader",
     lambda: _m_source("judge_read_set", "        if reader in lapses:\n", "        if lapses:\n")),
    ("a lapse naming no reader passes",
     lambda: _m_source("judge_read_set", '        v.findings.append(f"ir-read-set LAPSE-NAMES-NO-READER {name}")\n', "")),
    ("a reader lapse is not validated",
     lambda: _m_source("judge_read_set", "isinstance(k, str) and isinstance(w, str) and ls.LAPSED.fullmatch(w)",
                       "isinstance(k, str)")),
    ("a key carries the tree's blob",
     lambda: _m_source("judge_audits", 'MOVED {path} {blob}" if actual', 'MOVED {path} {actual}" if actual')),
    ("HEAD is judged instead of the pushed sha",
     lambda: _m_source("judge_push", '[(f"{ref} {sha[:12]}", sha) for ref, sha in live]',
                       '[(f"{ref} {sha[:12]}", "HEAD") for ref, sha in live]')),
    ("a tree it cannot read is a pass",
     lambda: _m_source("judge_subjects", "    complete, ok = not unreadable, not unreadable\n",
                       "    complete, ok = True, True\n")),
    ("the read set is not judged", lambda: patched(clp, "judge_read_set", lambda root, tree, raw: clp.Verdict(
        "ir-read-set", summary="skipped"))),
]


def main() -> int:
    if sys.argv[1:] == ["--mutants"]:
        loader = unittest.defaultTestLoader

        def suite():
            return unittest.TestSuite([loader.loadTestsFromTestCase(LedgerPinTests),
                                       loader.loadTestsFromTestCase(SubjectTests)])

        def quiet():
            return unittest.TextTestRunner(stream=io.StringIO(), verbosity=0, failfast=True)

        control = quiet().run(suite())
        if not control.wasSuccessful():
            print("MUTANTS: the unmutated suite is red")
            return 1
        survivors = []
        for name, factory in MUTANTS:
            with factory():
                result = quiet().run(suite())
            killed = bool(result.failures or result.errors)
            witness = (result.failures + result.errors)[0][0].id().rsplit(".", 1)[-1] if killed else "none"
            print(f"{'killed  ' if killed else 'SURVIVED'} {name}; witness={witness}", flush=True)
            if not killed:
                survivors.append(name)
        print(f"MUTANTS: {len(survivors)} survived" if survivors else f"MUTANTS: all {len(MUTANTS)} killed")
        return 1 if survivors else 0
    return 0 if unittest.main(exit=False).result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
