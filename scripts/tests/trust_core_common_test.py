#!/usr/bin/env python3
"""Controls for scripts/trust_core/common.py, the shared layer of the Trust core checkers.

Every function runs on REAL inputs (docs/trust-core/EXTERNAL_PINS.toml, the pinned source
clones, this repository at HEAD, the Core vocabulary's table, document and review registry)
and must report nothing; beside that control, each mutation of a temporary copy must make the
function report the violation the mutation introduces. A missing source clone is a FAILURE
that prints its clone command, never a skip. The source clones are never modified: every
mutation runs on a copy.

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
    _floor_sys.exit("trust_core_common_test.py requires Python 3.11+ (tomllib); none found on PATH")

import copy
import datetime
import hashlib
import importlib.util
import re
import shutil
import subprocess
import tempfile
import tomllib
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]


def load(name: str, rel: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = load("trust_core_common", "scripts/trust_core/common.py")
C_git = C.git
CV = load("trust_core_core_vocabulary_for_common", "scripts/trust_core/core_vocabulary.py")
PINS = None
CLONES = {}


def setUpModule():
    global PINS, CLONES
    PINS = C.load_pins()
    try:
        CLONES = C.locate_clones(PINS, sorted(PINS.sources))
    except C.MissingClone as error:
        raise AssertionError(str(error)) from None


def sh(cwd, *args):
    return subprocess.run(["git", "-C", str(cwd), *args], check=True, capture_output=True, text=True, env=C.git_environment()).stdout


def violations(run) -> list[str]:
    findings = C.Findings()
    run(findings)
    return findings.violations


class TempDir(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def assert_reports(self, found, *fragments):
        for fragment in fragments:
            self.assertTrue(any(fragment in v for v in found), f"{fragment!r} not in {found}")

    def git_repo(self, name="repo") -> Path:
        repo = self.tmp / name
        repo.mkdir()
        sh(repo, "init", "-q")
        sh(repo, "config", "user.email", "test@example.invalid")
        sh(repo, "config", "user.name", "test")
        return repo

    def commit(self, repo, rel, text, message="c"):
        (repo / rel).parent.mkdir(parents=True, exist_ok=True)
        (repo / rel).write_text(text, encoding="utf-8")
        sh(repo, "add", rel)
        sh(repo, "commit", "-q", "-m", message)


class PinsTest(TempDir):
    def test_real_pins_name_every_clone_at_its_revision(self):
        self.assertEqual(PINS.alignment, "cabb1ea4ced589dfee40c08aeffff3cac78af43b")
        self.assertEqual(sorted(PINS.sources), ["a-mir-formality", "fls", "minirust", "rfcs", "rust-reference"])
        self.assertEqual(sorted(n for n, s in PINS.sources.items() if s.read == "objects"), ["rfcs"])
        for name, path in CLONES.items():
            if PINS.sources[name].read == "objects":  # read from git objects at the pin; HEAD is not read
                self.assertEqual(sh(path, "rev-parse", PINS.sources[name].revision + "^{commit}").strip(), PINS.sources[name].revision, name)
            else:
                self.assertEqual(sh(path, "rev-parse", "HEAD").strip(), PINS.sources[name].revision, name)

    def test_a_read_mode_other_than_checkout_or_objects_is_refused(self):
        text = (ROOT / C.PINS_REL).read_text(encoding="utf-8")
        copy_path = self.tmp / "pins.toml"
        self.assertEqual(text.count('read = "objects"'), 1)
        copy_path.write_text(text.replace('read = "objects"', 'read = "worktree"'), encoding="utf-8")
        with self.assertRaises(C.PinsError):
            C.load_pins(copy_path)
        copy_path.write_text(text.replace('read = "objects"', ''), encoding="utf-8")
        self.assertEqual(C.load_pins(copy_path).sources["rfcs"].read, "checkout")  # the default

    def test_malformed_pins_are_refused(self):
        text = (ROOT / C.PINS_REL).read_text(encoding="utf-8")
        copy_path = self.tmp / "pins.toml"
        copy_path.write_text(text, encoding="utf-8")
        self.assertEqual(C.load_pins(copy_path), PINS)  # control
        # Read from the pins, not spelled here: moving [alignment] moves every pin, and a date
        # spelled here once "after the alignment" fell before it at the next move.
        minirust = PINS.sources["minirust"]
        after = (C.parse_date(PINS.alignment_date) + datetime.timedelta(seconds=1)).isoformat()
        self.assertIsNotNone(C.parse_date(after))
        for old, new in (
            (f'revision = "{minirust.revision}"', f'revision = "{minirust.revision[:8]}"'),
            (f'committer_date = "{minirust.committer_date}"', f'committer_date = "{after}"'),
            ('schema = "trust.core.external-pins.v1"', 'schema = "v0"'),
            ('repo = "https://github.com/minirust/minirust"', 'repo = "git@github.com:minirust/minirust"'),
        ):
            with self.subTest(new=new):
                self.assertEqual(text.count(old), 1)
                copy_path.write_text(text.replace(old, new), encoding="utf-8")
                with self.assertRaises(C.PinsError):
                    C.load_pins(copy_path)

    def test_a_branch_is_loaded_and_a_malformed_one_is_refused(self):
        rfcs = PINS.sources["rfcs"]
        self.assertEqual((rfcs.revision, rfcs.read, rfcs.branch, rfcs.directory),
                         ("3bdcd22feea6848a7920fa06d17ad4c6ada9db89", "objects", "refs/remotes/origin/main", "rfcs"))
        self.assertEqual(sorted(n for n, s in PINS.sources.items() if s.branch is not None), ["rfcs"])
        text = (ROOT / C.PINS_REL).read_text(encoding="utf-8")
        copy_path = self.tmp / "pins.toml"
        old = 'branch = "refs/remotes/origin/main"\n'
        self.assertEqual(text.count(old), 1)
        for new in ('branch = ""\n', "branch = 7\n", 'branch = "  "\n'):
            with self.subTest(new=new):
                copy_path.write_text(text.replace(old, new), encoding="utf-8")
                with self.assertRaises(C.PinsError):
                    C.load_pins(copy_path)
        copy_path.write_text(text.replace(old, ""), encoding="utf-8")
        self.assertIsNone(C.load_pins(copy_path).sources["rfcs"].branch)  # a pin with no branch is not derived

    def test_a_missing_clone_raises_with_its_clone_command(self):
        self.assertEqual(C.locate_clones(PINS, ["minirust"]), {"minirust": CLONES["minirust"]})  # control
        absent = self.tmp / "absent"
        with self.assertRaises(C.MissingClone) as raised:
            C.locate_clones(PINS, ["minirust", "fls"], {"minirust": absent})
        self.assertIn(f"git clone https://github.com/minirust/minirust {absent} && git -C {absent} checkout {PINS.sources['minirust'].revision}", str(raised.exception))
        self.assertNotIn("fls", str(raised.exception).split("(or point")[0])


class CloneTest(TempDir):
    def copy_clone(self, name="minirust") -> Path:
        target = self.tmp / name
        shutil.copytree(CLONES[name], target, symlinks=True)
        return target

    def verify(self, path, name="minirust", source=None):
        return violations(lambda f: C.verify_clone(f, path, source or PINS.sources[name], PINS))

    def test_real_clones_and_repository_verify(self):
        for name, path in CLONES.items():
            self.assertEqual(self.verify(path, name), [], name)
        self.assertEqual(violations(lambda f: C.verify_objects(f, "repository", ROOT)), [])
        self.assertEqual(violations(lambda f: C.verify_alignment(f, C.GitTree(ROOT, "HEAD"), PINS)), [])

    def test_each_substitution_or_edit_of_a_clone_is_refused(self):
        control = self.copy_clone()
        self.assertEqual(self.verify(control), [])
        mutations = {
            "dirty": (lambda p: (p / "README.md").write_text("edited\n"), "is not a clean checkout"),
            "untracked": (lambda p: (p / "spec" / "extra.md").write_text("x\n"), "is not a clean checkout"),
            "other head": (lambda p: (sh(p, "-c", "user.email=t@e.invalid", "-c", "user.name=t", "commit", "-q", "--allow-empty", "-m", "x")), "not the pinned"),
            "replace ref": (lambda p: sh(p, "update-ref", "refs/replace/" + PINS.sources["minirust"].revision, PINS.sources["minirust"].revision), "carries replace refs"),
            "grafts": (lambda p: (p / ".git" / "info").mkdir(exist_ok=True) or (p / ".git" / "info" / "grafts").write_text(PINS.sources["minirust"].revision + "\n"), "carries a grafts file"),
            "skip-worktree": (lambda p: sh(p, "update-index", "--skip-worktree", "README.md"), "not plain tracked files"),
            "assume-unchanged": (lambda p: sh(p, "update-index", "--assume-unchanged", "README.md"), "not plain tracked files"),
        }
        for label, (mutate, fragment) in mutations.items():
            with self.subTest(label):
                path = self.tmp / "mutated"
                shutil.copytree(CLONES["minirust"], path, symlinks=True)
                mutate(path)
                self.assert_reports(self.verify(path), fragment)
                shutil.rmtree(path)
        wrong_date = C.Source("minirust", PINS.sources["minirust"].url, PINS.sources["minirust"].revision, "2026-07-01T00:00:00Z")
        self.assert_reports(self.verify(control, source=wrong_date), "not the recorded 2026-07-01T00:00:00Z")

    def test_a_branch_pin_is_derived_and_each_substitution_is_refused(self):
        rfcs = PINS.sources["rfcs"]
        self.assertEqual(self.verify(CLONES["rfcs"], "rfcs"), [])  # control
        parent = sh(CLONES["rfcs"], "rev-parse", rfcs.revision + "^").strip()
        mutations = {
            "branch moved before the pin": (lambda p: sh(p, "update-ref", rfcs.branch, parent), "is " + parent),
            "replace ref": (lambda p: sh(p, "update-ref", "refs/replace/" + rfcs.revision, parent), "carries replace refs"),
            "shallow": (lambda p: (p / ".git" / "shallow").write_text(rfcs.revision + "\n"), "is shallow"),
        }
        for label, (mutate, fragment) in mutations.items():
            with self.subTest(label):
                path = self.tmp / "rfcs"
                shutil.copytree(CLONES["rfcs"], path, symlinks=True)
                self.assertEqual(self.verify(path, "rfcs"), [])  # control on the copy
                mutate(path)
                self.assert_reports(self.verify(path, "rfcs"), fragment)
                shutil.rmtree(path)
        for label, source, fragment in (
            ("absent commit", C.Source("rfcs", rfcs.url, "0" * 40, rfcs.committer_date, "objects", rfcs.branch), "does not hold the pinned commit"),
            ("another date", C.Source("rfcs", rfcs.url, rfcs.revision, "2026-06-30T00:00:00Z", "objects", rfcs.branch), "not the recorded 2026-06-30T00:00:00Z"),
            ("another branch", C.Source("rfcs", rfcs.url, rfcs.revision, rfcs.committer_date, "objects", "refs/remotes/origin/no-such-branch"), "is none, not the pinned"),
        ):
            with self.subTest(label):
                self.assert_reports(self.verify(CLONES["rfcs"], "rfcs", source), fragment)

    def test_alignment_record_mismatch_is_refused(self):
        text = C.GitTree(ROOT, "HEAD").text(C.TRUST_VERSION_REL)
        tree = C.DirTree(self.tmp, {C.TRUST_VERSION_REL: text})
        self.assertEqual(violations(lambda f: C.verify_alignment(f, tree, PINS)), [])  # control
        tree = C.DirTree(self.tmp, {C.TRUST_VERSION_REL: text.replace(PINS.alignment, "0" * 40)})
        self.assert_reports(violations(lambda f: C.verify_alignment(f, tree, PINS)), "[rust_alignment].revision")

    def test_an_objects_read_clone_needs_its_pin_but_not_its_checkout(self):
        rfcs = PINS.sources["rfcs"]
        self.assertEqual(self.verify(CLONES["rfcs"], "rfcs"), [])
        copied = self.tmp / "rfcs"
        shutil.copytree(CLONES["rfcs"], copied, symlinks=True)
        sh(copied, "checkout", "--detach", rfcs.revision + "^")
        self.assertNotEqual(sh(copied, "rev-parse", "HEAD").strip(), rfcs.revision)
        self.assertEqual(self.verify(copied, "rfcs"), [])  # objects mode ignores a different checkout
        as_checkout = C.Source(rfcs.name, rfcs.url, rfcs.revision, rfcs.committer_date)
        self.assert_reports(self.verify(copied, "rfcs", as_checkout), "not the pinned")
        repo = self.git_repo("objects")
        self.commit(repo, "a.txt", "a\n")
        head = sh(repo, "rev-parse", "HEAD").strip()
        stamp = sh(repo, "log", "-1", "--format=%cI").strip()
        pinned = C.Source("objects", "https://example.invalid/objects", head, stamp, "objects")
        pins = C.Pins(PINS.alignment, "2999-01-01T00:00:00Z", {})
        (repo / "a.txt").write_text("dirty\n", encoding="utf-8")
        self.assertEqual(violations(lambda f: C.verify_clone(f, repo, pinned, pins)), [])  # control: a dirty checkout is not read
        for label, source, fragment in (
            ("absent pin", C.Source("objects", pinned.url, "1" * 40, stamp, "objects"), "does not hold the pinned commit"),
            ("wrong date", C.Source("objects", pinned.url, head, "2000-01-01T00:00:00Z", "objects"), "not the recorded 2000-01-01T00:00:00Z"),
        ):
            with self.subTest(label):
                self.assert_reports(violations(lambda f: C.verify_clone(f, repo, source, pins)), fragment)
        sh(repo, "update-ref", "refs/replace/" + head, head)
        self.assert_reports(violations(lambda f: C.verify_clone(f, repo, pinned, pins)), "carries replace refs")

    def test_inherited_git_environment_cannot_redirect_a_read(self):
        other = self.git_repo("other")
        self.commit(other, "README.md", "not the pin\n")
        with mock.patch.dict("os.environ", {"GIT_DIR": str(other / ".git"), "GIT_WORK_TREE": str(other)}):
            self.assertEqual(self.verify(CLONES["minirust"]), [])


class TreeTest(TempDir):
    def test_git_tree_reads_the_commit_not_the_worktree(self):
        path = self.tmp / "minirust"
        shutil.copytree(CLONES["minirust"], path, symlinks=True)
        pinned = C.GitTree(path, PINS.sources["minirust"].revision)
        original = pinned.text("spec/lang/syntax.md")
        self.assertEqual(original, (CLONES["minirust"] / "spec/lang/syntax.md").read_text(encoding="utf-8"))  # control
        (path / "spec/lang/syntax.md").write_text("replaced\n", encoding="utf-8")
        self.assertEqual(C.GitTree(path, PINS.sources["minirust"].revision).text("spec/lang/syntax.md"), original)
        self.assertEqual(C.DirTree(path).text("spec/lang/syntax.md"), "replaced\n")
        self.assertIsNone(pinned.text("spec/lang/absent.md"))
        self.assertIn("spec/lang/syntax.md", pinned.files("spec/", (".md",)))

    def test_a_partial_clone_read_never_fetches(self):
        origin = self.git_repo("origin")
        self.commit(origin, "a.txt", "alpha\n")
        self.commit(origin, "b.txt", "beta\n")
        sh(origin, "config", "uploadpack.allowFilter", "true")
        partial = self.tmp / "partial"
        subprocess.run(["git", "clone", "-q", "--no-checkout", "--filter=blob:none", f"file://{origin}", str(partial)],
                       check=True, capture_output=True, env=C.git_environment())
        rev = sh(partial, "rev-parse", "HEAD").strip()
        packs = sorted((partial / ".git" / "objects" / "pack").iterdir())
        offline = C.GitTree(partial, rev)  # the default: no read fetches
        self.assertEqual(offline.files(), ["a.txt", "b.txt"])  # trees are present
        self.assertIsNone(offline.text("b.txt"))
        self.assertIsNone(C.git(partial, "cat-file", "-p", f"{rev}:b.txt"))
        self.assertEqual(sorted((partial / ".git" / "objects" / "pack").iterdir()), packs)  # nothing was fetched
        self.assertEqual(C.GitTree(partial, rev, lazy_fetch=True).text("b.txt"), "beta\n")  # control: a fetching read changes the clone
        self.assertNotEqual(sorted((partial / ".git" / "objects" / "pack").iterdir()), packs)

    def test_a_rooted_tree_reads_nothing_outside_its_roots(self):
        base = C.DirTree(self.tmp, {"lib/a/src/x.rs": "/// inside\n", "lib/a/tests/y.rs": "outside\n", "tools/z.rs": "outside\n"})
        rooted = C.RootedTree(base, ("lib/a/src/",))
        self.assertEqual(base.text("tools/z.rs"), "outside\n")  # control: the underlying tree holds it
        self.assertEqual(rooted.files("lib/", (".rs",)), ["lib/a/src/x.rs"])
        self.assertEqual(rooted.lines("lib/a/src/x.rs"), ["/// inside", ""])
        for rel in ("tools/z.rs", "lib/a/tests/y.rs", "lib/a/src/../tests/y.rs", "lib/a/src/./x.rs", None):
            self.assertIsNone(rooted.text(rel), rel)
        self.assertEqual(C.RootedTree(base, ()).files(), [])
        resolver = C.Resolver(ROOT, {"lib": rooted}, kinds=("lib",), comment_kinds=("lib",))
        self.assertIsNone(resolver.check("lib:lib/a/src/x.rs:1", "inside"))
        self.assertIn("does not exist in the lib tree", resolver.check("lib:tools/z.rs:1", "outside"))
        self.assertIsNone(C.Resolver(ROOT, {"lib": base}, kinds=("lib",)).check("lib:tools/z.rs:1", "outside"))  # control

    def test_first_party_is_read_at_its_gitlink(self):
        tree = C.first_party_tree(ROOT, "clean")
        gitlink = sh(ROOT, "ls-tree", "HEAD", "first-party/clean").split()[2]
        self.assertEqual(tree.rev, gitlink)
        self.assertIsNotNone(tree.text("README.md"))
        self.assertIsNone(C.first_party_tree(ROOT, "no-such-submodule"))

    def test_git_ok_codes_accept_an_empty_grep_and_nothing_else(self):
        repo = self.git_repo()
        self.commit(repo, "a.txt", "alpha\n")
        # Control: a match is stdout under the default and under ok_codes.
        self.assertEqual(C.git(repo, "grep", "-l", "-F", "-e", "alpha", "HEAD", "--"), "HEAD:a.txt\n")
        self.assertEqual(C.git(repo, "grep", "-l", "-F", "-e", "alpha", "HEAD", "--", ok_codes=(0, 1)), "HEAD:a.txt\n")
        # No match exits 1: a failure by default (every existing call is unchanged), empty with ok_codes.
        self.assertIsNone(C.git(repo, "grep", "-l", "-F", "-e", "omega", "HEAD", "--"))
        self.assertEqual(C.git(repo, "grep", "-l", "-F", "-e", "omega", "HEAD", "--", ok_codes=(0, 1)), "")
        # A real failure stays a failure: an unknown revision (exit 128), and an accepted code with an error.
        self.assertIsNone(C.git(repo, "grep", "-l", "-F", "-e", "alpha", "no-such-rev", "--", ok_codes=(0, 1)))
        self.assertIsNone(C.git(repo, "grep", "-l", "-E", "-e", "(", "HEAD", "--", ok_codes=(0, 1, 128)))


class CitationTest(TempDir):
    REAL = [
        ("design:841", "`Program`: items, impls, statics", False),
        ("design:841-842", "statics, `Target`, and `Config` (panic strategy, `overflow_checks`", False),
        ("minirust:spec/lang/syntax.md:462", "start", True),
        ("reference:src/items.md:9", "VisItem ->", False),
        ("reference:r[items.syntax]", "VisItem ->", False),
        ("fls:src/expressions.rst:67", "fls_pwut2jbmk66k", False),
        ("fls:fls_pwut2jbmk66k", "is any expression in category", False),
        ("a-mir-formality:Cargo.toml:1", "[", False),
        ("rustc:compiler/rustc_middle/src/mir/syntax.rs:1366", "Use(Operand<'tcx>, WithRetag),", False),
        ("rustc:library/core/src/ptr/non_null.rs:79", "pattern_type!", False),
        ("worktree:docs/trust-core/EXTERNAL_PINS.toml:16", 'schema = "trust.core.external-pins.v1"', False),
        ("first-party:clean/README.md:1", "#", False),
        ("rfcs:text/2394-async_await.md:3", "[rust-lang/rfcs#2394](https://github.com/rust-lang/rfcs/pull/2394)", False),
    ]

    @classmethod
    def setUpClass(cls):
        trees = {"worktree": C.GitTree(ROOT, "HEAD")}
        for name, source in (("minirust", "minirust"), ("rust-reference", "reference"), ("fls", "fls"), ("a-mir-formality", "a-mir-formality")):
            trees[source] = C.GitTree(CLONES[name], PINS.sources[name].revision)
        trees["rfcs"] = C.GitTree(CLONES["rfcs"], PINS.sources["rfcs"].revision)
        cls.resolver = C.Resolver(ROOT, trees)

    def test_real_citations_of_every_source_kind_resolve(self):
        for ref, quote, word in self.REAL:
            with self.subTest(ref=ref):
                self.assertIsNone(self.resolver.check(ref, quote, word))
        self.assertEqual({s for s, _ in self.resolver.read}, set(C.SOURCE_KINDS))

    def test_each_mutated_citation_fails(self):
        check = self.resolver.check
        for ref, quote, word in self.REAL:
            with self.subTest(ref=ref):
                self.assertIsNotNone(check(ref, quote + " x", word), "a changed quote")
                parts = C.parse_ref(ref)
                if parts["start"]:
                    moved = ref.rsplit(":", 1)[0] + (f":{parts['start'] + 2}" if parts["end"] == parts["start"] else f":{parts['start'] + 2}-{parts['end'] + 2}")
                    self.assertIsNotNone(check(moved, quote, word), f"a moved line {moved}")
        self.assertIsNotNone(check("minirust:spec/lang/syntax.md:462", "star", True), "a partial word")
        self.assertIsNone(check("minirust:spec/lang/syntax.md:462", "star", False), "control: a substring")
        self.assertIn("carries a `Trust:` edit (line 124)", check("rustc:compiler/rustc_mir_transform/src/validate.rs:124", "Trust", False))
        self.assertIn("file under", check("rustc:docs/trust-core/EXTERNAL_PINS.toml:16", "schema"))
        self.assertIn("defined 0 times", check("reference:r[items.no-such-rule]", "VisItem"))
        self.assertIn("defined 0 times", check("fls:fls_nosuchparagraph", "x"))
        self.assertIn("does not exist", check("minirust:spec/lang/absent.md:1", "x"))
        self.assertIn("lines", check("design:999999", "x"))
        for bad in ("design:docs/x.md:1", "minirust:12", "reference:fls_abc", "rust:compiler/x.rs:1", "design:5-3"):
            self.assertIn("is not a citation", check(bad, "x"), bad)

    def test_strip_resolves_a_quote_across_comment_and_blockquote_markers(self):
        # Additive: `strip` also compares the lines with one leading marker removed; the default is unchanged.
        cases = (
            ("rustc:library/core/src/sync/atomic.rs:44-45", "*data races* are undefined behavior. A data race is defined as conflicting non-synchronized accesses"),
            ("reference:src/behavior-considered-undefined.md:11-13", "or shrink. There is no formal model of Rust's semantics for what is and is not allowed in unsafe code, so there may be more behavior considered unsafe. We also reserve the right to make some of the behavior in that list defined in the future. In other words, this list does not say that anything will *definitely* always be undefined in all future Rust versions (but we might make such commitments for some list items in the future). Please read"),
        )
        for ref, quote in cases:
            with self.subTest(ref):
                self.assertIn("does not contain", self.resolver.check(ref, quote))  # control: the markers break the quote
                self.assertIsNone(self.resolver.check(ref, quote, strip=True))
                self.assertIn("does not contain", self.resolver.check(ref, quote.replace("defined", "definite", 1), strip=True))
        self.assertEqual(C.strip_marker("//! a"), "a")
        self.assertEqual(C.strip_marker("    /// a"), "a")
        self.assertEqual(C.strip_marker("> > [!NOTE]"), "[!NOTE]")
        self.assertEqual(C.strip_marker(":dp:`fls_x` text"), "text")
        self.assertEqual(C.strip_marker("let x = 1; // y"), "let x = 1; // y")  # control: only a leading marker

    SYNTAX = "compiler/rustc_middle/src/mir/syntax.rs"
    VALIDATE = "compiler/rustc_mir_transform/src/validate.rs"

    def worktree_resolver(self, overlay):
        """A resolver whose worktree is this repository at HEAD with `overlay` files replaced."""
        head = C.GitTree(ROOT, "HEAD")
        return C.Resolver(ROOT, dict(self.resolver.trees, worktree=C.DirTree(ROOT, {rel: text(head.text(rel)) for rel, text in overlay.items()})))

    @staticmethod
    def edit_lines(text, edits):
        lines = text.split("\n")
        for number, (old, new) in edits.items():
            assert lines[number - 1] == old, (number, lines[number - 1])
            lines[number - 1] = new
        return "\n".join(lines)

    def test_a_marker_on_the_line_above_a_cited_line_is_refused(self):
        # The verifier's attack: a marked Trust edit rewrites cited line 1026 (keeping the quoted
        # words) and puts its marker on the blank line above it.
        ref, quote = f"rustc:{self.SYNTAX}:1026", "The reason we are terminating the process during unwinding."
        reworded = {1026: ("/// The reason we are terminating the process during unwinding.",
                           "/// The reason we are terminating the process during unwinding. Trust builds also use it for aborts.")}
        marked = {**reworded, 1025: ("", "// Trust: the terminate reason now also covers aborts on a failed proof")}
        self.assertIsNone(self.worktree_resolver({self.SYNTAX: lambda t: self.edit_lines(t, reworded)}).check(ref, quote))  # control: no marker
        self.assertEqual(self.worktree_resolver({self.SYNTAX: lambda t: self.edit_lines(t, marked)}).check(ref, quote),
                         f"{ref}: {self.SYNTAX} carries a `Trust:` edit (line 1025), and the cited lines lie in no region the checker parses and verified free of one, so they are not verified upstream text")

    def test_a_marker_above_an_enum_adding_a_variant_is_refused(self):
        # The verifier's attack: a marked Trust edit adds `Abort` to UnwindAction, with the marker
        # in the doc comment above the enum; the new variant is cited inside the enum.
        ref, quote = f"rustc:{self.SYNTAX}:1012", "Abort,"
        added = {1012: ("    ///", "    Abort,")}
        marked = {**added, 1007: ("/// Action to be taken when a stack unwind happens.", "/// Action to be taken when a stack unwind happens. // Trust: adds Abort")}
        for label, edits, verified in (("control: no marker", added, True), ("marker above the enum", marked, False)):
            with self.subTest(label):
                resolver = self.worktree_resolver({self.SYNTAX: lambda t: self.edit_lines(t, edits)})
                variants, span = CV.Source(resolver.trees["worktree"].text(self.SYNTAX)).enum_variants("UnwindAction")
                self.assertEqual((variants["Abort"], span), (1012, (1005, 1024)))
                found = violations(lambda f: self.assertEqual(resolver.upstream_region(f, self.SYNTAX, *span, "enum UnwindAction"), verified))
                if verified:
                    self.assertEqual(found, [])
                    self.assertIsNone(resolver.check(ref, quote))
                else:
                    self.assertEqual(found, [f"PIN: {self.SYNTAX}: the parsed region of enum UnwindAction carries a `Trust:` edit (line 1007), so it is not the pinned upstream text"])
                    self.assertIn("carries a `Trust:` edit (line 1007)", resolver.check(ref, quote))
        # A citation inside a verified region of a file marked elsewhere passes; one outside fails.
        elsewhere = {1: (self.worktree_resolver({}).trees["worktree"].lines(self.SYNTAX)[0], "// Trust: an edit far from UnwindAction")}
        resolver = self.worktree_resolver({self.SYNTAX: lambda t: self.edit_lines(t, {**added, **elsewhere})})
        self.assertIn("carries a `Trust:` edit (line 1)", resolver.check(ref, quote))  # before the region is registered: fails closed
        self.assertEqual(violations(lambda f: resolver.upstream_region(f, self.SYNTAX, 1005, 1024, "enum UnwindAction")), [])
        self.assertIsNone(resolver.check(ref, quote))
        self.assertIn("carries a `Trust:` edit (line 1)", resolver.check(f"rustc:{self.SYNTAX}:1026", "The reason we are terminating the process during unwinding."))
        self.assertIn("carries a `Trust:` edit (line 1)", resolver.check(f"rustc:{self.SYNTAX}:1022-1026", "The reason we are terminating"), "a range leaving the region")

    def test_a_citation_of_trust_added_code_is_refused(self):
        # The verifier's attack: a citation of validate.rs:127, a field Trust added under the
        # marker at line 124, through either label for this repository.
        for ref in (f"rustc:{self.VALIDATE}:127", f"worktree:{self.VALIDATE}:127"):
            with self.subTest(ref):
                self.assertEqual(self.resolver.check(ref, "locals_with_def: DenseBitSet<Local>,"),
                                 f"{ref}: {self.VALIDATE} carries a `Trust:` edit (line 124), and the cited lines lie in no region the checker parses and verified free of one, so they are not verified upstream text")
        self.assertIn("carries a `Trust:` edit (line 124)", self.resolver.check(f"rustc:{self.VALIDATE}:1324", "ty::Float(..)"), "an unmarked line of a marked file")
        self.assertIsNone(self.resolver.check(f"rustc:{self.SYNTAX}:1366", "Use(Operand<'tcx>, WithRetag),"))  # control: a file with no marker
        self.assertIsNone(self.resolver.check(f"worktree:{self.SYNTAX}:1366", "Use(Operand<'tcx>, WithRetag),"))  # control

    def test_a_non_canonical_path_is_refused(self):
        # The round-18 B0 verifier's attack: `worktree:./compiler/...` resolved through git but
        # skipped the whole-file guard, which tested the path as written.
        for ref in (f"worktree:./{self.VALIDATE}:127", f"rustc:./{self.VALIDATE}:127",
                    "rustc:compiler//rustc_middle/src/mir/syntax.rs:1366",
                    "rustc:compiler/rustc_middle/../rustc_middle/src/mir/syntax.rs:1366",
                    f"worktree:/{self.SYNTAX}:1366"):
            with self.subTest(ref):
                self.assertIn("is not written canonically", self.resolver.check(ref, "Use(Operand<'tcx>, WithRetag),"))
        self.assertIsNone(self.resolver.check(f"worktree:{self.SYNTAX}:1366", "Use(Operand<'tcx>, WithRetag),"))  # control

    def test_every_marker_spelling_is_a_marker(self):
        # The tree marks Trust edits with tags as well as the bare form (measured 2026-09-17:
        # `// Trust (IN):`, `/// Trust #N (RN):`, `// Trust #N:` ...); the line-1026 attack with
        # a tagged marker must fail like the bare one.
        ref, quote = f"rustc:{self.SYNTAX}:1026", "The reason we are terminating the process during unwinding."
        reworded = {1026: ("/// The reason we are terminating the process during unwinding.",
                           "/// The reason we are terminating the process during unwinding. Trust builds also use it for aborts.")}
        for marker in ("// Trust (W6): aborts on a failed proof", "/// Trust #54: aborts", "// Trust #7 (R3): aborts",
                       "/* Trust (typeck-moonshot P4, Phase 2): aborts */", "//! Trust:"):
            with self.subTest(marker):
                self.assertTrue(C.is_trust_marker(marker))
                edits = {**reworded, 1025: ("", marker)}
                self.assertIn("carries a `Trust:` edit (line 1025)",
                              self.worktree_resolver({self.SYNTAX: lambda t: self.edit_lines(t, edits)}).check(ref, quote))
        for plain in ("// Trustworthy: not a marker", "// Trusted by the caller", "let trust = x;"):
            self.assertFalse(C.is_trust_marker(plain), plain)  # controls

    def test_an_enum_inside_a_macro_or_module_region_starts_at_the_enclosing_statement(self):
        # The B0 verifier's attack: PanicStrategy is declared inside `crate::target_spec_enum! {`,
        # and a marker directly above the macro lay outside the enum's region.
        text = "\n".join([
            "fn before() {}",                       # 1
            "// Trust: adds TrustProofAbort",       # 2
            "crate::target_spec_enum! {",           # 3
            "    /// The panic strategy.",           # 4
            "    pub enum PanicStrategy {",          # 5
            "        Unwind,",                       # 6
            "        TrustProofAbort,",              # 7
            "    }",                                 # 8
            "}",                                     # 9
            "mod inner {",                           # 10
            "    pub enum Nested { A }",             # 11
            "}",                                     # 12
            "pub enum TopLevel { B }",               # 13
        ])
        source = CV.Source(text)
        self.assertEqual(source.enum_variants("PanicStrategy"), ({"Unwind": 6, "TrustProofAbort": 7}, (1, 8)))
        self.assertEqual(source.enum_variants("Nested")[1], (9, 11))
        self.assertEqual(source.enum_variants("TopLevel")[1], (12, 13))  # control: a top-level enum is unchanged

    def test_declared_kinds_and_comment_kinds_resolve_only_when_declared(self):
        tree = C.DirTree(self.tmp, {"lib/doc.rs": "/// The first line of a doc\n/// comment continues here.\nfn f() {}\n"})
        plain = C.Resolver(ROOT, {"lib": tree})
        declared = C.Resolver(ROOT, {"lib": tree}, kinds=("lib",))
        comments = C.Resolver(ROOT, {"lib": tree}, kinds=("lib",), comment_kinds=("lib",))
        ref, quote = "lib:lib/doc.rs:1-2", "a doc comment continues"
        self.assertIn("is not a citation", plain.check(ref, quote))  # an undeclared kind
        self.assertIsNone(declared.check("lib:lib/doc.rs:3", "fn f()"))
        self.assertIn("does not contain", declared.check(ref, quote))  # control: the markers stay
        self.assertIsNone(comments.check(ref, quote))
        self.assertIn("does not contain", comments.check(ref, "a doc comment continued"))
        self.assertIn("is not a citation", comments.check("rust:lib/doc.rs:1", "The first"))
        text = "It says lib:lib/doc.rs:1-2 «a doc comment continues»."
        self.assertEqual(violations(lambda f: C.check_prose(f, "DOC", "s", text, comments)), [])
        self.assert_reports(violations(lambda f: C.check_prose(f, "DOC", "s", text.replace("continues", "ends"), comments)), "does not contain")
        self.assert_reports(violations(lambda f: C.check_prose(f, "DOC", "s", text, plain)), "is not in the checked")  # undeclared: an unchecked line citation

    def test_prose_citations_resolve_and_bare_line_citations_are_refused(self):
        text = "The design says design:841 «`Program`: items, impls» and rustc:compiler/rustc_middle/src/mir/syntax.rs:1366 «Use(Operand<'tcx>, WithRetag),»."
        self.assertEqual(violations(lambda f: C.check_prose(f, "DOC", "s", text, self.resolver)), [])
        for mutated, fragment in (
            (text.replace("items, impls", "items, imps"), "does not contain"),
            (text + " See design:842 for more.", "'design:842' is not in the checked"),
            (text + " See syntax.rs:1366.", "'syntax.rs:1366' is not in the checked"),
            (text + " See line 12.", "'line 12' is not in the checked"),
        ):
            self.assert_reports(violations(lambda f: C.check_prose(f, "DOC", "s", mutated, self.resolver)), fragment)


class UniquenessTest(unittest.TestCase):
    def setUp(self):
        self.data = tomllib.loads((ROOT / CV.TABLE_REL).read_text(encoding="utf-8"))

    def test_real_table_rows_are_unique_and_repeat_no_element(self):
        def run(f):
            for kind, (_, _, key) in CV.ROWS.items():
                C.unique_rows(f, "TABLE", kind, self.data[kind], key)
                for row in self.data[kind]:
                    C.repeated_elements(f, "TABLE", kind, row)
        self.assertEqual(violations(run), [])

    def test_a_duplicate_row_and_a_repeated_element_are_refused(self):
        rows = copy.deepcopy(self.data["entry"])
        self.assertEqual(violations(lambda f: C.unique_rows(f, "TABLE", "entry", rows, lambda r: r["name"])), [])  # control
        rows.append(copy.deepcopy(rows[3]))
        found = violations(lambda f: C.unique_rows(f, "TABLE", "entry", rows, lambda r: r["name"]))
        self.assertEqual(found, [f"TABLE: entry[{len(rows) - 1}]: duplicate row {rows[3]['name']!r}"])
        row = copy.deepcopy(next(r for r in self.data["not_in_core"] if "payload" in r))
        field = next(iter(row["payload"]))
        row["payload"][field].append(row["payload"][field][0])
        self.assertEqual(violations(lambda f: C.repeated_elements(f, "TABLE", "row", row)),
                         [f"TABLE: row: payload.{field} repeats {row['payload'][field][0]!r}"])
        row = copy.deepcopy(self.data["mir_operator"][0])
        row["maps_to"].append(row["maps_to"][0])
        self.assertTrue(violations(lambda f: C.repeated_elements(f, "TABLE", "row", row)))


class BlockTest(unittest.TestCase):
    def test_the_real_counts_block_and_its_mutations(self):
        text = (ROOT / CV.DOC_REL).read_text(encoding="utf-8")
        span = C.block_span(text, CV.COUNTS_BLOCK)
        body = text[span[0]:span[1]]
        self.assertEqual(violations(lambda f: C.check_block(f, "DOC", text, CV.COUNTS_BLOCK, body)), [])
        self.assertEqual(C.replace_block(text, CV.COUNTS_BLOCK, body), text)
        drifted = body.replace("| **Syntax total** |", "| **Syntax sum** |", 1)
        self.assertNotEqual(drifted, body)
        self.assertTrue(violations(lambda f: C.check_block(f, "DOC", text, CV.COUNTS_BLOCK, drifted)))
        self.assertTrue(violations(lambda f: C.check_block(f, "DOC", C.replace_block(text, CV.COUNTS_BLOCK, drifted), CV.COUNTS_BLOCK, body)))
        unmarked = text.replace(f"<!-- {CV.COUNTS_BLOCK}:end -->", "")
        self.assertIn("markers are missing", violations(lambda f: C.check_block(f, "DOC", unmarked, CV.COUNTS_BLOCK, body))[0])


class ReviewTest(TempDir):
    @classmethod
    def setUpClass(cls):
        f = C.Findings()
        cls.doc = (ROOT / CV.DOC_REL).read_text(encoding="utf-8")
        cls.table_text = (ROOT / CV.TABLE_REL).read_text(encoding="utf-8")
        cls.sections = C.document_judgments(f, "DOC", cls.doc, generated=(CV.COUNTS_BLOCK,))
        cls.judgments = CV.judgments(f, cls.table_text, cls.sections)
        assert not f.violations, f.violations
        cls.registry_text = (ROOT / CV.REGISTRY_REL).read_text(encoding="utf-8")

    def check(self, text, judgments=None, repo=None, path=None):
        path = path or self.tmp / "registry.toml"
        path.write_text(text, encoding="utf-8")
        return violations(lambda f: C.check_reviews(f, path, CV.DELIVERABLE, self.judgments if judgments is None else judgments, CV.JUDGMENT_KINDS, repo))

    def entry_line(self, jid):
        return next(line for line in self.registry_text.split("\n") if line.startswith(f'"{jid}" = '))

    def test_real_registry_registers_every_real_judgment(self):
        self.assertEqual(self.check(self.registry_text), [])
        self.assertEqual(violations(lambda f: C.check_reviews(f, ROOT / CV.REGISTRY_REL, CV.DELIVERABLE, self.judgments, CV.JUDGMENT_KINDS, ROOT)), [])

    def test_a_changed_judgment_needs_an_appended_review_of_its_digest(self):
        jid = "inductive:Operand"
        changed = dict(self.judgments)
        changed[jid] = dict(changed[jid], minirust_split_from="Statement")
        self.assert_reports(self.check(self.registry_text, changed), f"judgment {jid}: its content changed")
        new = C.digest(jid, changed[jid])
        line = self.entry_line(jid)
        old = line.split('digest = "')[1].split('"')[0]
        self.assertTrue(line.endswith(f'"{old}"]] }}'))

        def registry(digest, *appended):
            reviews = "".join(f', ["round18-prose", "{d}"]' for d in appended)
            return self.registry_text.replace(line, line.replace(f'digest = "{old}"', f'digest = "{digest}"')[:-5] + f'"]{reviews}] }}')

        self.assertEqual(self.check(registry(old), self.judgments), [])  # control: the unchanged entry
        self.assert_reports(self.check(registry(new), changed), f"judgment {jid}: its last review record (round5-verification) reviewed {old}")
        self.assert_reports(self.check(registry(new, old), changed), f"judgment {jid}: its last review record (round18-prose) reviewed {old}")
        self.assertEqual(self.check(registry(new, new), changed), [])  # control: the change with its review record passes

    def test_unregistered_stale_unknown_and_unused_are_refused(self):
        extra = dict(self.judgments, **{"entry:Ty.Invented": {"name": "Ty.Invented"}})
        self.assert_reports(self.check(self.registry_text, extra), "judgment entry:Ty.Invented is not registered")
        fewer = {k: v for k, v in self.judgments.items() if k != "entry:Ty.Str"}
        self.assert_reports(self.check(self.registry_text, fewer), "judgment entry:Ty.Str: is registered, but no such judgment exists")
        line = self.entry_line("entry:Ty.Str")
        retired = self.registry_text.replace(line, line[:-2] + ', retired = "round18-prose" }')
        self.assertEqual(self.check(retired, fewer), [])  # control: a retired judgment that is gone
        self.assert_reports(self.check(retired), "judgment entry:Ty.Str: is retired, but the judgment exists")
        unknown = self.registry_text.replace('"entry:Ty.Str" = ', '"widget:Ty.Str" = ')
        self.assert_reports(self.check(unknown), "'widget' is not a judgment kind")
        unused = self.registry_text.replace("[judgment]", '[record.unused]\nround = "r"\ndate = "2026-09-17"\nevidence = ["e"]\nreason = "r"\n\n[judgment]')
        self.assert_reports(self.check(unused), "review record unused reviews no judgment")
        cited = self.registry_text.replace('reason = "UB-NAME and', 'reason = "see line 12. UB-NAME and')
        self.assert_reports(self.check(cited), "its reason carries a line citation")
        commented = self.registry_text.replace("[judgment]\n", "[judgment]\n# the owner approved every judgment below\n")
        self.assert_reports(self.check(commented), "carries comments, which no review covers")
        line = self.entry_line("entry:Ty.Str")
        repeated = self.registry_text.replace(line, line[:-4] + "], " + line.split("reviews = [")[1][:-4] + "]] }")
        self.assert_reports(self.check(repeated), "judgment entry:Ty.Str: reviews repeats")

    def test_one_id_from_two_judgments_is_refused(self):
        pairs = list(self.judgments.items())
        self.assertEqual(violations(lambda f: self.assertEqual(C.merge_judgments(f, pairs), self.judgments)), [])  # control
        row = self.judgments["entry:Program.start"]
        found = violations(lambda f: C.merge_judgments(f, pairs + [("entry:Program.start", "A section under a row's id.\n")]))
        self.assertEqual(found, ["REVIEW: judgment id entry:Program.start is produced twice (two rows with one key, or two sources); each judgment has its own id"])
        kept = C.merge_judgments(C.Findings(), pairs + [("entry:Program.start", "A section under a row's id.\n")])
        self.assertEqual(kept["entry:Program.start"], row)

    def later_record(self, registry):
        return registry.replace("[judgment]", '[record.later]\nround = "r"\ndate = "2026-09-18"\nevidence = ["e"]\nreason = "r"\n\n[judgment]')

    def committed_registry(self):
        repo = self.git_repo()
        rel = "docs/trust-core/reviews/core_vocabulary.toml"
        self.commit(repo, rel, self.registry_text)
        return repo, rel, repo / rel

    def test_committed_review_records_are_append_only(self):
        repo, rel, path = self.committed_registry()
        self.assertEqual(self.check(self.registry_text, repo=repo, path=path), [])  # control: unchanged
        jid = "entry:Ty.Str"
        line = self.entry_line(jid)
        digest = line.split('digest = "')[1].split('"')[0]
        appended = self.later_record(self.registry_text.replace(line, line[:-4] + f'], ["later", "{digest}"]] }}'))
        self.assertEqual(self.check(appended, repo=repo, path=path), [])  # control: a review by a new record
        rewritten = self.registry_text.replace(line, line.replace('"round5-verification"', '"round18-prose"'))
        self.assert_reports(self.check(rewritten, repo=repo, path=path), f"judgment {jid}: its review records committed in")
        removed = self.registry_text.replace(line + "\n", "")
        self.assert_reports(self.check(removed, repo=repo, path=path), f"judgment {jid} was registered in")
        record = self.registry_text.replace('date = "2026-09-16"', 'date = "2026-09-15"')
        self.assert_reports(self.check(record, repo=repo, path=path), "review record round5-verification was committed in")
        self.commit(repo, rel, self.registry_text.replace(line, line[:-2] + ', retired = "round18-prose" }'))
        self.assert_reports(self.check(self.registry_text, repo=repo, path=path), f"judgment {jid}: its retirement committed in")

    def test_a_committed_record_reviews_no_later_change(self):
        repo, rel, path = self.committed_registry()
        changed = dict(self.judgments, **{"prose:oq-3": self.judgments["prose:oq-3"].replace("**before**", "after", 1)})
        self.assertNotEqual(changed["prose:oq-3"], self.judgments["prose:oq-3"])
        line = self.entry_line("prose:oq-3")
        old, new = line.split('digest = "')[1].split('"')[0], C.digest("prose:oq-3", changed["prose:oq-3"])

        def credit(registry, record):
            return registry.replace(line, line.replace(old, new, 1)[:-4] + f'], ["{record}", "{new}"]] }}')

        self.assertEqual(self.check(self.later_record(credit(self.registry_text, "later")), changed, repo=repo, path=path), [])  # control
        # The change credited to a committed record, the producer's or the independent one.
        for committed in ("round18-repair", "round5-verification"):
            with self.subTest(committed):
                self.assertEqual(self.check(credit(self.registry_text, committed), changed),  # without history it would pass
                                 [])
                self.assertEqual(self.check(credit(self.registry_text, committed), changed, repo=repo, path=path),
                                 [f"REVIEW-HISTORY: review record {committed} was committed in {sh(repo, 'rev-parse', 'HEAD')[:10]} and now also reviews ['prose:oq-3']; a change is reviewed by a new record, never credited to a committed one"])
        # A record committed once cannot take a later review either.
        self.commit(repo, rel, self.later_record(self.registry_text.replace(self.entry_line("entry:Ty.Str"), self.entry_line("entry:Ty.Str")[:-4] + '], ["later", "' + self.entry_line("entry:Ty.Str").split('digest = "')[1].split('"')[0] + '"]] }')))
        again = credit((repo / rel).read_text(encoding="utf-8"), "later")
        self.assert_reports(self.check(again, changed, repo=repo, path=path), "review record later was committed in")

    def test_a_change_credited_to_a_committed_record_stays_refused_once_committed(self):
        # The verifier's finding on 28f6ab4c01: a record was credited with the union of what every
        # committed version credits to it, HEAD included, so a change credited to a committed
        # record was refused only until `git commit` made HEAD credit it. A record now reviews what
        # the commit that introduced it credits, whatever later commits (or a MERGE_HEAD) hold.
        repo, rel, path = self.committed_registry()
        introduced = sh(repo, "rev-parse", "HEAD").strip()
        changed = dict(self.judgments, **{"prose:oq-3": self.judgments["prose:oq-3"].replace("**before**", "after", 1)})
        line = self.entry_line("prose:oq-3")
        old, new = line.split('digest = "')[1].split('"')[0], C.digest("prose:oq-3", changed["prose:oq-3"])
        laundered = self.registry_text.replace(line, line.replace(old, new, 1)[:-4] + f'], ["round18-repair", "{new}"]] }}')
        refusal = f"REVIEW-HISTORY: review record round18-repair was committed in {introduced[:10]} and now also reviews ['prose:oq-3']; a change is reviewed by a new record, never credited to a committed one"
        self.assertEqual(self.check(laundered, changed, repo=repo, path=path), [refusal])  # uncommitted
        # Committed on a side line and named by MERGE_HEAD, it is still refused.
        sh(repo, "checkout", "-q", "-b", "side")
        self.commit(repo, rel, laundered, "credit a change to a committed record")
        side = sh(repo, "rev-parse", "HEAD").strip()
        sh(repo, "checkout", "-q", "-")
        merge_head = Path(sh(repo, "rev-parse", "--path-format=absolute", "--git-path", "MERGE_HEAD").strip())
        merge_head.write_text(side + "\n", encoding="ascii")
        self.assertEqual(C.merge_heads(repo), [side])
        self.assertEqual(self.check(laundered, changed, repo=repo, path=path), [refusal])
        merge_head.unlink()
        # Committed on HEAD's own line, it is still refused.
        sh(repo, "reset", "-q", "--hard", side)
        self.assertEqual(sh(repo, "rev-parse", "HEAD").strip(), side)
        self.assertEqual(self.check(laundered, changed, repo=repo, path=path), [refusal])
        # A record removed and restored by later commits is not introduced again by the restore.
        self.commit(repo, rel, "", "remove every record")
        self.commit(repo, rel, laundered, "restore them, crediting the change")
        self.assertEqual(self.check(laundered, changed, repo=repo, path=path), [refusal])
        # Control: the same change reviewed by a new record passes, uncommitted and committed.
        control, crel, cpath = self.committed_registry_in("control")
        reviewed = self.later_record(self.registry_text.replace(line, line.replace(old, new, 1)[:-4] + f'], ["later", "{new}"]] }}'))
        self.assertEqual(self.check(reviewed, changed, repo=control, path=cpath), [])
        self.commit(control, crel, reviewed, "review the change by a new record")
        self.assertEqual(self.check(reviewed, changed, repo=control, path=cpath), [])

    def test_a_record_introduced_on_two_lines_reviews_what_both_credit(self):
        # Two lines each introduce record `twin` (a cherry-pick, say). The merge credits it only
        # with what both lines credit, so one line cannot widen what the other's record reviews.
        str_line, bool_line = self.entry_line("entry:Ty.Str"), self.entry_line("entry:Ty.Bool")
        str_digest = str_line.split('digest = "')[1].split('"')[0]
        bool_digest = bool_line.split('digest = "')[1].split('"')[0]
        record = '[record.twin]\nround = "r"\ndate = "2026-09-24"\nevidence = ["e"]\nreason = "r"\n\n[judgment]'

        def twin(both):
            text = self.registry_text.replace("[judgment]", record).replace(str_line, str_line[:-4] + f'], ["twin", "{str_digest}"]] }}')
            return text.replace(bool_line, bool_line[:-4] + f'], ["twin", "{bool_digest}"]] }}') if both else text

        for name, left_both in (("identical", True), ("wider", False)):
            with self.subTest(name):
                repo, rel, path = self.committed_registry_in(name)
                base = sh(repo, "rev-parse", "HEAD").strip()
                sh(repo, "checkout", "-q", "-b", "left")
                self.commit(repo, rel, twin(left_both))
                sh(repo, "checkout", "-q", "-b", "right", base)
                self.commit(repo, rel, twin(True))
                subprocess.run(["git", "-C", str(repo), "-c", "user.email=t@e.invalid", "-c", "user.name=t", "merge", "-q", "-s", "ours", "--no-edit", "left"],
                               check=True, capture_output=True, env=C.git_environment())
                found = self.check(twin(True), repo=repo, path=path)
                if left_both:
                    self.assertEqual(found, [])  # control: both lines credit the same pairs
                else:
                    self.assertIn("now also reviews ['entry:Ty.Bool']", "\n".join(found))

    def test_two_merged_lines_of_history_keep_each_lines_reviews_in_order(self):
        # Two branches each append a review to one judgment; the merge holds both, which no single
        # committed prefix can. Each line's reviews stay in its order, and a new review follows them.
        repo, rel, path = self.committed_registry()
        base = sh(repo, "rev-parse", "HEAD").strip()
        jid = "entry:Ty.Str"
        line = self.entry_line(jid)
        digest = line.split('digest = "')[1].split('"')[0]

        def with_record(text, rid):
            return text.replace("[judgment]", f'[record.{rid}]\nround = "r"\ndate = "2026-09-18"\nevidence = ["e"]\nreason = "r"\n\n[judgment]')

        def reviewed(rids):
            text = self.registry_text
            for rid in rids:
                text = with_record(text, rid)
            return text.replace(line, line[:-4] + "]" + "".join(f', ["{rid}", "{digest}"]' for rid in rids) + "] }")

        sh(repo, "checkout", "-q", "-b", "left")
        self.commit(repo, rel, reviewed(["left"]))
        sh(repo, "checkout", "-q", "-b", "right", base)
        self.commit(repo, rel, reviewed(["right"]))
        subprocess.run(["git", "-C", str(repo), "-c", "user.email=t@e.invalid", "-c", "user.name=t", "merge", "-q", "-s", "ours", "--no-edit", "left"],
                       check=True, capture_output=True, env=C.git_environment())
        for order in (["left", "right"], ["right", "left"], ["left", "right", "merged"]):
            with self.subTest(order=order):
                self.assertEqual(self.check(reviewed(order), repo=repo, path=path), [])
        # Before this rule, each line's committed prefix refused the merge.
        self.assert_reports(self.check(reviewed(["left"]), repo=repo, path=path), f"judgment {jid}: its review records committed in")
        for label, order, fragment in (
            ("a new review before the committed ones", ["merged", "left", "right"], "no version committed its record"),
            ("a new review between them", ["left", "merged", "right"], "no version committed its record"),
            ("one line's review dropped", ["left", "merged"], "are edited, removed or reordered"),
        ):
            with self.subTest(label):
                self.assert_reports(self.check(reviewed(order), repo=repo, path=path), fragment)
        # On one line, a review moved before a review committed earlier is refused as reordered.
        linear, lrel, lpath = self.committed_registry_in("linear")
        self.commit(linear, lrel, reviewed(["first"]))
        self.commit(linear, lrel, reviewed(["first", "second"]))
        self.assertEqual(self.check(reviewed(["first", "second"]), repo=linear, path=lpath), [])  # control
        self.assert_reports(self.check(reviewed(["second", "first"]), repo=linear, path=lpath), "are edited, removed or reordered")

    def two_record_registry(self, jid, digest, rids, text=None):
        """The registry with `rids` as new records and `jid` registered with one review by each."""
        text = self.registry_text if text is None else text
        for rid in rids:
            text = text.replace("[judgment]", f'[record.{rid}]\nround = "r"\ndate = "2026-09-24"\nevidence = ["e"]\nreason = "r"\n\n[judgment]')
        reviews = ", ".join(f'["{rid}", "{digest}"]' for rid in rids)
        # Into the [judgment] table itself: records also follow it, so the end of the file is
        # whichever record was appended last, and a key there would edit that record.
        self.assertEqual(text.count("\n[judgment]\n"), 1)
        return text.replace("\n[judgment]\n", f'\n[judgment]\n"{jid}" = {{ digest = "{digest}", reviews = [{reviews}] }}\n')

    def test_a_new_judgment_reviewed_by_two_new_records_is_accepted(self):
        # The verifier's finding on 184fc22223: with no review by a committed record, the index
        # of the last one defaulted to -1 and `reviews[:-1]` reported every earlier review as
        # standing before a committed review that does not exist.
        repo, rel, path = self.committed_registry()
        jid = "entry:Ty.Invented"
        judgments = dict(self.judgments, **{jid: {"name": "Ty.Invented"}})
        digest = C.digest(jid, judgments[jid])
        for rids in (["verifier-a"], ["verifier-a", "verifier-b"], ["verifier-a", "verifier-b", "verifier-c"]):
            with self.subTest(rids=rids):
                self.assertEqual(self.check(self.two_record_registry(jid, digest, rids), judgments, repo=repo, path=path), [])
        # Control: a new record's review before a committed one is still refused.
        line = self.entry_line("entry:Ty.Str")
        committed = line.split('digest = "')[1].split('"')[0]
        early = self.later_record(self.registry_text).replace(line, line.replace("reviews = [", f'reviews = [["later", "{committed}"], '))
        self.assert_reports(self.check(early, repo=repo, path=path), "judgment entry:Ty.Str: the review by ['later'] stands before a committed review")

    def merge_lines(self):
        """A repository whose branches `left` and `right` each add one record reviewing entry:Ty.Str,
        with `right` checked out. Returns (repo, rel, path, reviewed) where reviewed(rids) is the
        registry with those records and their reviews, in that order."""
        repo, rel, path = self.committed_registry()
        base = sh(repo, "rev-parse", "HEAD").strip()
        line = self.entry_line("entry:Ty.Str")
        digest = line.split('digest = "')[1].split('"')[0]

        def reviewed(rids, records=None):
            text = self.registry_text
            for rid in records if records is not None else rids:
                text = text.replace("[judgment]", f'[record.{rid}]\nround = "r"\ndate = "2026-09-24"\nevidence = ["e"]\nreason = "r"\n\n[judgment]')
            return text.replace(line, line[:-4] + "]" + "".join(f', ["{rid}", "{digest}"]' for rid in rids) + "] }")

        sh(repo, "checkout", "-q", "-b", "left")
        self.commit(repo, rel, reviewed(["left"]))
        sh(repo, "checkout", "-q", "-b", "right", base)
        self.commit(repo, rel, reviewed(["right"]))
        return repo, rel, path, reviewed

    def test_an_unfinished_merge_reads_the_incoming_branch(self):
        # The verifier's finding on 184fc22223: during `git merge --no-commit` the history was read
        # from HEAD alone, so a resolution that dropped the incoming branch's review passed and was
        # refused only once committed.
        repo, rel, path, reviewed = self.merge_lines()
        merge = subprocess.run(["git", "-C", str(repo), "merge", "--no-commit", "--no-ff", "left"], capture_output=True, text=True, env=C.git_environment())
        self.assertNotEqual(merge.returncode, 0, "both lines edit one registry line, so the merge stops on a conflict")
        self.assertTrue(C.merge_heads(repo), "MERGE_HEAD names the incoming commit")
        for order in (["left", "right"], ["right", "left"]):
            with self.subTest(order=order):
                self.assertEqual(self.check(reviewed(order), repo=repo, path=path), [])  # control: both lines kept
        dropped = reviewed(["right"], records=["left", "right"])
        self.assert_reports(self.check(dropped, repo=repo, path=path), "judgment entry:Ty.Str: its review records committed in")
        self.assert_reports(self.check(reviewed(["right"]), repo=repo, path=path), "review record left was committed in")
        sh(repo, "merge", "--abort")
        self.assertEqual(C.merge_heads(repo), [])
        self.assertEqual(self.check(reviewed(["right"]), repo=repo, path=path), [])  # control: no merge, no incoming line

    def test_a_review_a_committed_merge_dropped_can_be_restored(self):
        # The verifier's finding on 184fc22223: once a merge that kept record `left` but dropped its
        # review was committed, restoring the review was refused as a review credited to a committed
        # record, so neither the broken nor the repaired registry could pass.
        repo, rel, path, reviewed = self.merge_lines()
        subprocess.run(["git", "-C", str(repo), "-c", "user.email=t@e.invalid", "-c", "user.name=t", "merge", "-q", "-s", "ours", "--no-commit", "left"],
                       check=True, capture_output=True, env=C.git_environment())
        bad = reviewed(["right"], records=["left", "right"])
        (repo / rel).write_text(bad, encoding="utf-8")
        sh(repo, "add", rel)
        sh(repo, "commit", "-q", "-m", "a merge that drops left's review")
        self.assert_reports(self.check(bad, repo=repo, path=path), "judgment entry:Ty.Str: its review records committed in")
        # The repair appends the dropped review after the reviews the merge committed.
        self.assertEqual(self.check(reviewed(["right", "left"]), repo=repo, path=path), [])
        # The merge committed `right` after the base reviews, so `left` placed before it reorders that version.
        self.assert_reports(self.check(reviewed(["left", "right"]), repo=repo, path=path), "are edited, removed or reordered")
        # Control: a (judgment, digest) no committed version credits to `left` is still refused.
        other = self.entry_line("entry:Ty.Bool")
        other_digest = other.split('digest = "')[1].split('"')[0]
        credited = reviewed(["right", "left"]).replace(other, other[:-4] + f'], ["left", "{other_digest}"]] }}')
        self.assert_reports(self.check(credited, repo=repo, path=path), "review record left was committed in", "now also reviews ['entry:Ty.Bool']")

    def committed_registry_in(self, name):
        repo = self.git_repo(name)
        rel = "docs/trust-core/reviews/core_vocabulary.toml"
        self.commit(repo, rel, self.registry_text)
        return repo, rel, repo / rel

    def test_a_history_that_cannot_be_read_whole_is_refused(self):
        repo, rel, path = self.committed_registry()
        edited = self.registry_text.replace('date = "2026-09-16"', 'date = "2026-09-15"')
        self.commit(repo, rel, edited, "edit a committed record")
        committed_edit = [f"REVIEW-HISTORY: review record round5-verification was committed in {sh(repo, 'rev-list', '--max-parents=0', 'HEAD')[:10]} and is now edited or removed; records are append-only"]
        self.assertEqual(self.check(edited, repo=repo, path=path), committed_edit)  # control: a full history sees the edit
        shallow = f"REVIEW-HISTORY: {sh(repo, 'rev-parse', '--show-toplevel').strip()} is a shallow repository"
        # The verifier's attack: the shallow boundary at the edit hides the first commit.
        (repo / ".git" / "shallow").write_text(sh(repo, "rev-parse", "HEAD"), encoding="utf-8")
        self.assertEqual(sh(repo, "rev-parse", "--is-shallow-repository").strip(), "true")
        found = self.check(edited, repo=repo, path=path)
        self.assertFalse(any("round5-verification" in v for v in found), "the boundary hides the edit")
        self.assertEqual([v[:len(shallow)] for v in found], [shallow])
        # A linked worktree reads the shallow file of the common directory.
        linked = self.tmp / "linked"
        sh(repo, "worktree", "add", "-q", "--detach", str(linked))
        found = self.check(edited, repo=linked, path=linked / rel)
        self.assertTrue(any(v.startswith("REVIEW-HISTORY: ") and "is a shallow repository" in v for v in found), found)
        (repo / ".git" / "shallow").unlink()
        self.assertEqual(self.check(edited, repo=linked, path=linked / rel), committed_edit)  # control: the full history again
        # No repository, and a registry outside the repository.
        plain = self.tmp / "plain"
        plain.mkdir()
        self.assert_reports(self.check(self.registry_text, repo=plain, path=plain / "registry.toml"), "is not a git repository")
        self.assert_reports(self.check(self.registry_text, repo=repo, path=self.tmp / "outside.toml"), "is not in the repository")
        with mock.patch.object(C, "git", side_effect=lambda repo_, *args, **kw: None if "log" in args[:3] else C_git(repo_, *args, **kw)):
            self.assert_reports(self.check(edited, repo=repo, path=path), "cannot be listed (git log failed)")

    def test_an_unreadable_committed_version_is_refused(self):
        # The B0 verifier's attack: in an offline partial clone an older registry version cannot be
        # read, and a failed `git show` was taken for a deletion. Removing that version's blob from
        # the object store reproduces it.
        repo, rel, path = self.committed_registry()
        first = sh(repo, "rev-parse", "HEAD").strip()
        edited = self.registry_text.replace('date = "2026-09-16"', 'date = "2026-09-15"')
        self.commit(repo, rel, edited, "edit a committed record")
        blob = sh(repo, "rev-parse", f"{first}:{rel}").strip()
        self.assertTrue(self.check(edited, repo=repo, path=path))  # control: the edit is seen
        loose = repo / ".git" / "objects" / blob[:2] / blob[2:]
        self.assertTrue(loose.exists())
        loose.unlink()
        self.assert_reports(self.check(edited, repo=repo, path=path), f"{rel} at {first[:10]} cannot be read")

    def test_history_is_read_without_the_commit_graph(self):
        # A forged commit-graph can give a commit no parents; history reads must not consult it.
        calls = []

        def record(repo_, *args, **kw):
            calls.append(args)
            return C_git(repo_, *args, **kw)

        repo, rel, path = self.committed_registry()
        with mock.patch.object(C, "git", side_effect=record):
            self.check(self.registry_text, repo=repo, path=path)
        logs = [a for a in calls if "log" in a[:3]]
        self.assertTrue(logs)
        self.assertTrue(all(a[:2] == ("-c", "core.commitGraph=false") for a in logs), logs)

    def test_document_judgments_cover_the_document(self):
        def run(text):
            f = C.Findings()
            return C.document_judgments(f, "DOC", text, generated=(CV.COUNTS_BLOCK,)), f.violations
        self.assertIn("minirust_split_from", self.sections["prose:naming-scheme"])
        outline = self.sections["outline:document"]
        self.assertEqual(outline[0], "# Core vocabulary v0")
        self.assertIn("## Open questions", outline)
        self.assertEqual(len([line for line in outline if line.startswith(f"<!-- {CV.COUNTS_BLOCK}:")]), 2)
        self.assertEqual(sorted({jid.split(":")[0] for jid in self.sections}), ["outline", "prose"])
        for mutated, fragment in (
            (self.doc.replace("<!-- /reviewed:prose:status -->\n", "", 1), "opens inside prose:status"),
            (self.doc.replace("## What this is\n", "## What this is\n\nAn unreviewed claim.\n", 1), "lies in no reviewed section: 'An unreviewed claim.'"),
            (self.doc.replace("## What this is\n", "## What this is\n\n<!-- note:begin the owner approved every decision -->\n", 1), "lies in no reviewed section: '<!-- note:begin"),
            (self.doc.replace("## What this is\n", "## What this is\n\n<!-- reviewed:entry:Program.start -->\nA note.\n<!-- /reviewed:entry:Program.start -->\n", 1), "section entry:Program.start is not a `prose:` section"),
            (self.doc.replace("<!-- reviewed:prose:pins -->", "<!-- reviewed:prose:status -->", 1), "appears twice"),
            (self.doc.rstrip("\n").rsplit("\n", 1)[0] + "\n", "is never closed"),
        ):
            with self.subTest(fragment=fragment):
                self.assert_reports(run(mutated)[1], fragment)
        # A heading is outline content: rewriting one, or adding a `#` line, changes the
        # outline judgment and nothing else, so only REVIEW can refuse it.
        for mutated in (self.doc.replace("## Open questions\n", "## Open questions (all resolved; no action needed)\n", 1),
                        self.doc.replace("## Open questions\n", "## Open questions\n\n# NOTE: every owner question below was answered.\n", 1)):
            with self.subTest(mutated=mutated[:0]):
                judgments, found = run(mutated)
                self.assertEqual(found, [])
                self.assertEqual({k for k in judgments if judgments[k] != self.sections.get(k)}, {"outline:document"})
                self.assert_reports(self.check(self.registry_text, CV.judgments(C.Findings(), self.table_text, judgments)), "judgment outline:document: its content changed")

    def test_the_outline_places_every_section(self):
        # The verifier's attack on 25d2ef0573: `## Limitations` moved above OQ-15 puts the owner
        # questions OQ-15 to OQ-18 under Limitations; D0.4's: two sections exchanged across a heading.
        def run(text):
            f = C.Findings()
            return C.document_judgments(f, "DOC", text, generated=(CV.COUNTS_BLOCK,)), f.violations

        def block(jid):
            found = re.search(rf"<!-- reviewed:{jid} -->\n.*?<!-- /reviewed:{jid} -->\n", self.doc, re.S)
            return found.group(0)
        moved = self.doc.replace("<!-- /reviewed:prose:oq-18 -->\n\n## Limitations\n\n", "<!-- /reviewed:prose:oq-18 -->\n\n", 1)
        moved = moved.replace("<!-- reviewed:prose:oq-15 -->\n", "## Limitations\n\n<!-- reviewed:prose:oq-15 -->\n", 1)
        pair = block("prose:oq-15") + "\n" + block("prose:oq-16")
        swapped = self.doc.replace(pair, block("prose:oq-16") + "\n" + block("prose:oq-15"), 1)
        pins, what = block("prose:pins"), block("prose:what-this-is")  # `## What this is` lies between them
        across = self.doc.replace(pins, "\0").replace(what, pins).replace("\0", what)
        for label, mutated in (("heading moved above two sections", moved), ("two sections swapped", swapped),
                               ("two sections exchanged across a heading", across)):
            with self.subTest(label):
                self.assertNotEqual(mutated, self.doc)
                self.assertEqual(len(mutated.split("\n")), len(self.doc.split("\n")))
                judgments, found = run(mutated)
                self.assertEqual(found, [])
                self.assertEqual({k for k in judgments if judgments[k] != self.sections.get(k)}, {"outline:document"})
                self.assert_reports(self.check(self.registry_text, CV.judgments(C.Findings(), self.table_text, judgments)), "judgment outline:document: its content changed")
        outline = self.sections["outline:document"]
        # Every opening marker is in the outline, in document order, among the headings and block markers.
        opened = [line for line in self.doc.split("\n") if C.SECTION_OPEN.match(line)]
        self.assertEqual([line for line in outline if C.SECTION_OPEN.match(line)], opened)
        self.assertEqual(outline[:4], ["# Core vocabulary v0", "<!-- reviewed:prose:status -->", "<!-- reviewed:prose:pins -->", "## What this is"])
        self.assertLess(outline.index("<!-- reviewed:prose:oq-18 -->"), outline.index("## Limitations"))
        self.assertGreater(run(moved)[0]["outline:document"].index("<!-- reviewed:prose:oq-15 -->"), run(moved)[0]["outline:document"].index("## Limitations"))
        self.assertLess(run(across)[0]["outline:document"].index("## What this is"), run(across)[0]["outline:document"].index("<!-- reviewed:prose:pins -->"))
        # document_judgments has no mode that leaves sections out of the outline.
        self.assertNotIn("outline_sections", C.document_judgments.__code__.co_varnames)


class TomlCommentsTest(unittest.TestCase):
    def test_the_real_table_comments_are_exactly_its_comment_lines(self):
        text = (ROOT / CV.TABLE_REL).read_text(encoding="utf-8")
        found = C.toml_comments(text)
        self.assertEqual([comment for comment, _, _ in found], [line[1:] for line in text.split("\n") if line.startswith("#")])
        # Oracle: removing every comment leaves the data unchanged.
        stripped = "\n".join("" if line.startswith("#") else line for line in text.split("\n"))
        self.assertEqual(tomllib.loads(stripped), tomllib.loads(text))
        # Every placement is unambiguous: its lines occur once among the content lines, or reach the end.
        content = [line.strip() for line in stripped.split("\n") if line.strip()]
        for comment, where, lines in found:
            run = lines.split("\n") if lines else []
            starts = [k for k in range(len(content)) if content[k:k + len(run)] == run]
            self.assertTrue(run == [] or len(starts) == 1 or starts[-1] + len(run) == len(content), (comment, lines))

    def test_strings_hold_no_comment_and_a_trailing_comment_is_found(self):
        text = ('a = "x # not" # one\nb = \'y # not\' # two\nc = """\nz # not \\""" # still not\n""""# three\n'
                "d = \'\'\'\n# not\n\'\'\'\'\'# four\ne = \"\\\" # not\" # five\n")
        data = tomllib.loads(text)
        self.assertEqual(data["c"], 'z # not """ # still not\n"')
        self.assertEqual([c for c, _, _ in C.toml_comments(text)], [" one", " two", " three", " four", " five"])
        self.assertEqual([c for c, _, _ in C.toml_comments(text.replace("# five", ""))], [" one", " two", " three", " four"])
        # A comment after a value stands after its line, which here is unique on its own.
        self.assertEqual([(c, w) for c, w, _ in C.toml_comments(text)], [(" one", "after"), (" two", "after"), (" three", "after"), (" four", "after"), (" five", "after")])
        self.assertEqual(C.toml_comments(text)[0][2], 'a = "x # not"')
        # A comment alone on its line heads the next content line, extended until the run is unique.
        rows = '# kinds\n\n# first\n[[entry]]\n\nname = "A"\n\n[[entry]]\nname = "B" # the second\n# last\n'
        self.assertEqual(C.toml_comments(rows), [[" kinds", "heads", '[[entry]]\nname = "A"'], [" first", "heads", '[[entry]]\nname = "A"'],
                                                 [" the second", "after", 'name = "B"'], [" last", "heads", ""]])

    def test_rows_that_begin_with_the_same_line_place_a_comment_apart(self):
        # The verifier's finding on 9436f8d56b: seven [[design_item]] rows begin `line = 841`, and a comment
        # block moved from one to the next was tied to that one line both times.
        text = (ROOT / CV.TABLE_REL).read_text(encoding="utf-8")
        blocks = [part for part in re.split(r"\n(?=\[\[design_item\]\])", text) if part.startswith("[[design_item]]\nline = 841\n")]
        self.assertGreater(len(blocks), 2)
        comment = "# A comment on the first of the rows that begin alike.\n"
        first, second = blocks[0], blocks[1]
        on_first = text.replace(first, comment + first, 1)
        on_second = text.replace(second, comment + second, 1)
        self.assertEqual(tomllib.loads(on_first), tomllib.loads(on_second))
        placed_first = [p for p in C.toml_comments(on_first) if p[0] == comment[1:-1]]
        placed_second = [p for p in C.toml_comments(on_second) if p[0] == comment[1:-1]]
        self.assertEqual(len(placed_first), 1)
        self.assertNotEqual(placed_first, placed_second)
        self.assertTrue(placed_first[0][2].startswith("[[design_item]]\nline = 841\n"))
        # A trailing comment on one of several identical lines is placed apart the same way.
        line = "line = 841\n"
        after_first = on_first.replace(comment, "", 1).replace(first, first.replace(line, "line = 841 # here\n", 1), 1)
        after_second = on_first.replace(comment, "", 1).replace(second, second.replace(line, "line = 841 # here\n", 1), 1)
        self.assertNotEqual([p for p in C.toml_comments(after_first) if p[0] == " here"], [p for p in C.toml_comments(after_second) if p[0] == " here"])
        # Control: the same comment in the same place is placed the same, whatever other rows are added far away.
        far = on_first + '\n[[design_item]]\nline = 1\ntoken = "far"\n'
        self.assertEqual([p for p in C.toml_comments(far) if p[0] == comment[1:-1]], placed_first)

    def test_a_comment_moved_to_head_another_row_changes_the_comments(self):
        text = (ROOT / CV.TABLE_REL).read_text(encoding="utf-8")
        header = ("# ----------------------------------------------------------------------------\n"
                  "# One row per constructor (kind = variant) or record field (kind = field).\n"
                  "# ----------------------------------------------------------------------------\n\n")
        anchor = '[[inductive]]\nname = "TreeBorrowsUb"\n'
        self.assertEqual((text.count(header), text.count(anchor)), (1, 1))
        moved = text.replace(header, "", 1).replace(anchor, header + anchor, 1)
        self.assertEqual(tomllib.loads(moved), tomllib.loads(text))
        self.assertEqual([c for c, _, _ in C.toml_comments(moved)], [c for c, _, _ in C.toml_comments(text)])  # the text and order are unchanged
        self.assertNotEqual(C.toml_comments(moved), C.toml_comments(text))
        heads = [lines for comment, _, lines in C.toml_comments(moved) if comment.startswith(" One row per constructor")]
        self.assertEqual(heads, [anchor.rstrip("\n")])


class ImmutableTest(TempDir):
    def test_real_committed_file_equals_its_first_version(self):
        # A committed web snapshot, which is immutable by policy. (This control used EXTERNAL_PINS.toml,
        # which its own header moves with the alignment, and which gained the rfcs full-clone row.)
        snapshot = "docs/trust-core/snapshots/ucg-97.json"
        self.assertEqual(violations(lambda f: self.assertEqual(C.check_immutable(f, "SNAPSHOT", ROOT, [snapshot]), 1)), [])

    def test_an_edited_snapshot_and_a_wrong_sha256_are_refused(self):
        repo = self.git_repo()
        self.commit(repo, "snapshots/a.json", '{"a": 1}\n')
        pin = {"snapshots/a.json": hashlib.sha256(b'{"a": 1}\n').hexdigest()}
        self.assertEqual(violations(lambda f: C.check_immutable(f, "SNAPSHOT", repo, ["snapshots/a.json"], pin)), [])  # control
        self.commit(repo, "snapshots/a.json", '{"a": 2}\n', "edit")
        self.assert_reports(violations(lambda f: C.check_immutable(f, "SNAPSHOT", repo, ["snapshots/a.json"], pin)),
                            "differs from its first committed version", "does not match its sha256 pin")


if __name__ == "__main__":
    unittest.main(verbosity=1)
