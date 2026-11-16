#!/usr/bin/env python3
"""Regression test: the scoped push lane for the bootstrap scripts' own tests.

`scoped.bootstrap-script-tests` (scripts/check_bootstrap_script_tests.sh) runs
scripts/tests/recreate_bootstrap_test.py and scripts/tests/promote_toolchain_test.sh
when a push changes the bootstrap recreator, the sealing script, one of those
tests, or code they load. Until 2026-10-12 no push row ran either test, and two
fixes to those scripts landed on a green hook that had run neither.

Three things are held here.

  * THE SCOPE IS DERIVED. Every `scripts/` or `tools/` code file that a file in
    the lane's SCOPE names (a path literal, a bare file name beside it, an
    `import` of a sibling module, a `scripts/...` or `tools/...` word in a shell
    script) must be in SCOPE or in NOT_LOADED below with the reason it is not
    run; and every SCOPE entry must be named by something reachable from the
    two scripts and the two tests. A new import without a scope entry, and a
    scope entry nothing loads, both fail.
    What the derivation reads is names, so it cannot see a path a file builds
    from parts, or a load from outside `scripts/` and `tools/`. Two exist
    (found by an independent review, 2026-10-12) and neither is run by the two
    tests: check_pin_regression() in tools/preflight.py builds
    `root / "scripts" / "check_pin_regression.sh"` and runs it (the recreate
    test calls that module's read_bootstrap_facts, resolve_bootstrap_config,
    build_tool_model and fn_body, never its checks), and
    dist_producer_components() in scripts/mint_seed_support.py loads
    src/tools/trust-stage0-dist/prepare.py (only that script's own command
    line calls it). A test that starts to reach either must add the file to
    SCOPE by hand: nothing here would notice.
  * THE VERDICT IS ABOUT THE PUSHED TREE. In throwaway repositories with stub
    tests (the real two take about four minutes; the lane carries no test-only
    hook, the stubs are the fixture's): a pushed commit this checkout does not
    hold, a modified tracked file, a scope file whose edit an index flag
    hides, a file at a scope path the commit does not have, a submodule that
    is absent, off its pin or dirty, each REFUSES, red, with nothing run.
  * A RUN THAT TESTED NOTHING IS NOT A PASS: a red test, a test file that
    reports no test, a missing test file, no Python >= 3.11.

The scope DECISION itself (pushed refs, new branches, force pushes, deletions,
moves out of scope, an undiffable range) is the block this lane shares with
scoped.compiler-check and scoped.completion-gate-tests, and
scripts/tests/scoped_lane_push_scope_test.py drives all three through it.

Run: python3 -B scripts/tests/check_bootstrap_script_tests_test.py
     (as scripts/check_script_tests.sh and the push row do). It imports nothing
     from scripts/, so it needs no PYTHONPATH.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import ast
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LANE = "scripts/check_bootstrap_script_tests.sh"
GATE_ID = "scoped.bootstrap-script-tests"
SELFTEST_ID = "fast.bootstrap-script-tests-selftest"
ZERO = "0" * 40


def supported_python() -> Path:
    """The interpreter a Python >= 3.11 selection must land on: this one when it
    qualifies, else the lane's own newest-first search. The row runs this file
    under bare `python3`, which can be the system 3.9."""
    import shutil
    if sys.version_info >= (3, 11):
        return Path(sys.executable).resolve()
    for name in ("python3.14", "python3.13", "python3.12", "python3.11"):
        found = shutil.which(name)
        if not found:
            continue
        # The interpreter's own path: a launcher on PATH may be a shim, not a link.
        probe = subprocess.run(
            [found, "-c", "import os, sys; sys.exit(1) if sys.version_info < (3, 11) "
             "else print(os.path.realpath(sys.executable))"],
            capture_output=True, text=True,
        )
        if probe.returncode == 0:
            return Path(probe.stdout.strip())
    raise AssertionError("no Python >= 3.11 on PATH: the selection under test has nothing to select")


def supported_minor() -> int:
    return int(subprocess.run(
        [str(supported_python()), "-c", "import sys; print(sys.version_info.minor)"],
        capture_output=True, text=True, check=True,
    ).stdout)

# Named by a file in SCOPE and NOT run by it or by the tests: each with where
# the name stands. A file that starts being run moves to the lane's SCOPE.
NOT_LOADED = {
    "scripts/check_targo_trust_unit_tests.sh": (
        "landing_targo names the separate deferred push suite; seed consumers borrow only resource_fds, not run_targo"
    ),
    "scripts/tests/doctor_probe_custody_test.py": (
        "sdk_frontend_component.py names the separate test in its source-identity inventory; it never imports or runs it"
    ),
    "scripts/audit_first_party_pins.py": "submodule_sync.sh names the separate pin audit in comments; it does not execute it",
    "scripts/tests/submodule_sync_test.sh": "submodule_sync.sh names its separate regression suite in comments; daily unit tests use fixture synchronization owners",
    "scripts/prove_rust_free_build.sh": (
        "mint_and_prove_seed.sh names it in help; the imported Clean input "
        "test executes only the extracted run_clean function"
    ),
    "scripts/publish_seed_cut.sh": (
        "mint_and_prove_seed.sh prints it as a later operator command; the "
        "imported Clean input test executes only run_clean, never publication"
    ),
    "scripts/check_driver_extra_symbols.py": (
        "promote-toolchain.sh names it in a comment and in the refusal text of its "
        "tool-start gate; the promote test greps that text"
    ),
    "scripts/seed_staircase.py": "promote-toolchain.sh's usage text (--lineage)",
    "scripts/tests/promote_native_tools_surface_test.py": (
        "promote-toolchain.sh names it in the comment of native_linker_surface, which that test "
        "runs alone; the landing gate selects it for the script, and this lane does not run it"
    ),
    "scripts/tests/trust_serial_command_test.py": (
        "promote_toolchain_test.sh names it in a comment as the test of the real serial "
        "executor; its own executor is a shell fixture, and nothing here builds or runs the real one"
    ),
    "scripts/check_toolchain_coherence.py": (
        "comments in tools/verify-toolchain.sh and scripts/lib/trust_toolchain_surface.sh"
    ),
}

# The three subjects and four tests everything in SCOPE must be reachable from.
ROOTS = (
    "scripts/recreate_bootstrap.py",
    "scripts/promote-toolchain.sh",
    "scripts/tests/recreate_bootstrap_test.py",
    "scripts/tests/promote_toolchain_test.sh",
    "scripts/daily_toolchain_stage.py",
    "scripts/tests/daily_toolchain_stage_test.py",
    "scripts/tests/seed_lock_inventory_test.py",
)


def lane_array(name: str) -> list:
    """A `NAME=( ... )` list of the lane script, read from the script itself."""
    text = (ROOT / LANE).read_text(encoding="utf-8")
    match = re.search(rf"^{name}=\(\n(.*?)^\)", text, re.MULTILINE | re.DOTALL)
    if not match:
        raise AssertionError(f"no {name}=( ... ) block in {LANE}")
    return match.group(1).split()


CODE_NAME = r"(?:[A-Za-z0-9_-]+\.(?:py|sh)|build-slot)"
CODE_PATH = r"(?:x\.py|(?:src/tools|scripts|tools)/(?:[A-Za-z0-9_./-]+\.(?:py|sh)|build-slot))"
# A `scripts/...` or `tools/...` word anywhere in a shell script, comments and
# messages included: over-inclusive on purpose, NOT_LOADED says which are words.
SHELL_WORD = re.compile(rf"(?<![\w.-])({CODE_PATH})(?![\w-])")


def named_code_files(relative: str) -> dict:
    """The scripts/, tools/ and root x.py code files named, with their lines.

    Python: a string constant that is exactly a repo-relative path of such a
    file, or exactly a file name that exists beside the source (for a test in
    scripts/tests/, also beside the scripts it tests: `SCRIPT.with_name(...)`),
    and an import of a sibling module. Shell: SHELL_WORD.
    """
    source = ROOT / relative
    text = source.read_text(encoding="utf-8")
    found: dict = {}

    def note(path: Path, line: int) -> None:
        found.setdefault(path.resolve().relative_to(ROOT).as_posix(), []).append(line)

    if relative.endswith(".sh"):
        for number, line in enumerate(text.splitlines(), 1):
            for word in SHELL_WORD.findall(line):
                if (ROOT / word).is_file():
                    note(ROOT / word, number)
        return found
    beside = [source.parent]
    if source.parent == ROOT / "scripts" / "tests":
        beside.append(ROOT / "scripts")
    for node in ast.walk(ast.parse(text)):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            if re.fullmatch(CODE_PATH, node.value) and (ROOT / node.value).is_file():
                note(ROOT / node.value, node.lineno)
            elif re.fullmatch(CODE_NAME, node.value):
                for directory in beside:
                    if (directory / node.value).is_file():
                        note(directory / node.value, node.lineno)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            modules = (
                [alias.name for alias in node.names]
                if isinstance(node, ast.Import)
                else [node.module or ""]
            )
            for module in modules:
                sibling = source.parent / f"{module.split('.')[0]}.py"
                if module and sibling.is_file():
                    note(sibling, node.lineno)
    return found


class ScopeIsDerivedFromTheSources(unittest.TestCase):
    """Read off this checkout: the lane's lists against what the sources name."""

    @classmethod
    def setUpClass(cls):
        cls.scope = lane_array("SCOPE")
        cls.tests = lane_array("TESTS")
        # Everything reachable from the explicit roots through files in SCOPE, and
        # who names what.
        cls.named_by: dict = {}
        pending = list(ROOTS)
        cls.reached = set()
        while pending:
            current = pending.pop()
            if current in cls.reached:
                continue
            cls.reached.add(current)
            for name, lines in named_code_files(current).items():
                cls.named_by.setdefault(name, []).append(f"{current}:{lines[0]}")
                if name in cls.scope and name not in cls.reached:
                    pending.append(name)

    def test_the_lists_are_well_formed(self):
        self.assertEqual(len(self.scope), len(set(self.scope)), "a path is listed twice")
        self.assertEqual(self.tests, [ROOTS[2], ROOTS[3], ROOTS[5], ROOTS[6]])
        for path in (*ROOTS, LANE):
            self.assertIn(path, self.scope)
        for path in self.scope:
            self.assertTrue((ROOT / path).is_file(), f"{path} is in SCOPE and not in the tree")
        self.assertEqual(sorted(set(NOT_LOADED) & set(self.scope)), [])

    def test_every_code_file_the_scope_names_is_in_scope_or_explained(self):
        unexplained = {
            name: sites
            for name, sites in sorted(self.named_by.items())
            if name not in self.scope and name not in NOT_LOADED
        }
        self.assertEqual(
            unexplained,
            {},
            "a file in the lane's SCOPE names code the lane does not watch: add it to SCOPE in "
            f"{LANE} with its load site, or to NOT_LOADED here with the reason it is not run",
        )
        # Not vacuous: the derivation finds the loads this lane was built on.
        for loaded, loader in (
            ("scripts/seed_input_archives.py", "scripts/tests/seed_lock_inventory_test.py"),
            ("scripts/seed_input_records.py", "scripts/seed_input_archives.py"),
            ("scripts/tests/build_slot_test.py", "scripts/tests/recreate_bootstrap_test.py"),
            ("x.py", "scripts/tests/recreate_bootstrap_test.py"),
            ("scripts/build-slot", "scripts/tests/build_slot_test.py"),
            ("scripts/check_seed_freshness.py", "scripts/recreate_bootstrap.py"),
            ("scripts/seed_host_ledger.py", "scripts/recreate_bootstrap.py"),
            ("scripts/mint_seed_support.py", "scripts/check_seed_freshness.py"),
            ("scripts/mint_seed_support.py", "scripts/tests/recreate_bootstrap_test.py"),
            ("tools/preflight.py", "scripts/tests/recreate_bootstrap_test.py"),
            ("tools/verify-toolchain.sh", "scripts/promote-toolchain.sh"),
            ("scripts/lib/trust_build_provenance.py", "scripts/promote-toolchain.sh"),
            ("scripts/prune_seal_symlinks.py", "scripts/tests/promote_toolchain_test.sh"),
            ("scripts/freeze_toolchain_sources.py", "scripts/promote-toolchain.sh"),
            ("scripts/tests/freeze_toolchain_sources_test.py", "scripts/tests/promote_toolchain_test.sh"),
            ("src/tools/trust-stage0-dist/prepare.py", "scripts/freeze_toolchain_sources.py"),
        ):
            self.assertTrue(
                any(site.startswith(loader + ":") for site in self.named_by.get(loaded, ())),
                f"{loader} no longer names {loaded}: {self.named_by.get(loaded)}",
            )

    def test_every_scope_entry_is_named_by_something_reachable(self):
        unloaded = sorted(
            path
            for path in self.scope
            if path not in ROOTS and path != LANE and path not in self.named_by
        )
        self.assertEqual(
            unloaded, [], f"in SCOPE of {LANE}, and nothing reachable from the scripts and tests names it"
        )

    def test_a_not_loaded_entry_is_still_named(self):
        for path, reason in NOT_LOADED.items():
            with self.subTest(path=path):
                self.assertTrue((ROOT / path).is_file(), path)
                self.assertIn(path, self.named_by, f"no longer named ({reason}): drop the entry")

    def test_diagnostic_registration_stays_out_of_development_push(self):
        listing = subprocess.run(
            ["bash", str(ROOT / "tests" / "run_trust_comprehensive_harness.sh"), "--list", "fast"],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(listing.returncode, 0, listing.stderr)
        rows = [line.split("\t") for line in listing.stdout.splitlines()]
        commands = {row[0]: row[-1] for row in rows}
        self.assertEqual(commands.get(GATE_ID), f"bash {LANE}")
        self.assertEqual(
            commands.get(SELFTEST_ID),
            "python3 -B scripts/tests/check_bootstrap_script_tests_test.py",
        )
        # Preserve the actual diagnostic registration/order. The push profile
        # does not run gate self-tests yet: a defect, not policy (docs/STATUS.md,
        # docs/PLAN.md PKG-V1).
        order = [row[0] for row in rows]
        self.assertGreater(order.index(GATE_ID), order.index("scoped.crates-tests"))
        push = subprocess.run(
            ["bash", str(ROOT / "tests" / "run_trust_comprehensive_harness.sh"), "--list", "push"],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(push.returncode, 0, push.stderr)
        push_ids = [line.split("\t")[0] for line in push.stdout.splitlines()]
        self.assertNotIn(GATE_ID, push_ids)
        self.assertNotIn(SELFTEST_ID, push_ids)
        readers = subprocess.run(
            [sys.executable, "-B", str(ROOT / "scripts" / "check_gate_lane_coverage.py"),
             "--push-refs-readers"],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(readers.returncode, 0, readers.stderr)
        self.assertNotIn(GATE_ID, readers.stdout.split())
        self.assertNotIn(SELFTEST_ID, readers.stdout.split())


PASSING_PYTHON_TEST = '''\
import os
import unittest


class Stub(unittest.TestCase):
    def test_the_hook_variables_do_not_reach_a_test(self):
        self.assertNotIn("TRUST_PUSHED_REFS", os.environ)
        self.assertNotIn("TRUST_PUSH_REMOTE", os.environ)

    def test_stub(self):
        print("STUB recreate test ran")


if __name__ == "__main__":
    unittest.main()
'''
PASSING_SHELL_TEST = '''\
#!/usr/bin/env bash
[ -z "${TRUST_PUSHED_REFS:-}" ] || { echo "the hook's variable reached the test" >&2; exit 1; }
echo "STUB promote test ran"
echo "Promotion toolchain tests: 3 cases passed (stub)"
'''
RECREATOR = "scripts/recreate_bootstrap.py"
PYTHON_TEST = "scripts/tests/recreate_bootstrap_test.py"
SHELL_TEST = "scripts/tests/promote_toolchain_test.sh"
DAILY_TEST = "scripts/tests/daily_toolchain_stage_test.py"
LOCK_TEST = "scripts/tests/seed_lock_inventory_test.py"
DOCS = "docs/notes.md"
PASS_LINE = "bootstrap-script tests: PASS"
NOT_RUN_LINE = "bootstrap-script tests NOT RUN — this is a red, not a pass."


class LaneBehaviour(unittest.TestCase):
    """The real lane script in throwaway repositories whose tests are stubs."""

    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name).resolve() / "repo"
        # No operator config and no push context from whoever runs this test.
        self.env = {
            key: value for key, value in os.environ.items()
            if not key.startswith(("GIT_", "TRUST_PUSH"))
        }
        self.env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        self.run_git(["init", "--quiet", "--initial-branch=main", str(self.repo)])
        self.git("config", "user.name", "lane-test")
        self.git("config", "user.email", "lane-test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.base = self.commit(
            {
                "README.md": "fixture\n",
                DOCS: "notes\n",
                RECREATOR: "# stands for the recreator\n",
                "scripts/promote-toolchain.sh": "# stands for the sealing script\n",
                PYTHON_TEST: PASSING_PYTHON_TEST,
                SHELL_TEST: PASSING_SHELL_TEST,
                DAILY_TEST: PASSING_PYTHON_TEST,
                LOCK_TEST: PASSING_PYTHON_TEST.replace("STUB recreate test ran", "STUB lock inventory test ran"),
            },
            "base",
        )
        self.git("update-ref", "refs/remotes/origin/main", self.base)

    # -- fixture helpers ----------------------------------------------------

    def run_git(self, argv, cwd=None):
        return subprocess.run(
            ["git", *argv], env=self.env, cwd=cwd, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=True, timeout=30,
        ).stdout.strip()

    def git(self, *args):
        return self.run_git(["-C", str(self.repo), *args])

    def commit(self, files, message):
        """Write (or, for None, delete) files and commit on HEAD; return the commit."""
        for path, content in files.items():
            if content is None:
                self.git("rm", "--quiet", "--", path)
                continue
            target = self.repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")
            self.git("add", "--", path)
        self.git("commit", "--quiet", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def in_scope_commit(self, files=None, message="change the recreator"):
        return self.commit(files or {RECREATOR: "# the recreator, changed\n"}, message)

    def run_lane(self, *args, pushed=None, path=None):
        env = dict(self.env)
        if pushed is not None:
            env["TRUST_PUSHED_REFS"] = pushed
            env["TRUST_PUSH_REMOTE"] = "origin"
        if path is not None:
            env["PATH"] = path
        return subprocess.run(
            ["bash", str(ROOT / LANE), *args], cwd=self.repo, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
            timeout=300,
        )

    @staticmethod
    def update(local, remote, ref="refs/heads/main"):
        return f"{ref} {local} {ref} {remote}\n"

    def assert_green(self, result):
        out = result.stdout
        self.assertEqual(result.returncode, 0, out)
        self.assertIn(PASS_LINE, out)
        self.assertEqual(self.ran(out), [PYTHON_TEST, SHELL_TEST, DAILY_TEST, LOCK_TEST])
        self.assertIsNone(re.search(r"^\s*SKIPPED: ", out, re.MULTILINE), out)

    @staticmethod
    def ran(out):
        return re.findall(r"^=== (\S+) ===$", out, re.MULTILINE)

    def assert_refused(self, result, *fragments):
        out = result.stdout
        self.assertEqual(result.returncode, 1, out)
        self.assertIn(NOT_RUN_LINE, out)
        self.assertEqual(self.ran(out), [], f"a refusal must run nothing:\n{out}")
        self.assertNotIn(PASS_LINE, out)
        self.assertIsNone(re.search(r"^\s*SKIPPED: ", out, re.MULTILINE), out)
        for fragment in fragments:
            self.assertIn(fragment, out)

    # -- in scope, out of scope ---------------------------------------------

    def test_an_in_scope_push_of_the_checked_out_commit_runs_all_tests(self):
        tip = self.in_scope_commit()
        result = self.run_lane(pushed=self.update(tip, self.base))
        self.assert_green(result)
        out = result.stdout
        self.assertIn("SUBJECT: the pushed refs (TRUST_PUSHED_REFS, 1 update(s))", out)
        self.assertIn(f"in scope: 1 relevant file(s) changed vs the pushed refs:\n  {RECREATOR}\n", out)
        self.assertIn(f"tree under test: this checkout, which holds the tree of {tip}", out)
        self.assertIn(f"--- {PYTHON_TEST}: PASS (2 tests, 0 skipped, ", out)
        self.assertIn(f"--- {SHELL_TEST}: PASS (3 cases, ", out)
        # What the scope does not see is said on a run and on a skip.
        self.assertIn("NOT SEEN:", out)
        # The same commit under the standing reading, and with an explicit base.
        self.assert_green(self.run_lane())
        self.assert_green(self.run_lane(self.base))

    def test_each_lock_inventory_scope_path_runs_the_registered_regression(self):
        for path in (LOCK_TEST, "scripts/seed_input_archives.py", "scripts/seed_input_records.py"):
            with self.subTest(path=path):
                before = self.git("rev-parse", "HEAD")
                current = self.repo / path
                text = current.read_text() if current.is_file() else ""
                tip = self.commit({path: text + "# lock inventory scope control\n"}, "lock inventory change")
                result = self.run_lane(pushed=self.update(tip, before))
                self.assert_green(result)
                self.assertIn(f"--- {LOCK_TEST}: PASS (2 tests, 0 skipped, ", result.stdout)

    def test_every_scope_path_brings_the_lane_into_scope(self):
        for index, path in enumerate(lane_array("SCOPE")):
            with self.subTest(path=path):
                before = self.git("rev-parse", "HEAD")
                # The two stub tests are replaced by themselves plus a comment.
                current = self.repo / path
                content = (current.read_text(encoding="utf-8") if current.is_file() else "") + f"# touched {index}\n"
                tip = self.commit({path: content}, f"touch {path}")
                result = self.run_lane(pushed=self.update(tip, before))
                self.assert_green(result)
                self.assertIn(f"\n  {path}\n", result.stdout)

    def test_a_push_outside_the_scope_is_skipped_and_runs_nothing(self):
        look_alikes = {
            DOCS: "docs only\n",
            "scripts/recreate_bootstrap.py.orig": "not the recreator\n",
            "scripts/tests/recreate_bootstrap_test.py.md": "not the test\n",
            "other/scripts/recreate_bootstrap.py": "another directory\n",
            "INSTALL.md": "a document the recreate test reads: data, said NOT SEEN\n",
            "Cargo.toml": "[workspace]\n",
        }
        for path, content in look_alikes.items():
            with self.subTest(path=path):
                before = self.git("rev-parse", "HEAD")
                tip = self.commit({path: content}, f"touch {path}")
                result = self.run_lane(pushed=self.update(tip, before))
                out = result.stdout
                self.assertEqual(result.returncode, 0, out)
                self.assertRegex(out, re.compile(r"^SKIPPED: ", re.MULTILINE))
                self.assertEqual(self.ran(out), [])
                self.assertNotIn(PASS_LINE, out)
                self.assertIn("the tree files the registered tests read as data are outside", out)
        # Nothing pushed at all.
        result = self.run_lane(pushed=self.update(self.git("rev-parse", "HEAD"), self.git("rev-parse", "HEAD")))
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("SKIPPED: no changes against the pushed refs", result.stdout)

    # -- the verdict is about the pushed tree -------------------------------

    def test_a_pushed_commit_this_checkout_does_not_hold_is_refused(self):
        topic = self.in_scope_commit()
        # The checkout moves to a docs-only commit; `git push origin topic`.
        self.git("checkout", "--quiet", "-B", "docs", self.base)
        docs = self.commit({DOCS: "docs only\n"}, "docs")
        pushed = self.update(topic, self.base, "refs/heads/topic")
        self.assert_refused(
            self.run_lane(pushed=pushed),
            f"FAIL: the pushed commit {topic} is in scope, and this checkout holds another tree",
            f"(HEAD is {docs})",
        )
        # Beside an update the checkout does hold: one unjudged tree is enough.
        both = self.update(docs, self.base, "refs/heads/docs") + pushed
        self.assert_refused(self.run_lane(pushed=both), topic)
        # A commit this clone does not have at all.
        missing = "1" * 40
        self.assert_refused(
            self.run_lane(pushed=self.update(missing, self.base, "refs/heads/topic")),
            f"cannot compute the diff {self.base}..{missing}",
            f"FAIL: the pushed commit {missing} is in scope, and this clone cannot read its tree.",
        )
        # The same tree under another commit id is the same files: judged.
        self.git("checkout", "--quiet", "--detach", topic)
        twin = self.commit({}, "same tree, another commit")
        self.assertNotEqual(twin, topic)
        self.assert_green(self.run_lane(pushed=pushed))

    def test_a_modified_tracked_file_is_refused(self):
        tip = self.in_scope_commit()
        pushed = self.update(tip, self.base)
        cases = {
            "an unstaged edit outside the scope": lambda: (self.repo / DOCS).write_text("edited\n"),
            "a staged edit": lambda: (
                (self.repo / "README.md").write_text("staged\n"),
                self.git("add", "README.md"),
            ),
            "a deleted file": lambda: (self.repo / DOCS).unlink(),
        }
        for label, dirty in cases.items():
            with self.subTest(label):
                dirty()
                self.assert_refused(
                    self.run_lane(pushed=pushed),
                    "FAIL: this checkout has uncommitted changes to tracked files",
                )
                self.git("reset", "--quiet", "--hard", tip)
                self.assert_green(self.run_lane(pushed=pushed))

    def test_a_scope_file_that_is_not_the_commits_blob_is_refused(self):
        tip = self.in_scope_commit()
        pushed = self.update(tip, self.base)
        # An edit `git status` does not report: the index is told not to look.
        self.git("update-index", "--assume-unchanged", RECREATOR)
        (self.repo / RECREATOR).write_text("# edited after the commit\n", encoding="utf-8")
        self.assertEqual(self.git("status", "--porcelain", "--untracked-files=no"), "")
        self.assert_refused(
            self.run_lane(pushed=pushed),
            "FAIL: files this lane's tests run are not, byte for byte, what HEAD holds:",
            f"{RECREATOR} (differs from the blob HEAD holds)",
        )
        self.git("update-index", "--no-assume-unchanged", RECREATOR)
        self.git("checkout", "--quiet", "--", RECREATOR)
        self.assert_green(self.run_lane(pushed=pushed))
        # A scope path the commit does not have, present here (untracked).
        extra = "scripts/seed_host_ledger.py"
        (self.repo / extra).write_text("# never committed\n", encoding="utf-8")
        self.assert_refused(
            self.run_lane(pushed=pushed), f"{extra} (HEAD holds no such file; one exists here)"
        )
        (self.repo / extra).unlink()
        # A symbolic link standing where the commit holds a file, to a file
        # with the very bytes the commit holds: only the link gives it away.
        (self.repo / "elsewhere.py").write_text("# the recreator, changed\n", encoding="utf-8")
        (self.repo / RECREATOR).unlink()
        (self.repo / RECREATOR).symlink_to(self.repo / "elsewhere.py")
        self.git("update-index", "--assume-unchanged", RECREATOR)
        self.assert_refused(self.run_lane(pushed=pushed), f"{RECREATOR} (differs from the blob HEAD holds)")

    def test_a_submodule_the_commit_pins_must_be_checked_out_at_its_pin_and_clean(self):
        module = self.repo / "first-party" / "ty"
        module.mkdir(parents=True)
        self.run_git(["init", "--quiet", "--initial-branch=main", str(module)])
        for key, value in (("user.name", "lane-test"), ("user.email", "lane-test@example.invalid"),
                           ("commit.gpgsign", "false")):
            self.run_git(["-C", str(module), "config", key, value])
        (module / "Cargo.toml").write_text("[workspace]\n", encoding="utf-8")
        self.run_git(["-C", str(module), "add", "Cargo.toml"])
        self.run_git(["-C", str(module), "commit", "--quiet", "-m", "pinned"])
        pin = self.run_git(["-C", str(module), "rev-parse", "HEAD"])
        self.run_git(["-C", str(module), "commit", "--quiet", "--allow-empty", "-m", "later"])
        later = self.run_git(["-C", str(module), "rev-parse", "HEAD"])
        self.git("update-index", "--add", "--cacheinfo", f"160000,{pin},first-party/ty")
        tip = self.in_scope_commit(message="pin first-party/ty and change the recreator")
        pushed = self.update(tip, self.base)
        advice = "bash scripts/submodule_sync.sh --fetch --restore"
        # Checked out, one commit past the pin.
        self.assert_refused(
            self.run_lane(pushed=pushed),
            "FAIL: this checkout does not hold the submodule sources the pushed tree pins:",
            f"first-party/ty: at {later[:12]}, pinned {pin[:12]}",
            advice,
        )
        # At the pin: judged.
        self.run_git(["-C", str(module), "checkout", "--quiet", "--detach", pin])
        result = self.run_lane(pushed=pushed)
        self.assert_green(result)
        self.assertIn("1 submodule(s) at their pins", result.stdout)
        # At the pin, with a tracked file edited.
        (module / "Cargo.toml").write_text("[workspace]\nmembers = []\n", encoding="utf-8")
        self.assert_refused(
            self.run_lane(pushed=pushed), "first-party/ty: at its pin, but not clean", advice
        )
        # Not checked out: what a fresh worktree holds, an empty directory.
        (module / "Cargo.toml").unlink()
        git_dir = module / ".git"
        git_dir.rename(self.repo.parent / "ty.git")
        self.assert_refused(
            self.run_lane(pushed=pushed), f"first-party/ty: not checked out (pin {pin[:12]})", advice
        )
        # None of that is asked of a push that is out of scope.
        docs = self.commit({DOCS: "docs only\n"}, "docs")
        result = self.run_lane(pushed=self.update(docs, tip))
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertRegex(result.stdout, re.compile(r"^SKIPPED: ", re.MULTILINE))

    # -- a run that tested nothing is not a pass ----------------------------

    def red(self, files, *fragments, ran=(PYTHON_TEST, SHELL_TEST, DAILY_TEST, LOCK_TEST)):
        before = self.git("rev-parse", "HEAD")
        tip = self.commit(files, "break a test")
        result = self.run_lane(pushed=self.update(tip, before))
        out = result.stdout
        self.assertEqual(result.returncode, 1, out)
        self.assertNotIn(PASS_LINE, out)
        self.assertIsNone(re.search(r"^\s*SKIPPED: ", out, re.MULTILINE), out)
        self.assertEqual(self.ran(out), list(ran), out)
        for fragment in fragments:
            self.assertIn(fragment, out)
        return out

    def test_a_red_test_is_a_red_lane_and_the_other_test_still_runs(self):
        failing = PASSING_PYTHON_TEST.replace(
            'print("STUB recreate test ran")', 'self.fail("the recreator is broken")'
        )
        out = self.red(
            {PYTHON_TEST: failing},
            f"--- {PYTHON_TEST}: FAIL (exit 1, ",
            "AssertionError: the recreator is broken",
            f"--- {SHELL_TEST}: PASS (3 cases, ",
            f"FAIL: bootstrap-script tests red: {PYTHON_TEST}(exit=1)",
        )
        self.assertNotIn("STUB promote test ran", out)  # a passing test's log is not shown
        self.red(
            {PYTHON_TEST: PASSING_PYTHON_TEST, SHELL_TEST: PASSING_SHELL_TEST + "echo broken >&2\nexit 7\n"},
            f"--- {PYTHON_TEST}: PASS (2 tests, 0 skipped, ",
            "broken\n",
            f"--- {SHELL_TEST}: FAIL (exit 7, ",
            f"FAIL: bootstrap-script tests red: {SHELL_TEST}(exit=7)",
        )

    def test_the_lock_inventory_regression_cannot_fail_silently(self):
        failing = PASSING_PYTHON_TEST.replace(
            'print("STUB recreate test ran")', 'self.fail("lock inventory regression")'
        )
        self.red({LOCK_TEST: failing}, f"--- {LOCK_TEST}: FAIL (exit 1, ",
                 "AssertionError: lock inventory regression", f"{LOCK_TEST}(exit=1)")

    def test_a_test_file_that_reports_no_test_is_red(self):
        # Exit 0 and no closing count: the promote test stopped before its end.
        self.red(
            {SHELL_TEST: "#!/usr/bin/env bash\nexit 0\n"},
            f"--- {SHELL_TEST}: FAIL (exit 0 without reporting a single test",
            f"{SHELL_TEST}(ran-nothing)",
        )
        # No test in the Python file (unittest exits 5 for that since 3.12, 0 before).
        out = self.red(
            {SHELL_TEST: PASSING_SHELL_TEST,
             PYTHON_TEST: "import unittest\n\nif __name__ == '__main__':\n    unittest.main()\n"},
            f"--- {PYTHON_TEST}: FAIL (",
        )
        self.assertRegex(out, rf"{re.escape(PYTHON_TEST)}\((exit=5|ran-nothing)\)")
        # Skips are counted, not hidden.
        skipping = PASSING_PYTHON_TEST.replace(
            "    def test_stub(self):", '    @unittest.skip("not here")\n    def test_stub(self):'
        )
        before = self.git("rev-parse", "HEAD")
        tip = self.commit({PYTHON_TEST: skipping}, "skip one")
        result = self.run_lane(pushed=self.update(tip, before))
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn(f"--- {PYTHON_TEST}: PASS (2 tests, 1 skipped, ", result.stdout)

    def test_a_missing_test_file_is_refused(self):
        before = self.git("rev-parse", "HEAD")
        tip = self.commit({SHELL_TEST: None}, "delete the promote test")
        self.assert_refused(
            self.run_lane(pushed=self.update(tip, before)),
            f"in scope: 1 relevant file(s) changed vs the pushed refs:\n  {SHELL_TEST}\n",
            f"FAIL: {SHELL_TEST} is missing",
        )

    def test_no_python_3_11_is_refused(self):
        # Every name the lane tries resolves to an interpreter too old for it.
        old = Path(self.temp.name) / "old-python"
        old.mkdir()
        for name in ("python3.14", "python3.13", "python3.12", "python3.11", "python3", "python"):
            stub = old / name
            stub.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
            stub.chmod(0o755)
        tip = self.in_scope_commit()
        result = self.run_lane(
            pushed=self.update(tip, self.base), path=f"{old}{os.pathsep}{self.env['PATH']}"
        )
        self.assert_refused(result, "FAIL: no Python >= 3.11 on PATH")

    def test_selected_python_reaches_nested_shell_children(self):
        # A supported versioned interpreter must survive the shell boundary;
        # bare python3 can still be the system's incompatible interpreter.
        tools = Path(self.temp.name) / "python-selection"
        tools.mkdir()
        attempted = tools / "bare-python-ran"
        old = tools / "python3"
        old.write_text(f"#!/bin/sh\ntouch '{attempted}'\nexit 77\n", encoding="utf-8")
        old.chmod(0o755)
        (tools / "python3.14").symlink_to(supported_python())
        shell = '''#!/usr/bin/env bash
set -eu
"${PYTHON_BIN:?selected Python was not propagated}" -B - <<'PY'
import json, sys, tomllib
from pathlib import Path
assert sys.version_info >= (3, 11)
assert tomllib.loads("selected = true")["selected"] is True
Path("nested-python.json").write_text(json.dumps({"executable": str(Path(sys.executable).resolve())}))
PY
echo 'Promotion toolchain tests: 1 cases passed (interpreter boundary fixture)'
'''
        tip = self.in_scope_commit({SHELL_TEST: shell})
        result = self.run_lane(
            pushed=self.update(tip, self.base), path=f"{tools}{os.pathsep}{self.env['PATH']}"
        )
        self.assert_green(result)
        observed = json.loads((self.repo / "nested-python.json").read_text())
        self.assertEqual(observed["executable"], str(supported_python()))
        self.assertFalse(attempted.exists(), "the incompatible default python3 was invoked")

    def test_promote_test_refuses_incompatible_explicit_python(self):
        old = Path(self.temp.name) / "explicit-old-python"
        old.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
        old.chmod(0o755)
        result = subprocess.run(
            ["bash", str(ROOT / SHELL_TEST)], cwd=self.repo,
            env={**self.env, "PYTHON_BIN": str(old)}, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL, timeout=30,
        )
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("selected test Python requires Python >= 3.11", result.stdout)
        self.assertNotIn("Traceback", result.stdout)


class PromotionPythonBoundary(unittest.TestCase):
    def check_lock_interpreter(self, *, standalone: bool):
        # Run the real selector, resolution, and promotion function, with only
        # the downstream sealer replaced by an owned lock/identity observer.
        source = (ROOT / SHELL_TEST).read_text(encoding="utf-8")
        selection = re.search(
            r'^if \[\[ -n "\$\{PYTHON_BIN:-\}" \]\]; then\n.*?^fi\n',
            source, re.MULTILINE | re.DOTALL,
        )
        resolution = re.search(
            r'^SOURCE_PYTHON=.*?^ln -s .*?\n',
            source, re.MULTILINE | re.DOTALL,
        )
        promotion = re.search(
            r'^run_promotion\(\) \{\n.*?^\}\n',
            source, re.MULTILINE | re.DOTALL,
        )
        self.assertIsNotNone(selection)
        self.assertIsNotNone(resolution)
        self.assertIsNotNone(promotion)
        for hostile in (False, True):
            with self.subTest(standalone=standalone, hostile_inner_path=hostile):
                with tempfile.TemporaryDirectory(prefix="promotion-python-lock-") as temp:
                    work = Path(temp)
                    for name in ("selector-bin", "fake-bin", "case/home", "fixture/scripts"):
                        (work / name).mkdir(parents=True)
                    # The fallback name deliberately differs from the actual
                    # minor that the fixture exposes inside its isolated PATH.
                    selected = "python3.13" if supported_minor() != 13 else "python3.12"
                    if standalone:
                        for candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
                            if candidate == selected:
                                break
                            stub = work / "selector-bin" / candidate
                            stub.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
                            stub.chmod(0o755)
                    else:
                        selected = "selected-python"
                    (work / "selector-bin" / selected).symlink_to(supported_python())
                    if hostile:
                        trap = work / "fake-bin" / selected
                        trap.write_text(
                            '#!/bin/sh\nprintf wrong > "$HOME/wrong-python"\nexit 77\n',
                            encoding="utf-8",
                        )
                        trap.chmod(0o755)
                    lock = work / "owned-lock"
                    observer = work / "fixture/scripts/promote-toolchain.sh"
                    observer.write_text(
                        "#!/bin/sh\nexec " + shlex.quote(sys.executable) + " - "
                        + shlex.quote(str(lock)) + " <<'PY'\n"
                        "import fcntl, json, os, sys\n"
                        "from pathlib import Path\n"
                        "with open(sys.argv[1], 'a') as lock:\n"
                        "    try:\n"
                        "        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)\n"
                        "    except BlockingIOError:\n"
                        "        pass\n"
                        "    else:\n"
                        "        raise AssertionError('promotion lock was not held')\n"
                        "Path(os.environ['HOME'], 'observed.json').write_text(json.dumps(\n"
                        "    {'executable': os.path.realpath(sys.executable), 'lock_held': True}))\n"
                        "PY\n", encoding="utf-8",
                    )
                    values = {
                        "WORK": str(work), "CASE": str(work / "case"),
                        "FIXTURE_REPO": str(work / "fixture"), "SRC": str(work / "input"),
                        "COMMIT": ZERO, "SEAL": str(work / "seal"),
                        "FIXTURE_PROBE_TIMEOUT": "1", "TEST_LOCK_PATH": str(lock),
                    }
                    script = "set -eu\n" + "\n".join(
                        key + "=" + shlex.quote(value) for key, value in values.items()
                    ) + "\n" + selection[0] + resolution[0] + promotion[0]
                    script += 'printf "%s\\n" "$PYTHON_BIN" > "$WORK/selected"\nrun_promotion\n'
                    env = {
                        "PATH": f"{work / 'selector-bin'}:/usr/bin:/bin:/usr/sbin:/sbin",
                        "HOME": str(work / "case/home"), "LC_ALL": "C", "TZ": "UTC",
                    }
                    if not standalone:
                        env["PYTHON_BIN"] = selected
                    result = subprocess.run(
                        ["/bin/bash", "-c", script], cwd=work, env=env,
                        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT, text=True, timeout=30,
                    )
                    output = work / "case/output"
                    details = result.stdout + (output.read_text() if output.exists() else "")
                    self.assertEqual(result.returncode, 0, details)
                    self.assertEqual((work / "selected").read_text().strip(), selected)
                    self.assertFalse((work / "case/home/wrong-python").exists())
                    observed = json.loads((work / "case/home/observed.json").read_text())
                    self.assertEqual(observed, {
                        "executable": str(Path(sys.executable).resolve()), "lock_held": True,
                    })

    def test_explicit_command_name_survives_isolated_lock_path(self):
        self.check_lock_interpreter(standalone=False)

    def test_standalone_fallback_survives_isolated_lock_path(self):
        self.check_lock_interpreter(standalone=True)


if __name__ == "__main__":
    unittest.main()
