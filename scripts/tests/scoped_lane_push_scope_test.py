#!/usr/bin/env python3
"""Regression test: the shell-scoped push lanes judge WHAT IS PUSHED.

`scoped.compiler-check` (scripts/check_compiler_targets_build.sh) and
`scoped.completion-gate-tests` (scripts/check_completion_gate_tests.sh) decide
whether to run from the set of changed paths, and since 2026-10-12 so does
`scoped.bootstrap-script-tests` (scripts/check_bootstrap_script_tests.sh),
which carries the same block and is driven through the same cases below (its
own behaviour past the scope decision is
scripts/tests/check_bootstrap_script_tests_test.py's), and since 2026-10-14
`scoped.targo-trust-unit-tests` (scripts/check_targo_trust_unit_tests.sh),
whose heavy command is the fixture's stub `targo` (its `metadata` fails, so a
first-party pin move reaches the stub through the lane's "cannot read the
dependency graph — running" path). Until 2026-09-27:

  * both read `origin/main...HEAD` whatever was pushed, so `git push origin
    topic` from a checkout whose HEAD touched only docs skipped both lanes
    however much compiler or gate code `topic` carried. scripts/hooks/pre-push
    exports the pushed refs as TRUST_PUSHED_REFS; neither lane read it;
  * the compiler lane swallowed a FAILING diff (`2>/dev/null` into an empty
    string) and printed "SKIPPED: no changes" — fail-open;
  * the compiler lane diffed with rename detection on, so a file moved OUT of
    compiler/ was listed only under its new path and the lane skipped, and
    without -z, so a non-ASCII path came back C-quoted (`"compiler/\\303\\251.rs"`)
    and never matched the anchored scope pattern. The completion lane had those
    two fixed in 3db0e0b0fd;
  * both diffed without --ignore-submodules=none, so diff.ignoreSubmodules or
    a .gitmodules `ignore = all` (read from the worktree, and pushable) hid a
    moved first-party pin, which both lanes list as in scope, and they skipped.

And from f7a15dc698 (which added the TRUST_PUSHED_REFS reading) until the fix
the same day, a pushed update was diffed `<remote-sha>...<local-sha>`: changes
since the merge base. A force push that DROPS the remote's in-scope commits and
adds only a docs commit was judged on the docs commit and skipped, although the
tree it installs differs from the remote's in scope. An update is now the tree
diff `<remote-sha>..<local-sha>`; a new branch keeps `origin/main...<local-sha>`
(the lanes' WHAT THIS PUSH CHANGES comment says why).

Each case below builds a throwaway repository and runs the REAL lane script in
it. Nothing heavy runs: the fixture's `x.py` is a stub that prints a marker,
and its `scripts/tests/` holds one trivial module per name in the completion
lane's MODULES list, so "the lane ran" is observable in well under a second
without an x.py build or the 385-test suite. The lane scripts carry no
test-only hook; the stubs are the fixture's, not the lanes'.

Every case runs against EVERY lane: they compute their subject with the same
block, and this is what keeps the copies from drifting apart. The third lane's
scope is a list of files with no directory and no gitlink in it, so the three
cases that need one of those (a file added under an in-scope directory, a
non-ASCII path, a moved submodule pin) do not apply to it and say so.

Run: python3 -B -m unittest scripts.tests.scoped_lane_push_scope_test
     (or `python3 -B scripts/tests/scoped_lane_push_scope_test.py`, as
     scripts/check_script_tests.sh does).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
COMPILER_LANE = SCRIPTS / "check_compiler_targets_build.sh"
COMPLETION_LANE = SCRIPTS / "check_completion_gate_tests.sh"
BOOTSTRAP_LANE = SCRIPTS / "check_bootstrap_script_tests.sh"
TARGO_TRUST_LANE = SCRIPTS / "check_targo_trust_unit_tests.sh"
ZERO = "0" * 40
OUT_OF_SCOPE = "docs/notes.md"

# Per lane: the script, an in-scope file, a directory whose files are in scope
# (for the non-ASCII case), and the output that proves the lane got PAST its
# scope decision into the heavy command (here, the fixture's stub).
LANES = {
    "scoped.compiler-check": {
        "script": COMPILER_LANE,
        "in_scope": "compiler/rustc_trust/src/lib.rs",
        "in_scope_dir": "compiler/",
        "ran": ("STUB x.py ran",),
    },
    "scoped.completion-gate-tests": {
        "script": COMPLETION_LANE,
        "in_scope": "scripts/completion_gates/check_g1_rust_input.py",
        "in_scope_dir": "tests/two-language-programs/",
        # The stub suite passes. A machine lacking one of the lane's
        # prerequisites (git >= 2.41, /usr/bin/ssh-keygen) makes the lane red
        # AFTER scope instead, which is still "ran", never "skipped".
        "ran": ("completion-gate tests: PASS", "completion-gate tests NOT RUN"),
    },
    "scoped.bootstrap-script-tests": {
        "script": BOOTSTRAP_LANE,
        "in_scope": "scripts/recreate_bootstrap.py",
        # Its scope is exact files: no directory, and no first-party gitlink.
        "in_scope_dir": None,
        "gitlink_in_scope": False,
        # The stub tests pass where the checkout holds the pushed commit.
        # Where a case pushes a commit the checkout does not hold, the lane
        # refuses AFTER scope (it will not judge a tree it does not have),
        # and so it does on a machine without Python >= 3.11: red, which is
        # still "ran", never "skipped".
        "ran": ("bootstrap-script tests: PASS", "bootstrap-script tests NOT RUN"),
    },
    "scoped.targo-trust-unit-tests": {
        "script": TARGO_TRUST_LANE,
        "in_scope": "targo-trust/src/main.rs",
        "in_scope_dir": "targo-trust/",
        # The fixture's stub `targo` (STUB_TARGO) prints this for a test run.
        "ran": ("STUB targo test ran",),
    },
}
# The `targo` every lane finds first on PATH in the fixture: the targo-trust
# lane's heavy command, reached without a build. `metadata` fails, as it does
# in a tree with no targo-trust/Cargo.toml.
STUB_TARGO = (
    "#!/bin/sh\n"
    'case "$1" in metadata) echo "stub targo: no metadata" >&2; exit 1 ;; esac\n'
    'echo "STUB targo test ran: $*"\n'
)
# The four registered test files the bootstrap lane runs, as accepted stubs.
BOOTSTRAP_STUB_TESTS = {
    "scripts/tests/recreate_bootstrap_test.py": (
        "import unittest\n\n\n"
        "class Stub(unittest.TestCase):\n"
        "    def test_stub(self):\n"
        "        pass\n\n\n"
        'if __name__ == "__main__":\n'
        "    unittest.main()\n"
    ),
    "scripts/tests/promote_toolchain_test.sh": (
        "#!/usr/bin/env bash\n"
        'echo "Promotion toolchain tests: 1 cases passed (stub)"\n'
    ),
}

# Keep all four real bootstrap TESTS represented, so these scope controls reach
# execution instead of accepting a missing-test refusal as their only evidence.
BOOTSTRAP_STUB_TESTS.update({
    "scripts/tests/daily_toolchain_stage_test.py": BOOTSTRAP_STUB_TESTS["scripts/tests/recreate_bootstrap_test.py"],
    "scripts/tests/seed_lock_inventory_test.py": BOOTSTRAP_STUB_TESTS["scripts/tests/recreate_bootstrap_test.py"],
})


def completion_modules() -> list:
    """The completion lane's MODULES list, read from the script itself so the
    fixture's stub suite always matches what the lane asserts exists."""
    text = COMPLETION_LANE.read_text()
    match = re.search(r"^MODULES=\(\n(.*?)^\)", text, re.MULTILINE | re.DOTALL)
    if not match:
        raise AssertionError(f"no MODULES=( ... ) block in {COMPLETION_LANE}")
    return match.group(1).split()


class ScopedLanePushScopeTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name) / "repo"
        # No operator config and no push context from whoever runs this test:
        # a GIT_DIR from an enclosing hook would point every git call here at
        # the real repository.
        self.env = {
            key: value for key, value in os.environ.items()
            if not key.startswith(("GIT_", "TRUST_PUSH"))
        }
        self.env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        stub_bin = Path(self.temp.name) / "bin"
        stub_bin.mkdir()
        (stub_bin / "targo").write_text(STUB_TARGO, encoding="utf-8")
        (stub_bin / "targo").chmod(0o755)
        self.env["PATH"] = f"{stub_bin}{os.pathsep}{self.env.get('PATH', os.defpath)}"
        self.run_git_raw(["init", "--quiet", "--initial-branch=main", str(self.repo)])
        self.git("config", "user.name", "scope-test")
        self.git("config", "user.email", "scope-test@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        # Both are git's defaults; set so the controls below do not depend on
        # the default staying what it is.
        self.git("config", "diff.renames", "true")
        self.git("config", "core.quotePath", "true")

        files = {"README.md": "fixture\n", OUT_OF_SCOPE: "notes\n"}
        files["x.py"] = 'print("STUB x.py ran")\n'
        files["scripts/__init__.py"] = ""
        files["scripts/tests/__init__.py"] = ""
        stub = (
            "import unittest\n\n\n"
            "class Stub(unittest.TestCase):\n"
            "    def test_stub(self):\n"
            "        pass\n"
        )
        for module in completion_modules():
            files[f"scripts/tests/{module}.py"] = stub
        files.update(BOOTSTRAP_STUB_TESTS)
        for lane in LANES.values():
            files[lane["in_scope"]] = "original in-scope content\n" * 8
        self.base = self.commit(files, "base")
        self.git("update-ref", "refs/remotes/origin/main", self.base)

    # -- fixture helpers ----------------------------------------------------

    def run_git_raw(self, argv, check=True):
        return subprocess.run(
            ["git", *argv], env=self.env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=check, timeout=30,
        ).stdout.strip()

    def git(self, *args, check=True):
        return self.run_git_raw(["-C", str(self.repo), *args], check=check)

    def commit(self, files, message):
        """Write (or, for a None value, delete) files and commit on HEAD."""
        for path, content in files.items():
            target = self.repo / path
            if content is None:
                self.git("rm", "--quiet", "--", path)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")
            self.git("add", "--", path)
        self.git("commit", "--quiet", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def branch(self, name, start, files, message):
        """Commit `files` on a new branch `name` from `start`; leave it checked out."""
        self.git("checkout", "--quiet", "-B", name, start)
        return self.commit(files, message)

    def run_lane(self, lane, *args, pushed=None):
        env = dict(self.env)
        if pushed is not None:
            env["TRUST_PUSHED_REFS"] = pushed
        result = subprocess.run(
            ["bash", str(LANES[lane]["script"]), *args], cwd=self.repo, env=env,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL, timeout=120,
        )
        return result

    def assert_ran(self, lane, result):
        out = result.stdout
        self.assertIsNone(
            re.search(r"^\s*SKIPPED: ", out, re.MULTILINE),
            f"{lane} SKIPPED where the push is in scope:\n{out}",
        )
        self.assertTrue(
            any(marker in out for marker in LANES[lane]["ran"]),
            f"{lane} never reached its check:\n{out}",
        )

    def assert_skipped(self, lane, result):
        out = result.stdout
        self.assertEqual(result.returncode, 0, f"{lane} skip must exit 0:\n{out}")
        self.assertRegex(out, re.compile(r"^SKIPPED: ", re.MULTILINE))
        for marker in LANES[lane]["ran"]:
            self.assertNotIn(marker, out)

    def assert_subject(self, lane, result, fragment):
        subjects = [
            line for line in result.stdout.splitlines() if line.startswith("SUBJECT: ")
        ]
        self.assertEqual(len(subjects), 1, f"{lane}: want one SUBJECT line:\n{result.stdout}")
        self.assertIn(fragment, subjects[0])

    @staticmethod
    def ref_line(ref, local, remote):
        return f"{ref} {local} {ref} {remote}"

    # -- the cases ----------------------------------------------------------

    def test_unset_or_empty_env_reads_origin_main_to_head(self):
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                self.branch(f"docs-{lane}", self.base, {OUT_OF_SCOPE: "docs only\n"}, "docs")
                for pushed in (None, ""):
                    result = self.run_lane(lane, pushed=pushed)
                    self.assert_skipped(lane, result)
                    self.assert_subject(lane, result, "origin/main...HEAD (no push in flight")
                self.branch(f"code-{lane}", self.base, {spec["in_scope"]: "changed\n"}, "code")
                result = self.run_lane(lane)
                self.assert_ran(lane, result)
                self.assert_subject(lane, result, "origin/main...HEAD (no push in flight")

    def test_pushed_refs_are_read_as_a_union(self):
        # HEAD touches only docs; `topic`, pushed from here, carries the code.
        # The standing origin/main...HEAD reading skipped this push.
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                other = self.branch(f"other-{lane}", self.base, {"docs/other.md": "x\n"}, "other")
                topic = self.branch(f"topic-{lane}", self.base, {spec["in_scope"]: "changed\n"}, "code")
                self.branch(f"head-{lane}", self.base, {OUT_OF_SCOPE: "docs only\n"}, "docs")
                both = "\n".join([
                    self.ref_line(f"refs/heads/other-{lane}", other, self.base),
                    self.ref_line(f"refs/heads/topic-{lane}", topic, self.base),
                ])
                result = self.run_lane(lane, pushed=both)
                self.assert_ran(lane, result)
                self.assert_subject(lane, result, "the pushed refs (TRUST_PUSHED_REFS, 2 update(s))")
                self.assertIn(f"{self.base}..{topic}", result.stdout)
                self.assertNotIn(f"{self.base}...{topic}", result.stdout)
                # Only the docs-only update: the union is out of scope.
                only_other = self.ref_line(f"refs/heads/other-{lane}", other, self.base)
                result = self.run_lane(lane, pushed=only_other + "\n")
                self.assert_skipped(lane, result)
                self.assert_subject(lane, result, "the pushed refs (TRUST_PUSHED_REFS, 1 update(s))")

    def test_new_branch_is_diffed_against_origin_main(self):
        # origin/main already carries a code change; a NEW branch cut from it
        # that adds only docs must be judged against origin/main (skip), not
        # against nothing (which would fail and run) or against HEAD's history.
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                advanced = self.branch(f"main-{lane}", self.base, {spec["in_scope"]: "landed\n"}, "landed")
                self.git("update-ref", "refs/remotes/origin/main", advanced)
                fresh = self.branch(f"fresh-{lane}", advanced, {OUT_OF_SCOPE: "docs\n"}, "docs")
                # The checkout itself is in scope against origin/main.
                self.branch(f"work-{lane}", advanced, {spec["in_scope"]: "more\n"}, "more")
                pushed = self.ref_line(f"refs/heads/fresh-{lane}", fresh, ZERO)
                result = self.run_lane(lane, pushed=pushed)
                self.assert_skipped(lane, result)
                self.assertIn(f"origin/main...{fresh}", result.stdout)
                code = self.branch(f"fresh-code-{lane}", advanced, {spec["in_scope"]: "new\n"}, "code")
                pushed = self.ref_line(f"refs/heads/fresh-code-{lane}", code, ZERO)
                self.assert_ran(lane, self.run_lane(lane, pushed=pushed))
                self.git("update-ref", "refs/remotes/origin/main", self.base)

    def assert_tree_diff(self, lane, result, remote, local):
        """The SUBJECT names the update as the two-dot tree diff, not `...`."""
        self.assert_subject(lane, result, f" {remote}..{local}")
        self.assertNotIn(f"{remote}...{local}", result.stdout)

    def test_a_force_push_that_drops_in_scope_commits_runs(self):
        # The remote branch carries an in-scope commit; the force push replaces
        # it with a docs commit cut from the base. Since the merge base, the
        # push adds only docs, but the tree it installs LOSES the remote's
        # in-scope change: the lane must run.
        for lane, spec in LANES.items():
            for dropped in ("edit", "add"):
                with self.subTest(lane=lane, dropped=dropped):
                    if dropped == "add" and spec["in_scope_dir"] is None:
                        self.skipTest(f"{lane}: its scope holds no directory to add a file under")
                    path = spec["in_scope"]
                    if dropped == "add":
                        path = spec["in_scope_dir"] + f"added_on_remote_{lane}.rs"
                    remote = self.branch(
                        f"remote-{lane}-{dropped}", self.base,
                        {path: "on the remote only\n"}, "in-scope work on the remote",
                    )
                    # HEAD is the pushed tip and touches only docs against
                    # origin/main, so the fallback reading would skip as well.
                    forced = self.branch(
                        f"forced-{lane}-{dropped}", self.base,
                        {OUT_OF_SCOPE: "rewritten\n"}, "docs only",
                    )
                    # Control: the merge-base reading sees only the docs commit.
                    self.assertEqual(
                        self.git("diff", "--no-renames", "--name-only", f"{remote}...{forced}"),
                        OUT_OF_SCOPE,
                    )
                    pushed = self.ref_line(f"refs/heads/topic-{lane}-{dropped}", forced, remote)
                    result = self.run_lane(lane, pushed=pushed)
                    self.assert_ran(lane, result)
                    self.assert_tree_diff(lane, result, remote, forced)

    def test_a_fast_forward_docs_push_still_skips(self):
        # Control for the case above: for a fast-forward the tree diff equals
        # the merge-base diff, so a docs commit on top of in-scope history the
        # remote already has is out of scope. origin/main is behind that
        # history, so the fallback reading would RUN: the skip is the pushed
        # refs' verdict.
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                remote = self.branch(f"ff-{lane}", self.base, {spec["in_scope"]: "landed\n"}, "code")
                local = self.commit({OUT_OF_SCOPE: "docs on top\n"}, "docs")
                pushed = self.ref_line(f"refs/heads/ff-{lane}", local, remote)
                result = self.run_lane(lane, pushed=pushed)
                self.assert_skipped(lane, result)
                self.assert_tree_diff(lane, result, remote, local)
                # The same update carrying an in-scope commit runs.
                code = self.commit({spec["in_scope"]: "more\n"}, "more code")
                pushed = self.ref_line(f"refs/heads/ff-{lane}", code, local)
                self.assert_ran(lane, self.run_lane(lane, pushed=pushed))

    def test_a_new_branch_is_judged_since_its_fork_not_against_the_main_tree(self):
        # The decision the lanes' comment argues: a new branch keeps the
        # three-dot `origin/main...<local-sha>`. Pinned both ways, because the
        # two-dot `origin/main..<local-sha>` gets each of these wrong.
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                landed = self.branch(f"main2-{lane}", self.base, {spec["in_scope"]: "landed\n"}, "landed")
                self.git("update-ref", "refs/remotes/origin/main", landed)
                # (a) A docs branch cut from the OLDER main carries none of the
                # in-scope change main landed since: skip. Two dots would run.
                stale = self.branch(f"stale-{lane}", self.base, {OUT_OF_SCOPE: "docs\n"}, "docs")
                self.assertIn(
                    spec["in_scope"],
                    self.git("diff", "--name-only", f"origin/main..{stale}").splitlines(),
                )
                result = self.run_lane(lane, pushed=self.ref_line(f"refs/heads/stale-{lane}", stale, ZERO))
                self.assert_skipped(lane, result)
                self.assertIn(f"origin/main...{stale}", result.stdout)
                # (b) A branch from the older main that cherry-picks main's
                # in-scope change adds that change: run. Its tree matches
                # origin/main there, so two dots would list only the docs.
                pick = self.branch(
                    f"pick-{lane}", self.base,
                    {spec["in_scope"]: "landed\n", OUT_OF_SCOPE: "docs\n"}, "cherry-pick + docs",
                )
                self.assertEqual(
                    self.git("diff", "--name-only", f"origin/main..{pick}"), OUT_OF_SCOPE,
                )
                result = self.run_lane(lane, pushed=self.ref_line(f"refs/heads/pick-{lane}", pick, ZERO))
                self.assert_ran(lane, result)
                self.assertIn(f"origin/main...{pick}", result.stdout)
                self.git("update-ref", "refs/remotes/origin/main", self.base)

    def test_deletions_contribute_nothing(self):
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                docs = self.branch(f"docs-{lane}", self.base, {OUT_OF_SCOPE: "docs\n"}, "docs")
                self.branch(f"head-{lane}", self.base, {spec["in_scope"]: "changed\n"}, "code")
                deletion = f"(delete) {ZERO} refs/heads/gone {self.base}"
                # A deletion beside a docs-only update: the deletion is not an
                # undiffable range (which would run); it is simply nothing.
                pushed = deletion + "\n" + self.ref_line(f"refs/heads/docs-{lane}", docs, self.base)
                result = self.run_lane(lane, pushed=pushed)
                self.assert_skipped(lane, result)
                self.assert_subject(lane, result, "1 update(s)")
                # Only deletions: fall back to origin/main...HEAD, and say so.
                result = self.run_lane(lane, pushed=deletion)
                self.assert_ran(lane, result)
                self.assert_subject(lane, result, "only deletions")
                self.git("checkout", "--quiet", f"docs-{lane}")
                result = self.run_lane(lane, pushed=deletion)
                self.assert_skipped(lane, result)
                self.assert_subject(lane, result, "only deletions")
                # Lines that are not four fields are skipped the same way
                # (check_crates_tests_scoped.py does too); the SUBJECT line
                # must not call them deletions.
                result = self.run_lane(lane, pushed="hello world")
                self.assert_skipped(lane, result)
                self.assert_subject(lane, result, "only deletions or malformed lines")

    def test_a_move_out_of_scope_is_in_scope(self):
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                self.git("checkout", "--quiet", "-B", f"move-{lane}", self.base)
                self.git("mv", spec["in_scope"], "docs/moved.txt")
                moved = self.commit({}, "move out of scope")
                # Control: with rename detection git lists only the new path.
                self.assertEqual(
                    self.git("diff", "--name-only", f"{self.base}...HEAD"), "docs/moved.txt"
                )
                self.assert_ran(lane, self.run_lane(lane))
                pushed = self.ref_line(f"refs/heads/move-{lane}", moved, self.base)
                self.assert_ran(lane, self.run_lane(lane, pushed=pushed))

    def test_a_non_ascii_path_is_matched(self):
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                if spec["in_scope_dir"] is None:
                    self.skipTest(f"{lane}: its scope is exact ASCII file names")
                path = spec["in_scope_dir"] + "é.rs"
                self.branch(f"accent-{lane}", self.base, {path: "fn e() {}\n"}, "accent")
                # Control: without -z git C-quotes the path, leading quote included.
                quoted = self.git("diff", "--name-only", f"{self.base}...HEAD")
                self.assertTrue(quoted.startswith('"'), quoted)
                self.assert_ran(lane, self.run_lane(lane))

    def test_a_submodule_ignore_setting_does_not_hide_a_pin_move(self):
        # Both lanes list first-party gitlinks as in scope (the compiler lane
        # via ^first-party/, the completion lane via first-party/clean$). A
        # plain `git diff` honours diff.ignoreSubmodules and a .gitmodules
        # `ignore = all` — the latter read from the WORKTREE even for a
        # commit-to-commit diff, and a push can carry it — and then lists
        # nothing, so the lane printed SKIPPED on a pin move.
        gitlink = "first-party/clean"
        for lane, spec in LANES.items():
            for setting in ("diff.ignoreSubmodules", ".gitmodules"):
                with self.subTest(lane=lane, setting=setting):
                    if not spec.get("gitlink_in_scope", True):
                        self.skipTest(f"{lane}: no first-party gitlink is in its scope")
                    name = f"pin-{lane}-{setting.strip('.')}"
                    self.git("checkout", "--quiet", "-B", name, self.base)
                    self.git(
                        "update-index", "--add", "--cacheinfo",
                        f"160000,{self.base},{gitlink}",
                    )
                    files = {}
                    if setting == ".gitmodules":
                        # Committed with the pin move, as a push would carry it;
                        # .gitmodules itself is in neither lane's scope.
                        files[".gitmodules"] = (
                            '[submodule "clean"]\n'
                            f"\tpath = {gitlink}\n"
                            "\turl = https://example.invalid/clean.git\n"
                            "\tignore = all\n"
                        )
                    else:
                        self.git("config", "diff.ignoreSubmodules", "all")
                    pin = self.commit(files, "move the clean pin")
                    # Control: the setting really does hide the gitlink from a
                    # plain diff, so this case exercises the override.
                    plain = self.git(
                        "-c", "diff.renames=false", "diff", "--no-renames",
                        "--name-only", f"{self.base}...HEAD",
                    )
                    self.assertNotIn(gitlink, plain.splitlines())
                    self.assert_ran(lane, self.run_lane(lane))
                    pushed = self.ref_line(f"refs/heads/{name}", pin, self.base)
                    self.assert_ran(lane, self.run_lane(lane, pushed=pushed))
                    self.assert_ran(lane, self.run_lane(lane, self.base))
                    self.git("config", "--unset-all", "diff.ignoreSubmodules", check=False)
                    self.git("checkout", "--quiet", "-f", "main")

    def test_a_diff_that_cannot_be_computed_runs_the_check(self):
        for lane in LANES:
            with self.subTest(lane=lane):
                # HEAD is out of scope, so every "ran" below is the failure path.
                self.branch(f"docs-{lane}", self.base, {OUT_OF_SCOPE: "docs\n"}, "docs")
                docs = self.git("rev-parse", "HEAD")
                # No merge base: `git diff A...B` exits 128 while `rev-parse A`
                # succeeds. The compiler lane read the empty output as "no changes".
                self.git("checkout", "--quiet", "--orphan", f"orphan-{lane}")
                orphan = self.commit({}, "unrelated history")
                self.git("checkout", "--quiet", "-f", f"docs-{lane}")
                result = self.run_lane(lane, orphan)
                self.assert_ran(lane, result)
                self.assertIn("cannot compute the diff", result.stdout)
                # A pushed range naming an object this clone does not have.
                missing = "1" * 40
                pushed = self.ref_line(f"refs/heads/docs-{lane}", docs, missing)
                result = self.run_lane(lane, pushed=pushed)
                self.assert_ran(lane, result)
                self.assertIn(f"cannot compute the diff {missing}..{docs}", result.stdout)
                # One good range does not launder a bad one in the same push.
                good = self.ref_line(f"refs/heads/docs-{lane}", docs, self.base)
                self.assert_ran(lane, self.run_lane(lane, pushed=good + "\n" + pushed))
                # No origin/main at all under the standing reading.
                self.git("update-ref", "-d", "refs/remotes/origin/main")
                self.assert_ran(lane, self.run_lane(lane))
                self.git("update-ref", "refs/remotes/origin/main", self.base)

    def test_compiler_lane_scope_is_what_x_py_check_reads(self):
        # 2026-09-28: `x.py check --stage 1` compiles std, the default tool
        # steps, the vendored and locked dependencies and rustc_llvm, but the
        # lane's scope was compiler/, crates/, src/bootstrap/, targo-trust/ and
        # first-party/ only, so a push touching nothing but one of these paths
        # SKIPPED (measured on the old IN_SCOPE_RE: every row below skipped).
        # Each must now RUN. x.py itself is left out here only because the
        # fixture's x.py is the stub that proves the lane ran.
        lane = "scoped.compiler-check"
        read_by_check = (
            "library/core/src/lib.rs",
            "src/tools/tidy/src/main.rs",
            "src/librustdoc/lib.rs",
            "src/llvm-project/llvm/lib/IR/Core.cpp",
            "vendor/some-crate/src/lib.rs",
            "Cargo.lock",
            "Cargo.toml",
            ".cargo/config.toml",
            "src/stage0",
            "src/version",
            "src/rust-compat-version",
            "release/trust-version.toml",
            "tools/preflight.py",
            "crates/trust-build-tree/src/trust_repo_lock/management.rs",
            "scripts/frozen-files.txt",
            "tests/fixtures/binary_decomp/x86_64-load-elf.hex",
        )
        for index, path in enumerate(read_by_check):
            with self.subTest(path=path):
                name = f"read-{index}"
                local = self.branch(name, self.base, {path: f"touched {index}\n"}, path)
                pushed = self.ref_line(f"refs/heads/{name}", local, self.base)
                self.assert_ran(lane, self.run_lane(lane, pushed=pushed))
        # Controls: paths x.py check does not read still skip, including
        # look-alikes of the new prefixes.
        not_read = (
            "src/doc/book.md",
            "tests/ui/trust/a.rs",
            "tests/some-fixture/Cargo.lock",
            "scripts/other.sh",
            "src/versions.txt",
        )
        for index, path in enumerate(not_read):
            with self.subTest(path=path):
                name = f"unread-{index}"
                local = self.branch(name, self.base, {path: f"touched {index}\n"}, path)
                pushed = self.ref_line(f"refs/heads/{name}", local, self.base)
                self.assert_skipped(lane, self.run_lane(lane, pushed=pushed))

    def test_an_explicit_base_keeps_its_meaning(self):
        for lane, spec in LANES.items():
            with self.subTest(lane=lane):
                docs = self.branch(f"docs-{lane}", self.base, {OUT_OF_SCOPE: "docs\n"}, "docs")
                code = self.branch(f"code-{lane}", self.base, {spec["in_scope"]: "x\n"}, "code")
                docs_push = self.ref_line(f"refs/heads/docs-{lane}", docs, self.base)
                code_push = self.ref_line(f"refs/heads/code-{lane}", code, self.base)
                # HEAD (code) is in scope vs the base; the pushed refs are not read.
                result = self.run_lane(lane, self.base, pushed=docs_push)
                self.assert_ran(lane, result)
                self.assert_subject(lane, result, f"{self.base}...HEAD (explicit base argument")
                self.git("checkout", "--quiet", f"docs-{lane}")
                result = self.run_lane(lane, self.base, pushed=code_push)
                self.assert_skipped(lane, result)
                self.assert_subject(lane, result, "explicit base argument")


if __name__ == "__main__":
    unittest.main()
