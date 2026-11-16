#!/usr/bin/env python3
"""The UI differential sweep must compile a fixture the way compiletest does.

`scripts/ui_trust_budget_sensitivity.py` compares two compilations of every
verification-bearing `tests/ui/trust` fixture by exit code. Measured
2026-09-27, it could not see what compiletest sees: its default pattern was
top-level only (737 of 851 non-auxiliary fixtures at 8c39674bbb -- the exact
count a differential sweep reported as "all 737 tests/ui/trust fixtures ...
exit codes identical" while `memory_safe/reject_diverging_call_gap.rs`
regressed), it ignored `//@ edition`, `//@ rustc-env` and the in-tree
`//@ [rev] compile-flags` spelling, and it reported "zero sensitive" even when
nothing compiled. docs/KNOWN_HAZARDS.md carries the general hazard.

The end-to-end rows run the real script with a FAKE compiler that logs every
invocation, so they fail on the old script for the reason that matters -- the
fixture never reaches the compiler with its flags -- not on a renamed helper.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import importlib.util
import json
import os
import stat
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "ui_trust_budget_sensitivity.py"
REGRESSED = "tests/ui/trust/memory_safe/reject_diverging_call_gap.rs"

FAKE_TRUSTC = textwrap.dedent(
    """\
    #!/usr/bin/env python3
    import json, os, sys
    with open(os.environ["FAKE_TRUSTC_LOG"], "a") as log:
        log.write(json.dumps({"argv": sys.argv[1:],
                              "env": os.environ.get("SWEEP_TEST_ENV")}) + "\\n")
    sys.exit(int(os.environ.get("FAKE_TRUSTC_RC", "0")))
    """
)


def load_script():
    spec = importlib.util.spec_from_file_location("ui_trust_budget_sensitivity", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def write(root: Path, rel: str, text: str) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(textwrap.dedent(text))
    return path


class SweepHarness:
    """Run the real script against a fake compiler; return (rc, stdout, invocations)."""

    def __init__(self, tmp: Path) -> None:
        self.tmp = tmp
        self.trustc = tmp / "fake-trustc"
        self.trustc.write_text(FAKE_TRUSTC)
        self.trustc.chmod(self.trustc.stat().st_mode | stat.S_IXUSR)
        self.log = tmp / "invocations.jsonl"

    def run(self, *args: str, rc: int = 0):
        self.log.write_text("")
        env = dict(os.environ, FAKE_TRUSTC_LOG=str(self.log), FAKE_TRUSTC_RC=str(rc))
        env.pop("SWEEP_TEST_ENV", None)
        proc = subprocess.run(
            [sys.executable, str(SCRIPT), "--trustc", str(self.trustc), "--jobs", "8",
             "--low", "1", "--high", "2", *args],
            capture_output=True, text=True, env=env, cwd=self.tmp, timeout=900,
        )
        invocations = [json.loads(line) for line in self.log.read_text().splitlines() if line]
        return proc.returncode, proc.stdout + proc.stderr, invocations


def invocations_of(invocations, suffix: str):
    return [inv for inv in invocations if inv["argv"] and inv["argv"][-1].endswith(suffix)]


class EndToEndTests(unittest.TestCase):
    """Red on the pre-2026-09-27 script, green after."""

    def test_the_default_sweep_compiles_the_regressed_memory_safe_fixture_with_both_flag_lines(self):
        # THE regression row. With no --tests the sweep must reach the fixture
        # the "all 737" sweep never compiled, and pass it the policy from its
        # SECOND compile-flags line.
        with tempfile.TemporaryDirectory() as tmp:
            rc, out, invocations = SweepHarness(Path(tmp)).run()
            self.assertEqual(rc, 0, out)
            hits = invocations_of(invocations, REGRESSED)
            self.assertEqual(len(hits), 2, f"one compilation per arm expected\n{out}")
            for hit in hits:
                argv = hit["argv"]
                self.assertIn("-Ztrust-verify=on", argv)
                self.assertIn("-Ztrust-policy=memory-safe", argv)
                self.assertIn("--crate-type=lib", argv)

    def test_nested_revisioned_edition_and_env_fixtures_are_compiled_as_compiletest_would(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "ui"
            write(root, "a/b/nested.rs", """\
                //@ edition: 2021
                //@ compile-flags: -Ztrust-verify=on
                //@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
                //@ check-pass
                pub fn f() {}
                """)
            write(root, "revs.rs", """\
                //@ revisions: x y
                //@ [x] compile-flags: -Ztrust-verify=on -Cdebug-assertions=on
                //@[y] compile-flags: -Ztrust-verify=on -Cdebug-assertions=off
                //@ rustc-env: SWEEP_TEST_ENV=from-directive
                //@ check-pass
                pub fn g() {}
                """)
            write(root, "auxiliary/helper.rs", """\
                //@ compile-flags: -Ztrust-verify=on
                pub fn h() {}
                """)
            rc, out, invocations = SweepHarness(Path(tmp)).run("--tests", f"{root}/**/*.rs")
            self.assertEqual(rc, 0, out)

            nested = invocations_of(invocations, "nested.rs")
            self.assertEqual(len(nested), 2, out)
            argv = nested[0]["argv"]
            self.assertEqual(argv[0], "--edition=2021", "the edition goes first, as compiletest puts it")
            self.assertIn("-Ztrust-policy=memory-safe", argv)

            revs = invocations_of(invocations, "revs.rs")
            self.assertEqual(len(revs), 4, f"two revisions x two arms\n{out}")
            seen = {(inv["argv"][inv["argv"].index("--cfg") + 1],
                     next(a for a in inv["argv"] if a.startswith("-Cdebug-assertions")))
                    for inv in revs}
            self.assertEqual(seen, {("x", "-Cdebug-assertions=on"),
                                    ("y", "-Cdebug-assertions=off")},
                             "a spaced `//@ [x]` line is a real directive")
            self.assertEqual({inv["env"] for inv in revs}, {"from-directive"})

            self.assertEqual(invocations_of(invocations, "helper.rs"), [],
                             "an auxiliary crate is not a test")

    def test_a_sweep_in_which_nothing_compiles_is_reported_blind_not_clean(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "ui"
            fixture = write(root, "p.rs", """\
                //@ compile-flags: -Ztrust-verify=on --crate-type=lib
                //@ check-pass
                pub fn p() {}
                """)
            # A literal path, so the row isolates the guard from discovery.
            rc, out, invocations = SweepHarness(Path(tmp)).run("--tests", str(fixture), rc=1)
            self.assertEqual(len(invocations), 2, out)
            self.assertEqual(rc, 3, f"identical exit codes over a blind sweep must not pass\n{out}")

    def test_a_set_with_no_pass_mode_case_is_blind_too(self):
        # A narrowed sweep of fail-mode fixtures on a trustc that exits 1 for
        # everything: both arms agree, yet nothing showed the verifier ran.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "ui"
            fixture = write(root, "f.rs", """\
                //@ compile-flags: -Ztrust-verify=on --crate-type=lib
                //@ check-fail
                pub fn f() {}
                """)
            rc, out, invocations = SweepHarness(Path(tmp)).run("--tests", str(fixture), rc=1)
            self.assertEqual(len(invocations), 2, out)
            self.assertEqual(rc, 3, f"a sweep with no pass-mode witness must not pass\n{out}")


class DirectiveTests(unittest.TestCase):
    """The directive reader against compiletest's rules, row by row."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.m = load_script()

    def test_parse_directive_follows_compiletest_line_splitting(self):
        p = self.m.parse_directive
        self.assertEqual(p("//@ compile-flags: -Ztrust-verify=on"),
                         (None, "compile-flags", " -Ztrust-verify=on"))
        self.assertEqual(p("   //@[r] compile-flags: -O"), ("r", "compile-flags", " -O"))
        self.assertEqual(p("//@ [r] compile-flags: -O"), ("r", "compile-flags", " -O"))
        self.assertEqual(p("//@ check-pass"), (None, "check-pass", None))
        self.assertIsNone(p("// compile-flags: -O"))
        self.assertIsNone(p("//! //@ compile-flags: -O"))

    def test_every_compile_flags_line_accumulates_and_edition_goes_first(self):
        lines = [self.m.parse_directive(line) for line in (
            "//@ compile-flags: -Ztrust-verify=on",
            "//@ edition:2018..",
            "//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib",
            "//@ check-pass",
        )]
        args, env, mode = self.m.resolve(lines, None)
        self.assertEqual(args, ["--edition=2018", "-Ztrust-verify=on",
                                "-Ztrust-policy=memory-safe", "--crate-type=lib"])
        self.assertEqual((env, mode), ([], "check-pass"))

    def test_revision_scoping_and_the_default_mode(self):
        lines = [self.m.parse_directive(line) for line in (
            "//@ revisions: a b",
            "//@ compile-flags: -Ztrust-verify=on",
            "//@[a] compile-flags: -Ca",
            "//@ [b] compile-flags: -Cb",
            "//@[b] check-pass",
        )]
        self.assertEqual(self.m.resolve(lines, "a"), (["-Ztrust-verify=on", "-Ca"], [], "check-fail"))
        self.assertEqual(self.m.resolve(lines, "b"), (["-Ztrust-verify=on", "-Cb"], [], "check-pass"))

    def test_single_quoted_flags_stay_whole(self):
        self.assertEqual(self.m.split_flags(" -A x '--cfg=a b' -O"), ["-A", "x", "--cfg=a b", "-O"])

    def test_a_revision_only_fixture_is_not_dropped(self):
        # The old reader skipped a fixture whose every compile-flags line was
        # revision-scoped ("no base flags").
        with tempfile.TemporaryDirectory() as tmp:
            path = write(Path(tmp), "r.rs", """\
                //@ revisions: only
                //@[only] compile-flags: -Ztrust-verify=on
                """)
            cases = list(self.m.cases(str(path)))
            self.assertEqual([(c[1], c[2]) for c in cases], [("only", ["-Ztrust-verify=on"])])

    def test_same_basename_in_two_directories_gives_two_results(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for d in ("one", "two"):
                write(root, f"{d}/same.rs", "//@ compile-flags: -Ztrust-verify=on\n")
            cases = list(self.m.cases(f"{root}/**/*.rs"))
            tags = {self.m.case_tag(c, root=str(root)) for c in cases}
            self.assertEqual(tags, {os.path.join("one", "same.rs"), os.path.join("two", "same.rs")})

    def test_skips_are_counted_by_reason(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write(root, "noverify.rs", "//@ compile-flags: -O\n")
            write(root, "pinned.rs", "//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-timeout-ms=9\n")
            write(root, "aux.rs", "//@ aux-build: x.rs\n//@ compile-flags: -Ztrust-verify=on\n")
            write(root, "ignored/compiletest-ignore-dir", "")
            write(root, "ignored/t.rs", "//@ compile-flags: -Ztrust-verify=on\n")
            write(root, "never.rs", "//@ ignore-test (red on purpose)\n//@ compile-flags: -Ztrust-verify=on\n")
            skipped: dict = {}
            self.assertEqual(list(self.m.cases(f"{root}/**/*.rs", True, skipped)), [])
            self.assertEqual(skipped, {"no -Ztrust-verify=on": 1, "pins its own budget": 1,
                                       "aux-build": 1, "ignore-test": 1})

    def test_the_real_tree_default_reaches_subdirectories(self):
        files = self.m.discover(self.m.DEFAULT_TESTS)
        rel = {os.path.relpath(f, REPO) for f in files}
        self.assertIn(REGRESSED, rel)
        self.assertFalse(any("/auxiliary/" in r for r in rel))
        (case,) = [c for c in self.m.cases(self.m.DEFAULT_TESTS)
                   if os.path.relpath(c[0], REPO) == REGRESSED]
        # Its mode is whatever the file declares today (it moved check-pass ->
        # check-fail in f7c53ca0c2); what is pinned is that BOTH flag lines arrive.
        self.assertIn(case[4], self.m.PASS_MODES + self.m.FAIL_MODES)
        self.assertIn("-Ztrust-policy=memory-safe", case[2])
        self.assertIn("--crate-type=lib", case[2])


if __name__ == "__main__":
    unittest.main()
