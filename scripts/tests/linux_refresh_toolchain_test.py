#!/usr/bin/env python3
"""Regressions for scripts/linux_refresh_toolchain.py: one staircase rung as one command.

The script only sequences commands that have their own tests (seed_staircase.py,
bootstrap_dependency_closure.py, mint_seed_support.py, promote-toolchain.sh). What
is its own, and what these fixtures hold it to:

* the rung worktree it clones has every submodule at its pin, nested ones included,
  taken from another checkout's module store and never from the network (the
  2026-11-06 run stopped twice on a clone without trust-cg's nested submodules);
* a pin the store lacks, a dirty or moved worktree, and a rung record that is not
  clean are refusals, and a refused or failed step leaves no file that a later run
  would read as that step done;
* the order of the commands, and that the only seal it runs is `--no-flip`.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import contextlib
import importlib.util
import io
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO = Path(__file__).resolve().parents[2]
SCRIPT = REPO / "scripts" / "linux_refresh_toolchain.py"
SPEC = importlib.util.spec_from_file_location("linux_refresh_toolchain", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
refresh = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = refresh
SPEC.loader.exec_module(refresh)

GIT_ENV = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
           "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
           "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}
HOST = "aarch64-unknown-linux-gnu"


def git(repo: Path, *args: str) -> str:
    command = refresh.git_command(repo, "-c", "protocol.file.allow=always", *args)
    return subprocess.run(command, check=True, capture_output=True,
                          text=True, env=GIT_ENV).stdout.strip()


def commit_file(repo: Path, name: str, text: str) -> str:
    (repo / name).write_text(text)
    git(repo, "add", name)
    git(repo, "commit", "-qm", f"{name}: {text}")
    return git(repo, "rev-parse", "HEAD")


def new_repo(path: Path) -> Path:
    path.mkdir(parents=True)
    git(path, "init", "-q", "-b", "main")
    commit_file(path, "f.txt", "one")
    return path


class Fixture:
    """A superproject with first-party/a, which has its own third_party/n: the shape
    of trust with trust-cg. `source` is a checkout with both initialised."""

    def __init__(self, root: Path):
        self.root = root
        self.nested = new_repo(root / "donor-n")
        self.donor_a = new_repo(root / "donor-a")
        git(self.donor_a, "submodule", "-q", "add", str(self.nested), "third_party/n")
        git(self.donor_a, "commit", "-qm", "add n")
        self.upstream = new_repo(root / "upstream")
        git(self.upstream, "submodule", "-q", "add", str(self.donor_a), "first-party/a")
        git(self.upstream, "commit", "-qm", "add a")
        self.source = root / "source"
        git(root, "clone", "-q", "--recurse-submodules", str(self.upstream), str(self.source))
        self.commit = git(self.source, "rev-parse", "HEAD")


def arguments(ledger: Path, **changes) -> argparse.Namespace:
    base = dict(mode="run", ledger=ledger, stage0=ledger / "stage0", commit="HEAD", repo=ledger / "repo",
                worktree=None, label=None, jobs=3, tool_dir=[], fixed_point=False, seal=False, lld=False,
                host=HOST)
    base.update(changes)
    return argparse.Namespace(**base)


class HostTests(unittest.TestCase):
    def test_a_linux_host_names_its_triple_and_any_other_is_refused(self):
        self.assertEqual(refresh.host_triple("Linux", "aarch64"), "aarch64-unknown-linux-gnu")
        self.assertEqual(refresh.host_triple("Linux", "x86_64"), "x86_64-unknown-linux-gnu")
        with self.assertRaisesRegex(refresh.Refusal, "src/stage0 pin"):
            refresh.host_triple("Darwin", "arm64")
        with self.assertRaisesRegex(refresh.Refusal, "riscv64"):
            refresh.host_triple("Linux", "riscv64")


class CloneTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name).resolve()
        self.fixture = Fixture(self.root)
        patcher = mock.patch.dict(os.environ, GIT_ENV)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.addCleanup(self.tmp.cleanup)

    def test_a_rung_clone_has_every_submodule_at_its_pin_from_the_local_store(self):
        worktree = self.root / "ledger" / "w"
        worktree.parent.mkdir()
        done = refresh.clone_rung(self.fixture.source, self.fixture.commit, worktree)
        self.assertEqual(done, ["first-party/a", "first-party/a/third_party/n"])
        self.assertEqual(refresh.worktree_problems(worktree, self.fixture.commit), [])
        self.assertTrue((worktree / "first-party/a/third_party/n/f.txt").is_file())
        store = self.fixture.source / ".git/modules/first-party/a"
        # Nothing names the donors: both levels were taken from the source checkout's store.
        self.assertEqual(git(worktree / "first-party/a", "remote", "get-url", "origin"), str(store))
        self.assertEqual(git(worktree / "first-party/a/third_party/n", "remote", "get-url", "origin"),
                         str(store / "modules/third_party/n"))

    def test_a_second_worktree_with_linked_submodules_is_cloned_from_the_shared_stores(self):
        # What `submodule_sync.sh --restore` makes of a second worktree: no module store
        # under its own git directory, each submodule checkout a linked worktree of the
        # store the first checkout cloned.
        second = self.root / "second"
        git(self.fixture.source, "worktree", "add", "-q", "--detach", str(second), "HEAD")
        store = self.fixture.source / ".git/modules/first-party/a"
        for linked, shared in (("first-party/a", store),
                               ("first-party/a/third_party/n", store / "modules/third_party/n")):
            pin = git(self.fixture.source / linked, "rev-parse", "HEAD")
            subprocess.run(["git", "--git-dir", str(shared), "worktree", "add", "-q", "--detach",
                            str(second / linked), pin], check=True, capture_output=True, env=GIT_ENV)
        self.assertFalse((Path(git(second, "rev-parse", "--absolute-git-dir")) / "modules").exists())
        worktree = self.root / "w3"
        done = refresh.clone_rung(second, self.fixture.commit, worktree)
        self.assertEqual(done, ["first-party/a", "first-party/a/third_party/n"])
        self.assertEqual(refresh.worktree_problems(worktree, self.fixture.commit), [])
        self.assertEqual(git(worktree / "first-party/a", "remote", "get-url", "origin"), str(store))
        self.assertEqual(git(worktree / "first-party/a/third_party/n", "remote", "get-url", "origin"),
                         str(store / "modules/third_party/n"))

    def test_a_pin_the_store_lacks_is_refused_with_the_command_that_fetches_it(self):
        # The donor moves on and upstream pins the new commit; the source checkout's
        # superproject is pulled, but its module store is not.
        moved = commit_file(self.fixture.donor_a, "g.txt", "two")
        git(self.fixture.upstream / "first-party/a", "fetch", "-q", "origin")
        git(self.fixture.upstream / "first-party/a", "checkout", "-q", moved)
        git(self.fixture.upstream, "commit", "-qam", "pin moved")
        git(self.fixture.source, "pull", "-q", "--no-recurse-submodules")
        target = git(self.fixture.source, "rev-parse", "HEAD")
        with self.assertRaisesRegex(refresh.Refusal, r"submodule_sync\.sh --fetch --restore"):
            refresh.clone_rung(self.fixture.source, target, self.root / "w2")

    def test_an_existing_path_is_never_cloned_over(self):
        (self.root / "taken").mkdir()
        with self.assertRaisesRegex(refresh.Refusal, "exists"):
            refresh.clone_rung(self.fixture.source, self.fixture.commit, self.root / "taken")

    def test_a_worktree_that_is_dirty_moved_or_off_its_pins_is_named(self):
        worktree = self.root / "w"
        refresh.clone_rung(self.fixture.source, self.fixture.commit, worktree)
        (worktree / "f.txt").write_text("edited")
        self.assertRegex("; ".join(refresh.worktree_problems(worktree, self.fixture.commit)), "differ from HEAD")
        git(worktree, "checkout", "-q", "f.txt")
        self.assertRegex("; ".join(refresh.worktree_problems(worktree, "0" * 40)), "HEAD is")
        git(worktree / "first-party/a", "checkout", "-q", "HEAD~1")
        self.assertRegex("; ".join(refresh.worktree_problems(worktree, self.fixture.commit)), "first-party/a")


class RecordTests(unittest.TestCase):
    def test_only_a_zero_exit_with_clean_no_stock_evidence_is_a_rung(self):
        self.assertEqual(refresh.rung_problems({"rc": 0, "no_stock_evidence": True}), [])
        self.assertRegex(refresh.rung_problems({"rc": 1, "no_stock_evidence": True})[0], "exited 1")
        problems = refresh.rung_problems({"rc": 0, "no_stock_evidence": False, "trap_hits": ["rustc"]})
        self.assertRegex(problems[0], "trap_hits")
        # A record that does not say is not clean.
        self.assertEqual(len(refresh.rung_problems({})), 2)

    def test_the_last_table_of_a_config_is_found(self):
        self.assertEqual(refresh.last_table("a = 1\n[llvm]\nb = 2\n[build]\nrustc = 'x'\n"), "[build]")
        self.assertIsNone(refresh.last_table("a = 1\n"))


class PlanTests(unittest.TestCase):
    def test_the_commands_come_in_order_and_the_only_seal_does_not_flip(self):
        ledger = Path("/ledger")
        plan = refresh.Plan(arguments(ledger, fixed_point=True, seal=True, tool_dir=[Path("/tools")]),
                            HOST, "c" * 40)
        lines = plan.lines()[1:]
        order = ["clone ", " admit ", " seed-config ", " config ", " prepare ", "x.py --version", " run ",
                 "cp -a ", "mv ", " admit ", " config ", "x.py --version", " run ", " stage2-manifest ",
                 " stage2-manifest ", " ddc-compare ", "--bin trust-serial-command", "promote-toolchain.sh"]
        self.assertEqual(len(lines), len(order))
        for line, word in zip(lines, order):
            self.assertIn(word, line)
        self.assertIn("--no-flip", lines[-1])
        # The seal runs under a build slot and names the executor the line before it builds:
        # by the rung's own targo, from the rung's own crate, into the ledger.
        self.assertIn(f"TRUST_TOOLCHAIN_SERIAL_COMMAND=/ledger/r-{'c' * 10}-serial-command/release/trust-serial-command ",
                      lines[-1])
        self.assertRegex(lines[-1], r"scripts/build-slot --cpus 1 --wait-timeout 900 -- bash \S+/scripts/promote-toolchain\.sh --no-flip")
        self.assertIn(f"(cd /ledger/w-{'c' * 10}/crates/trust-resource-controller && env -i ", lines[-2])
        self.assertIn(f"/ledger/w-{'c' * 10}/build/{HOST}/stage2/bin/targo --unverified build --locked --offline "
                      "--release --features serial-command", lines[-2])
        # Its own lock is fetched first, by the same targo; a fetch takes no lane flag.
        self.assertIn(f"/ledger/w-{'c' * 10}/build/{HOST}/stage2/bin/targo fetch --locked && ", lines[-2])
        self.assertIn(f"CARGO_TARGET_DIR=/ledger/r-{'c' * 10}-serial-command ", lines[-2])
        self.assertIn(f"PATH=/ledger/w-{'c' * 10}/build/{HOST}/stage2/bin:/ledger/trap:/usr/bin:/bin ", lines[-2])
        self.assertIn("--tool-dir /tools", lines[6])
        self.assertIn("--timeout 900", lines[4])
        self.assertIn(f"/ledger/r-{'c' * 10}-stage2 --repo", lines[9])  # the second build's stage0
        # Each build constructs Bootstrap from its own config, so from its own stage0.
        self.assertIn(f"RUST_BOOTSTRAP_CONFIG=/ledger/r-{'c' * 10}.bootstrap.toml", lines[5])
        self.assertIn(f"RUST_BOOTSTRAP_CONFIG=/ledger/r-{'c' * 10}-fp.bootstrap.toml", lines[11])
        self.assertIn("/ledger/trap:", lines[5])
        self.assertNotIn(" lineage ", "\n".join(lines))

    def test_the_first_manifest_is_of_the_first_builds_own_tree(self):
        # Until 2026-11-12 it was of the read-only copy, whose modes no build has.
        plan = refresh.Plan(arguments(Path("/ledger"), fixed_point=True), HOST, "c" * 40)
        label = f"r-{'c' * 10}"
        first, second = [line for line in plan.lines() if " stage2-manifest " in line]
        self.assertIn(f" stage2-manifest /ledger/{label}-build/{HOST}/stage2 /ledger/{label}.stage2.json ", first)
        self.assertIn(f" stage2-manifest /ledger/w-{'c' * 10}/build/{HOST}/stage2 /ledger/{label}-fp.stage2.json ",
                      second)
        # The copy is the second build's stage0 and nothing else: no manifest is of it.
        self.assertNotIn(f"/ledger/{label}-stage2", first + second)
        self.assertEqual(sum(f"/ledger/{label}-stage2 " in line for line in plan.lines()), 3)  # cp, admit, config
        # Each manifest is written anew, and the comparison reads those two files.
        for line, name in ((first, f"{label}.stage2.json"), (second, f"{label}-fp.stage2.json")):
            self.assertTrue(line.startswith(f"rm -f /ledger/{name} && "), line)
        self.assertIn(f" ddc-compare /ledger/{label}.stage2.json /ledger/{label}-fp.stage2.json ", plan.lines()[-1])
        # What `run` compares is what `plan` prints.
        self.assertEqual(plan.compared(), [("first", plan.kept_build() / HOST / "stage2", label),
                                           ("second", plan.stage2(), label + "-fp")])
        self.assertEqual(plan.first_stage2(), Path(f"/ledger/{label}-build/{HOST}/stage2"))

    def test_without_the_flags_there_is_no_second_build_and_no_seal(self):
        lines = refresh.Plan(arguments(Path("/ledger")), HOST, "c" * 40).lines()
        self.assertEqual(len(lines), 8)
        self.assertNotIn("promote-toolchain", "\n".join(lines))
        self.assertNotIn("trust-serial-command", "\n".join(lines))

    def test_a_commit_whose_script_predates_the_executor_is_sealed_bare(self):
        plan = refresh.Plan(arguments(Path("/ledger"), seal=True), HOST, "c" * 40)
        plan.serial = False
        lines = plan.lines()
        self.assertEqual(len(lines), 9)
        self.assertIn("promote-toolchain.sh --no-flip", lines[-1])
        self.assertNotIn("build-slot", lines[-1])
        self.assertNotIn("trust-serial-command", "\n".join(lines))
        self.assertEqual(plan.seal()[0], "bash")

    def test_a_caller_that_holds_a_slot_is_not_asked_to_wait_for_another(self):
        plan = refresh.Plan(arguments(Path("/ledger")), HOST, "c" * 40)
        self.assertIn("build-slot", " ".join(plan.seal()))
        held = plan.seal(held=True)
        self.assertEqual(held[0], "bash")
        self.assertNotIn("build-slot", " ".join(held))
        self.assertEqual(held[-2:], ["--no-flip", str(plan.stage2())])


class FakePlan(refresh.Plan):
    """A plan whose commands are small scripts, so the control flow runs for real."""

    record = {"rc": 0, "no_stock_evidence": True, "elapsed_s": 1}

    def script(self, body: str) -> list[str]:
        return [sys.executable, "-c", f"import sys, json, pathlib\n"
                f"pathlib.Path({str(self.ledger / 'calls')!r}).open('a').write(sys.argv[1] + '\\n')\n{body}",
                ]

    def admit(self, stage0):
        return self.script("print('{}')") + ["admit"]

    def seed_config(self):
        return self.script(f"pathlib.Path({str(self.worktree / 'bootstrap.toml')!r}).write_text('[rust]\\n')") + ["seed-config"]

    def config(self, stage0, label):
        return self.script("pathlib.Path(sys.argv[3]).write_text('[build]\\nrustc = 1\\n')") + ["config", "--out", "PATH"]

    def prepare(self, stage0):
        return self.script("print('ready')") + ["prepare"]

    def run(self, label):
        return self.script(f"print(json.dumps({self.record!r}))") + ["run"]

    # What the built Bootstrap answers x.py's probe with; None builds nothing.
    protocol: str | None = "trust-build-tree-manager-v2"

    def construct(self):
        build = "" if self.protocol is None else (
            f"b = pathlib.Path({str(self.bootstrap())!r}); b.parent.mkdir(parents=True, exist_ok=True)\n"
            f"b.write_text('#!/bin/sh\\n[ \"$*\" = \"--trust-build-tree-lock --protocol\" ] && echo {self.protocol}\\n')\n"
            "b.chmod(0o755)\n")
        # Like the real one: Bootstrap is built, then refuses the flag.
        return self.script(build + "print('error: unexpected argument --version'); raise SystemExit(1)") + ["construct"]


# The line of x.py (since fb01581fb3) that requires a v2 manager, and the start of
# 82bb867edd's own lock, which asks for none.
XPY_ASKS_V2 = 'if probe.returncode == 0 and probe.stdout == b"trust-build-tree-manager-v2\\n":\n'
XPY_LOCKS_ITSELF = 'path = os.path.join(os.path.realpath(root), ".trust-build-lock.guard")\n'
MANIFEST = ('[features]\nserial-command = ["client"]\n\n[[bin]]\nname = "trust-serial-command"\n'
            'required-features = ["serial-command"]\n')
PROMOTE_WITH = 'executor="${TRUST_TOOLCHAIN_SERIAL_COMMAND:-}"\n'
SLOT_NOW = 'usage: build-slot [--exclusive] [--wait-timeout S] [--cpus N] -- <command>\n'


class SealSourceTests(unittest.TestCase):
    """What `--seal` runs is decided by reading the commit, before anything is built."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = new_repo(Path(self.tmp.name).resolve() / "repo")

    def commit(self, **files: str | None) -> str:
        names = {"promote": "scripts/promote-toolchain.sh", "manifest": "crates/trust-resource-controller/Cargo.toml",
                 "slot": "scripts/build-slot"}
        for key, text in files.items():
            path = self.repo / names[key]
            if text is None:
                path.unlink()
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-qm", "next", "--allow-empty")
        return git(self.repo, "rev-parse", "HEAD")

    def test_a_commit_says_whether_its_script_needs_the_executor(self):
        with self.assertRaisesRegex(refresh.Refusal, "has no scripts/promote-toolchain.sh"):
            refresh.seal_uses_executor(self.repo, self.commit())
        # The pinned seed's shape: a script that reads no variable is sealed bare,
        # whatever else the commit has or lacks.
        self.assertFalse(refresh.seal_uses_executor(self.repo, self.commit(promote="ui_gate\n")))
        self.assertTrue(refresh.seal_uses_executor(
            self.repo, self.commit(promote=PROMOTE_WITH, manifest=MANIFEST, slot=SLOT_NOW)))

    def test_a_commit_that_needs_the_executor_and_cannot_supply_it_is_refused_by_name(self):
        whole = dict(promote=PROMOTE_WITH, manifest=MANIFEST, slot=SLOT_NOW)
        for change, words in (
                (dict(manifest=MANIFEST.replace('name = "trust-serial-command"', 'name = "other"')),
                 "no trust-serial-command binary"),
                (dict(manifest=MANIFEST.replace("serial-command = ", "other = ")), "no serial-command feature"),
                (dict(manifest=None), "no trust-serial-command binary.*no serial-command feature"),
                (dict(slot=None), "no scripts/build-slot"),
                (dict(slot="usage: build-slot [--exclusive [--wait-timeout S]] [--cpus N]\n"),
                 "bounds only an --exclusive wait")):
            with self.subTest(words=words):
                self.commit(**whole)
                with self.assertRaisesRegex(refresh.Refusal, words + ".*seal it by hand"):
                    refresh.seal_uses_executor(self.repo, self.commit(**change))

    def main(self, commit: str, mode: str = "plan") -> tuple[int, str, str]:
        import contextlib, io
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = refresh.main([mode, "--seal", "--ledger", str(self.repo.parent / "ledger"), "--stage0",
                                 str(self.repo.parent / "stage0"), "--repo", str(self.repo), "--commit", commit,
                                 "--host", HOST])
        return code, out.getvalue(), err.getvalue()

    def test_the_command_line_asks_the_commit_before_it_plans_or_builds(self):
        clean = {k: v for k, v in os.environ.items() if k not in (refresh.SERIAL_VARIABLE, refresh.SLOT_VARIABLE)}
        with mock.patch.dict(os.environ, clean, clear=True):
            code, out, _ = self.main(self.commit(promote="ui_gate\n"))
            self.assertEqual(code, 0)
            self.assertNotIn("build-slot", out.splitlines()[-1])
            self.assertNotIn("trust-serial-command", out)
            code, out, err = self.main(self.commit(promote=PROMOTE_WITH))
            self.assertEqual((code, out), (2, ""))
            self.assertIn("seal it by hand", err)
            whole = self.commit(promote=PROMOTE_WITH, manifest=MANIFEST, slot=SLOT_NOW)
            code, out, _ = self.main(whole)
            self.assertEqual(code, 0)
            self.assertIn("build-slot --cpus 1", out.splitlines()[-1])
            self.assertIn("--bin trust-serial-command", out.splitlines()[-2])
        # An executor the caller names is judged by the script's own rule before anything is built.
        real = self.repo.parent / "helper"
        real.write_text("#!/bin/sh\n")
        real.chmod(0o755)
        link, plain = self.repo.parent / "link", self.repo.parent / "plain"
        link.symlink_to(real)
        plain.write_text("")
        for value in (str(link), str(plain), "helper", str(self.repo.parent), str(self.repo.parent / "absent")):
            with self.subTest(value=value), mock.patch.dict(os.environ, {**clean, refresh.SERIAL_VARIABLE: value},
                                                            clear=True), \
                    mock.patch.object(refresh, "refresh", side_effect=AssertionError("a build was started")):
                code, out, err = self.main(whole, "run")
                self.assertEqual((code, out), (2, ""))
                self.assertIn(f"{refresh.SERIAL_VARIABLE}={value} is not the absolute path", err)
        # ... and what refresh() returns is the command's exit status (1: --fixed-point found a difference).
        for status in (0, 1):
            with mock.patch.dict(os.environ, {**clean, refresh.SERIAL_VARIABLE: str(real)}, clear=True), \
                    mock.patch.object(refresh, "refresh", return_value=status) as ran:
                self.assertEqual(self.main(whole, "run")[0], status)
                self.assertEqual(ran.call_count, 1)

    def test_this_tree_is_one_the_seal_step_can_serve(self):
        # The names this script reads the commit for are the ones the tree uses: a
        # rename of the variable, the feature or the binary fails here, not at a seal.
        root = Path(refresh.__file__).resolve().parents[1]
        self.assertIn(refresh.SERIAL_VARIABLE, (root / "scripts/promote-toolchain.sh").read_text())
        manifest = (root / "crates/trust-resource-controller/Cargo.toml").read_text()
        self.assertIn('name = "trust-serial-command"', manifest)
        self.assertRegex(manifest, r"(?m)^serial-command\s*=")
        self.assertNotIn(refresh.OLD_SLOT_WAIT, (root / "scripts/build-slot").read_text())


class SealPlan(FakePlan):
    """The seal's two commands as scripts that record what they were given."""

    build_exit = 0
    fetch_exit = 0
    builds_executor = True

    def serial_fetch(self):
        return self.script(f"print('fetched'); raise SystemExit({self.fetch_exit})") + ["serial-fetch"]

    def serial_build(self):
        made = "" if not self.builds_executor else (
            "e = pathlib.Path(sys.argv[2]); e.parent.mkdir(parents=True, exist_ok=True); e.write_text('executor')\n")
        return self.script(made + "import os\n"
                           f"pathlib.Path({str(self.ledger / 'build-env')!r}).write_text(json.dumps("
                           "[os.getcwd(), os.environ['PATH'], os.environ['CARGO_TARGET_DIR'], sorted(os.environ)]))\n"
                           f"print('built'); raise SystemExit({self.build_exit})") + ["serial-build", str(self.serial_command())]

    def seal(self, held=False):
        return self.script("import os\n"
                           f"pathlib.Path({str(self.ledger / 'seal-env')!r}).write_text(json.dumps("
                           "[os.getcwd(), os.environ.get('TRUST_TOOLCHAIN_SERIAL_COMMAND'), sys.argv[2]]"
                           " + ([os.environ['REFRESH_TEST_CALLER'], os.environ.get('CARGO_BUILD_JOBS')]"
                           " if 'REFRESH_TEST_CALLER' in os.environ else [])))\n"
                           f"raise SystemExit({1 if self.args.label == 'refused' else 0})") + ["seal", "held" if held else "slot"]


class SealTests(unittest.TestCase):
    """`--seal` gives promote-toolchain.sh the executor and the slot its gates need.
    Run bare, as this step did until 2026-11-12, the script refused a stage2 that
    passes every gate (the GB10, 2026-11-10)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.ledger = Path(self.tmp.name).resolve()
        (self.ledger / "w" / "crates" / "trust-resource-controller").mkdir(parents=True)
        self.addCleanup(self.tmp.cleanup)
        quiet = mock.patch.object(refresh, "say", lambda text: None)
        quiet.start()
        self.addCleanup(quiet.stop)

    def plan(self, label="r", **changes) -> SealPlan:
        plan = SealPlan(arguments(self.ledger, worktree=self.ledger / "w", label=label, seal=True), HOST, "c" * 40)
        for name, value in changes.items():
            setattr(plan, name, value)
        return plan

    def environment(self, **changes):
        base = {k: v for k, v in os.environ.items() if k not in (refresh.SERIAL_VARIABLE, refresh.SLOT_VARIABLE)}
        return mock.patch.dict(os.environ, {**base, **changes}, clear=True)

    def calls(self) -> list[str]:
        return (self.ledger / "calls").read_text().split()

    def test_the_executor_is_built_by_the_rung_and_named_to_a_seal_under_a_slot(self):
        plan = self.plan()
        with self.environment(REFRESH_TEST_CALLER="caller", CARGO_BUILD_JOBS="8"):
            refresh.seal(plan)
        self.assertEqual(self.calls(), ["serial-fetch", "serial-build", "seal"])
        cwd, path, target, names = json.loads((self.ledger / "build-env").read_text())
        self.assertEqual(cwd, str(plan.serial_crate()))
        self.assertEqual(path, f"{plan.stage2() / 'bin'}:{self.ledger / 'trap'}:/usr/bin:/bin")
        self.assertEqual(target, str(self.ledger / "r-serial-command"))
        # Built in the rung's environment: nothing of the caller's reaches it.
        # (macOS gives every process CoreFoundation's text-encoding cache, and a Python
        # that finds no C.UTF-8 locale coerces LC_CTYPE; neither is the caller's.)
        own = ("__CF_USER_TEXT_ENCODING", "LC_CTYPE") if sys.platform == "darwin" else ()
        self.assertEqual([name for name in names if name not in own],
                         ["CARGO_HOME", "CARGO_TARGET_DIR", "HOME", "LANG", "PATH",
                          "RUSTUP_AUTO_INSTALL", "RUSTUP_TOOLCHAIN", "USER"])
        # The seal is the caller's own command: it keeps the caller's environment, less
        # the job count build-slot would refuse beside `--cpus 1`.
        self.assertEqual(json.loads((self.ledger / "seal-env").read_text()),
                         [str(plan.worktree), str(plan.serial_command()), "slot", "caller", None])
        self.assertEqual((self.ledger / "r.serial-command.log").read_text(), "fetched\nbuilt\n")

    def test_a_second_seal_finds_the_executor_in_the_ledger_and_fetches_nothing(self):
        # A rerun after a refused seal: the offline build checks the executor is current,
        # and the dependency fetch, which may need the network, is not repeated.
        with self.environment():
            refresh.seal(self.plan())
            refresh.seal(self.plan())
        self.assertEqual(self.calls(), ["serial-fetch", "serial-build", "seal", "serial-build", "seal"])
        self.assertEqual((self.ledger / "r.serial-command.log").read_text(), "built\n")

    def test_an_executor_the_caller_names_is_used_as_given_and_none_is_built(self):
        with self.environment(TRUST_TOOLCHAIN_SERIAL_COMMAND="/packaged/trust-serial-command"):
            refresh.seal(self.plan())
        self.assertEqual(self.calls(), ["seal"])
        self.assertEqual(json.loads((self.ledger / "seal-env").read_text())[1], "/packaged/trust-serial-command")

    def test_a_run_that_holds_a_slot_seals_in_it(self):
        with self.environment(BUILD_SLOT_HELD="1"):
            refresh.seal(self.plan())
        self.assertEqual(json.loads((self.ledger / "seal-env").read_text())[2], "held")
        # Only the holder's own "1" is a held slot.
        with self.environment(BUILD_SLOT_HELD="0"):
            refresh.seal(self.plan())
        self.assertEqual(json.loads((self.ledger / "seal-env").read_text())[2], "slot")

    def test_an_executor_that_does_not_build_is_a_refusal_before_the_seal(self):
        for changes, step, exit_code, ran in (
                (dict(fetch_exit=101), "fetch its locked dependencies", 101, ["serial-fetch"]),
                (dict(build_exit=101), "build", 101, ["serial-fetch", "serial-build"]),
                (dict(builds_executor=False), "build", 0, ["serial-fetch", "serial-build"])):
            with self.subTest(changes=changes):
                (self.ledger / "calls").unlink(missing_ok=True)
                shutil.rmtree(self.ledger / "r-serial-command", ignore_errors=True)
                with self.environment(), self.assertRaisesRegex(
                        refresh.Refusal,
                        rf"did not {step} \(exit {exit_code}\).*nothing was sealed.*r\.serial-command\.log"):
                    refresh.seal(self.plan(**changes))
                self.assertEqual(self.calls(), ran)

    def test_a_commit_that_predates_the_executor_gets_the_bare_command_and_no_executor(self):
        plan = self.plan()
        plan.serial = False
        with self.environment():
            refresh.seal(plan)
        self.assertEqual(self.calls(), ["seal"])
        self.assertIsNone(json.loads((self.ledger / "seal-env").read_text())[1])

    def test_a_refused_seal_is_a_refusal(self):
        # Under a slot the command that ended is build-slot's, which may never have started
        # the script (no slot in time, a request it rejects): the refusal names both.
        with self.environment(), self.assertRaisesRegex(
                refresh.Refusal, r"build-slot or promote-toolchain\.sh refused the seal \(exit 1\).*was not started"):
            refresh.seal(self.plan(label="refused"))
        # In a held slot, and for a commit that predates the executor, the command is the script.
        with self.environment(BUILD_SLOT_HELD="1"), self.assertRaisesRegex(
                refresh.Refusal, r"^promote-toolchain\.sh refused the seal"):
            refresh.seal(self.plan(label="refused"))
        with self.environment(), self.assertRaisesRegex(refresh.Refusal, r"^promote-toolchain\.sh refused the seal"):
            refresh.seal(self.plan(label="refused", serial=False))


class RefreshTests(unittest.TestCase):
    def test_a_comparison_that_failed_is_not_followed_by_a_seal(self):
        # --fixed-point --seal: the two stage2 trees differ, and neither is sealed.
        with tempfile.TemporaryDirectory() as tmp:
            ledger = Path(tmp).resolve()
            (ledger / "w").mkdir()
            for verdict, sealed in ((1, []), (0, ["seal"])):
                order = []
                plan = FakePlan(arguments(ledger, worktree=ledger / "w", label="r", seal=True, fixed_point=True),
                                HOST, "c" * 40)
                plan.manifest = lambda tree, out: plan.script("pathlib.Path(sys.argv[2]).write_text('{}')") \
                    + ["manifest", str(out)]
                plan.compare = lambda: plan.script(f"print('compared'); raise SystemExit({verdict})") + ["compare"]
                with mock.patch.object(refresh, "worktree_problems", return_value=[]), \
                        mock.patch.object(refresh, "say", lambda text: None), \
                        mock.patch.object(refresh, "set_aside", lambda p: None), \
                        mock.patch.object(refresh, "rung", lambda *a: None), \
                        mock.patch.object(refresh, "seal", side_effect=lambda p: order.append("seal")):
                    if verdict:
                        with self.assertRaisesRegex(refresh.Refusal, "not sealing .* NOT identical .*Both are kept"):
                            refresh.refresh(plan)
                    else:
                        self.assertEqual(refresh.refresh(plan), 0)
                self.assertEqual(order, sealed)
                self.assertEqual(plan.file("r", "fixed-point.txt").read_text(), "compared\n")
                for name in ("r.stage2.json", "r-fp.stage2.json"):
                    (ledger / name).unlink()

    def test_a_comparison_that_failed_without_a_seal_is_exit_1(self):
        # --fixed-point alone: nothing is refused and nothing is sealed, so the exit
        # status is all that tells a caller the two stage2 trees are not identical.
        with tempfile.TemporaryDirectory() as tmp:
            ledger = Path(tmp).resolve()
            (ledger / "w").mkdir()
            for verdict, status in ((3, 1), (0, 0)):
                plan = FakePlan(arguments(ledger, worktree=ledger / "w", label="r", fixed_point=True), HOST, "c" * 40)
                plan.manifest = lambda tree, out: plan.script("pathlib.Path(sys.argv[2]).write_text('{}')") \
                    + ["manifest", str(out)]
                plan.compare = lambda: plan.script(f"print('compared'); raise SystemExit({verdict})") + ["compare"]
                with mock.patch.object(refresh, "worktree_problems", return_value=[]), \
                        mock.patch.object(refresh, "say", lambda text: None), \
                        mock.patch.object(refresh, "set_aside", lambda p: None), \
                        mock.patch.object(refresh, "rung", lambda *a: None), \
                        mock.patch.object(refresh, "seal") as sealed:
                    self.assertEqual(refresh.refresh(plan), status)
                sealed.assert_not_called()
                self.assertEqual(plan.file("r", "fixed-point.txt").read_text(), "compared\n")

    def test_a_refresh_seals_only_when_asked_and_only_after_the_rung(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = Path(tmp).resolve()
            (ledger / "w").mkdir()
            for asked in (False, True):
                order = []
                plan = refresh.Plan(arguments(ledger, worktree=ledger / "w", label="r", seal=asked), HOST, "c" * 40)
                with mock.patch.object(refresh, "worktree_problems", return_value=[]), \
                        mock.patch.object(refresh, "rung", side_effect=lambda *a: order.append("rung")), \
                        mock.patch.object(refresh, "seal", side_effect=lambda p: order.append("seal")):
                    self.assertEqual(refresh.refresh(plan), 0)
                self.assertEqual(order, ["rung", "seal"] if asked else ["rung"])


def tiny_stage2(top: Path) -> None:
    """What a build leaves at its stage2 path, in five entries with a build's modes."""
    for directory in (top, top / "bin", top / "lib"):
        directory.mkdir(parents=True)
        directory.chmod(0o755)
    for name, mode in (("bin/trustc", 0o755), ("lib/librustc_driver.so", 0o644)):
        (top / name).write_text(name)
        (top / name).chmod(mode)
    (top / "lib" / "libdriver.so").symlink_to("librustc_driver.so")


class FixedPointTests(unittest.TestCase):
    """`--fixed-point` compares each build's own stage2, and says why when it cannot.

    Measured 2026-11-12 on aarch64 Linux, two builds of 6762badf3c: the first build's
    manifest was taken from the read-only copy the second build is built from, a
    manifest records each entry's mode, and 559 of 561 entries with the same bytes
    were reported as differing. The manifest command itself had failed first, under
    `check=True`: a traceback after the second build."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.ledger = Path(self.tmp.name).resolve()
        (self.ledger / "w").mkdir()
        self.addCleanup(self.tmp.cleanup)
        # set_aside removes every write bit of its copy; they come back before the directory goes.
        self.addCleanup(lambda: subprocess.run(["chmod", "-R", "u+w", str(self.ledger)], check=True))
        self.said: list[str] = []

    def patched(self, rung, plan_class=refresh.Plan, **changes):
        """refresh() with a rung that is `rung` and everything after it real."""
        plan = plan_class(arguments(self.ledger, worktree=self.ledger / "w", label="r", fixed_point=True, **changes),
                          HOST, "c" * 40)
        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(refresh, "worktree_problems", return_value=[]))
        stack.enter_context(mock.patch.object(refresh, "say", self.said.append))
        stack.enter_context(mock.patch.object(refresh, "rung", side_effect=rung))
        self.sealed = stack.enter_context(mock.patch.object(refresh, "seal"))
        self.addCleanup(stack.close)
        return plan

    def mint(self, *words) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(refresh.MINT_SUPPORT), *map(str, words)],
                              capture_output=True, text=True)

    def test_each_builds_own_tree_is_compared_and_not_the_read_only_copy(self):
        # Every command is the real one: set_aside's cp -a and chmod -R a-w, and
        # mint_seed_support.py's stage2-manifest and ddc-compare. Only the two builds
        # are stand-ins: each leaves the same five entries at the one stage2 path.
        built = []

        def rung(plan, label, stage0):
            built.append((label, stage0))
            tiny_stage2(plan.stage2())

        plan = self.patched(rung)
        status = refresh.refresh(plan)
        report = plan.file("r", "fixed-point.txt").read_text()
        self.assertEqual(status, 0, f"two builds of the same five entries were not reported identical:\n{report}")
        self.assertRegex(report, r"\A[0-9a-f]{64}\n\Z")
        self.assertIn(f"fixed point: the two stage2 trees are identical ({plan.file('r', 'fixed-point.txt')})", self.said)
        self.assertEqual(built, [("r", plan.stage0), ("r-fp", plan.kept_stage2())])
        # What was read: the first build where set_aside moved it, with its own modes.
        first, second = (json.loads(plan.file(label, "stage2.json").read_text()) for label in ("r", "r-fp"))
        self.assertEqual(first, second)
        self.assertEqual({record["path"]: record.get("mode") for record in first["records"]},
                         {"bin": 0o755, "bin/trustc": 0o755, "lib": 0o755, "lib/librustc_driver.so": 0o644,
                          "lib/libdriver.so": None})
        self.assertEqual(stat.S_IMODE((plan.first_stage2() / "bin/trustc").stat().st_mode), 0o755)
        # Control, with the same two commands: the copy the second build was built from
        # holds the same bytes and differs from that build in every entry that has a mode.
        copy = plan.kept_stage2()
        self.assertEqual(stat.S_IMODE((copy / "bin/trustc").stat().st_mode), 0o555)
        self.assertEqual((copy / "bin/trustc").read_bytes(), (plan.stage2() / "bin/trustc").read_bytes())
        made = self.mint("stage2-manifest", copy, self.ledger / "copy.json")
        self.assertEqual((made.returncode, made.stderr), (0, ""))
        control = self.mint("ddc-compare", self.ledger / "copy.json", plan.file("r-fp", "stage2.json"))
        self.assertEqual(control.returncode, 1, control.stdout)
        for path in ("bin", "bin/trustc", "lib", "lib/librustc_driver.so"):
            self.assertIn(f"\n  differs: {path}\n", control.stderr)
        self.assertEqual(control.stderr.count("\n  differs: "), 4, control.stderr)
        self.assertNotIn("libdriver.so", control.stderr)  # a symlink has no mode

    def test_a_tree_that_is_not_there_is_refused_in_the_comparers_own_words_and_the_run_resumes(self):
        # The real commands again. The second build left nothing (a stand-in for any
        # reason the comparer cannot read a tree): no traceback, no manifest, no seal.
        built = []

        def rung(plan, label, stage0):
            if label == "r" and not built:
                tiny_stage2(plan.stage2())
            built.append(label)  # a rung whose record is in the ledger is not built again

        plan = self.patched(rung, seal=True)
        with self.assertRaises(refresh.Refusal) as refused:
            refresh.refresh(plan)
        words = str(refused.exception)
        self.assertIn(f"no manifest of the second build's stage2, {plan.stage2()}, could be written", words)
        self.assertIn(f" stage2-manifest {plan.stage2()} {plan.file('r-fp', 'stage2.json')}.partial` exited 1", words)
        self.assertIn(f"the last line it printed on stderr is: error: stage2 sysroot is unavailable: {plan.stage2()}",
                      words)
        self.assertIn(f"Both builds are kept (the first in {plan.kept_build()}, the second in {plan.worktree / 'build'}) "
                      "and neither is built again", words)
        self.assertIn("the same command line resumes at the comparison", words)
        self.assertIn("were not compared and nothing was sealed", words)
        self.sealed.assert_not_called()
        self.assertEqual(sorted(p.name for p in self.ledger.glob("r-fp.stage2.json*")), [])
        self.assertFalse(plan.file("r", "fixed-point.txt").exists())
        # The cause removed, the same call compares and seals; the first build is not touched.
        before = (plan.first_stage2() / "bin/trustc").stat()
        tiny_stage2(plan.stage2())
        self.assertEqual(refresh.refresh(plan), 0)
        self.assertEqual(self.sealed.call_count, 1)
        self.assertEqual(built, ["r", "r-fp"] * 2)
        after = (plan.first_stage2() / "bin/trustc").stat()
        self.assertEqual((before.st_ino, before.st_mtime_ns, before.st_mode), (after.st_ino, after.st_mtime_ns, after.st_mode))

    def stub(self, plan, fails=None, exits=1):
        """Manifest and compare commands as scripts. The manifest of `fails` half-writes
        its output, says why on stderr and exits `exits`; or, with `exits=0`, writes
        nothing, says nothing and exits 0."""
        asked = []

        def manifest(tree, out):
            asked.append((tree, out))
            if tree != fails:
                body = f"pathlib.Path(sys.argv[2]).write_text({str(tree)!r})"
            elif exits:
                body = ("pathlib.Path(sys.argv[2]).write_text('{')\n"
                        "print('Traceback (most recent call last):\\n  File x, line 1\\n"
                        "OSError: [Errno 28] No space left on device\\n\\n', file=sys.stderr)\n"
                        f"raise SystemExit({exits})")
            else:
                body = "pass"
            return plan.script(body) + ["manifest", str(out)]

        plan.manifest = manifest
        plan.compare = lambda: plan.script("print('compared')") + ["compare"]
        return asked

    def test_a_manifest_command_that_fails_is_a_refusal_and_leaves_no_manifest(self):
        for which, label in (("first", "r"), ("second", "r-fp")):
            for exits, how in ((1, "exited 1"), (0, "exited 0 and wrote no manifest")):
                with self.subTest(which=which, exits=exits):
                    plan = self.patched(lambda *a: None, FakePlan, seal=True)
                    tree = dict((which, tree) for which, tree, _ in plan.compared())[which]
                    self.stub(plan, fails=tree, exits=exits)
                    # An earlier comparison's files: a verdict and both manifests.
                    for name in ("r.stage2.json", "r-fp.stage2.json", "r.fixed-point.txt"):
                        (self.ledger / name).write_text("left by an earlier comparison\n")
                    (self.ledger / "calls").unlink(missing_ok=True)
                    with mock.patch.object(refresh, "set_aside", lambda p: None), \
                            self.assertRaises(refresh.Refusal) as refused:
                        refresh.refresh(plan)
                    words = str(refused.exception)
                    self.assertIn(f"no manifest of the {which} build's stage2, {tree}, could be written", words)
                    self.assertIn(f"` {how}, and the last line it printed on stderr is: ", words)
                    self.assertIn("is: OSError: [Errno 28] No space left on device\n" if exits
                                  else "is: (it printed nothing on stderr)\n", words)
                    self.assertIn("Both builds are kept", words)
                    self.assertIn("the same command line resumes at the comparison", words)
                    self.sealed.assert_not_called()
                    # Neither a finished nor a half-written manifest of that tree, no
                    # verdict of an earlier comparison, and no comparison of this one.
                    self.assertEqual(sorted(p.name for p in self.ledger.glob(f"{label}.stage2.json*")), [])
                    self.assertFalse((self.ledger / "r.fixed-point.txt").exists())
                    self.assertNotIn("compare", (self.ledger / "calls").read_text().split())

    def test_both_manifests_are_written_anew_on_every_comparison(self):
        plan = self.patched(lambda *a: None, FakePlan)
        asked = self.stub(plan)
        for name in ("r.stage2.json", "r-fp.stage2.json"):
            (self.ledger / name).write_text("left by an earlier comparison, of the read-only copy\n")
        with mock.patch.object(refresh, "set_aside", lambda p: None):
            for _ in range(2):
                self.assertEqual(refresh.refresh(plan), 0)
        self.assertEqual((self.ledger / "calls").read_text().split(), ["manifest", "manifest", "compare"] * 2)
        # Of each build's own tree, written beside the final name and moved there.
        self.assertEqual(asked, [(plan.first_stage2(), self.ledger / "r.stage2.json.partial"),
                                 (plan.stage2(), self.ledger / "r-fp.stage2.json.partial")] * 2)
        self.assertEqual((self.ledger / "r.stage2.json").read_text(), str(plan.first_stage2()))
        self.assertEqual((self.ledger / "r-fp.stage2.json").read_text(), str(plan.stage2()))
        self.assertEqual(sorted(p.name for p in self.ledger.glob("*.partial")), [])


class ComparerStartsTests(unittest.TestCase):
    """`--fixed-point` asks whether mint_seed_support.py starts before anything is built."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.repo = new_repo(self.root / "repo")

    def main(self, mode: str, *flags: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = refresh.main([mode, *flags, "--ledger", str(self.root / "ledger"), "--stage0",
                                 str(self.root / "stage0"), "--repo", str(self.repo), "--host", HOST])
        return code, out.getvalue(), err.getvalue()

    def test_a_comparer_that_does_not_start_is_refused_before_anything_is_cloned_or_built(self):
        # The measured shape: the program in a tree without the file it loads at start.
        lone = self.root / "elsewhere" / "scripts" / "mint_seed_support.py"
        lone.parent.mkdir(parents=True)
        shutil.copy(refresh.MINT_SUPPORT, lone)
        for mode in ("plan", "run"):
            with self.subTest(mode=mode), mock.patch.object(refresh, "MINT_SUPPORT", lone), \
                    mock.patch.object(refresh, "clone_rung", side_effect=AssertionError("a clone was started")), \
                    mock.patch.object(refresh, "rung", side_effect=AssertionError("a rung was started")), \
                    mock.patch.object(refresh, "set_aside", side_effect=AssertionError("a build was set aside")):
                code, out, err = self.main(mode, "--fixed-point")
                self.assertEqual((code, out), (2, ""))
                self.assertTrue(err.startswith("linux-refresh: refused: --fixed-point compares the two builds with "
                                               f"{lone}, and that program does not start from this checkout: `"), err)
                self.assertIn(f" {lone} --help` exited 1, and the last line it printed on stderr is: "
                              "FileNotFoundError: ", err)
                self.assertIn(str(lone.parents[1] / "src/bootstrap/stage0_identity.py"), err)
                self.assertIn("This is asked before anything is cloned or built because the comparison comes last", err)
                self.assertNotIn("Traceback", err)
                self.assertFalse((self.root / "ledger").exists())
                # Without --fixed-point the program is not needed and is not asked.
                code, out, err = self.main("plan")
                self.assertEqual((code, err), (0, ""))

    def test_this_checkouts_comparer_starts(self):
        code, out, err = self.main("plan", "--fixed-point")
        self.assertEqual((code, err), (0, ""))
        self.assertIn(" ddc-compare ", out.splitlines()[-1])


class RungTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.ledger = Path(self.tmp.name).resolve()
        (self.ledger / "w").mkdir()
        (self.ledger / "w" / "x.py").write_text(XPY_ASKS_V2)
        patcher = mock.patch.object(refresh, "write_traps", lambda ledger: None)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.addCleanup(self.tmp.cleanup)

    def plan(self, **record) -> FakePlan:
        plan = FakePlan(arguments(self.ledger, worktree=self.ledger / "w", label="r"), HOST, "c" * 40)
        plan.record = {**FakePlan.record, **record}
        return plan

    def calls(self) -> list[str]:
        return (self.ledger / "calls").read_text().split()

    def test_a_clean_rung_leaves_its_files_and_is_not_repeated(self):
        with mock.patch.object(refresh, "say", lambda text: None):
            refresh.rung(self.plan(), "r", self.ledger / "stage0")
            self.assertEqual(self.calls(), ["admit", "seed-config", "config", "prepare", "construct", "run"])
            self.assertIn("unexpected argument", (self.ledger / "r.bootstrap.log").read_text())
            config = (self.ledger / "r.bootstrap.toml").read_text()
            self.assertTrue(config.startswith("[build]\nrustc = 1\n"))
            self.assertTrue(config.endswith("jobs = 3\n"))
            self.assertEqual(json.loads((self.ledger / "r.run.json").read_text())["rc"], 0)
            refresh.rung(self.plan(), "r", self.ledger / "stage0")
            self.assertEqual(self.calls().count("run"), 1)

    def test_a_rung_that_is_not_clean_is_refused_now_and_on_the_next_run(self):
        with mock.patch.object(refresh, "say", lambda text: None):
            with self.assertRaisesRegex(refresh.Refusal, "not a clean rung"):
                refresh.rung(self.plan(no_stock_evidence=False), "r", self.ledger / "stage0")
            with self.assertRaisesRegex(refresh.Refusal, "did not finish clean"):
                refresh.rung(self.plan(), "r", self.ledger / "stage0")
            self.assertEqual(self.calls().count("run"), 1)

    def test_bootstrap_is_constructed_only_when_the_tree_has_no_v2_manager(self):
        with mock.patch.object(refresh, "say", lambda text: None):
            plan = self.plan()
            refresh.construct_bootstrap(plan, "r")
            self.assertEqual(self.calls(), ["construct"])
            # The step's exit status was 1; the binary it left is what is judged.
            self.assertTrue(refresh.speaks_manager_v2(plan.bootstrap(), plan.worktree))
            refresh.construct_bootstrap(plan, "r")
            self.assertEqual(self.calls(), ["construct"])  # a tree that has one is left alone

    def test_an_x_py_that_asks_for_no_manager_gets_none_and_the_rung_runs(self):
        # 82bb867edd's x.py takes the lock itself, and its Bootstrap refuses the probe.
        (self.ledger / "w" / "x.py").write_text(XPY_LOCKS_ITSELF)
        for protocol in (None, "trust-build-tree-manager-v1"):
            with self.subTest(protocol=protocol), mock.patch.object(refresh, "say", lambda text: None):
                for name in ("calls", "r.run.json", "r.admission.json", "r.bootstrap.toml", "w/bootstrap.toml"):
                    (self.ledger / name).unlink(missing_ok=True)
                plan = self.plan()
                plan.protocol = protocol
                plan.bootstrap().unlink(missing_ok=True)
                self.assertFalse(refresh.asks_manager_v2(plan.worktree))
                refresh.rung(plan, "r", self.ledger / "stage0")
                self.assertEqual(self.calls(), ["admit", "seed-config", "config", "prepare", "run"])
                self.assertFalse((self.ledger / "r.bootstrap.log").exists())
                self.assertEqual(json.loads((self.ledger / "r.run.json").read_text())["rc"], 0)

    def test_an_unreadable_x_py_is_refused_before_anything_runs(self):
        (self.ledger / "w" / "x.py").unlink()
        with mock.patch.object(refresh, "say", lambda text: None):
            with self.assertRaisesRegex(refresh.Refusal, r"x\.py cannot be read .*build-tree manager is not known"):
                refresh.construct_bootstrap(self.plan(), "r")
        self.assertFalse((self.ledger / "calls").exists())

    def test_a_rung_is_refused_before_x_py_when_no_v2_manager_results(self):
        for protocol in (None, "trust-build-tree-manager-v1"):
            with self.subTest(protocol=protocol), mock.patch.object(refresh, "say", lambda text: None):
                plan = self.plan()
                plan.protocol = protocol
                plan.bootstrap().unlink(missing_ok=True)
                with self.assertRaisesRegex(refresh.Refusal, "not a protocol-v2 build-tree manager"):
                    refresh.rung(plan, "r", self.ledger / "stage0")
                self.assertNotIn("run", self.calls())
                self.assertFalse((self.ledger / "r.run.json").exists())

    def test_lld_is_written_only_for_a_stage0_that_ships_its_own_linker(self):
        stage0 = self.ledger / "stage0"
        with mock.patch.object(refresh, "say", lambda text: None):
            plan = self.plan()
            plan.args.lld = True
            with self.assertRaisesRegex(refresh.Refusal, "rust-lld"):
                refresh.rung(plan, "r", stage0)
            self.assertFalse((self.ledger / "r.bootstrap.toml").exists())
            for path in refresh.self_contained_lld(stage0, HOST):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("")
            refresh.rung(plan, "r", stage0)
        config = (self.ledger / "r.bootstrap.toml").read_text()
        self.assertTrue(config.endswith('[rust]\nbootstrap-override-lld = "self-contained"\n'))
        self.assertLess(config.index("jobs = 3"), config.index("[rust]"))  # jobs stays in [build]
        self.assertNotIn("override-lld", refresh.config_tail(3, False))

    def test_a_failed_command_leaves_no_file_under_the_finished_name(self):
        out = self.ledger / "step.json"
        code = refresh.to_file([sys.executable, "-c", "print('half'); raise SystemExit(3)"], out)
        self.assertEqual(code, 3)
        self.assertFalse(out.exists())
        self.assertEqual((self.ledger / "step.json.partial").read_text(), "half\n")
        self.assertEqual(refresh.to_file([sys.executable, "-c", "print('whole')"], out), 0)
        self.assertEqual(out.read_text(), "whole\n")


class SetAsideTests(unittest.TestCase):
    def test_the_first_build_is_kept_and_only_the_native_outputs_stay(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = Path(tmp).resolve()
            build = ledger / "w" / "build" / HOST
            for path in ("stage2/bin/trustc", "llvm/bin/llvm-config", "lld/bin/lld", "stage1-rustc/x.rlib"):
                (build / path).parent.mkdir(parents=True, exist_ok=True)
                (build / path).write_text(path)
            plan = refresh.Plan(arguments(ledger, worktree=ledger / "w", label="r"), HOST, "c" * 40)
            refresh.set_aside(plan)
            kept = ledger / "r-stage2" / "bin" / "trustc"
            self.assertEqual(kept.read_text(), "stage2/bin/trustc")
            self.assertEqual(stat.S_IMODE(kept.stat().st_mode) & 0o222, 0)
            self.assertTrue((ledger / "r-build" / HOST / "stage1-rustc" / "x.rlib").is_file())
            self.assertEqual(sorted(p.name for p in build.iterdir()), ["lld", "llvm"])
            self.assertEqual((build / "llvm/bin/llvm-config").read_text(), "llvm/bin/llvm-config")
            refresh.set_aside(plan)  # repeating it changes nothing
            self.assertEqual(sorted(p.name for p in build.iterdir()), ["lld", "llvm"])
            subprocess.run(["chmod", "-R", "u+w", str(ledger / "r-stage2")], check=True)

    def test_a_copy_that_fails_is_a_refusal_that_names_the_command_and_can_be_repeated(self):
        # It was `check=True`: `cp`'s one line and then this script's traceback,
        # after the first build of the commit.
        with tempfile.TemporaryDirectory() as tmp:
            ledger = Path(tmp).resolve()
            plan = refresh.Plan(arguments(ledger, worktree=ledger / "w", label="r"), HOST, "c" * 40)
            (ledger / "w" / "build" / HOST).mkdir(parents=True)  # a build with no stage2 in it
            with self.assertRaises(refresh.Refusal) as refused:
                refresh.set_aside(plan)
            said = str(refused.exception)
            self.assertIn(f"{plan.stage2()} could not be copied to {ledger / 'r-stage2'}", said)
            self.assertIn(f"`cp -a {plan.stage2()} {ledger / 'r-stage2.partial'}` exited 1", said)
            self.assertFalse((ledger / "r-stage2").exists(), "a copy that failed is under its final name")
            self.assertFalse((ledger / "r-build").exists(), "the build tree was moved before its stage2 was kept")
            # Once the cause is removed the same call finishes the job.
            (plan.stage2() / "bin").mkdir(parents=True)
            (plan.stage2() / "bin" / "trustc").write_text("x")
            refresh.set_aside(plan)
            self.assertEqual((ledger / "r-stage2" / "bin" / "trustc").read_text(), "x")
            subprocess.run(["chmod", "-R", "u+w", str(ledger / "r-stage2")], check=True)

    def test_a_command_that_fails_is_said_with_how_it_ended(self):
        with self.assertRaises(refresh.Refusal) as refused:
            refresh.must([sys.executable, "-c", "import sys; sys.exit(7)"], "the thing being done")
        self.assertRegex(str(refused.exception), r"^the thing being done: `.* -c 'import sys; sys\.exit\(7\)'` "
                                                 r"exited 7; what it said is above$")
        with self.assertRaises(refresh.Refusal) as refused:
            refresh.must([sys.executable, "-c", "import os, signal; os.kill(os.getpid(), signal.SIGKILL)"], "it")
        self.assertIn("was killed by signal 9", str(refused.exception))
        refresh.must([sys.executable, "-c", "pass"], "nothing is raised for exit 0")


if __name__ == "__main__":
    unittest.main()
