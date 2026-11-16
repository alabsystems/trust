#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "prewarm_push_test.py requires Python 3.11+" >&2
exit 2
":"""
from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 prewarm_push_test.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here. The fixture
# hands prewarm_push.sh PYTHON=sys.executable, and the script refuses anything under 3.11 by
# design; without this re-exec every test failed at that refusal on such a machine, which read
# as seven landing-orchestration failures (comprehensive-20261112T055926Z).
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("prewarm_push_test.py requires Python 3.11+; none found on PATH")
# Local-Git integration regressions for automatic landing retries.
#
# The Git transport, merge, hooks, and push are real. Compiler gates, build-slot
# admission and the source lease are explicit synthetic fixtures: these tests
# exercise orchestration and confer no compiler, admission, or release credit.
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest

REPO = Path(__file__).resolve().parents[2]

class LandingFixture:
    def __init__(self, case: unittest.TestCase, mode: str = "race"):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-prewarm-git-")
        case.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.local = self.root / "local"
        self.rival = self.root / "rival"
        self.remote = self.root / "origin.git"
        self.logs = self.root / "landing-logs"
        self.home = self.root / "home"
        self.home.mkdir()
        self.mode = self.root / "mode"
        self.mode.write_text(mode)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        for name in ("python3", "python3.14"):
            (self.bin / name).symlink_to(Path(sys.executable).resolve())
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("GIT_", "BUILD_SLOT_", "TRUST_BUILD_LOCK"))}
        self.env.update(HOME=str(self.home), XDG_CONFIG_HOME=str(self.home / "xdg"),
                        GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_SYSTEM=os.devnull,
                        GIT_CONFIG_GLOBAL=os.devnull, GIT_ATTR_NOSYSTEM="1",
                        GIT_AUTHOR_NAME="fixture", GIT_COMMITTER_NAME="fixture",
                        GIT_AUTHOR_EMAIL="fixture@example.invalid",
                        GIT_COMMITTER_EMAIL="fixture@example.invalid",
                        GIT_TERMINAL_PROMPT="0", GIT_TRACE=str(self.root / "git.trace"),
                        PATH=str(self.bin) + os.pathsep + os.environ.get("PATH", ""),
                        PYTHON=str(Path(sys.executable).resolve()),
                        PYTHONDONTWRITEBYTECODE="1", FIXTURE_ROOT=str(self.root))
        self.git(self.root, "init", "--bare", "--initial-branch=main", str(self.remote))
        seed = self.root / "seed"
        self.git(self.root, "init", "--initial-branch=main", str(seed))
        for name in ("scripts/prewarm_push.sh",):
            target = seed / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO / name, target)
        self.write(seed / "scripts/build-slot", """\
            #!/usr/bin/env python3
            # SYNTHETIC admission only: no real build or host budget is exercised.
            import os, sys
            assert sys.argv[1] == "--", sys.argv
            os.environ["BUILD_SLOT_HELD"] = "1"
            os.execvp(sys.argv[2], sys.argv[2:])
            """)
        self.write(self.bin / "targo", """\
            #!/bin/sh
            # SYNTHETIC source lease only, private to this no-compiler fixture.
            [ "$1:$2:$3" = trust:repo:lock ] || exit 2
            shift 3
            case "$1" in acquire) printf 'token=fixture-only-token\\n';; release|status) exit 0;; *) exit 2;; esac
            """)
        self.env["TARGO"] = str(self.bin / "targo")
        self.write(seed / "scripts/submodule_sync.sh", "#!/bin/sh\n# No submodules in this fixture.\nexit 0\n")
        # This must never be invoked by development-main publication.
        self.write(seed / "scripts/land_gate.py", "raise SystemExit('unexpected broad gate')\n")
        self.write(seed / "scripts/hooks/pre-push", self.hook_script())
        (seed / "initial.txt").write_text("initial\n")
        self.git(seed, "add", ".")
        self.git(seed, "commit", "-m", "synthetic fixture seed")
        self.git(seed, "remote", "add", "origin", str(self.remote))
        self.git(seed, "push", "origin", "HEAD:refs/heads/main")
        self.initial = self.git(seed, "rev-parse", "HEAD").stdout.strip()
        self.git(self.root, "clone", str(self.remote), str(self.local))
        self.git(self.root, "clone", str(self.remote), str(self.rival))
        self.git(self.local, "checkout", "-b", "work")
        self.git(self.local, "config", "core.hooksPath", "scripts/hooks")
        (self.local / "local.txt").write_text("local work\n")
        self.git(self.local, "add", "local.txt")
        self.git(self.local, "commit", "-m", "local work")
        self.first_head = self.git(self.local, "rev-parse", "HEAD").stdout.strip()
        (self.rival / "rival.txt").write_text("independent main work\n")
        self.git(self.rival, "add", "rival.txt")
        self.git(self.rival, "commit", "-m", "rival main work")
        self.rival_head = self.git(self.rival, "rev-parse", "HEAD").stdout.strip()

    @staticmethod
    def write(path: Path, body: str):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(body))
        path.chmod(0o755)

    def git(self, at: Path, *args: str, check=True):
        return subprocess.run(["git", "-C", str(at), *args], env=self.env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              check=check, timeout=30)

    @staticmethod
    def hook_script():
        return "#!/usr/bin/env python3\n" + textwrap.dedent('''\
            import json, os, pathlib, subprocess, sys
            root = pathlib.Path(os.environ["FIXTURE_ROOT"])
            calls = root / "hook-calls.jsonl"
            old = calls.read_text().splitlines() if calls.exists() else []
            with calls.open("a") as stream:
                stream.write(json.dumps({"argv": sys.argv[1:], "refs": sys.stdin.read(), "home": os.environ.get("HOME")}) + "\\n")
            mode = (root / "mode").read_text()
            if not old and mode in ("race", "red-with-move", "red-stale-with-move"):
                subprocess.run(["git", "-C", str(root / "rival"), "push", "origin", "HEAD:refs/heads/main"], check=True)
                if mode == "race":
                    print("PRE-PUSH: STALE — every ref this push updates moved on the destination while this hook ran:")
                    sys.exit(2)
            if mode == "red-stale-with-move":
                print("PRE-PUSH: STALE — synthetic stale text with a genuine failure")
            if mode == "rewind":
                target = (root / "rewritten-main").read_text().strip()
                subprocess.run(["git", "-C", str(root / "origin.git"), "update-ref", "refs/heads/main", target], check=True)
                print("PRE-PUSH: STALE — synthetic destination history rewrite")
                sys.exit(2)
            if mode == "stale-unchanged":
                print("PRE-PUSH: STALE — destination has not actually advanced")
                sys.exit(2)
            if mode in ("red", "red-with-move", "red-stale-with-move"):
                print("PRE-PUSH: RED — explicit synthetic hook failure")
                sys.exit(1)
            print("PRE-PUSH: GREEN")
            ''')

    def run(self, *extra: str):
        return subprocess.run(["bash", "scripts/prewarm_push.sh", "--log-dir", str(self.logs),
                               "--base", self.initial, *extra], cwd=self.local, env=self.env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=45)

    def calls(self, name="gate-calls.jsonl"):
        path = self.root / name
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

class PrewarmLandingTests(unittest.TestCase):
    def test_new_compiled_inputs_require_a_focused_build_before_push(self):
        fixture = LandingFixture(self, "race")
        path = fixture.rival / "compiler/changed.rs"
        path.parent.mkdir()
        path.write_text("pub fn added() {}\n")
        fixture.git(fixture.rival, "add", "compiler/changed.rs")
        fixture.git(fixture.rival, "commit", "-m", "new compiled input")
        remote_head = fixture.git(fixture.rival, "rev-parse", "HEAD").stdout.strip()
        result = fixture.run()
        self.assertEqual(result.returncode, 4, result.stdout)
        self.assertIn("build the changed source", result.stdout)
        self.assertEqual(fixture.git(fixture.remote, "rev-parse", "main").stdout.strip(), remote_head)
        self.assertEqual(len(fixture.calls("hook-calls.jsonl")), 1)
        self.assertTrue((fixture.local / "compiler/changed.rs").is_file())

    def test_main_advances_during_hook_without_repeating_builds(self):
        fixture = LandingFixture(self, "race")
        result = fixture.run()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(len(fixture.calls("hook-calls.jsonl")), 2)
        self.assertFalse((fixture.logs / "landing-state.json").exists())
        self.assertEqual(fixture.calls(), [])
        self.assertEqual(fixture.calls("warm-calls.jsonl"), [])
        remote = fixture.git(fixture.remote, "rev-parse", "main").stdout.strip()
        self.assertEqual(remote, fixture.git(fixture.local, "rev-parse", "HEAD").stdout.strip())
        for head in (fixture.first_head, fixture.rival_head):
            self.assertEqual(fixture.git(fixture.local, "merge-base", "--is-ancestor", head, remote, check=False).returncode, 0)
        trace = (fixture.root / "git.trace").read_text()
        for forbidden in ("--no-verify", "--force", " reset ", " clean ", "land_gate.py", "fixture_warm.py"):
            self.assertNotIn(forbidden, trace)

    def test_network_home_supplies_real_merge_identity(self):
        fixture = LandingFixture(self, "race")
        home = fixture.root / "network-home"
        home.mkdir()
        (home / ".gitconfig").write_text("[user]\n name = network fixture\n email = network@example.invalid\n")
        for key in ("GIT_AUTHOR_NAME", "GIT_AUTHOR_EMAIL", "GIT_COMMITTER_NAME", "GIT_COMMITTER_EMAIL", "GIT_CONFIG_GLOBAL"):
            fixture.env.pop(key, None)
        result = fixture.run("--network-home", str(home))
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertTrue(all(row["home"] == str(home) for row in fixture.calls("hook-calls.jsonl")))
        self.assertEqual(fixture.git(fixture.local, "show", "-s", "--format=%an <%ae>", "HEAD").stdout.strip(), "network fixture <network@example.invalid>")

    def test_genuine_hook_red_stops_even_when_main_advances(self):
        fixture = LandingFixture(self, "red-with-move")
        result = fixture.run()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(len(fixture.calls("hook-calls.jsonl")), 1)
        self.assertEqual(fixture.git(fixture.remote, "rev-parse", "main").stdout.strip(), fixture.rival_head)
        self.assertEqual(fixture.git(fixture.local, "rev-parse", "HEAD").stdout.strip(), fixture.first_head)

    def test_real_red_wins_over_stale_text(self):
        fixture = LandingFixture(self, "red-stale-with-move")
        result = fixture.run()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(len(fixture.calls("hook-calls.jsonl")), 1)
        self.assertIn("PRE-PUSH: RED", result.stdout)

    def test_runs_with_no_arguments(self):
        # Every other case passes options. With none, ORIGINAL_ARGS is an empty
        # array, and macOS /bin/bash 3.2 calls "${ORIGINAL_ARGS[@]}" unbound
        # under set -u: the documented bare invocation died before any push
        # (2026-11-04, m113).
        fixture = LandingFixture(self, "green")
        result = subprocess.run(["bash", "scripts/prewarm_push.sh"], cwd=fixture.local, env=fixture.env,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=45)
        self.assertNotIn("unbound variable", result.stdout)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(len(fixture.calls("hook-calls.jsonl")), 1)
        self.assertEqual(fixture.git(fixture.remote, "rev-parse", "main").stdout.strip(),
                         fixture.git(fixture.local, "rev-parse", "HEAD").stdout.strip())

    def test_stale_text_without_actual_main_advance_does_not_retry(self):
        fixture = LandingFixture(self, "stale-unchanged")
        result = fixture.run()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(len(fixture.calls("hook-calls.jsonl")), 1)
        self.assertEqual(fixture.git(fixture.remote, "rev-parse", "main").stdout.strip(), fixture.initial)


if __name__ == "__main__":
    unittest.main()
