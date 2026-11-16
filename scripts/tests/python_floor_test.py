#!/usr/bin/env python3
"""A script that needs Python 3.11 must reach 3.11 however it is started.

HOST-01B. Plain `python3` is 3.9.6 on this machine (macOS CommandLineTools)
while python3.12/3.14 are installed, and the stdlib `tomllib` is 3.11+. A
script that imports `tomllib` with no `tomli` fallback therefore has an
interpreter FLOOR, and it must enforce that floor itself, because it is started
three ways:

  * executed (`scripts/x.py`, shebang)   -> `#!/bin/sh` polyglot block re-execs;
  * `sh scripts/x.py`                   -> the same block;
  * `python3 scripts/x.py`              -> Python reads the block as a string,
                                           so a Python-side re-exec must follow.

Until 2026-09-23 check_dependency_cycle_anchor.py had only the sh half (its
`python3` invocation died with "requires Python 3.11+"), four scripts had
neither half, and four harness rows ran floor scripts as `python3 <script>`.

What this test measures, per floor script: start it under an interpreter
older than 3.11 with a >=3.11 one on PATH, and record (through a
`sitecustomize` hook, and through the >=3.11 one's own launcher for a start
that isolates itself from the hook) every interpreter that starts. The LAST
one must be >=3.11. It also refuses a harness row that runs a floor script through bare
`python3`, and a floor helper whose driver would hand it a bare `python3`.
"""
from __future__ import annotations

import ast
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SCRIPT_DIRS = ("scripts/", "tools/", "tests/upstream-rust/")
HARNESS = REPO / "tests" / "run_trust_comprehensive_harness.sh"

# Helpers run by ONE authenticating driver under `python -I -S`: the driver
# pins and fingerprints the interpreter, so the helper must not silently
# re-exec into another one. The driver owns the floor instead.
DRIVER_OWNED = {
    "scripts/mint_seed_support.py": "scripts/mint_and_prove_seed.sh",
    "scripts/off_stock_rust_audit.py": "scripts/prove_rust_free_build.sh",
    # Started as `"$PYTHON_BIN" -I -S` with the driver's pinned >=3.11 PYTHON_BIN.
    "scripts/mint_seed_recovery.py": "scripts/mint_and_prove_seed.sh",
    # Started as `[sys.executable, "-I", "-B", helper, "--policy", ...]` by the
    # stage, whose own floor makes that interpreter >=3.11.
    "scripts/daily_dependency_git.py": "scripts/daily_toolchain_stage.py",
}

# Floor-detected files that are DESIGNED to run on an older python.
RUNS_BELOW_FLOOR = {
    "scripts/tests/recreate_bootstrap_test.py":
        "imports tomllib only inside a test decorated skipUnless(>= 3.11)",
}

NEW_VERSION = "%d.%d" % tuple(sys.version_info[:2])

SITECUSTOMIZE = """
import os, sys
_log = os.environ.get("TRUST_FLOOR_LOG")
if _log:
    with open(_log, "a") as _handle:
        _handle.write("%d.%d\\n" % tuple(sys.version_info[:2]))
"""


def tracked_python() -> list[str]:
    out = subprocess.run(
        ["git", "-C", str(REPO), "ls-files", "*.py"],
        capture_output=True, text=True, check=True,
    ).stdout.splitlines()
    return [p for p in out if p.startswith(SCRIPT_DIRS)]


def needs_311(path: Path) -> bool:
    """Imports stdlib tomllib with no tomli fallback, and is runnable."""
    tree = ast.parse(path.read_text(encoding="utf-8"))
    imports = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imports.add(node.module)
    runnable = any(
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and isinstance(node.test.left, ast.Name)
        and node.test.left.id == "__name__"
        for node in tree.body
    )
    return "tomllib" in imports and "tomli" not in imports and runnable


def floor_scripts() -> list[str]:
    return sorted(
        p for p in tracked_python() if p not in RUNS_BELOW_FLOOR and needs_311(REPO / p)
    )


def tomli_fallback_scripts() -> list[str]:
    """Runnable scripts that import tomllib but fall back to `tomli`.

    `needs_311` leaves these out because a `tomli` fallback runs on 3.8-3.10 —
    but only where `tomli` is INSTALLED. Where it is not, the fallback path is
    taken instead, and in this repo that path has crashed (a subset TOML parser
    meeting a triple-quoted string) or printed the wrong verdict (a seed gate
    telling a 3.9 machine to re-seed). Measured 2026-09-27: both
    check_cargo_manifest_alignment.py and check_seed_freshness.py did exactly
    that under /usr/bin/python3 3.9, which has no tomli, while this test was
    green — they were never in its inventory.
    """
    found = []
    for p in tracked_python():
        if p in RUNS_BELOW_FLOOR:
            continue
        tree = ast.parse((REPO / p).read_text(encoding="utf-8"))
        imports = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imports.update(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imports.add(node.module)
        runnable = any(
            isinstance(node, ast.If)
            and isinstance(node.test, ast.Compare)
            and isinstance(node.test.left, ast.Name)
            and node.test.left.id == "__name__"
            for node in tree.body
        )
        if "tomllib" in imports and "tomli" in imports and runnable:
            found.append(p)
    return sorted(found)


def has_tomli(interpreter: str) -> bool:
    return subprocess.run([interpreter, "-c", "import tomli"], capture_output=True).returncode == 0


def behavioural_floor_scripts(old: str) -> list[str]:
    """What must reach 3.11 when started under `old`, on THIS machine.

    `floor_scripts()` plus, when `old` cannot import tomli, every tomli-fallback
    script — for those the fallback is not available here, so they need 3.11 as
    much as a script with no fallback does. The static row policy above keeps
    using `floor_scripts()`: a script that re-execs itself is fine under bare
    `python3`, and whether tomli is installed is a fact about a machine, not
    about the manifest.
    """
    extra = [] if has_tomli(old) else tomli_fallback_scripts()
    return sorted(set(floor_scripts()) | set(extra))


def old_interpreter() -> str | None:
    for name in ("/usr/bin/python3", "python3.9", "python3.10", "python3"):
        path = shutil.which(name) if "/" not in name else (name if os.access(name, os.X_OK) else None)
        if not path:
            continue
        probe = subprocess.run(
            [path, "-c", "import sys; raise SystemExit(sys.version_info >= (3, 11))"],
            capture_output=True,
        )
        if probe.returncode == 0:
            return path
    return None


class FloorInventoryTests(unittest.TestCase):
    def test_inventory_is_not_empty(self) -> None:
        # A detector that finds nothing proves nothing.
        self.assertIn("scripts/check_dependency_cycle_anchor.py", floor_scripts())

    def test_no_harness_row_runs_a_floor_script_through_bare_python3(self) -> None:
        floor = set(floor_scripts())
        offenders = []
        for line in HARNESS.read_text(encoding="utf-8").splitlines():
            if not re.match(r"^[a-z0-9][a-z0-9._-]*\|", line):
                continue
            for script in re.findall(r"(?:^|[|;&\s])python3\s+(\S+\.py)\b", line):
                if script.lstrip("./") in floor:
                    offenders.append(f"{line.split('|', 1)[0]}: python3 {script}")
        self.assertEqual(offenders, [], "run floor scripts directly; they select their own interpreter")

    def test_floor_scripts_a_row_executes_directly_are_executable(self) -> None:
        floor = set(floor_scripts())
        missing = []
        for line in HARNESS.read_text(encoding="utf-8").splitlines():
            if not re.match(r"^[a-z0-9][a-z0-9._-]*\|", line):
                continue
            command = line.split("|", 5)[-1]
            for script in re.findall(r"(?:^|[;&\s])(scripts/\S+\.py)\b", command):
                if script in floor and not os.access(REPO / script, os.X_OK):
                    missing.append(script)
        self.assertEqual(missing, [])

    def test_driver_owned_helpers_get_a_311_interpreter_from_their_driver(self) -> None:
        for helper, driver in DRIVER_OWNED.items():
            text = (REPO / driver).read_text(encoding="utf-8")
            self.assertIn("python3.14 python3.13 python3.12 python3.11", text, driver)
            self.assertNotRegex(text, r"PYTHON_BIN=\$\(type -P python3 \|\| true\)", driver)


@unittest.skipUnless(os.name == "posix", "re-exec paths are POSIX")
class FloorReexecTests(unittest.TestCase):
    """Every floor script, started under an old python, ends up on a new one."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.old = old_interpreter()
        cls.new = sys.executable if sys.version_info >= (3, 11) else None
        if cls.old is None or cls.new is None:
            raise unittest.SkipTest("needs both a <3.11 and a >=3.11 interpreter")

    def final_version(self, argv: list[str]) -> tuple[list[str], str]:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            bin_dir = tmp_path / "bin"
            bin_dir.mkdir()
            # The >=3.11 interpreter a floor finds on PATH. It records its own
            # start before it hands over, because the hook below cannot: a floor
            # may re-exec ISOLATED (tools/preflight.py runs `-I -S`, 5e944555e4),
            # and such an interpreter loads no sitecustomize, so until 2026-10-14
            # its start was never logged and the floor read as stuck below 3.11.
            # A `-c` interpreter probe is not the script's start and is not
            # logged here (a probe that does not isolate is still logged by the
            # hook, as before).
            wrapper = bin_dir / "python3.12"
            wrapper.write_text(
                "#!/bin/sh\n"
                'case " $* " in\n'
                '    *" -c "*) ;;\n'
                f'    *) printf \'%s\\n\' {NEW_VERSION} >> "$TRUST_FLOOR_LOG" ;;\n'
                "esac\n"
                f'exec {shlex.quote(self.new)} "$@"\n',
                encoding="utf-8",
            )
            wrapper.chmod(0o755)
            site = tmp_path / "site"
            site.mkdir()
            (site / "sitecustomize.py").write_text(SITECUSTOMIZE, encoding="utf-8")
            log = tmp_path / "log"
            env = {
                "PATH": f"{bin_dir}:/usr/bin:/bin",
                "HOME": os.environ.get("HOME", tmp),
                "PYTHONPATH": str(site),
                "TRUST_FLOOR_LOG": str(log),
            }
            result = subprocess.run(
                argv, cwd=REPO, env=env, capture_output=True, text=True, timeout=180,
                stdin=subprocess.DEVNULL,
            )
            started = log.read_text().split() if log.exists() else []
            return started, (result.stdout + result.stderr)[-600:]

    def test_python3_invocation_reaches_311(self) -> None:
        stuck = []
        for script in behavioural_floor_scripts(self.old):
            if script in DRIVER_OWNED:
                continue
            started, tail = self.final_version([self.old, script, "--help"])
            if not started or tuple(map(int, started[-1].split("."))) < (3, 11):
                stuck.append(f"{script}: interpreters {started}; {tail.strip()[-200:]}")
        self.assertEqual(stuck, [], "\n".join(stuck))

    def test_tomli_fallback_scripts_are_in_the_behavioural_inventory_without_tomli(self) -> None:
        # The inventory is not vacuous about the gap it closes: on a machine
        # whose old interpreter lacks tomli, the two scripts that hid behind the
        # fallback are checked.
        if has_tomli(self.old):
            self.skipTest("the old interpreter has tomli; the fallback really runs there")
        inventory = behavioural_floor_scripts(self.old)
        # check_seed_freshness.py left this class on 2026-09-29 (c6fe4d2973): it
        # now refuses by name when neither tomllib nor tomli is importable.
        for script in ("scripts/check_cargo_manifest_alignment.py",):
            self.assertIn(script, inventory)

    def test_sh_polyglot_scripts_reach_311_when_run_by_sh(self) -> None:
        stuck = []
        for script in behavioural_floor_scripts(self.old):
            if not (REPO / script).read_text(encoding="utf-8").startswith('#!/bin/sh\n""":"'):
                continue
            started, tail = self.final_version(["/bin/sh", script, "--help"])
            if not started or tuple(map(int, started[-1].split("."))) < (3, 11):
                stuck.append(f"{script}: interpreters {started}; {tail.strip()[-200:]}")
        self.assertEqual(stuck, [], "\n".join(stuck))


if __name__ == "__main__":
    unittest.main()
