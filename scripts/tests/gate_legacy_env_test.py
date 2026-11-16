#!/usr/bin/env python3
"""No shell script may hand `trustc` an environment variable `trustc` refuses.

WHY THIS EXISTS (SUPERIORITY-GATE-DEAD, 2026-10-06). Since 80a35e2c7e
(2026-07-14) `AY_PATH` is in `LEGACY_TRUST_SEMANTIC_ENV_VARS`
(compiler/rustc_session/src/config.rs), and a verifying `trustc` refuses every
compile that inherits one of those names ("environment variable `AY_PATH` is an
untracked Trust semantic/codegen control"). `scripts/trust_superiority_gate.sh`
and `scripts/trust_clean_certification_gate.sh` both ran `export AY_PATH=…`, so
for about three months every one of their compiles died before verifying, and
the release rows `verify.superiority` and `verify.clean-certification` measured
nothing. The clean-certification gate even printed four `PASS  mutant` rows over
those dead compiles.

The list is the compiler's, so this test reads it from the compiler source
rather than copying it, and fails when a tracked `scripts/` or `tests/` shell
script exports one of those names (or a name under
`UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES`, which `trustc` always refuses), passes
one as an `env NAME=…` / `NAME=… cmd` prefix, or stages one as a quoted
`"NAME=…"` environment entry.

A site is allowed only through `ALLOWED`, and only for a name `targo` itself
consumes and then scrubs before it starts a compiler: the name must appear in
`PROOF_COMPILER_AUTHORITY_ENV` (targo-trust/src/pipeline/process_environment.rs),
which this test also reads from source. The one other exception,
`HOSTILE_ON_PURPOSE`, is a self-test under scripts/tests/ that hands a gate a
refused name deliberately, to prove the gate scrubs its caller's environment. An
exception row that no longer matches a site fails the test, so neither list can
rot into a blanket waiver.

Shell only: Python launchers are not scanned (recorded as a residual in
docs/KNOWN_HAZARDS.md, 2026-10-06 SUPERIORITY-GATE-DEAD).

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import os
import re
import subprocess
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
CONFIG_RS = REPO / "compiler" / "rustc_session" / "src" / "config.rs"
TARGO_SCRUB_RS = REPO / "targo-trust" / "src" / "pipeline" / "process_environment.rs"
SCAN_ROOTS = ("scripts", "tests")

# (path, NAME) -> why the site is not a trustc environment. Each NAME must be one
# targo consumes and scrubs (PROOF_COMPILER_AUTHORITY_ENV), checked below.
ALLOWED: dict[tuple[str, str], str] = {
    ("scripts/build.sh", "TRUST_VERIFY_WORKER_THREADS"):
        "env prefix of `targo trust verify self`, which reads it (self_verify_cli.rs) "
        "and scrubs it before any compiler starts",
    ("tests/e2e_build_full_verify_tcargo_provenance.sh", "TRUST_VERIFY_WORKER_THREADS"):
        "asserts the logged `targo trust verify self` command line, which carries the targo input",
}

# (path, NAME) -> why a SELF-TEST hands a refused name to a gate ON PURPOSE: to
# prove the gate does not pass its caller's environment on to trustc. Only
# `scripts/tests/*_test.{sh,py}` files may appear here.
HOSTILE_ON_PURPOSE: dict[tuple[str, str], str] = {
    ("scripts/tests/superiority_gates_stub_test.sh", "AY_PATH"):
        "exports a hostile AY_PATH to the superiority gate, whose fake trustc refuses it like the real one",
}


def rust_str_array(source: str, const: str) -> list[str]:
    match = re.search(
        r"pub const " + re.escape(const) + r": &\[&str\] = &\[(.*?)\];", source, re.S
    )
    if not match:
        raise AssertionError(f"`{const}` not found; did the compiler move it?")
    names = re.findall(r'"([A-Za-z0-9_]+)"', match.group(1))
    if not names:
        raise AssertionError(f"`{const}` parsed empty")
    return names


def targo_scrubbed_names(source: str) -> set[str]:
    match = re.search(r"const PROOF_COMPILER_AUTHORITY_ENV: &\[&str\] = &\[(.*?)\];", source, re.S)
    if not match:
        raise AssertionError("PROOF_COMPILER_AUTHORITY_ENV not found in targo-trust")
    return set(re.findall(r'"([A-Za-z0-9_]+)"', match.group(1)))


def logical_lines(text: str):
    """Yield (first_line_number, joined_text) with backslash continuations joined
    and whole-line comments dropped."""
    buf: list[str] = []
    start = 0
    for number, line in enumerate(text.splitlines(), 1):
        if not buf:
            start = number
            if line.lstrip().startswith("#"):
                continue
        if line.endswith("\\"):
            buf.append(line[:-1])
            continue
        buf.append(line)
        yield start, " ".join(buf)
        buf = []
    if buf:
        yield start, " ".join(buf)


class Detector:
    def __init__(self, names: list[str], prefixes: list[str]):
        alternatives = [re.escape(n) for n in sorted(names, key=len, reverse=True)]
        alternatives += [re.escape(p) + r"[A-Za-z0-9_]*" for p in prefixes]
        name = r"(?:" + "|".join(alternatives) + r")"
        word = r"(?:\"[^\"]*\"|'[^']*'|[^\s;&|\"'])+"
        self.patterns = [
            # export NAME / export A=1 NAME=2 / declare -x NAME
            re.compile(
                r"(?:^|[\s;&|(])(?:export|(?:declare|typeset|local|readonly)\s+-[A-Za-z]*x[A-Za-z]*)"
                r"(?:\s+[A-Za-z_][A-Za-z0-9_]*(?:=" + word + r")?)*?\s+(" + name + r")\b"
            ),
            # env [-opts] [A=1 ...] NAME=…
            re.compile(r"(?:^|[\s;&|(])env(?:\s+-\S+)*(?:\s+\S+=\S*)*?\s+[\"']?(" + name + r")="),
            # NAME=value cmd  (an assignment followed by a command word)
            re.compile(
                r"(?:^|[;&|(]\s*|\s)(" + name + r")=" + word + r"?\s+(?!then\b|do\b|fi\b|done\b|esac\b)[^\s;&|)#]"
            ),
            # "NAME=…" / 'NAME=…' staged as an environment entry
            re.compile(r"[\"'](" + name + r")="),
        ]

    def sites(self, text: str):
        for number, line in logical_lines(text):
            found = set()
            for pattern in self.patterns:
                for match in pattern.finditer(line):
                    found.add(match.group(1))
            for name in sorted(found):
                yield number, name, line.strip()


def tracked_shell_files() -> list[str]:
    try:
        out = subprocess.run(
            ["git", "-C", str(REPO), "ls-files", "-z", "--", *SCAN_ROOTS],
            check=True, capture_output=True, text=True,
        ).stdout
        files = [f for f in out.split("\0") if f]
    except (OSError, subprocess.CalledProcessError):
        files = []
        for root in SCAN_ROOTS:
            for dirpath, _dirs, names in os.walk(REPO / root, followlinks=False):
                for n in names:
                    files.append(os.path.relpath(os.path.join(dirpath, n), REPO))
    return sorted(f for f in files if f.endswith(".sh"))


class GateLegacyEnvTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        config = CONFIG_RS.read_text(encoding="utf-8")
        cls.names = rust_str_array(config, "LEGACY_TRUST_SEMANTIC_ENV_VARS")
        cls.prefixes = rust_str_array(config, "UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES")
        cls.scrubbed = targo_scrubbed_names(TARGO_SCRUB_RS.read_text(encoding="utf-8"))
        cls.detector = Detector(cls.names, cls.prefixes)

    def test_compiler_list_names_ay_path(self):
        # The incident's own name; if it ever leaves the list this test's premise moved.
        self.assertIn("AY_PATH", self.names)

    def test_detector_controls(self):
        hits = [
            'export AY_PATH="$AY_BIN"',
            "export FOO=1 AY_PATH",
            "declare -x TRUST_SOLVER=ay",
            'AY_PATH="$x" "$TRUSTC" --edition 2021 f.rs',
            "env -i PATH=/bin AY_PATH=/x trustc f.rs",
            'env "TRUST_TIMEOUT_MS=5" trustc f.rs',
            'cmd=(env "TRUST_VERIFY_POLICY=strict" trustc)',
            "export TRUST_CG_FOO=1",
            "TCG_DUMP=1 trustc f.rs",
            "VAR=1 \\\n  AY_PATH=/x trustc f.rs",
        ]
        for line in hits:
            with self.subTest(line=line):
                self.assertTrue(list(self.detector.sites(line)), f"missed: {line!r}")
        misses = [
            "unset AY_PATH TRUST_SOLVER",
            "env -u AY_PATH trustc f.rs",
            'AY_BIN="${AY_PATH:-x}"',
            "# export AY_PATH=x",
            'echo "AY_PATH is retired"',
            'TRUST_CG_CRATE="compiler/rustc_codegen_trust_cg"',
            'if TRUST_CG_LINK_TARGETS="$(f)"; then',
            "MY_AY_PATH=1 cmd",
            "export NOT_AY_PATH_X=1",
        ]
        for line in misses:
            with self.subTest(line=line):
                self.assertEqual(list(self.detector.sites(line)), [], f"false hit: {line!r}")

    def test_allowed_names_are_targo_scrubbed(self):
        for (path, name), reason in ALLOWED.items():
            with self.subTest(path=path, name=name):
                self.assertTrue(reason)
                self.assertIn(
                    name, self.scrubbed,
                    f"{path}: {name} is allowed only as a targo input, but targo does not scrub it",
                )

    def test_hostile_sites_are_self_tests(self):
        for (path, name), reason in HOSTILE_ON_PURPOSE.items():
            with self.subTest(path=path, name=name):
                self.assertTrue(reason)
                self.assertRegex(path, r"^scripts/tests/[A-Za-z0-9_]+_test\.(sh|py)$")
                self.assertNotIn((path, name), ALLOWED)

    def test_no_script_hands_trustc_a_refused_variable(self):
        files = tracked_shell_files()
        self.assertTrue(files, "no shell files found under scripts/ and tests/")
        offenders = []
        used = set()
        for rel in files:
            try:
                text = (REPO / rel).read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            for number, name, line in self.detector.sites(text):
                if (rel, name) in ALLOWED or (rel, name) in HOSTILE_ON_PURPOSE:
                    used.add((rel, name))
                    continue
                offenders.append(f"{rel}:{number}: {name}: {line[:160]}")
        self.assertEqual(
            offenders, [],
            "these sites hand a trustc-refused environment variable to a child process; "
            "trustc refuses the whole compile (config.rs LEGACY_TRUST_SEMANTIC_ENV_VARS / "
            "UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES) — use the tracked -Z option instead:\n  "
            + "\n  ".join(offenders),
        )
        stale = sorted((set(ALLOWED) | set(HOSTILE_ON_PURPOSE)) - used)
        self.assertEqual(stale, [], f"exception rows that match no site (remove them): {stale}")


if __name__ == "__main__":
    unittest.main()
