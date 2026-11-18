#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Bridge build selection controls; fake tools never build or certify artifacts."""

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor. This test imports tomllib (3.11+) at its top.
# `python3 lean_bridge_roots_test.py` on a machine whose python3 is older (3.9 on macOS
# CommandLineTools) re-execs here under the newest >=3.11 on PATH
# (scripts/tests/python_floor_test.py holds every such script to this).
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("lean_bridge_roots_test.py requires Python 3.11+ (tomllib); none found on PATH")

import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest
from unittest import mock

REPO = Path(__file__).resolve().parents[2]
ROOTS = ["TrustIr.Semantics.Compare", "TrustIr.Semantics.Cast",
         "TrustIr.Semantics.Step", "TrustIr.Semantics.Eval"]


class BridgeRootBuildTests(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        (self.root / "scripts").mkdir()
        for name in ("regen-trustir-oleans.sh",):
            (self.root / "scripts" / name).write_bytes((REPO / "scripts" / name).read_bytes())
        for name in ("trust-ir", "clean"):
            path = self.root / "first-party" / name
            path.mkdir(parents=True)
            subprocess.run(["git", "init", "-q", str(path)], check=True)
            subprocess.run(["git", "-C", str(path), "-c", "user.name=fixture",
                            "-c", "user.email=fixture@invalid", "commit", "-qm",
                            "fixture", "--allow-empty"], check=True)
        source = self.root / "first-party/trust-ir/lean/trust_ir-semantics"
        source.mkdir(parents=True)
        (source / "lean-toolchain").write_text("leanprover/lean4:v4.8.0\n")
        subprocess.run(["git", "-C", str(self.root / "first-party/trust-ir"),
                        "add", "lean"], check=True)
        subprocess.run(["git", "-C", str(self.root / "first-party/trust-ir"),
                        "-c", "user.name=fixture", "-c", "user.email=fixture@invalid",
                        "commit", "-qm", "pin"], check=True)
        self.bin = self.root / "fixture-toolchain/bin"
        self.bin.mkdir(parents=True)
        (self.bin.parent / "lib/lean").mkdir(parents=True)
        self.write_tool("lean", """
if sys.argv[1:] == ['--version']:
    print('Lean (version 4.8.0, aarch64-unknown-linux-gnu, commit df668f00e6c0, Release)')
elif sys.argv[1:] == ['--print-prefix']:
    print(Path(__file__).resolve().parent.parent)
else:
    sys.exit(97)
""")
        self.write_tool("lake", """
arguments = sys.argv[1:]
if arguments == ['--version']:
    print('Lake version 5.0.0-df668f0 (Lean version 4.8.0)')
else:
    expected_linker = os.environ.get('FIXTURE_NATIVE_LINKER')
    if expected_linker is not None:
        if arguments[:2] != ['-K', 'nativeLinker=' + expected_linker]:
            sys.exit(97)
        arguments = arguments[2:]
    if not arguments or arguments[0] != 'build':
        sys.exit(97)
    Path(os.environ['LAKE_CAPTURE']).write_text(json.dumps(sys.argv[1:]))
    sys.exit(42)  # Stop before creating any fake olean or manifest.
""")
        self.write_tool("targo", """
if sys.argv[1:] == ['--unverified', '--version']:
    print('targo (unit fixture only)')
elif '--snapshot-lean' in sys.argv:
    repo, commit, destination = sys.argv[-3:]
    destination = Path(destination)
    destination.mkdir()
    pin = subprocess.check_output(['git', '-C', repo, 'show',
                                   commit + ':lean/trust_ir-semantics/lean-toolchain'])
    (destination / 'lean-toolchain').write_bytes(pin)
elif '--admit-lean-toolchain' in sys.argv:
    status = int(os.environ.get('ADMISSION_STATUS', '0'))
    if status:
        sys.exit(status)
    source, selected, report = map(Path, sys.argv[-3:])
    selected = selected.resolve()
    fields = ['trust.lean-toolchain-readback.v1', 'aarch64-unknown-linux-gnu',
              (source / 'lean-toolchain').read_text().rstrip('\\n'),
              'Lean (version 4.8.0, aarch64-unknown-linux-gnu, commit df668f00e6c0, Release)',
              str(selected), str(selected.parent / 'lib/lean')]
    mode = os.environ.get('READBACK_MODE', 'good')
    if mode == 'schema':
        fields[0] = 'unknown-schema'
    data = ('\\0'.join(fields) + '\\0').encode()
    if mode == 'truncated':
        data = data[:-1]
    elif mode == 'trailing':
        data += b'junk'
    Path(report).write_bytes(data)
elif sys.argv[-2:] == ['--', '--roots']:
    sys.stdout.write(os.environ['FIXTURE_ROOTS'])
    sys.exit(int(os.environ.get('ROOT_EXPORT_STATUS', '0')))
else:
    sys.exit(97)
""")
        self.capture = self.root / "lake-command.json"

    def write_tool(self, name, body):
        path = self.bin / name
        path.write_text("#!/usr/bin/python3\nimport json, os, subprocess, sys\nfrom pathlib import Path\n" + body)
        path.chmod(0o700)

    def run_script(self, roots=ROOTS, status=0, admission=0, readback='good', relative=False,
                   native_linker=None):
        # The fixture owns producer configuration. Explicit linker controls below
        # exercise admission without inheriting any caller's producer settings.
        env = {k: v for k, v in os.environ.items() if not k.startswith("TRUST_REGEN_")}
        env.update(LEAN_TOOLCHAIN_BIN=str(self.bin),
                   TRUST_REGEN_TARGO=str(self.bin / "targo"), LAKE_CAPTURE=str(self.capture),
                   FIXTURE_ROOTS="".join(root + "\n" for root in roots),
                   ROOT_EXPORT_STATUS=str(status), ADMISSION_STATUS=str(admission),
                   READBACK_MODE=readback, TMPDIR=str(self.root))
        # Keep fixture controls independent of the real producer's caller.
        env.pop('TRUST_REGEN_NATIVE_LINKER', None)
        env.pop('FIXTURE_NATIVE_LINKER', None)
        if native_linker is not None:
            env['TRUST_REGEN_NATIVE_LINKER'] = os.fspath(native_linker)
            env['FIXTURE_NATIVE_LINKER'] = os.fspath(native_linker)
        cwd = None
        if relative:
            cwd = self.root / "caller"
            cwd.mkdir(exist_ok=True)
            env['LEAN_TOOLCHAIN_BIN'] = os.path.relpath(self.bin, cwd)
            env['TMPDIR'] = os.path.relpath(self.root, cwd)
        return subprocess.run(["bash", str(self.root / "scripts/regen-trustir-oleans.sh")],
                              env=env, cwd=cwd, capture_output=True, text=True, timeout=15)

    def test_default_builds_every_exported_root_with_olean_facet(self):
        result = self.run_script()
        self.assertEqual(result.returncode, 42, result.stderr)
        self.assertEqual(json.loads(self.capture.read_text()),
                         ["build", *("+" + root + ":olean" for root in ROOTS)])

    def test_caller_native_linker_does_not_change_fixture_build(self):
        with mock.patch.dict(os.environ, TRUST_REGEN_NATIVE_LINKER=str(self.bin / "lean")):
            result = self.run_script()
        self.assertEqual(result.returncode, 42, result.stderr)
        self.assertEqual(json.loads(self.capture.read_text()),
                         ["build", *("+" + root + ":olean" for root in ROOTS)])

    def test_caller_producer_settings_do_not_enter_fixture(self):
        with mock.patch.dict(os.environ, TRUST_REGEN_KEEP_WORK="caller-value",
                             TRUST_REGEN_NATIVE_LINKER="caller-relative-linker",
                             TRUST_REGEN_TARGO="/caller/targo",
                             LEAN_TOOLCHAIN_BIN="/caller/lean"):
            result = self.run_script()
        self.assertEqual(result.returncode, 42, result.stderr)
        self.assertEqual(json.loads(self.capture.read_text()),
                         ["build", *("+" + root + ":olean" for root in ROOTS)])

    def test_added_exported_root_is_built_without_a_second_allowlist(self):
        roots = ROOTS + ["TrustIr.Semantics.NewRoot"]
        result = self.run_script(roots)
        self.assertEqual(result.returncode, 42, result.stderr)
        self.assertEqual(json.loads(self.capture.read_text())[-1],
                         "+TrustIr.Semantics.NewRoot:olean")

    def test_relative_tool_bin_and_scratch_paths_keep_caller_context(self):
        result = self.run_script(relative=True)
        self.assertEqual(result.returncode, 42, result.stderr)
        self.assertEqual(json.loads(self.capture.read_text()),
                         ["build", *("+" + root + ":olean" for root in ROOTS)])

    def native_linker(self):
        linker = self.bin / "native linker"
        linker.write_text("#!/bin/sh\nexit 0\n")
        linker.chmod(0o700)
        return linker

    def test_default_build_is_independent_of_an_ambient_native_linker(self):
        with mock.patch.dict(os.environ, {'TRUST_REGEN_NATIVE_LINKER': 'ambient-relative-linker'}):
            result = self.run_script()
        self.assertEqual(result.returncode, 42, result.stderr)
        self.assertEqual(json.loads(self.capture.read_text()),
                         ["build", *("+" + root + ":olean" for root in ROOTS)])

    def test_native_linker_arguments_reach_lake_before_exported_roots(self):
        linker = self.native_linker()
        result = self.run_script(native_linker=linker)
        self.assertEqual(result.returncode, 42, result.stderr)
        self.assertEqual(json.loads(self.capture.read_text()),
                         ["-K", "nativeLinker=" + str(linker), "build",
                          *("+" + root + ":olean" for root in ROOTS)])

    def test_invalid_root_with_native_linker_cannot_start_lake(self):
        result = self.run_script(["../bad-root"], native_linker=self.native_linker())
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("invalid exported bridge root module", result.stderr)
        self.assertFalse(self.capture.exists())

    def test_native_linker_must_be_an_absolute_executable_file(self):
        not_executable = self.root / "not-executable"
        not_executable.write_text("not executable")
        not_executable.chmod(0o600)
        for linker in ("relative-linker", self.root / "missing-linker", not_executable):
            with self.subTest(linker=linker):
                result = self.run_script(native_linker=linker)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("must name an absolute executable file", result.stderr)
                self.assertFalse(self.capture.exists())

    def test_fake_lake_rejects_unexpected_linker_options(self):
        linker = str(self.native_linker())
        env = dict(os.environ, LAKE_CAPTURE=str(self.capture), FIXTURE_NATIVE_LINKER=linker)
        for arguments in (
            ["-K", "nativeLinker=/wrong", "build"],
            ["-K"],
            ["build"],
            ["-K", "nativeLinker=" + linker, "-K", "nativeLinker=" + linker, "build"],
            ["-K", "nativeLinker=" + linker, "--unknown", "build"],
        ):
            with self.subTest(arguments=arguments):
                result = subprocess.run([str(self.bin / "lake"), *arguments], env=env,
                                        capture_output=True, text=True, timeout=15)
                self.assertEqual(result.returncode, 97, result.stderr)
                self.assertFalse(self.capture.exists())

    def test_empty_roots_refuse_before_lake_build(self):
        result = self.run_script([])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("exports no root modules", result.stderr)
        self.assertFalse(self.capture.exists())

    def test_invalid_roots_cannot_become_lake_options_or_paths(self):
        for root in ("--help", "../TrustIr.Semantics.Arith", "TrustIr.Semantics.Arith:shared",
                     "TrustIr.$(touch injected)"):
            with self.subTest(root=root):
                result = self.run_script([root])
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("invalid exported bridge root", result.stderr)
                self.assertFalse(self.capture.exists())

    def test_failed_root_export_cannot_start_lake(self):
        result = self.run_script(status=23)
        self.assertEqual(result.returncode, 23)
        self.assertFalse(self.capture.exists())

    def test_failed_admission_cannot_start_lake(self):
        result = self.run_script(admission=29)
        self.assertEqual(result.returncode, 29)
        self.assertFalse(self.capture.exists())

    def test_invalid_native_readback_never_starts_lake(self):
        for mode in ('schema', 'truncated', 'trailing'):
            with self.subTest(mode=mode):
                result = self.run_script(readback=mode)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('native toolchain readback', result.stderr)
                self.assertFalse(self.capture.exists())

    def test_each_platform_union_matches_its_declared_producer(self):
        manifest = tomllib.loads((REPO / "crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml").read_text())
        self.assertTrue(manifest["platforms"])
        cache = {}
        git_env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        git_env.update(GIT_NO_LAZY_FETCH="1", GIT_ALLOW_PROTOCOL="",
                       GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")

        # The declared producer is the manifest's recorded roots (what
        # regen-trustir-oleans.sh read from the bridge's exported roots) at
        # each platform's recorded trust-ir revision. Its closure follows
        # every import whose source is in the trust-ir Lean package at that
        # revision, whatever its name (`TrustIrNativeLink` has no `TrustIr.`
        # prefix), and stops at Lean core, which the package does not hold.
        roots = manifest["provenance"]["root_modules"]
        self.assertEqual(roots[0], manifest["provenance"]["root_module"])
        package = manifest["provenance"]["source_subdir"]
        trust_ir = str(REPO / "first-party/trust-ir")

        def import_union(revision):
            self.assertRegex(revision, r"^[0-9a-f]{40}$")
            if revision in cache:
                return cache[revision]
            listing = subprocess.check_output(
                ["git", "--no-replace-objects", "-C", trust_ir, "ls-tree", "-r", "--name-only",
                 revision, "--", package + "/"], env=git_env, text=True)
            local = {path[len(package) + 1:].removesuffix(".lean").replace("/", ".")
                     for path in listing.splitlines() if path.endswith(".lean")}
            seen, pending = set(), list(roots)
            while pending:
                module = pending.pop()
                if module in seen:
                    continue
                self.assertIn(module, local, f"{module} has no source at {revision}")
                seen.add(module)
                path = package + "/" + module.replace(".", "/") + ".lean"
                text = subprocess.check_output(
                    ["git", "--no-replace-objects", "-C", trust_ir,
                     "show", revision + ":" + path], env=git_env, text=True)
                for line in text.splitlines():
                    if line.startswith("import "):
                        pending.extend(name for name in line.split("--")[0].split()[1:]
                                       if name in local)
            cache[revision] = seen
            return seen

        for triple, platform in manifest["platforms"].items():
            with self.subTest(platform=triple):
                # A carried stale platform is still refused by the consumer;
                # qualify its full inventory against its own recorded producer.
                seen = import_union(platform["built_from_trustir_commit"])
                files = set(manifest["files"]) | set(platform.get("files", {}))
                self.assertEqual({name.replace("/", ".").removesuffix(".olean")
                                  for name in files}, seen)
        seen = import_union(manifest["provenance"]["trustir_commit"])
        self.assertIn("TrustIr.Semantics.Arith", seen)
        self.assertNotIn("TrustIr.Proofs.MemorySafety", seen)


class CoreManifestProvenanceTests(unittest.TestCase):
    def test_core_origin_names_no_installer_the_producer_cannot_observe(self):
        # The producer admits a Lean toolchain by its version readback, whether elan or
        # LEAN_TOOLCHAIN_BIN supplied it. The vendored origin must be the producer's own
        # template, which names no installer; a hand-edited or stale stamp fails here.
        script = (REPO / "scripts/regen-trustir-oleans.sh").read_text()
        template = "f'origin = \"{toolchain} release toolchain, lib/lean\"',"
        self.assertEqual(script.count(template), 1)
        self.assertNotIn("elan-installed", script)
        provenance = tomllib.loads(
            (REPO / "vendor/lean-core-oleans/MANIFEST.toml").read_text())["provenance"]
        self.assertEqual(provenance["origin"],
                         provenance["lean_toolchain"] + " release toolchain, lib/lean")

    def test_a_change_to_the_core_manifest_reruns_this_module_at_landing(self):
        from scripts.lib import land_select
        self.assertIn("scripts.tests.lean_bridge_roots_test",
                      land_select.validation_test_modules(["vendor/lean-core-oleans/MANIFEST.toml"]))


if __name__ == "__main__":
    unittest.main()
