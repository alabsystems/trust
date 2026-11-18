#!/usr/bin/env python3
"""Feedback custody and phase semantics, using stand-ins, never compiler builds."""
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
from __future__ import annotations

import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "stack_feedback.py"
SPEC = importlib.util.spec_from_file_location("stack_feedback", SCRIPT)
STACK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(STACK)


# A `#!{sys.executable}` shebang cannot carry an interpreter path with spaces (atpkg's python
# lives under `Application Support/`): exec splits it and the fake never runs. This sh/python
# polyglot execs the interpreter quoted and keeps argv[0] as the fake's own path.
PYTHON_SHEBANG = f'#!/bin/sh\n""":"\nexec "{sys.executable}" "$0" "$@"\n":"""\n'


def executable(path, body):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body)
    path.chmod(0o755)


TARGO = r'''
import json, pathlib, sys
root = pathlib.Path.cwd()
ay = root if root.name == 'ay' else root.parent / 'ay'
if '--version' in sys.argv:
    print('targo 1.99.0-dev'); sys.exit(0)
if 'metadata' in sys.argv:
    if '--unverified' in sys.argv:
        print('`--unverified` is valid only for a Targo compilation command', file=sys.stderr); sys.exit(2)
    if METADATA_FAIL:
        print('named dependency resolution failure', file=sys.stderr); sys.exit(12)
    packages = [{'id':'ay-proof-common 0.1.0', 'name':'ay-proof-common', 'version':'0.1.0',
                 'source':None,'manifest_path':str(ay/'crates/ay-proof-common/Cargo.toml')}]
    if root.name != 'ay':
        packages.append({'id':'trust-vc-core 0.1.0','name':'trust-vc-core','version':'0.1.0',
                         'source':None,'manifest_path':str(root/'Cargo.toml')})
    packages.extend(json.loads(EXTRA_PACKAGES))
    print(json.dumps({'packages':packages,'resolve':{'nodes':[]},'workspace_members':[p['id'] for p in packages]}))
    sys.exit(0)
target_root = pathlib.Path(__import__('os').environ['CARGO_TARGET_DIR'])
target_root.mkdir(parents=True,exist_ok=True)
for name in ('ay_refutation_step_realbody','ay_refutation_loop_realbody'):
    path = target_root/name
    # sh/python polyglot: a shebang cannot carry an interpreter path with spaces.
    body = '#!/bin/sh\n""":"\nexec "'+sys.executable+'" "$0" "$@"\n":"""\nimport sys\n'
    if NATIVE_MUTATION:
        body += 'from pathlib import Path\n'
        condition = '"--list" in sys.argv' if NATIVE_MUTATION == 'inventory' else '"--list" not in sys.argv'
        body += 'if '+condition+':\n p=Path(__file__); p.write_text(p.read_text()+"\\n# changed native bytes\\n")\n'
    body += 'if "--list" in sys.argv:\n print("honest_verified: test\\nmutant_refuted: test")\n'
    body += 'else:\n print("running 2 tests\\ntest result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;")\n'
    if TEST_FAIL:
        body += ' if "--list" not in sys.argv: sys.exit(9)\n'
    path.write_text(body);path.chmod(0o755)
    print(json.dumps({'reason':'compiler-artifact','target':{'name':name},'executable':str(path)}))
'''

RATCHET = r'''
import json, os, pathlib, subprocess
root = pathlib.Path.cwd()
out = pathlib.Path(os.environ['TRUST_RATCHET_OUT']);out.mkdir(parents=True,exist_ok=True)
git=lambda *args:subprocess.check_output(['/usr/bin/git','-C',str(root),*args],text=True).strip()
data={'schema_version':'ay.trust.ratchet.v3',
      'metadata':{'git_commit':git('rev-parse','HEAD'),
                  'crate_sources_tree':git('rev-parse','HEAD:crates/ay-proof-common'),
                  'crate_sources_clean_at_commit':True},
      'verdicts':{'obligations':3,'proved_solver_discharged':1,'kernel_certified':0}}
data['obligation_ledger']={'entries':{'f|overflow|lib.rs:'+str(i):{'class':'unknown'} for i in range(3)},
                           'denominator_is_complete':True,'vcgen_truncated_functions':0,
                           'vcgen_truncated_function_names':[]}
data['strict_lane']={'verdict_census_matches_advisory':True}
(out/'current.json').write_text(json.dumps(data))
print('stand-in census, no proof claim')
'''


class FeedbackTests(unittest.TestCase):
    def setUp(self):
        # Stand-ins must not discover or contact the operator's real aterm.
        self.enterContext(mock.patch.dict(os.environ, {
            key: value for key, value in os.environ.items()
            if not key.startswith("ATERM_") and key != "BUILD_SLOT_ATERM_CLI"
        }, clear=True))
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name).resolve()
        self.ay = self.base / "subjects/ay"
        self.vc = self.base / "subjects/trust-vc"
        for root in (self.ay, self.vc):
            root.mkdir(parents=True)
            (root / "Cargo.toml").write_text('[package]\nname="fixture"\nversion="0.1.0"\n')
            (root / "Cargo.lock").write_text("version = 4\n")
        crate = self.ay / "crates/ay-proof-common"
        crate.mkdir(parents=True)
        (crate / "Cargo.toml").write_text('[package]\nname="ay-proof-common"\nversion="0.1.0"\n')
        for path in STACK.FIXTURES.values():
            target = self.ay / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text("// fixed stand-in proof source\n")
        gate = self.ay / "scripts/ci/trust_verification_ratchet_gate.sh"
        executable(gate, f"#!/bin/sh\nexec \"{sys.executable}\" - <<'PY'\n{RATCHET}\nPY\n")
        accounting = self.ay / "scripts/trust_ratchet_accounting.py"
        accounting.write_text("def accounting(b,c): return {'obligations_removed_unattributed': 0}\n"
                              "def regressions(a,b,c): return []\n")
        for root in (self.ay, self.vc):
            self.git(root, "init", "-q", "-b", "main")
            self.commit(root)
        self.control = self.make_toolchain("a" * 40)
        self.candidate = self.make_toolchain("b" * 40)
        self.slot = self.base / "build-slot"
        executable(self.slot, '#!/bin/sh\n[ "$1" = -- ] || exit 3\nshift\nexec "$@"\n')
        self.spec = self.base / "scaffold.rs"
        self.spec.write_text("// explicit stand-in measurement scaffold\n")
        self.args = argparse.Namespace(action="run", control=self.control, candidate=self.candidate,
                                       candidate_receipt=self.candidate / "tool-provenance.json",
                                       candidate_commit="b" * 40, ay=self.ay, trust_vc=self.vc,
                                       out=self.base / "results", build_slot=self.slot, timeout=20,
                                       repetitions=1, trust_spec_source=self.spec)

    def git(self, root, *args):
        return subprocess.run(["/usr/bin/git", "-C", str(root), "-c", "core.hooksPath=/dev/null",
                               "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", *args],
                              check=True, capture_output=True, text=True).stdout.strip()

    def commit(self, root):
        self.git(root, "add", ".")
        self.git(root, "commit", "-qm", "fixed source")

    def test_aterm_context_reaches_admission_without_entering_the_report(self):
        context = {"ATERM_CHILD": "1", "ATERM_PARENT_SESSION_ID": "s-current",
                   "ATERM_SESSION_ID": "s-stale", "ATERM_EDGE_TOKENS": "fixture-private-edge-token"}
        routing = {"HOME": str(self.base / "routing-home"),
                   "XDG_RUNTIME_DIR": str(self.base / "private-runtime"),
                   "XDG_STATE_HOME": str(self.base / "private-state")}
        inherited = {**context, **routing}
        observed = self.base / "admission-context.json"
        executable(self.slot, PYTHON_SHEBANG + f"import json, os, pathlib, sys\n"
                   f"pathlib.Path({str(observed)!r}).write_text(json.dumps("
                   f"{{key: os.environ.get(key) for key in {tuple(inherited)!r}}}))\n"
                   "assert sys.argv[1] == '--'\n"
                   "os.execvpe(sys.argv[2], sys.argv[2:], os.environ)\n")
        with mock.patch.dict(os.environ, inherited), \
                mock.patch.object(shutil, "which", return_value=None):
            runner = STACK.Feedback(self.args)
            runner.preflight()
            for label in ("control", "candidate"):
                with self.subTest(label=label):
                    phase = runner.job(f"{label}.context", [sys.executable, "-c", "pass"],
                                       self.ay, label, "context_transport")
                    self.assertEqual(phase["status"], "passed")
                    self.assertEqual(json.loads(observed.read_text()), inherited)
                    self.assertFalse(set(inherited) & phase["environment"].keys())
        report = (self.args.out / "result.json").read_text()
        for value in (context["ATERM_PARENT_SESSION_ID"], context["ATERM_SESSION_ID"],
                      context["ATERM_EDGE_TOKENS"], routing["XDG_RUNTIME_DIR"], routing["XDG_STATE_HOME"]):
            self.assertNotIn(value, report)

    def test_aterm_discovery_preserves_the_compiler_path_and_binds_the_cli(self):
        cli = self.base / "application/aterm"
        executable(cli, "#!/bin/sh\nexit 0\n")
        observed = self.base / "admission-cli.json"
        executable(self.slot, PYTHON_SHEBANG + f"import json, os, pathlib, sys\n"
                   f"pathlib.Path({str(observed)!r}).write_text(json.dumps("
                   "{key: os.environ.get(key) for key in ('PATH', 'BUILD_SLOT_ATERM_CLI')}))\n"
                   "assert sys.argv[1] == '--'\n"
                   "os.execvpe(sys.argv[2], sys.argv[2:], os.environ)\n")
        with mock.patch.dict(os.environ, {"ATERM_CHILD": "1"}), \
                mock.patch.object(shutil, "which", return_value=str(cli)):
            runner = STACK.Feedback(self.args)
            runner.preflight()
            phase = runner.job("control.discovery", [sys.executable, "-c", "pass"],
                               self.ay, "control", "context_transport")
        self.assertEqual(phase["status"], "passed")
        env = json.loads(observed.read_text())
        self.assertEqual(env["BUILD_SLOT_ATERM_CLI"], str(cli))
        self.assertNotIn(str(cli.parent), env["PATH"].split(os.pathsep))
        self.assertEqual(runner.report["inputs"]["aterm_cli"],
                         {"path": str(cli), "sha256": STACK.sha(cli)})
        cli.write_text("#!/bin/sh\nexit 1\n")
        with self.assertRaisesRegex(STACK.Refused, "aterm discovery executable changed"):
            runner.check_inputs()

    def test_explicit_aterm_discovery_survives_the_minimal_environment(self):
        cli = self.base / "application/explicit-aterm"
        executable(cli, "#!/bin/sh\nexit 0\n")
        observed = self.base / "explicit-admission-cli.json"
        executable(self.slot, PYTHON_SHEBANG + f"import json, os, pathlib, sys\n"
                   f"pathlib.Path({str(observed)!r}).write_text(json.dumps("
                   "{key: os.environ.get(key) for key in ('PATH', 'BUILD_SLOT_ATERM_CLI')}))\n"
                   "assert sys.argv[1] == '--'\n"
                   "os.execvpe(sys.argv[2], sys.argv[2:], os.environ)\n")
        with mock.patch.dict(os.environ, {"ATERM_CHILD": "1", "BUILD_SLOT_ATERM_CLI": str(cli)}), \
                mock.patch.object(shutil, "which", side_effect=AssertionError("explicit client must not search PATH")):
            runner = STACK.Feedback(self.args)
            runner.preflight()
            phase = runner.job("control.explicit-discovery", [sys.executable, "-c", "pass"],
                               self.ay, "control", "context_transport")
        self.assertEqual(phase["status"], "passed")
        env = json.loads(observed.read_text())
        self.assertEqual(env["BUILD_SLOT_ATERM_CLI"], str(cli))
        self.assertNotIn(str(cli.parent), env["PATH"].split(os.pathsep))
        self.assertEqual(runner.report["inputs"]["aterm_cli"],
                         {"path": str(cli), "sha256": STACK.sha(cli)})
        cli.write_text("#!/bin/sh\nexit 1\n")
        with self.assertRaisesRegex(STACK.Refused, "aterm discovery executable changed"):
            runner.check_inputs()

    def test_invalid_explicit_aterm_discovery_refuses_without_searching_path(self):
        fallback = self.base / "application/fallback-aterm"
        executable(fallback, "#!/bin/sh\nexit 0\n")
        not_executable = self.base / "not-executable-aterm"
        not_executable.write_text("fixture bytes\n")
        for index, value in enumerate(("", "relative/aterm", str(self.base / "missing-aterm"),
                                       str(self.base), str(not_executable))):
            with self.subTest(value=value):
                self.args.out = self.base / f"invalid-explicit-{index}"
                with mock.patch.dict(os.environ, {"ATERM_CHILD": "1", "BUILD_SLOT_ATERM_CLI": value}), \
                        mock.patch.object(shutil, "which", return_value=str(fallback)) as discover:
                    runner = STACK.Feedback(self.args)
                    with self.assertRaisesRegex(STACK.Refused, "explicit aterm discovery executable unavailable"):
                        runner.preflight()
                discover.assert_not_called()
                self.assertEqual(runner.report["phases"], [])

    def make_toolchain(self, commit, metadata_fail=False, test_fail=False, extra_packages=(), native_mutation=None,
                       artifact_ambiguity=None):
        root = self.base / f"toolchains/trust-{commit[:8]}"
        (root / "bin").mkdir(parents=True, exist_ok=True)
        compiler = ("#!/bin/sh\nif [ \"$*\" = '--print sysroot' ]; then\n"
                    f" echo '{root}'\nelse\n"
                    f" echo 'binary: trustc'; echo 'commit-hash: {commit}'; echo 'trust: 0.1.0'\nfi\n")
        executable(root / "bin/trustc", compiler)
        executable(root / "bin/rustc", compiler)
        for name in ("targo-trust", "trustd", "ay", "rustdoc"):
            executable(root / "bin" / name, "#!/bin/sh\nexit 0\n")
        program = TARGO
        if artifact_ambiguity == "shared-executable":
            program = program.replace("path = target_root/name", "path = target_root/'shared-executable'")
        elif artifact_ambiguity == "hardlinked-executable":
            program = program.replace("    path.write_text(body);path.chmod(0o755)",
                "    path.write_text(body);path.chmod(0o755)\n"
                "    if name=='ay_refutation_loop_realbody':\n"
                "        path.unlink();path.hardlink_to(target_root/'ay_refutation_step_realbody')")
        elif artifact_ambiguity == "duplicate-target":
            artifact = "    print(json.dumps({'reason':'compiler-artifact','target':{'name':name},'executable':str(path)}))"
            self.assertIn(artifact, program)
            program = program.replace(artifact, artifact + "\n"
                "    duplicate=path.with_name(path.name+'-duplicate')\n"
                "    duplicate.write_bytes(path.read_bytes());duplicate.chmod(0o755)\n"
                "    print(json.dumps({'reason':'compiler-artifact','target':{'name':name},'executable':str(duplicate)}))")
        executable(root / "bin/targo", PYTHON_SHEBANG + f"METADATA_FAIL={metadata_fail!r}\nTEST_FAIL={test_fail!r}\n"
                   f"NATIVE_MUTATION={native_mutation!r}\n"
                   f"EXTRA_PACKAGES={json.dumps(extra_packages)!r}\n" + program)
        executable(root / "libexec/helper", "#!/bin/sh\nexit 0\n")
        stage = "build/fixture-host/stage2"
        digest = "c" * 64
        data = {
            "schema": STACK.receipt.RECEIPT_SCHEMA, "status": "internal-release-ready",
            "tool_binding_status": "ready", "source_tree_clean": True, "trust_from_trust": True,
            "stage": 2, "host": "fixture-host", "stage_root": stage,
            "path_scope": "repository-root-relative", "errors": [],
            "compiler": {"path": f"{stage}/bin/trustc", "compiler_sha256": STACK.sha(root / "bin/trustc"),
                         "compatibility_alias": f"{stage}/bin/rustc",
                         "compatibility_alias_sha256": STACK.sha(root / "bin/rustc"), "source_commit": commit},
            "tools": [{"name": name, "path": f"{stage}/bin/{name}",
                       "sha256": STACK.sha(root / "bin" / name),
                       "producer_sha256": STACK.sha(root / "bin" / name), "status": "bound"}
                      for name in STACK.TOOLS[1:]],
            "rustdoc_alias": {"path": f"{stage}/bin/rustdoc", "sha256": STACK.sha(root / "bin/rustdoc")},
            "proc_macro_helper": {"path": f"{stage}/libexec/helper", "sha256": STACK.sha(root / "libexec/helper")},
            "bootstrap_lineage": {"schema": "trust.bootstrap-lineage.v1", "mode": "seed",
                                  "status": "trust_from_trust", "trust_from_trust": True, "errors": [],
                                  "validated_seed": {"materialization_status": "fresh-from-validated-archives"}},
            "source_lineage": {"schema": "trust.source-lineage.v1", "status": "immutable_release",
                               "source_tree_clean": True,
                               "errors": [], "stable_across_build": True, "closure_sha256": digest,
                               "pre_build_closure_sha256": digest, "post_build_closure_sha256": digest,
                               "repositories": [{"path": ".", "head": commit}]}}
        (root / "tool-provenance.json").write_text(json.dumps(data))
        self.reseal(root, commit)
        return root

    def reseal(self, root, commit="b" * 40):
        (root / "PROVENANCE").write_text(
            f"sealed_by=scripts/promote-toolchain.sh\nreported_commit={commit}\n"
            f"artifact_content_scope={STACK.seal.SCOPE}\n"
            f"artifact_content_sha256={STACK.seal.identity(root)[0]}\n")

    def result(self):
        return json.loads((self.args.out / "result.json").read_text())

    def test_complete_standin_run_retains_separate_compilation_and_execution(self):
        self.assertEqual(STACK.Feedback(self.args).run(), 0, self.result())
        data = self.result()
        self.assertEqual(data["status"], "measured")
        phases = data["phases"]
        self.assertEqual(len([p for p in phases if p["metric_scope"] == "consumer_compilation_only"]), 2)
        samples = [p for p in phases if p["metric_scope"] == "native_test_execution"]
        self.assertEqual(len(samples), 4)
        self.assertTrue(all(p["resources"] for p in samples))
        native = [p for p in phases if p["metric_scope"] in ("test_inventory", "native_test_execution")]
        self.assertEqual(len(native), 8)
        self.assertTrue(all(p["native_executable"] == p["native_executable_after"] for p in native))
        for label, targets in data["inputs"]["native_test_executables"].items():
            self.assertEqual(set(targets), set(STACK.TARGETS))
            for identity in targets.values():
                self.assertEqual(identity["sha256"], STACK.sha(Path(identity["path"])))
                self.assertTrue(Path(identity["path"]).is_relative_to(self.args.out / f"{label}-target"))
        self.assertTrue(all(p["argv"][0:2] == [str(self.slot), "--"] for p in phases))
        self.assertTrue((self.args.out / "proof-comparison.json").is_file())
        self.assertIn("no proof", data["claim_scope"])

    def test_same_seal_baseline_retains_independent_targets_and_identical_tools(self):
        self.args.control = self.args.candidate
        self.assertEqual(STACK.Feedback(self.args).run(), 0, self.result())
        data = self.result()
        self.assertEqual(data["inputs"]["control"]["content_sha256"], data["inputs"]["candidate"]["content_sha256"])
        binaries = data["inputs"]["native_test_executables"]
        for target in STACK.TARGETS:
            self.assertNotEqual(binaries["control"][target]["path"], binaries["candidate"][target]["path"])

    def test_distinct_proof_targets_cannot_share_one_native_executable(self):
        for commit in ("a" * 40, "b" * 40):
            self.make_toolchain(commit, artifact_ambiguity="shared-executable")
        rc = STACK.Feedback(self.args).run()
        data = self.result()
        self.assertEqual(rc, 1, {"status": data["status"], "artifacts": data["inputs"].get("native_test_executables")})
        self.assertIn("same native executable", data["failures"][-1]["reason"])
        self.assertFalse(any(p["metric_scope"] == "test_inventory" for p in data["phases"]))

    def test_duplicate_native_target_reports_are_refused_before_inventory(self):
        for commit in ("a" * 40, "b" * 40):
            self.make_toolchain(commit, artifact_ambiguity="duplicate-target")
        rc = STACK.Feedback(self.args).run()
        data = self.result()
        self.assertEqual(rc, 1, {"status": data["status"], "artifacts": data["inputs"].get("native_test_executables")})
        self.assertIn("ambiguous native test executable", data["failures"][-1]["reason"])
        self.assertFalse(any(p["metric_scope"] == "test_inventory" for p in data["phases"]))

    def test_distinct_native_paths_cannot_alias_one_hardlinked_executable(self):
        for commit in ("a" * 40, "b" * 40):
            self.make_toolchain(commit, artifact_ambiguity="hardlinked-executable")
        self.assertEqual(STACK.Feedback(self.args).run(), 1, self.result())
        data = self.result()
        self.assertIn("same native executable", data["failures"][-1]["reason"])
        self.assertFalse(any(p["metric_scope"] == "test_inventory" for p in data["phases"]))

    def test_missing_failed_build_receipt_is_retained_without_jobs(self):
        self.args.candidate_receipt = self.base / "failed-build/tool-provenance.json"
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        self.assertIn("no completed candidate", self.result()["failures"][0]["reason"])
        self.assertEqual(self.result()["phases"], [])

    def test_stale_candidate_commit_is_refused(self):
        self.args.candidate_commit = "d" * 40
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        self.assertIn("requested candidate", self.result()["failures"][0]["reason"])

    def test_rejected_and_unstable_receipts_do_not_run(self):
        path = self.args.candidate_receipt
        data = json.loads(path.read_text())
        data["source_lineage"]["stable_across_build"] = False
        path.write_text(json.dumps(data))
        self.reseal(self.candidate)
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        self.assertIn("stable, completed", self.result()["failures"][0]["reason"])
        self.assertEqual(self.result()["phases"], [])

    def test_modified_library_is_rejected_even_though_receipt_binds_only_executables(self):
        (self.candidate / "lib").mkdir()
        (self.candidate / "lib/changed.dylib").write_bytes(b"unrecorded compiler implementation")
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        self.assertIn("content differs", self.result()["failures"][0]["reason"])

    def test_metadata_failure_is_retained_with_actual_exit_and_logs(self):
        self.make_toolchain("b" * 40, metadata_fail=True)
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        failed = [p for p in self.result()["phases"] if p.get("returncode") == 12]
        self.assertTrue(failed)
        self.assertIn("named dependency resolution failure", Path(failed[0]["stderr"]).read_text())

    def test_native_test_failure_remains_visible_after_other_phases_finish(self):
        self.make_toolchain("b" * 40, test_fail=True)
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        data = self.result()
        self.assertEqual(data["status"], "measured_with_failures")
        self.assertTrue(any(p.get("returncode") == 9 for p in data["phases"]))
        self.assertTrue((self.args.out / "proof-comparison.json").is_file())

    def test_native_inventory_mutation_is_refused_before_any_sample(self):
        self.make_toolchain("b" * 40, native_mutation="inventory")
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        data = self.result()
        self.assertEqual(data["status"], "refused")
        self.assertIn("native test executable changed", data["failures"][-1]["reason"])
        phase = data["phases"][-1]
        self.assertEqual(phase["name"], "candidate.ay_refutation_step_realbody.inventory")
        self.assertEqual(phase["returncode"], 0)
        self.assertIn("honest_verified: test", Path(phase["stdout"]).read_text())
        self.assertNotEqual(phase["native_executable"]["sha256"], phase["native_executable_after"]["sha256"])

    def test_final_native_sample_mutation_is_refused_and_actual_exit_retained(self):
        for fail in (False, True):
            with self.subTest(fail=fail):
                self.args.out = self.base / f"sample-mutation-{fail}"
                self.make_toolchain("b" * 40, native_mutation="sample", test_fail=fail)
                self.assertEqual(STACK.Feedback(self.args).run(), 1)
                data = self.result()
                self.assertEqual(data["status"], "refused")
                self.assertIn("native test executable changed", data["failures"][-1]["reason"])
                phase = data["phases"][-1]
                self.assertEqual(phase["name"], "candidate.ay_refutation_step_realbody.sample-1")
                self.assertEqual(phase["returncode"], 9 if fail else 0)
                self.assertTrue(phase["resources"])
                self.assertTrue(Path(phase["stdout"]).is_file())
                self.assertNotEqual(phase["native_executable"]["sha256"], phase["native_executable_after"]["sha256"])

    def test_changed_native_artifact_before_phase_never_starts_a_job(self):
        runner = STACK.Feedback(self.args)
        runner.preflight()
        binary = self.args.out / "control-target/native"
        executable(binary, "#!/bin/sh\nexit 0\n")
        identity = runner.native_identity(binary, "control")
        binary.write_text("#!/bin/sh\nexit 9\n")
        with self.assertRaisesRegex(STACK.Refused, "native test executable changed before phase"):
            runner.job("must-not-start", [str(binary)], self.vc, "control", "test_inventory", native_executable=identity)
        self.assertEqual(runner.report["phases"], [])

    def test_source_drift_stops_the_next_job_and_preserves_prior_output(self):
        runner = STACK.Feedback(self.args)
        runner.preflight()
        argv = [sys.executable, "-c", "from pathlib import Path; print('retained'); Path('Cargo.lock').write_text('changed')"]
        with self.assertRaisesRegex(STACK.Refused, "source is dirty"):
            runner.job("drift", argv, self.ay, "control", "stand-in")
        self.assertEqual(Path(runner.report["phases"][0]["stdout"]).read_text().strip(), "retained")
        self.assertEqual(len(runner.report["phases"]), 1)

    def test_assume_unchanged_source_cannot_hide_a_mutation(self):
        self.git(self.ay, "update-index", "--assume-unchanged", "Cargo.lock")
        (self.ay / "Cargo.lock").write_text("hidden change")
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        self.assertIn("assume-unchanged", self.result()["failures"][0]["reason"])

    def test_plan_performs_no_measurements_and_keeps_explicit_commands(self):
        self.args.action = "plan"
        self.assertEqual(STACK.Feedback(self.args).run(), 0)
        data = self.result()
        self.assertEqual(data["status"], "planned")
        self.assertTrue(all(p["status"] == "planned" for p in data["phases"]))
        self.assertFalse(any(self.args.out.glob("*.stdout")))
        self.assertIn("candidate.consumer-build", data["commands"])

    def test_metadata_uses_the_real_targo_noncompiling_command_contract(self):
        done = subprocess.run([str(self.control / "bin/targo"), "--unverified", "metadata"],
                              cwd=self.ay, capture_output=True, text=True)
        self.assertEqual(done.returncode, 2)
        runner = STACK.Feedback(self.args)
        runner.preflight()
        self.assertIsNotNone(runner.metadata("control", "ay"))
        self.assertEqual(runner.report["phases"][0]["payload_argv"][1], "metadata")
        self.assertNotIn("--unverified", runner.report["phases"][0]["payload_argv"])

    def external_link(self, relative):
        external = self.base / "external.rs"
        external.write_text("// mutable external source\n")
        path = self.ay / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.unlink(missing_ok=True)
        path.symlink_to(external)
        self.commit(self.ay)
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        self.assertIn("fully bound file closure", self.result()["failures"][0]["reason"])
        self.assertEqual(self.result()["phases"], [])

    def test_external_source_symlink_is_refused(self):
        self.external_link("src/external.rs")

    def test_external_proof_fixture_symlink_is_refused(self):
        self.external_link(next(iter(STACK.FIXTURES.values())))

    def test_symlink_to_internal_ignored_source_is_refused(self):
        (self.ay / ".gitignore").write_text("ignored.rs\n")
        (self.ay / "ignored.rs").write_text("// unbound\n")
        (self.ay / "linked.rs").symlink_to("ignored.rs")
        self.commit(self.ay)
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        self.assertIn("fully bound file closure", self.result()["failures"][0]["reason"])

    def test_internal_symlink_to_tracked_source_is_bound(self):
        (self.ay / "linked.rs").symlink_to("Cargo.toml")
        self.commit(self.ay)
        runner = STACK.Feedback(self.args)
        runner.preflight()
        (self.ay / "Cargo.toml").write_text("changed symlink target")
        with self.assertRaisesRegex(STACK.Refused, "source is dirty"):
            runner.check_inputs()

    def test_ignored_intermediate_link_cannot_change_frozen_source(self):
        (self.ay / ".gitignore").write_text("ignored/\n")
        for name in ("first.rs", "second.rs"):
            (self.ay / name).write_text(name)
        (self.ay / "ignored").mkdir()
        hop = self.ay / "ignored/hop"
        hop.symlink_to("../first.rs")
        selected = self.ay / "linked.rs"
        selected.symlink_to("ignored/hop")
        self.commit(self.ay)
        runner = STACK.Feedback(self.args)
        runner.preflight()
        self.assertEqual(selected.read_text(), "first.rs")
        hop.unlink()
        hop.symlink_to("../second.rs")
        self.assertEqual(selected.read_text(), "second.rs")
        self.assertEqual(self.git(self.ay, "status", "--porcelain"), "")
        with self.assertRaisesRegex(STACK.Refused, "frozen source changed: ay"):
            runner.check_inputs()

    def test_excluded_link_hop_cannot_change_frozen_dependency(self):
        root = self.base / "registry-package"
        (root / ".git").mkdir(parents=True)
        manifest = root / "Cargo.toml"
        manifest.write_text('[package]\nname="fixture-dependency"\nversion="0.1.0"\n')
        for name in ("first.rs", "second.rs"):
            (root / name).write_text(name)
        hop = root / ".git/hop"
        hop.symlink_to("../first.rs")
        selected = root / "linked.rs"
        selected.symlink_to(".git/hop")
        package = {"id": "fixture-dependency 0.1.0", "name": "fixture-dependency", "version": "0.1.0",
                   "source": "registry+https://github.com/rust-lang/crates.io-index", "manifest_path": str(manifest)}
        self.make_toolchain("a" * 40, extra_packages=[package])
        runner = STACK.Feedback(self.args)
        runner.preflight()
        runner.metadata("control", "ay")
        runner.check_inputs()
        self.assertEqual(selected.read_text(), "first.rs")
        before = runner.dependencies[str(root)]["sha256"]
        hop.unlink()
        hop.symlink_to("../second.rs")
        self.assertEqual(selected.read_text(), "second.rs")
        with self.subTest("between phases"), self.assertRaisesRegex(STACK.Refused, "dependency source bytes changed"):
            runner.check_inputs()
        with self.subTest("complete content digest"):
            self.assertNotEqual(STACK.dependency_identity(root), before)

    def test_ignored_path_package_under_source_root_is_refused(self):
        (self.ay / ".gitignore").write_text("ignored-package/\n")
        self.commit(self.ay)
        package = self.ay / "ignored-package"
        package.mkdir()
        manifest = package / "Cargo.toml"
        manifest.write_text('[package]\nname="extra"\nversion="0.1.0"\n')
        extra = [{"id": "extra 0.1.0", "name": "extra", "source": None,
                  "manifest_path": str(manifest)}]
        self.make_toolchain("a" * 40, extra_packages=extra)
        runner = STACK.Feedback(self.args)
        runner.preflight()
        with self.assertRaisesRegex(STACK.Refused, "unbound path-package manifest"):
            runner.metadata("control", "ay")
        self.assertEqual(runner.report["phases"][0]["status"], "passed")

    def test_new_ignored_package_source_is_refused_between_phases(self):
        (self.ay / ".gitignore").write_text("*.generated.rs\n")
        self.commit(self.ay)
        runner = STACK.Feedback(self.args)
        runner.preflight()
        runner.metadata("control", "ay")
        (self.ay / "crates/ay-proof-common/unbound.generated.rs").write_text("// ignored mutation\n")
        with self.assertRaisesRegex(STACK.Refused, "unbound ignored path-package input"):
            runner.check_inputs()

    def test_ignored_root_cargo_configs_are_bound_and_mutation_refuses(self):
        (self.ay / ".gitignore").write_text(".cargo/\n")
        self.commit(self.ay)
        configs = self.ay / ".cargo"
        configs.mkdir()
        for name in ("config", "config.toml"):
            (configs / name).write_text("[build]\njobs = 1\n")
        runner = STACK.Feedback(self.args)
        runner.preflight()
        for name in ("config", "config.toml"):
            path = configs / name
            self.assertEqual(runner.config_identity[str(path)], STACK.sha(path))
        (configs / "config.toml").write_text("[build]\njobs = 2\n")
        with self.assertRaisesRegex(STACK.Refused, "Cargo configuration changed"):
            runner.check_inputs()

    def test_git_dependency_binds_enclosing_workspace_and_shared_files(self):
        root = self.base / "dependency-workspace"
        package = root / "crates/helper"
        package.mkdir(parents=True)
        (root / "Cargo.toml").write_text('[workspace]\nmembers=["crates/helper"]\n')
        manifest = package / "Cargo.toml"
        manifest.write_text('[package]\nname="helper"\nversion="0.1.0"\n')
        shared = root / "shared.rs"
        shared.write_text("// workspace shared source\n")
        self.git(root, "init", "-q", "-b", "main")
        self.commit(root)
        commit = self.git(root, "rev-parse", "HEAD")
        extra = [{"id": "helper 0.1.0", "name": "helper", "source": f"git+file://{root}#{commit}",
                  "manifest_path": str(manifest)}]
        self.make_toolchain("a" * 40, extra_packages=extra)
        runner = STACK.Feedback(self.args)
        runner.preflight()
        runner.metadata("control", "ay")
        self.assertIn(str(root), runner.dependencies)
        self.assertNotIn(str(package), runner.dependencies)
        shared.write_text("// shared source changed outside package subtree\n")
        with self.assertRaisesRegex(STACK.Refused, "dependency source bytes changed"):
            runner.check_inputs()

    def git_dependency(self):
        root = self.base / "cargo-checkout"
        root.mkdir()
        manifest = root / "Cargo.toml"
        manifest.write_text('[package]\nname="helper"\nversion="0.1.0"\n')
        self.git(root, "init", "-q", "-b", "main")
        self.commit(root)
        commit = self.git(root, "rev-parse", "HEAD")
        packages = [{"id": "helper 0.1.0", "name": "helper", "source": f"git+file://{root}#{commit}",
                     "manifest_path": str(manifest)}]
        return root, packages

    def test_empty_cargo_marker_is_bound_only_for_git_dependency_checkouts(self):
        root, _ = self.git_dependency()
        before = STACK.dependency_identity(root)
        (root / ".cargo-ok").touch()
        with self.assertRaisesRegex(STACK.Refused, "source is dirty"):
            STACK.source_identity(root, require_lock=False)
        identity = STACK.source_identity(root, require_lock=False, cargo_checkout=True)
        marker = identity["cargo_checkout_marker"]
        self.assertEqual(marker["sha256"], hashlib.sha256(b"").hexdigest())
        self.assertEqual(marker["mode"], (root / ".cargo-ok").lstat().st_mode)
        self.assertNotEqual(STACK.dependency_identity(root), before)

    def test_cargo_marker_exception_does_not_admit_other_untracked_paths(self):
        root, _ = self.git_dependency()
        (root / ".cargo-ok").touch()
        for name in (".cargo-ok\n", "nested/.cargo-ok", ".cargo-ok-extra", "unexpected.rs"):
            with self.subTest(name=name):
                path = root / name
                path.parent.mkdir(exist_ok=True)
                path.touch()
                with self.assertRaisesRegex(STACK.Refused, "source is dirty"):
                    STACK.source_identity(root, require_lock=False, cargo_checkout=True)
                path.unlink()

    def test_nonempty_link_directory_and_fifo_cargo_markers_refuse(self):
        root, _ = self.git_dependency()
        marker = root / ".cargo-ok"
        for kind in ("nonempty", "symlink", "directory", "fifo"):
            with self.subTest(kind=kind):
                if kind == "nonempty":
                    marker.write_bytes(b"\n")
                elif kind == "symlink":
                    marker.symlink_to("Cargo.toml")
                elif kind == "directory":
                    marker.mkdir()
                else:
                    os.mkfifo(marker)
                with self.assertRaisesRegex(STACK.Refused, "invalid Cargo checkout marker"):
                    STACK.source_identity(root, require_lock=False, cargo_checkout=True)
                if kind == "directory":
                    marker.rmdir()
                else:
                    marker.unlink()

    def test_marker_replacement_before_open_refuses_without_following_or_blocking(self):
        root, _ = self.git_dependency()
        marker = root / ".cargo-ok"
        real_open = os.open
        for kind in ("symlink", "fifo"):
            with self.subTest(kind=kind):
                marker.touch()
                def replace_then_open(path, flags):
                    self.assertTrue(flags & os.O_NOFOLLOW)
                    self.assertTrue(flags & os.O_NONBLOCK)
                    marker.unlink()
                    if kind == "symlink":
                        marker.symlink_to("Cargo.toml")
                    else:
                        os.mkfifo(marker)
                    return real_open(path, flags)
                with mock.patch.object(STACK.os, "open", side_effect=replace_then_open):
                    with self.assertRaises(STACK.Refused):
                        STACK.cargo_checkout_marker(root)
                marker.unlink()

    def test_cargo_marker_mutation_and_removal_refuse_between_metadata_and_next_job(self):
        root, packages = self.git_dependency()
        marker = root / ".cargo-ok"
        self.make_toolchain("a" * 40, extra_packages=packages)
        for kind in ("mutation", "removal"):
            with self.subTest(kind=kind):
                marker.write_bytes(b"")
                self.args.out = self.base / f"marker-drift-{kind}"
                runner = STACK.Feedback(self.args)
                runner.preflight()
                runner.metadata("control", "ay")
                runner.check_inputs()
                if kind == "mutation":
                    marker.write_bytes(b"changed")
                else:
                    marker.unlink()
                with self.assertRaisesRegex(STACK.Refused, "dependency source bytes changed"):
                    runner.check_inputs()

    def test_complete_standin_run_with_pinned_git_dependency_and_empty_marker(self):
        root, packages = self.git_dependency()
        (root / ".cargo-ok").touch()
        for commit in ("a" * 40, "b" * 40):
            self.make_toolchain(commit, extra_packages=packages)
        self.assertEqual(STACK.Feedback(self.args).run(), 0, self.result())
        self.assertEqual(self.result()["status"], "measured")
        self.assertEqual(self.result()["inputs"]["dependency_source_sha256"][str(root)],
                         STACK.dependency_identity(root))
        self.assertIn("no proof", self.result()["claim_scope"])

    def test_incomplete_or_divergent_censuses_remain_named_failures(self):
        gate = self.ay / "scripts/ci/trust_verification_ratchet_gate.sh"
        incomplete = RATCHET.replace("(out/'current.json').write_text", """
data['obligation_ledger']['denominator_is_complete']=False
data['obligation_ledger']['vcgen_truncated_functions']=1
data['obligation_ledger']['vcgen_truncated_function_names']=['truncated_function']
data['strict_lane']['verdict_census_matches_advisory']=False
(out/'current.json').write_text""")
        executable(gate, f"#!/bin/sh\nexec \"{sys.executable}\" - <<'PY'\n{incomplete}\nPY\n")
        self.commit(self.ay)
        self.assertEqual(STACK.Feedback(self.args).run(), 1)
        data = self.result()
        self.assertEqual(data["status"], "measured_with_failures")
        self.assertEqual(len([f for f in data["failures"] if ".census-" in f["phase"]]), 4)
        for census in data["census"].values():
            self.assertIs(census["obligation_ledger"]["denominator_is_complete"], False)
            self.assertEqual(census["obligation_ledger"]["vcgen_truncated_functions"], 1)
            self.assertIs(census["strict_lane"]["verdict_census_matches_advisory"], False)
        self.assertFalse((self.args.out / "proof-comparison.json").exists())

    def test_each_census_integrity_field_is_required_independently(self):
        complete = {"obligation_ledger": {"denominator_is_complete": True, "vcgen_truncated_functions": 0},
                    "strict_lane": {"verdict_census_matches_advisory": True}}
        self.assertEqual(STACK.census_failures(complete), [])
        for section, key, value, phase in (
                ("obligation_ledger", "denominator_is_complete", False, "census-completeness"),
                ("obligation_ledger", "vcgen_truncated_functions", 1, "census-completeness"),
                ("obligation_ledger", "vcgen_truncated_functions", False, "census-completeness"),
                ("strict_lane", "verdict_census_matches_advisory", False, "census-lane-agreement")):
            with self.subTest(key=key, value=value):
                census = json.loads(json.dumps(complete))
                census[section][key] = value
                self.assertEqual([f[0] for f in STACK.census_failures(census)], [phase])
                del census[section][key]
                self.assertEqual([f[0] for f in STACK.census_failures(census)], [phase])

    def test_forbidden_output_placement_never_creates_directories_or_records(self):
        alias = self.base / "source-alias"
        alias.symlink_to(self.ay, target_is_directory=True)
        for root in (self.ay, self.vc, self.control, self.candidate, alias):
            with self.subTest(root=root):
                forbidden = root / "must-not-exist/results"
                self.args.out = forbidden
                with self.assertRaisesRegex(STACK.Refused, "outside every source/toolchain"):
                    STACK.Feedback(self.args)
                self.assertFalse((root / "must-not-exist").exists())

    def test_timeout_kills_owned_term_ignoring_group_before_admission_release(self):
        lease = self.base / "admission.lock"
        check = self.base / "lease-at-release.json"
        state = self.args.out / "timeout.process.json"
        # Match build-slot's separate session and lease lifetime, without using
        # the machine-wide pool for a tiny stand-in regression.
        executable(self.slot, PYTHON_SHEBANG + f'''import fcntl,json,os,pathlib,subprocess,sys
with open({str(lease)!r},'w') as lease:
    fcntl.flock(lease,fcntl.LOCK_EX)
    child=subprocess.Popen(sys.argv[2:],start_new_session=True)
    rc=child.wait()
    state=json.load(open({str(state)!r}))
    rows=subprocess.check_output(['/bin/ps','-axo','pgid=,stat='],text=True).splitlines()
    live=any(len(p:=r.split())==2 and int(p[0])==state['workload_pgid'] and not p[1].startswith('Z') for r in rows)
    pathlib.Path({str(check)!r}).write_text(json.dumps({{'live_at_lease_release':live}}))
sys.exit(rc)
''')
        unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"], start_new_session=True)
        self.addCleanup(lambda: (unrelated.kill(), unrelated.wait()) if unrelated.poll() is None else None)
        self.args.timeout = 1
        runner = STACK.Feedback(self.args)
        runner.preflight()
        observations = []
        finished = threading.Event()

        def observe():
            while not finished.wait(0.05):
                if state.is_file() and (data := STACK.load(state)).get("term_sent"):
                    with lease.open() as lock:
                        try:
                            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                            held = False
                        except BlockingIOError:
                            held = True
                    observations.append(held)

        observer = threading.Thread(target=observe)
        observer.start()
        child = "import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); time.sleep(60)"
        workload = ("import signal,subprocess,sys,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); "
                    f"subprocess.Popen([sys.executable,'-c',{child!r}]); "
                    "print('owned workload retained',flush=True); time.sleep(60)")
        try:
            with self.assertRaisesRegex(STACK.Refused, "phase interrupted"):
                runner.job("timeout", [sys.executable, "-c", workload], self.ay, "control", "stand-in")
        finally:
            finished.set()
            observer.join(timeout=5)
        phase = runner.report["phases"][0]
        self.assertEqual(phase["status"], "interrupted")
        self.assertIs(phase["process"]["terminal_confirmed"], True)
        self.assertIs(phase["process"]["kill_sent"], True)
        self.assertEqual(phase["process"]["workload_returncode"], -9)
        self.assertFalse(STACK.process_group_live(phase["process"]["workload_pgid"]))
        self.assertFalse(STACK.load(check)["live_at_lease_release"])
        self.assertTrue(any(observations), "admission was never observed held during TERM grace")
        self.assertIsNone(unrelated.poll())
        self.assertIn("owned workload retained", Path(phase["stdout"]).read_text())

    def test_timeout_before_admission_cannot_launch_a_workload_later(self):
        executable(self.slot, PYTHON_SHEBANG + "import time\ntime.sleep(60)\n")
        self.args.timeout = 1
        marker = self.base / "must-not-launch"
        runner = STACK.Feedback(self.args)
        runner.preflight()
        with self.assertRaisesRegex(STACK.Refused, "phase interrupted"):
            runner.job("queued", [sys.executable, "-c", f"open({str(marker)!r},'w').close()"],
                       self.ay, "control", "stand-in")
        self.assertFalse(marker.exists())
        self.assertEqual(runner.report["phases"][0]["status"], "interrupted")


if __name__ == "__main__":
    unittest.main()
