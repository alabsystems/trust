#!/usr/bin/env python3
"""Focused mock tests for the real-code coverage evidence receipt."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path


SOURCE_SCRIPT = Path(__file__).resolve().parents[1] / "collect_realcode_coverage_evidence.py"
TRUSTC_IDENTITY = """rustc 1.99.0-dev (012345678 2026-07-20) (trustc)
binary: trustc
commit-hash: 0123456789012345678901234567890123456789
commit-date: 2026-07-20
host: test-host
release: 1.99.0-dev
LLVM version: test"""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_executable(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    path.chmod(0o755)


class Fixture:
    def __init__(self, root: Path, mode: str) -> None:
        # macOS exposes /var as a system symlink to /private/var. Normal fixture
        # outputs use the canonical parent; the dedicated symlink test adds its
        # own lexical parent symlink below that safe root.
        root = root.resolve()
        self.repo = root / "repo"
        self.output = root / "receipt.json"
        self.repo.mkdir()
        (self.repo / "scripts/tests").mkdir(parents=True)
        (self.repo / "reports/2026-06-29-honest-real-code-coverage/corpus").mkdir(parents=True)
        shutil.copy2(SOURCE_SCRIPT, self.repo / "scripts/collect_realcode_coverage_evidence.py")
        (self.repo / ".gitignore").write_text("build/\n", encoding="utf-8")
        (self.repo / "reports/2026-06-29-honest-real-code-coverage/corpus/realcode.rs").write_text(
            "pub fn alpha() -> i32 { 1 }\npub fn beta() -> i32 { 2 }\n", encoding="utf-8"
        )
        (self.repo / "reports/2026-06-29-honest-real-code-coverage/analyze.py").write_text(
            textwrap.dedent(
                """\
                #!/usr/bin/env python3
                import json, pathlib, sys
                files = sorted(pathlib.Path(sys.argv[1]).glob("*.json"))
                documents = [json.loads(path.read_text()) for path in files]
                print(json.dumps({
                    "n_functions": len(files),
                    "type_coverage": {"method": "report-local-syntactic-ty-constructor-count.v1",
                                      "claim_boundary": "fixture secondary census",
                                      "total_ty_nodes": 0, "structural_nodes": 0,
                                      "failclosed_nodes": 0, "pct_structural": 0,
                                      "structural_by_ctor": {}, "failclosed_by_ctor": {}},
                    "func_type_coverage": {"func_with_only_structural_types": len(files),
                                           "pct_func_clean_types": 100,
                                           "func_with_failclosed_ty_by_ctor": {},
                                           "func_with_unsupported_stmt": 0},
                    "loop_coverage": {"method": "report-local-mir-shape-heuristic.v1",
                                      "claim_boundary": "fixture approximation",
                                      "n_functions_with_loops": 0, "total_loop_headers": 0,
                                      "by_kind": {}, "pct_recognized": None},
                    "per_func": [{"def_path": document["def_path"]} for document in documents]
                }))
                """
            ),
            encoding="utf-8",
        )
        (self.repo / "scripts/recreate_bootstrap.py").write_text(
            "#!/usr/bin/env python3\nprint('verified existing stage provenance (internal-release-ready)')\n",
            encoding="utf-8",
        )
        self._git("init", "-q")
        self._git("config", "user.email", "fixture@example.invalid")
        self._git("config", "user.name", "Coverage Fixture")
        self._git("add", ".")
        self._git("-c", "commit.gpgsign=false", "commit", "-qm", "fixture")
        self.head = self._git("rev-parse", "HEAD").stdout.strip()

        self.trustc = self.repo / "build/test-host/stage2/bin/trustc"
        self.targo = self.repo / "build/test-host/stage2/bin/targo-trust"
        write_executable(self.trustc, self._fake_trustc(mode))
        write_executable(self.targo, self._fake_targo(mode))
        provenance = {
            "schema": "trust.stage-tool-provenance.v2",
            "status": "internal-release-ready",
            "stage": 2,
            "host": "test-host",
            "path_scope": "repository-root-relative",
            "source_tree_clean": True,
            "tool_binding_status": "ready",
            "errors": [],
            "bootstrap_lineage": {"status": "trust_from_trust"},
            "source_lineage": {
                "schema": "trust.source-lineage.v1",
                "status": "immutable_release",
                "errors": [],
                "stable_across_build": True,
                "source_tree_clean": True,
                "repositories": [{"path": ".", "head": self.head}],
            },
            "compiler": {
                "path": "build/test-host/stage2/bin/trustc",
                "compiler_sha256": sha256(self.trustc),
                "source_commit": self.head,
                "compiler_verbose": TRUSTC_IDENTITY,
            },
            "tools": [
                {
                    "name": "targo-trust",
                    "path": "build/test-host/stage2/bin/targo-trust",
                    "sha256": sha256(self.targo),
                    "status": "bound",
                }
            ],
        }
        (self.repo / "build/test-host/stage2/tool-provenance.json").write_text(
            json.dumps(provenance, sort_keys=True), encoding="utf-8"
        )

    def _git(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", "-C", str(self.repo), *args],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    @staticmethod
    def _fake_trustc(mode: str) -> str:
        return textwrap.dedent(
            f'''\
            #!/usr/bin/env python3
            import json, os, pathlib, sys
            MODE = {mode!r}
            IDENTITY = {TRUSTC_IDENTITY!r}
            forbidden = ("PYTHONPATH", "PYTHONHOME", "LD_PRELOAD", "DYLD_INSERT_LIBRARIES")
            if any(name in os.environ for name in forbidden):
                print("hostile ambient variable reached trustc", file=sys.stderr)
                raise SystemExit(91)
            if any("/hostile/" in os.environ.get(name, "")
                   for name in ("LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH")):
                print("ambient dynamic path reached trustc", file=sys.stderr)
                raise SystemExit(91)
            if "-vV" in sys.argv:
                print(IDENTITY)
                raise SystemExit(0)
            session = next((arg.split("=", 1)[1] for arg in sys.argv
                            if arg.startswith("-Ztrust-verify-session=")), "")
            dump_arg = next((arg for arg in sys.argv if arg.startswith("-Ztrust-dump=mir-only:")), None)
            dump_only = "-Ztrust-dump=mir-only:<dir>" in sys.argv
            functions = ["realcode::alpha", "realcode::beta"]
            if dump_arg is not None:
                dump = pathlib.Path(dump_arg.split("=", 1)[1])
                dump.mkdir(parents=True, exist_ok=True)
                for index, function in enumerate(functions):
                    if MODE == "missing_dump" and index == 1:
                        continue
                    path = dump / ("function-" + str(index) + ".json")
                    if MODE == "malformed_dump" and index == 1:
                        path.write_text("{{malformed")
                    else:
                        path.write_text(json.dumps({{"name": function.rsplit("::", 1)[-1],
                                                    "def_path": function,
                                                    "body": {{"locals": [], "blocks": []}}}}))
            processed_functions = functions if MODE != "incomplete" else functions[:1]
            for function in processed_functions:
                outcome = "unknown" if dump_only else ("proved" if function.endswith("alpha") else "failed")
                print("TRUST_COVERAGE: " + function + " => analyzed:1", file=sys.stderr)
                result = {{"kind": "overflow:add", "description": "fixture obligation",
                          "outcome": outcome, "solver": "fixture", "time_ms": 0}}
                counts = {{"proved": int(outcome == "proved"), "failed": int(outcome == "failed"),
                          "unknown": int(outcome == "unknown"), "timed_out": 0, "skipped": 0,
                          "runtime_checked": 0, "cached": 0, "total": 1}}
                message = {{"type": "function_result", "function": function,
                           "package_name": None, "crate_name": "realcode", "primary_package": False,
                           "verification_session": session, "results": [result], **counts}}
                print("TRUST_JSON:" + json.dumps(message, separators=(",", ":")), file=sys.stderr)
            eligible = len(functions)
            processed = len(processed_functions)
            coverage = {{"type": "coverage_summary", "crate_name": "realcode",
                        "package_name": "", "primary_package": False,
                        "verification_session": session, "eligible": eligible, "processed": processed,
                        "function_identities": {{"schema": "trustc.coverage-function-identities.v1",
                            "eligible_functions": functions, "processed_functions": processed_functions}}}}
            print("TRUST_JSON:" + json.dumps(coverage, separators=(",", ":")), file=sys.stderr)
            proved = 0 if dump_only else 1
            failed = 0 if dump_only or processed == 1 else 1
            unknown = processed if dump_only else 0
            summary = {{"type": "crate_summary", "crate_name": "realcode", "package_name": None,
                       "primary_package": False, "verification_session": session,
                       "functions_analyzed": processed,
                       "functions_verified": proved,
                       "total_proved": proved, "total_failed": failed, "total_unknown": unknown,
                       "total_timed_out": 0, "total_skipped": 0, "total_runtime_checked": 0,
                       "total_obligations": processed}}
            print("TRUST_JSON:" + json.dumps(summary, separators=(",", ":")), file=sys.stderr)
            '''
        )

    @staticmethod
    def _fake_targo(mode: str) -> str:
        return textwrap.dedent(
            """\
            #!/usr/bin/env python3
            import json, os, pathlib, sys
            MODE = __MODE__
            forbidden = ("PYTHONPATH", "PYTHONHOME", "LD_PRELOAD", "DYLD_INSERT_LIBRARIES")
            if any(name in os.environ for name in forbidden):
                print("hostile ambient variable reached targo-trust", file=sys.stderr)
                raise SystemExit(91)
            if any("/hostile/" in os.environ.get(name, "")
                   for name in ("LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH")):
                print("ambient dynamic path reached targo-trust", file=sys.stderr)
                raise SystemExit(91)
            if "--version" in sys.argv:
                print("targo-trust 0.1.0-fixture")
                raise SystemExit(0)
            dump = pathlib.Path(sys.argv[sys.argv.index("--dump-dir") + 1])
            total = len(list(dump.glob("*.json")))
            budget = int(next(arg.split("=", 1)[1] for arg in sys.argv if arg.startswith("--budget-secs=")))
            scorecard = {
                "total": total,
                "inhabited": 0,
                "type_grounded_not_inhabited": 0,
                "not_grounded": total,
                "kernel_rejected": int(MODE == "kernel_rejected"),
                "proven": [],
                "rejections": (["fixture kernel rejection"] if MODE == "kernel_rejected" else []),
                "total_obligations": total,
                "postcondition_obligations": 0,
                "safety_obligations": total,
                "safety_discharged": 0,
                "structural_adts": 0,
                "structural_enums": 0,
                "structural_floats": 0,
                "structural_field_obligations": 0,
                "opaque_struct_obligations": 0,
                "faithfulness_certified": 0,
                "faithfulness_full": 0,
                "safety_vc_faithful": 0,
                "safety_vc_faithful_overflow": 0,
                "safety_vc_faithful_usub": 0,
                "safety_vc_faithful_signed_overflow": 0,
                "safety_vc_faithful_bounds": 0,
                "safety_vc_faithful_div": 0,
                "safety_vc_faithful_rem": 0,
                "safety_vc_faithful_negation": 0,
                "safety_vc_faithful_shift": 0,
                "fully_faithful": 0,
                "mirsem_refinement_proven": 0,
                "mirsem_branch_refinement_proven": 0,
                "loop_refinement_proven": 0,
                "loop_total_correct_proven": 0,
                "loop_headers_detected": 1,
                "loop_headers_recognized": 0,
                "loop_synth_invariant_proven": 0,
                "nested_loop_proven": 0,
                "break_loop_proven": 0,
                "monotone_nested_proven": 0,
                "structural_containers": 0,
                "fully_faithful_via_trustir": 0,
                "fully_faithful_mirsem_fallback": 0,
                "declined": 0,
                "declined_paths": [],
                "bridge_agreement": {"status": "fixture-agreed"},
            }
            if MODE == "inflated_fully_faithful":
                scorecard["fully_faithful"] = total + 1
                scorecard["fully_faithful_via_trustir"] = total + 1
            elif MODE == "overdischarged_safety":
                scorecard["safety_discharged"] = total + 1
            elif MODE == "broken_obligation_partition":
                scorecard["total_obligations"] = total + 1
            elif MODE == "missing_bridge_agreement":
                scorecard["bridge_agreement"] = None
            print(json.dumps({
                "schema": "trust.prove-scorecard.v1",
                "status": "rejected" if MODE == "kernel_rejected" else "measured",
                "claim_boundary": "fixture",
                "budget_secs_per_function": budget,
                "scorecard": scorecard,
                "bridge_gate_error": None
            }))
            if MODE == "kernel_rejected":
                print("fixture kernel rejection", file=sys.stderr)
                raise SystemExit(1)
            """
        ).replace("__MODE__", repr(mode))

    def run(
        self, ambient_updates: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        script = str(self.repo / "scripts/collect_realcode_coverage_evidence.py")
        arguments = [
                "--repo-root",
                str(self.repo),
                "--trustc",
                str(self.trustc),
                "--targo-trust",
                str(self.targo),
                "--output",
                str(self.output),
                "--prove-budget-secs",
                "1",
                "--compile-timeout-secs",
                "20",
                "--prove-timeout-secs",
                "20",
                "--provenance-timeout-secs",
                "20",
        ]
        if ambient_updates is None:
            command = [sys.executable, script, *arguments]
        else:
            # Apply hostile ambient values after Python startup so PYTHONHOME and
            # loader variables cannot interfere with the test launcher itself.
            launcher = (
                "import json, os, runpy, sys; "
                "os.environ.update(json.loads(sys.argv[1])); "
                "script = sys.argv[2]; sys.argv = [script, *sys.argv[3:]]; "
                "runpy.run_path(script, run_name='__main__')"
            )
            command = [
                sys.executable,
                "-c",
                launcher,
                json.dumps(ambient_updates),
                script,
                *arguments,
            ]
        return subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )


class CoverageEvidenceReceiptTest(unittest.TestCase):
    def test_complete_receipt_accepts_measured_negative_outcomes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = Fixture(Path(temporary), "ok")
            fixture.output.write_bytes(b'{"old":true}\n')
            result = fixture.run()
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads(fixture.output.read_text(encoding="utf-8"))
            self.assertEqual(receipt["schema"], "trust.realcode-coverage-evidence.v1")
            self.assertTrue(receipt["population"]["coverage_complete"])
            self.assertEqual(receipt["population"]["eligible"], 2)
            self.assertEqual(receipt["population"]["dump_count"], 2)
            self.assertEqual(receipt["analysis"]["n_functions"], 2)
            self.assertEqual(receipt["proof"]["scorecard"]["total"], 2)
            self.assertEqual(receipt["verifier_loop_coverage"]["loop_headers_detected"], 1)
            self.assertEqual(receipt["survey"]["transport"]["outcome_counts"]["failed"], 1)
            self.assertEqual(receipt["stage2_provenance"]["status"], "internal-release-ready")
            self.assertIn("prove", receipt["raw_evidence"])
            self.assertEqual(
                receipt["corpus_classification"],
                {
                    "kind": "curated-hand-authored-synthetic-fixture",
                    "selection": (
                        "deliberately selected language patterns in one spec-free source file"
                    ),
                    "external_projects_sampled": 0,
                    "claim_boundary": (
                        "Measures the exact pinned fixture only; it is neither an uncurated nor a "
                        "statistically representative sample of downstream Rust projects."
                    ),
                },
            )

    def test_hostile_ambient_environment_is_excluded_from_children(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            fixture = Fixture(root, "ok")
            stage_library = fixture.trustc.parent.parent / "lib"
            stage_library.mkdir()
            hostile_bin = root / "hostile-bin"
            hostile_git_marker = root / "hostile-git-invoked"
            write_executable(
                hostile_bin / "git",
                f"#!/bin/sh\n/usr/bin/touch {hostile_git_marker}\nexit 97\n",
            )
            hostile = {
                "PATH": str(hostile_bin),
                "HOME": "/hostile/home",
                "PYTHONPATH": "/hostile/python-path",
                "PYTHONHOME": "/hostile/python-home",
                "PYTHONSTARTUP": "/hostile/python-startup.py",
                "LD_PRELOAD": "/hostile/preload.so",
                "LD_LIBRARY_PATH": "/hostile/ld-library",
                "DYLD_INSERT_LIBRARIES": "/hostile/insert.dylib",
                "DYLD_LIBRARY_PATH": "/hostile/dyld-library",
                "DYLD_FRAMEWORK_PATH": "/hostile/frameworks",
                "RUSTFLAGS": "--cfg hostile_environment",
                "CARGO_HOME": "/hostile/cargo-home",
                "DEVELOPER_DIR": "/hostile/developer",
                "SDKROOT": "/hostile/sdk",
                "MACOSX_DEPLOYMENT_TARGET": "0.0-hostile",
            }
            result = fixture.run(hostile)
            self.assertEqual(result.returncode, 0, result.stderr)
            document = json.loads(fixture.output.read_text(encoding="utf-8"))
            authority = document["environment_authority"]
            self.assertEqual(authority["schema"], "trust.coverage-environment-authority.v2")
            names = authority["value_sha256_by_name"]
            runtime_variable = authority["runtime_library_variable"]
            self.assertFalse(hostile_git_marker.exists())

            for forbidden in (
                "PYTHONPATH",
                "PYTHONHOME",
                "PYTHONSTARTUP",
                "LD_PRELOAD",
                "DYLD_INSERT_LIBRARIES",
                "DYLD_FRAMEWORK_PATH",
                "RUSTFLAGS",
                "CARGO_HOME",
                "DEVELOPER_DIR",
                "SDKROOT",
                "MACOSX_DEPLOYMENT_TARGET",
            ):
                self.assertNotIn(forbidden, names)
                self.assertIn(forbidden, authority["excluded_ambient_names"])
            ambient_library_variable = (
                "LD_LIBRARY_PATH" if runtime_variable == "DYLD_LIBRARY_PATH" else "DYLD_LIBRARY_PATH"
            )
            self.assertNotIn(ambient_library_variable, names)
            self.assertEqual(authority["derived_runtime_library_paths"], [str(stage_library)])
            self.assertEqual(
                names[runtime_variable],
                hashlib.sha256(str(stage_library).encode("utf-8")).hexdigest(),
            )
            self.assertNotEqual(
                names["HOME"], hashlib.sha256(hostile["HOME"].encode("utf-8")).hexdigest()
            )
            fixed_path = "/usr/bin:/bin:/usr/sbin:/sbin"
            self.assertEqual(names["PATH"], hashlib.sha256(fixed_path.encode()).hexdigest())
            system_git = document["tools"]["system-git"]
            self.assertTrue(Path(system_git["path"]).is_absolute())
            self.assertIn(Path(system_git["path"]), (Path("/usr/bin/git"), Path("/bin/git")))

    def test_inflated_or_inconsistent_scorecard_preserves_all_prior_evidence(self) -> None:
        cases = (
            ("inflated_fully_faithful", "one-per-function tallies exceed"),
            ("overdischarged_safety", "discharges more safety obligations"),
            ("broken_obligation_partition", "obligation partition is inconsistent"),
        )
        for mode, diagnostic in cases:
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                fixture = Fixture(Path(temporary), mode)
                accepted = b'{"accepted":"prior"}\n'
                attempted = b'{"attempt":"prior"}\n'
                fixture.output.write_bytes(accepted)
                attempt_path = fixture.output.with_name(fixture.output.name + ".last-attempt.json")
                attempt_path.write_bytes(attempted)
                result = fixture.run()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)
                self.assertEqual(fixture.output.read_bytes(), accepted)
                self.assertEqual(attempt_path.read_bytes(), attempted)

    def test_measured_scorecard_without_bridge_evidence_cannot_replace_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = Fixture(Path(temporary), "missing_bridge_agreement")
            accepted = b'{"accepted":"prior"}\n'
            fixture.output.write_bytes(accepted)
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("zero-credit diagnostic published", result.stderr)
            self.assertEqual(fixture.output.read_bytes(), accepted)
            attempt_path = fixture.output.with_name(fixture.output.name + ".last-attempt.json")
            attempt = json.loads(attempt_path.read_text(encoding="utf-8"))
            self.assertFalse(attempt["admissible_as_measurement"])
            self.assertEqual(attempt["proof_credit"], 0)
            self.assertTrue(
                any(
                    "no attached bridge agreement evidence" in reason
                    for reason in attempt["rejection_reasons"]
                )
            )

    def test_incomplete_coverage_preserves_prior_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = Fixture(Path(temporary), "incomplete")
            prior = b'{"durable":"prior"}\n'
            fixture.output.write_bytes(prior)
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("coverage incomplete", result.stderr)
            self.assertEqual(fixture.output.read_bytes(), prior)

    def test_malformed_or_missing_dump_preserves_prior_receipt(self) -> None:
        for mode, diagnostic in (("malformed_dump", "malformed JSON"), ("missing_dump", "dump population")):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                fixture = Fixture(Path(temporary), mode)
                prior = b'{"durable":"prior"}\n'
                fixture.output.write_bytes(prior)
                result = fixture.run()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)
                self.assertEqual(fixture.output.read_bytes(), prior)

    def test_output_parent_symlink_is_rejected_without_touching_target(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            fixture = Fixture(root, "ok")
            target_dir = root / "target"
            target_dir.mkdir()
            target = target_dir / "receipt.json"
            prior = b'{"durable":"prior"}\n'
            target.write_bytes(prior)
            link = root / "linked-output"
            link.symlink_to(target_dir, target_is_directory=True)
            fixture.output = link / "receipt.json"
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("parent component is a symlink", result.stderr)
            self.assertEqual(target.read_bytes(), prior)

    def test_kernel_rejection_preserves_accepted_receipt_and_publishes_zero_credit_attempt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = Fixture(Path(temporary), "kernel_rejected")
            prior = b'{"accepted":"prior"}\n'
            fixture.output.write_bytes(prior)
            diagnostic = fixture.output.with_name(fixture.output.name + ".last-attempt.json")
            diagnostic.write_bytes(b'{"older":"attempt"}\n')
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("zero-credit diagnostic published", result.stderr)
            self.assertEqual(fixture.output.read_bytes(), prior)
            attempt = json.loads(diagnostic.read_text(encoding="utf-8"))
            self.assertEqual(attempt["schema"], "trust.realcode-coverage-attempt.v1")
            self.assertEqual(attempt["status"], "rejected")
            self.assertFalse(attempt["admissible_as_measurement"])
            self.assertEqual(attempt["proof_credit"], 0)
            self.assertEqual(attempt["population"]["eligible"], 2)
            self.assertEqual(attempt["proof"]["scorecard"]["kernel_rejected"], 1)
            self.assertEqual(
                attempt["corpus_classification"]["kind"],
                "curated-hand-authored-synthetic-fixture",
            )
            self.assertIn("prove process exited 1", attempt["rejection_reasons"])


if __name__ == "__main__":
    unittest.main()
