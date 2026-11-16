"""Malformed caller evidence must produce refusals, not checker crashes."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from scripts import two_language_completion_gate as runner
from scripts.completion_gates import check_g1_rust_input as g1
from scripts.completion_gates import check_g2_lean_input as g2
from scripts.completion_gates import check_g3_producer_totality as g3
from scripts.completion_gates import check_g4_semantic_faithfulness as g4
from scripts.completion_gates import check_g5_mixed_linking as g5
from scripts.completion_gates import check_g6_proof_authority as g6
from scripts.completion_gates import check_g7_codegen_authority as g7
from scripts.completion_gates import check_g8_release_reproducibility as g8


class MalformedInputTests(unittest.TestCase):
    def test_deep_json_refuses_in_runner_and_g1_g2(self) -> None:
        nested = ("[" * 1100 + "0" + "]" * 1100).encode()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "deep.json"
            path.write_bytes(nested)
            validator = runner.ReceiptValidator(root, root / "receipt.json", None)
            self.assertIsNone(validator.load_json(path, "receipt"))
            self.assertTrue(any("cannot read JSON" in error for error in validator.errors))
            with self.assertRaises(g1.Refusal):
                g1.json_object(nested, "artifact")
            with self.assertRaises(g2.Refusal):
                g2.load_json_object(path)

    def test_embedded_nul_reference_refuses_in_runner_g2_g3(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            validator = runner.ReceiptValidator(root, root / "receipt.json", None)
            self.assertIsNone(validator.resolve_ref(
                {"path": "x\0y", "sha256": "0" * 64}, "artifact"
            ))
            self.assertTrue(any("artifact.path" in error for error in validator.errors))
            path, reason = g2.resolve_ref(root, {"path": "x\0y", "sha256": "0" * 64})
            self.assertIsNone(path)
            self.assertIsNotNone(reason)
            context = g3.Context.__new__(g3.Context)
            context.root = root
            with self.assertRaises(g3.Refusal):
                context.path("x\0y", "artifact")

    def test_g8_malformed_evidence_refuses(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "deep.json"
            path.write_text("[" * 1100 + "0" + "]" * 1100, encoding="utf-8")
            with self.assertRaises(g8.Refusal):
                g8.json_object(path)
            with self.assertRaises(g8.Refusal):
                g8.ref(root, {"path": "x\0y", "sha256": "0" * 64}, "artifact")

    def test_g4_symlink_loop_and_g6_nul_path_refuse(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "loop").symlink_to("loop")
            context = g4.Context.__new__(g4.Context)
            context.root = root
            with self.assertRaises(g4.Refusal):
                context.path("loop", "certificate")
            g6_context = g6.Context.__new__(g6.Context)
            g6_context.root = root
            with self.assertRaises(g6.Refusal):
                g6_context.relative_path("x\0y", "artifact")

    def test_g8_symlink_loops_yield_one_refusing_verdict(self) -> None:
        # Python 3.9's Path.resolve raises RuntimeError on a symlink loop; the
        # checker must still print exactly one verdict, never a traceback.
        from scripts.tests.completion_gates_g8_test import CHECKER, Fixture

        def one_verdict(fixture: Fixture, **override: str) -> None:
            args = fixture.args()
            for name, value in override.items():
                args[args.index(f"--{name}") + 1] = value
            result = subprocess.run([sys.executable, "-I", str(CHECKER), *args],
                                    cwd=fixture.root, capture_output=True, text=True, check=False)
            self.assertNotIn("Traceback", result.stderr)
            self.assertEqual(result.returncode, 1)
            lines = result.stdout.splitlines()
            self.assertEqual(len(lines), 1, result.stdout)
            verdict = json.loads(lines[0])
            self.assertIs(verdict["passed"], False)
            self.assertEqual(len(verdict["checks"]), len(g8.REQUIRED))
            self.assertTrue(all(row["passed"] is False for row in verdict["checks"]))

        with tempfile.TemporaryDirectory() as tmp:
            fixture = Fixture(Path(tmp))
            loop = fixture.root / "loop"
            loop.symlink_to("loop")
            with self.subTest("receipt"):
                one_verdict(fixture, receipt=str(loop))
            with self.subTest("verify-evidence"):
                one_verdict(fixture, **{"verify-evidence": str(loop)})
            outer_loop = Path(tmp) / "root-loop"
            outer_loop.symlink_to("root-loop")
            with self.subTest("root"):
                one_verdict(fixture, root=str(outer_loop))
            fixture.artifacts["pinned_reproducible_environment"] = {"path": "loop", "sha256": "0" * 64}
            fixture.write_bundle()
            fixture.refresh_refs()
            with self.subTest("bundle artifact"):
                one_verdict(fixture)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "loop").symlink_to("loop")
            with self.subTest("ref"), self.assertRaises(g8.Refusal):
                g8.ref(root, {"path": "loop", "sha256": "0" * 64}, "artifact")
            with self.subTest("input_file"), self.assertRaises(g8.Refusal):
                g8.input_file(root, str(root / "loop"), "0" * 64, "artifact")
            with self.subTest("external_path"), self.assertRaises(g8.Refusal):
                g8.external_path(root, str(root / "loop"), "--trusted-owner-key")

    def test_g5_unhashable_identity_and_producer_refuse(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "artifact.json"
            path.write_text(json.dumps({
                "clean_origin": {
                    "recorded": True,
                    "emitted": [{"def_index": [], "func_id": 3}],
                    "linked": [{
                        "edges_repointed": 1, "source_def_index": 7,
                        "target_func_id": 3,
                    }],
                },
            }), encoding="utf-8")
            with self.assertRaisesRegex(g5.Refusal, "emitted row identity"):
                g5.verify_rust_to_lean_typed_link(path)
            path.write_text(json.dumps({
                "schema": g5.ABI_MODEL_SCHEMA,
                "abi_id": "abi", "memory_model_id": "memory",
                "conforming_producers": ["Trust", "Clean", {}],
                "divergences": [],
            }), encoding="utf-8")
            with self.assertRaisesRegex(g5.Refusal, "both producers"):
                g5.verify_shared_abi_and_memory_model(path)

    def test_g5_g7_deep_json_and_g7_nul_refuse(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "deep.json"
            path.write_text('{"rows":' + "[" * 1200 + "0" + "]" * 1200 + "}", encoding="utf-8")
            with self.assertRaises(g5.Refusal):
                g5.load_json_object(path)
            with self.assertRaises(g7.Refusal):
                g7.load_json_object(path)
            resolved, reason = g7.resolve_ref(root, {"path": "x\0y", "sha256": "0" * 64})
            self.assertIsNone(resolved)
            self.assertIsNotNone(reason)

    def test_long_lean_import_chain_and_cycle_do_not_recurse(self) -> None:
        class PinnedToolchain:
            def lean_toolchain_pin(self):
                return "pinned", None

        modules = [
            {
                "name": f"M{i}", "origin": "olean", "admission": "loaded",
                "imports": [f"M{i + 1}"] if i < 1099 else [],
                "path": f"M{i}.olean", "olean_sha256": "0" * 64,
            }
            for i in range(1100)
        ]
        doc = {
            "schema": g2.OLEAN_IMPORT_GRAPH_SCHEMA,
            "authority": g2.OLEAN_IMPORT_GRAPH_AUTHORITY,
            "toolchain": "pinned",
            "modules": modules,
        }
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "graph.json"
            path.write_text(json.dumps(doc), encoding="utf-8")
            with self.assertRaisesRegex(g2.Refusal, "no instrument produces"):
                g2.verify_external_olean_and_dependency_graphs(path, PinnedToolchain())
            modules[-1]["imports"] = ["M0"]
            path.write_text(json.dumps(doc), encoding="utf-8")
            with self.assertRaisesRegex(g2.Refusal, "import cycle"):
                g2.verify_external_olean_and_dependency_graphs(path, PinnedToolchain())


class CompletionRunnerJsonTests(unittest.TestCase):
    """Exercise the actual file and isolated-checker JSON protocol readers."""

    def checker_verdict(self, root: Path, output: str):
        validator = runner.ReceiptValidator(root, root / "receipt.json", None)
        verdict = validator.run_checker(
            gate="G1", checker_bytes=("print(" + repr(output) + ")\n").encode(),
            evidence_path=root / "evidence.json", toolchain_path=root / "toolchain.json",
            corpus_path=root / "corpus.json", subject_graph_path=root / "subjects.json",
            linked_module_path=root / "module.json", release_artifact_path=root / "program",
            policy_path=root / "policy.json", policy_authorization_path=root / "authorization.json",
            acceptance_run_id="json-reader-control", subject_graph_digest="0" * 64,
            linked_module_digest="0" * 64, release_artifact_digest="0" * 64,
            policy_digest="0" * 64, policy_authorization_digest="0" * 64,
            source_revision="1" * 40, checker_digest="0" * 64,
            evidence_digest="0" * 64, toolchain_digest="0" * 64,
            corpus_digest="0" * 64, prior_gates_root=None,
        )
        return validator, verdict

    def test_file_reader_refuses_ambiguous_and_nonfinite_json(self) -> None:
        cases = [
            '{"passed":false,"passed":true}',
            '{"nested":{"passed":false,"pa\\u0073sed":true}}',
            '{"rows":[{"id":"a","id":"b"}]}',
            '{"value":NaN}', '{"value":Infinity}', '{"value":-Infinity}',
            '{"value":1e999}', '{"value":-1e999}',
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "artifact.json"
            for document in cases:
                with self.subTest(document=document):
                    original = document.encode()
                    path.write_bytes(original)
                    validator = runner.ReceiptValidator(root, root / "receipt.json", None)
                    value, observed = validator.load_json_bytes(path, "artifact")
                    self.assertIsNone(value)
                    self.assertEqual(observed, original)
                    self.assertTrue(any("cannot read JSON" in e for e in validator.errors))
                    self.assertEqual(path.read_bytes(), original)

    def test_checker_stdout_refuses_ambiguous_nonfinite_and_deep_json(self) -> None:
        cases = [
            '{"passed":false,"passed":true}',
            '{"checks":[{"passed":false,"passed":true}]}',
            '{"value":NaN}', '{"value":Infinity}', '{"value":-Infinity}',
            '{"value":1e999}', '{"value":-1e999}',
            '{"value":' + '[' * 65 + '0' + ']' * 65 + '}',
        ]
        with tempfile.TemporaryDirectory() as tmp:
            for document in cases:
                with self.subTest(document=document):
                    validator, verdict = self.checker_verdict(Path(tmp), document)
                    self.assertIsNone(verdict)
                    self.assertTrue(any("checker stdout is not one JSON verdict" in e
                                        for e in validator.errors))

    def test_file_reader_retains_exact_bytes_and_valid_json_values(self) -> None:
        original = b'{ "rows": [{"id":"a"},{"id":"b"}], "value":1.25e2, "label":"NaN [ ]", "n":null }\n'
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "artifact.json"
            path.write_bytes(original)
            validator = runner.ReceiptValidator(root, root / "receipt.json", None)
            value, observed = validator.load_json_bytes(path, "artifact")
            self.assertEqual(value, {"rows": [{"id": "a"}, {"id": "b"}],
                                     "value": 125.0, "label": "NaN [ ]", "n": None})
            self.assertEqual(observed, original)
            self.assertEqual(validator.errors, [])
            self.assertEqual(path.read_bytes(), original)

    def test_checker_stdout_preserves_valid_favorable_and_refusing_rows(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            for passed in (False, True):
                with self.subTest(passed=passed):
                    expected = {"passed": passed, "checks": [{"id": "row", "passed": passed}],
                                "label": "Infinity { [", "value": 0.5}
                    validator, verdict = self.checker_verdict(Path(tmp), json.dumps(expected))
                    self.assertEqual(verdict, expected)
                    self.assertEqual(validator.errors, [])


if __name__ == "__main__":
    unittest.main()
