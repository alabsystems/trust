#!/usr/bin/env python3
"""A successful empty, ignored or renamed filter is never a native probe pass."""
import importlib.util
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "check_storage_geometry_visitors.py"
SPEC = importlib.util.spec_from_file_location("storage_geometry_probe", SCRIPT)
probe = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(probe)


def output(passed=5, failed=0, ignored=0, names=None):
    rows = "".join("test " + name + " ... ok\n" for name in (names or sorted(probe.EXPECTED_TESTS)))
    return rows + f"test result: ok. {passed} passed; {failed} failed; {ignored} ignored; 0 measured; 19 filtered out; finished in 0.01s\n"


class ProbePopulation(unittest.TestCase):
    def test_all_five_named_controls_must_execute(self):
        self.assertEqual(probe.test_population(output())["passed"], 5)

    def test_zero_ignored_failed_renamed_or_duplicate_populations_refuse(self):
        for raw in [output(0), output(4, 0, 1), output(4, 1),
                    output(names=["wrong"] * 5), output() + output(), ""]:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                probe.test_population(raw)


class ProbeSourceClosure(unittest.TestCase):
    def test_complete_diagnostic_module_retains_adjacent_tests_and_real_caller(self):
        root = SCRIPT.parent.parent
        with tempfile.TemporaryDirectory() as temporary:
            fixture = Path(temporary)
            ir = fixture / "identity-only-fixture"
            subprocess.run(["git", "init", "-q", str(ir)], check=True)
            subprocess.run(["git", "-C", str(ir), "-c", "user.name=Source Fixture",
                            "-c", "user.email=fixture@invalid", "commit", "-qm", "source identity",
                            "--allow-empty"], check=True)
            output = fixture / "prepared"
            result = subprocess.run([sys.executable, "-B", str(SCRIPT), "--source-root", str(root),
                                     "--ir-root", str(ir), "--output", str(output), "--prepare-only"],
                                    check=True, capture_output=True, text=True)
            source = root / "crates/trust-thir-lower/src"
            self.assertEqual((output / "src/diagnostic.rs").read_bytes(),
                             (source / "crate_module/validation_type_context.rs").read_bytes())
            self.assertEqual((output / "src/validation_type_context_caller_tests.rs").read_bytes(),
                             (source / "crate_module/validation_type_context_caller_tests.rs").read_bytes())
            generated = (output / "src/lib.rs").read_text()
            self.assertIn("pub(crate) fn final_module_validation_errors(module: &Module)", generated)
            self.assertIn("fn locate_validation_error(", generated)
            self.assertIn("fn validation_error_class(", generated)
            imports = probe.ordinary_ir_imports((source / "template_lowering.rs").read_text())
            self.assertIn("FatPtrKind", imports)
            self.assertIn(imports, generated)
            receipt = json.loads((output / "SOURCE-INPUTS.json").read_text())
            self.assertIn("crate_module.rs", receipt["source_sha256"])
            self.assertIn("crate_module/validation_type_context_caller_tests.rs", receipt["source_sha256"])
            for name, digest in receipt["generated_artifacts_sha256"].items():
                self.assertEqual(hashlib.sha256((output / name).read_bytes()).hexdigest(), digest)
            self.assertEqual(receipt["proof_claim"], "none")
            self.assertIn("no Rust executed", result.stdout)
            self.assertFalse((output / "RESULT.json").exists())
            self.assertFalse((output / "NATIVE-TEST.log").exists())

    def test_requalification_refuses_mutated_copied_module_or_adjacent_tests(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            contents = {"src/lib.rs": b"actual generated caller closure",
                        "src/diagnostic.rs": b"actual copied production module",
                        "src/validation_type_context_caller_tests.rs": b"actual adjacent test module"}
            expected = {}
            for name, content in contents.items():
                path = output / name
                path.parent.mkdir(exist_ok=True)
                path.write_bytes(content)
                expected[name] = hashlib.sha256(content).hexdigest()
            producer = {"generated_sha256": expected["src/lib.rs"],
                        "source_sha256": {
                            "crate_module/validation_type_context.rs": expected["src/diagnostic.rs"],
                            "crate_module/validation_type_context_caller_tests.rs":
                                expected["src/validation_type_context_caller_tests.rs"]},
                        "generated_artifacts_sha256": expected}
            probe.check_generated_artifacts(producer, output)
            for name in ("src/diagnostic.rs", "src/validation_type_context_caller_tests.rs"):
                (output / name).write_bytes(contents[name] + b" altered")
                with self.subTest(name=name), self.assertRaisesRegex(ValueError, "source changed"):
                    probe.check_generated_artifacts(producer, output)
                (output / name).write_bytes(contents[name])
            with self.assertRaisesRegex(ValueError, "map is missing"):
                probe.check_generated_artifacts({key: value for key, value in producer.items()
                                                 if key != "generated_artifacts_sha256"}, output)

    def test_requalification_binds_path_dependency_even_when_lock_is_unchanged(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            template = b'[dependencies]\ntrust-ir = { path = "@IR@/crates/trust-ir" }\n'
            producer = {"ir_root": "/original/frozen/ir"}
            actual = template.decode().replace("@IR@", producer["ir_root"]).encode()
            manifest = output / "Cargo.toml"
            manifest.write_bytes(actual)
            lock = output / "Cargo.lock"
            lock.write_bytes(b"unchanged path-package lock")
            original_lock = lock.read_bytes()
            probe.check_generated_manifest(producer, output, template)
            manifest.write_bytes(actual.replace(b"/original/frozen/ir", b"/different/source/ir"))
            with self.assertRaisesRegex(ValueError, "dependency binding"):
                probe.check_generated_manifest(producer, output, template)
            self.assertEqual(lock.read_bytes(), original_lock)


if __name__ == "__main__":
    unittest.main()
