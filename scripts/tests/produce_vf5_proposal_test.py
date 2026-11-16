"""Producer IO/order controls only: no Lean/Rust/compiler/proof execution."""
from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "produce_vf5_proposal.py"
SPEC = importlib.util.spec_from_file_location("produce_vf5_proposal", SCRIPT)
producer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(producer)


class Vf5ProposalPreparationTests(unittest.TestCase):
    def test_fixed_consumer_identity_does_not_follow_the_roots_newer_clean_revision(self):
        identity = {"schema": 1, "kind": "vf5-fixed-source-identity-v1",
                    "clean_revision": "24861300fea40294bb485bb630eb216756dc558d",
                    "lean_world": producer.WORLD, "production_admission": False}
        commands = []
        def run(argv, **kwargs):
            commands.append((argv, kwargs))
            return SimpleNamespace(returncode=0, stdout=json.dumps(identity))
        actual = producer.fixed_source_identity(SimpleNamespace(run=run), Path("own-prepare"),
                                               cwd=Path("own-work"), env={"declared": "input"})
        self.assertEqual(actual, identity)
        self.assertNotEqual(actual["clean_revision"], "9f7c36edd4514fe08f288a45c351a8e3b79227aa")
        self.assertEqual(commands, [(["own-prepare", "source-identity"],
                                    {"cwd": Path("own-work"), "env": {"declared": "input"}})])

    def test_fixed_git_blobs_are_materialized_without_relabelling_the_current_checkout(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            def git(*args):
                return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.PIPE)
            git("init", "-q")
            git("config", "user.name", "Source fixture")
            git("config", "user.email", "source-fixture@example.invalid")
            path = root / "VF5Check.lean"
            path.write_bytes(b"-- original fixed mathematical source\n")
            git("add", "VF5Check.lean"); git("commit", "-q", "-m", "fixed source")
            fixed = git("rev-parse", "HEAD").decode().strip()
            original = path.read_bytes()
            path.write_bytes(b"-- current source with a different identity\n")
            git("commit", "-qam", "advance current source")
            current = git("rev-parse", "HEAD").decode().strip()
            self.assertNotEqual(fixed, current)
            self.assertEqual(producer.read_source_blob(root, fixed, "VF5Check.lean"), original)
            self.assertNotEqual(producer.read_source_blob(root, fixed, "VF5Check.lean"),
                                producer.read_source_blob(root, current, "VF5Check.lean"))
            self.assertEqual(path.read_bytes(), b"-- current source with a different identity\n")
            with self.assertRaises(subprocess.CalledProcessError):
                producer.read_source_blob(root, "0" * 40, "VF5Check.lean")

    def test_fixed_source_blob_ignores_a_real_replacement_commit(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            def git(*args, **kwargs):
                return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.PIPE, **kwargs)
            git("init", "-q"); git("config", "user.name", "Source fixture")
            git("config", "user.email", "source-fixture@example.invalid")
            path = root / "VF5Check.lean"
            original = b"-- fixed original source\n"
            path.write_bytes(original); git("add", "VF5Check.lean")
            git("commit", "-q", "-m", "fixed source")
            fixed = git("rev-parse", "HEAD").decode().strip()
            replacement = b"-- substituted current source\n"
            path.write_bytes(replacement); git("commit", "-qam", "replacement source")
            current = git("rev-parse", "HEAD").decode().strip()
            git("replace", fixed, current)
            ordinary = dict(os.environ); ordinary.pop("GIT_NO_REPLACE_OBJECTS", None)
            self.assertEqual(git("cat-file", "blob", fixed + ":VF5Check.lean", env=ordinary), replacement)
            with patch.dict(os.environ, ordinary, clear=True):
                self.assertEqual(producer.read_source_blob(root, fixed, "VF5Check.lean"), original)
            self.assertEqual(path.read_bytes(), replacement)

    def test_missing_malformed_or_favorable_fixed_consumer_identity_refuses(self):
        original = {"schema": 1, "kind": "vf5-fixed-source-identity-v1",
                    "clean_revision": "24861300fea40294bb485bb630eb216756dc558d",
                    "lean_world": producer.WORLD, "production_admission": False}
        invalid = ["{}", "[]", "null", "{", json.dumps(original) + "\n{}",
                   json.dumps(original)[:-1] + ',"schema":1}']
        for field, value in [("schema", True), ("schema", 2), ("kind", "other"),
                             ("clean_revision", ""), ("clean_revision", "A" * 40),
                             ("clean_revision", 248), ("lean_world", "v4.8.0"),
                             ("production_admission", True)]:
            invalid.append(json.dumps({**original, field: value}))
        invalid.append(json.dumps({**original, "extra": "input"}))
        for payload in invalid:
            with self.subTest(payload=payload), self.assertRaises(ValueError):
                producer.fixed_source_identity(SimpleNamespace(run=lambda *args, **kwargs:
                    SimpleNamespace(returncode=0, stdout=payload)), Path("tool"), cwd=Path("work"), env={})
        with self.assertRaisesRegex(ValueError, "query failed"):
            producer.fixed_source_identity(SimpleNamespace(run=lambda *args, **kwargs:
                SimpleNamespace(returncode=7, stdout=json.dumps(original))), Path("tool"), cwd=Path("work"), env={})

    def test_produce_reads_fixed_git_source_before_a_current_checkout_can_substitute_for_it(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            source = root / "source"; source.mkdir()
            def git(*args):
                return subprocess.check_output(["git", "-C", str(source), *args], stderr=subprocess.PIPE)
            git("init", "-q"); git("config", "user.name", "Source fixture")
            git("config", "user.email", "source-fixture@example.invalid")
            # A failing fixed source is deliberate: current's valid-looking
            # toolchain must not replace it and allow further preparation.
            fixed_source = b"invalid-fixed-source-world\n"
            (source / "lean-toolchain").write_bytes(fixed_source)
            git("add", "lean-toolchain"); git("commit", "-q", "-m", "fixed source")
            fixed = git("rev-parse", "HEAD").decode().strip()
            (source / "lean-toolchain").write_bytes(b"leanprover/lean4:v4.30.0-rc2\n")
            git("commit", "-qam", "current source")
            current = git("rev-parse", "HEAD").decode().strip()
            provider = root / "provider"; (provider / "bin").mkdir(parents=True)
            library = provider / "lib/lean"; library.mkdir(parents=True)
            lean = provider / "bin/lean"
            lean.write_text("#!/bin/sh\nprintf 'DATA fixture version 4.30.0-rc2\\n'\n")
            lean.chmod(0o700)
            identity = {"schema": 1, "kind": "vf5-fixed-source-identity-v1",
                        "clean_revision": fixed, "lean_world": producer.WORLD, "production_admission": False}
            prepare = root / "prepare"
            prepare.write_text("#!/bin/sh\nprintf '%s\\n' '" + json.dumps(identity) + "'\n")
            prepare.chmod(0o700)
            validations = []
            selection = SimpleNamespace(environment=lambda _root: validations.append(_root) or {})
            args = SimpleNamespace(output=root / "output", lean_lib=library,
                lean_manifest=root / "manifest", lean_manifest_sha256="DATA-only",
                clean_source=source, artifact=root / "not-reached", prepare_tool=prepare)
            with patch.dict(sys.modules, {"recreate_bootstrap": SimpleNamespace(CleanLeanSelection=lambda *_args: selection)}), \
                 patch.object(producer, "selected_clean_revision", return_value=current):
                with self.assertRaisesRegex(ValueError, "different Lean world"):
                    producer.produce(args)
            saved = json.loads((args.output / "RESULT.json").read_text())
            self.assertFalse(saved["completed"])
            self.assertEqual(saved["clean_revision"], fixed)
            self.assertEqual(saved["root_clean_revision"], current)
            self.assertEqual(saved["source_files"], {"lean-toolchain": producer.sha(fixed_source)})
            self.assertEqual(len(validations), 2)
            self.assertEqual((source / "lean-toolchain").read_bytes(), b"leanprover/lean4:v4.30.0-rc2\n")

    def test_handwritten_order_stops_before_generated_historical_rows(self):
        rows = {
            f"{producer.FAMILY}/ORDER": b"# own order\ntheory chk_lia\nfrom semr SemR\nVF5Check\nVF5Mutants\nVF5Rows\n",
            "theories/chk_lia/ORDER": b"ChkLIA\nChkLIASpec\nChkLIACases\n",
        }
        actual = producer.build_sources(rows.__getitem__)
        self.assertEqual([name for name, _ in actual],
                         ["ChkLIA", "ChkLIASpec", "ChkLIACases", "SemR", "VF5Check", "VF5Mutants"])
        self.assertNotIn("VF5Rows", [name for name, _ in actual])

    def test_unknown_build_directive_and_missing_endpoint_refuse(self):
        for body in (b"run arbitrary.lean output.olean\n", b"VF5Check\n"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                producer.build_sources(lambda _path: body)

    def test_regular_descriptor_limit_and_actual_fifo_or_symlink_refuse(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            regular = root / "artifact"
            regular.write_bytes(b"actual")
            self.assertEqual(producer.read_regular(regular, 6), b"actual")
            with self.assertRaises(ValueError):
                producer.read_regular(regular, 5)
            if os.name == "posix":
                link = root / "alias"
                link.symlink_to(regular)
                with self.assertRaises(OSError):
                    producer.read_regular(link, 6)
                fifo = root / "pipe"
                os.mkfifo(fifo)
                with self.assertRaises(ValueError):
                    producer.read_regular(fifo, 6)

    def test_real_child_status_raw_and_reused_source_are_retained_per_command(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            # Python executes this owned fixture; its suffix exercises the
            # Lean-source DATA capture branch, not a Lean or proof oracle.
            source = root / "Dump.lean"
            source.write_text("import sys\nprint('first')\nprint('diagnostic', file=sys.stderr)\nsys.exit(7)\n")
            calls = producer.RecordedCommands(root)
            first = calls.run([sys.executable, "Dump.lean"], cwd=root)
            self.assertEqual(first.returncode, 7)
            self.assertEqual(first.stdout, "first\n")
            self.assertEqual(first.stderr, "diagnostic\n")
            first_source = (root / "command-0000.input.lean").read_bytes()
            source.write_text("print('second')\n")
            second = calls.run([sys.executable, "Dump.lean"], cwd=root)
            self.assertEqual(second.returncode, 0)
            self.assertEqual(second.stdout, "second\n")
            self.assertEqual((root / "command-0000.input.lean").read_bytes(), first_source)
            self.assertNotEqual((root / "command-0001.input.lean").read_bytes(), first_source)

    def test_missing_child_retains_spawn_failure_without_inventing_exit_status(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            calls = producer.RecordedCommands(root)
            with self.assertRaises(FileNotFoundError):
                calls.run([str(root / "missing-tool")], cwd=root)
            saved = json.loads((root / "command-0000.json").read_text())
            self.assertIsNone(saved["returncode"])
            self.assertEqual(saved["spawn_error"]["type"], "FileNotFoundError")
            self.assertEqual(calls.records, [saved])
            self.assertEqual((root / "command-0000.stdout").read_bytes(), b"")
            self.assertEqual((root / "command-0000.stderr").read_bytes(), b"")

    def test_failed_first_child_still_records_result_and_revalidates_provider(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            lean_root = root / "declared-provider"
            (lean_root / "bin").mkdir(parents=True)
            library = lean_root / "lib" / "lean"
            library.mkdir(parents=True)
            # An owned shell fixture exercises process failure recording only.
            # It is not Lean or a substitute for whole-provider validation.
            child = lean_root / "bin" / "lean"
            child.write_text("#!/bin/sh\nprintf 'fixture failure\\n' >&2\nexit 7\n")
            child.chmod(0o700)
            validations = []
            selection = SimpleNamespace(environment=lambda _root: validations.append(_root) or {})
            module = SimpleNamespace(CleanLeanSelection=lambda *_args: selection)
            args = SimpleNamespace(output=root / "output", lean_lib=library,
                lean_manifest=root / "manifest", lean_manifest_sha256="test-only",
                clean_source=root / "source", artifact=root / "artifact",
                prepare_tool=root / "declared-prepare")
            # DATA-only helper fixture, separate from the failing Lean child.
            identity = {"schema": 1, "kind": "vf5-fixed-source-identity-v1",
                        "clean_revision": "24861300fea40294bb485bb630eb216756dc558d",
                        "lean_world": producer.WORLD, "production_admission": False}
            args.prepare_tool.write_text("#!/bin/sh\nprintf '%s\\n' '" + json.dumps(identity) + "'\n")
            args.prepare_tool.chmod(0o700)
            with patch.dict(sys.modules, {"recreate_bootstrap": module}), \
                 patch.object(producer, "selected_clean_revision", return_value="9f7c36edd4514fe08f288a45c351a8e3b79227aa"):
                with self.assertRaisesRegex(ValueError, "wrong version"):
                    producer.produce(args)
            saved = json.loads((args.output / "RESULT.json").read_text())
            self.assertIs(saved["completed"], False)
            self.assertIs(saved["production_admission"], False)
            self.assertIs(saved["lean_after_validated"], True)
            self.assertEqual(len(validations), 2)
            self.assertEqual(saved["clean_revision"], identity["clean_revision"])
            self.assertEqual(saved["root_clean_revision"], "9f7c36edd4514fe08f288a45c351a8e3b79227aa")
            self.assertEqual(len(saved["commands"]), 2)
            self.assertEqual(saved["commands"][0]["returncode"], 0)
            self.assertEqual(saved["commands"][1]["returncode"], 7)
            self.assertEqual((args.output / "command-0001.stderr").read_text(), "fixture failure\n")
            original = (args.output / "RESULT.json").read_bytes()
            with patch.dict(sys.modules, {"recreate_bootstrap": module}):
                with self.assertRaises(FileExistsError):
                    producer.produce(args)
            self.assertEqual((args.output / "RESULT.json").read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
