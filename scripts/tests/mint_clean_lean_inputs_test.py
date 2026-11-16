#!/usr/bin/env python3
"""Original-file controls for the mint's declared Clean library input."""
from __future__ import annotations

import contextlib
import importlib.util
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import mint_seed_support as mint

PIN = "leanprover/lean4:v4.30.0-rc2"
DIRECTORY = "leanprover--lean4---v4.30.0-rc2"


def fixture(root: Path) -> Path:
    """Use the pinned repository's actual Oracle and wrong-world files."""
    source = ROOT / "first-party/clean"
    clean = root / "first-party/clean"
    table = source / "crates/clean-olean/lean_worlds.tsv"
    rows = [line.split("\t") for line in table.read_text().splitlines()
            if line and not line.startswith("#")]
    oracle = next(row for row in rows if row[1] == "oracle")
    for relative in ["lean-toolchain", "crates/clean-olean/lean_worlds.tsv", *oracle[3].split()]:
        target = clean / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / relative, target)
    lib = root / "elan/toolchains" / DIRECTORY / "lib/lean"
    (lib / "Init").mkdir(parents=True)
    base = source / oracle[3].split()[0]
    # The directory is a controlled test installation; these are original
    # Oracle bytes, not a generated proof or a real full installation claim.
    shutil.copyfile(base, lib / "Init/Prelude.olean")
    shutil.copyfile(base, lib / "Init.olean")
    for suffix in (".server", ".private"):
        companion = Path(str(base) + suffix)
        if companion.exists():
            shutil.copyfile(companion, Path(str(lib / "Init.olean") + suffix))
    return lib


class CleanLeanInputTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.lib = fixture(self.root)

    def tearDown(self):
        self.temp.cleanup()

    def test_original_oracle_files_and_entire_installation_are_bound(self):
        value = mint.clean_lean_inputs(self.root, self.lib)
        self.assertEqual(value["toolchain"], PIN)
        self.assertEqual(value["world"], "v4.30.0-rc2")
        self.assertEqual(value["environment"], {
            "CLEAN_OLEAN_PINNED_LEAN_LIB": str(self.lib), "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"})
        self.assertEqual(mint.selected_clean_lean_lib(self.root, self.root / "elan"), self.lib)
        extra = self.lib.parent.parent / "share/input.txt"
        extra.parent.mkdir()
        extra.write_bytes(b"additional installation input")
        self.assertNotEqual(mint.clean_lean_inputs(self.root, self.lib)["fingerprint"], value["fingerprint"])

    def test_missing_and_wrong_directory_pin_refuse(self):
        with self.assertRaises((mint.WorkflowError, OSError)):
            mint.clean_lean_inputs(self.root, self.lib.with_name("missing"))
        wrong = self.lib.parent.parent.with_name("leanprover--lean4---v4.8.0") / "lib/lean"
        wrong.mkdir(parents=True)
        shutil.copyfile(self.lib / "Init.olean", wrong / "Prelude.olean")
        with self.assertRaisesRegex(mint.WorkflowError, "exact pinned"):
            mint.clean_lean_inputs(self.root, wrong)

    def test_real_48_bytes_under_correct_430_name_are_not_the_oracle(self):
        original = ROOT / "first-party/clean/tests/fixtures/olean/v4.8.0/witness/FactLib.olean"
        shutil.copyfile(original, self.lib / "Init/Prelude.olean")
        with self.assertRaisesRegex(mint.WorkflowError, "differs from the pinned Oracle world"):
            mint.clean_lean_inputs(self.root, self.lib)

    def test_foreign_companion_is_refused_even_when_prelude_is_correct(self):
        original = ROOT / "first-party/clean/tests/fixtures/olean/v4.8.0/witness/FactLib.olean"
        shutil.copyfile(original, self.lib / "Init.olean.private")
        with self.assertRaisesRegex(mint.WorkflowError, "pinned Oracle world"):
            mint.clean_lean_inputs(self.root, self.lib)

    def test_changed_library_body_invalidates_record(self):
        value = mint.clean_lean_inputs(self.root, self.lib)
        part = self.lib / "Init.olean"
        part.write_bytes(part.read_bytes() + b"changed body, same header")
        self.assertNotEqual(mint.clean_lean_inputs(self.root, self.lib), value)

    def test_links_cannot_hide_external_or_directory_contents(self):
        outside = self.root / "outside"
        outside.mkdir()
        (outside / "input").write_bytes(b"unbound")
        link = self.lib / "escape"
        link.symlink_to(outside / "input")
        with self.assertRaisesRegex(mint.WorkflowError, "unbound linked input"):
            mint.clean_lean_inputs(self.root, self.lib)
        link.unlink()
        link.symlink_to(self.lib / "Init", target_is_directory=True)
        with self.assertRaisesRegex(mint.WorkflowError, "unbound linked input"):
            mint.clean_lean_inputs(self.root, self.lib)

    def test_direct_elan_link_binds_real_contents_and_link_selection(self):
        installation = self.lib.parent.parent
        physical = self.root / "owned-installation"
        installation.rename(physical)
        installation.symlink_to(physical, target_is_directory=True)
        value = mint.clean_lean_inputs(self.root, self.lib)
        self.assertEqual(value["physical_installation"], str(physical))
        self.assertEqual(value["installation_link"], str(physical))
        (physical / "notice").write_bytes(b"changed selected input")
        self.assertNotEqual(mint.clean_lean_inputs(self.root, self.lib), value)

    def test_link_components_must_exist_and_be_directories_before_dotdot(self):
        installation = self.lib.parent.parent
        internal = installation / "lib/internal.dylib"
        internal.write_bytes(b"captured native library input")
        link = installation / "lib/broken.dylib"
        for target in ("missing/../internal.dylib", "internal.dylib/../internal.dylib"):
            with self.subTest(target=target):
                link.symlink_to(target)
                with self.assertRaises((FileNotFoundError, NotADirectoryError)):
                    link.read_bytes()
                with self.assertRaisesRegex(mint.WorkflowError, "unbound linked input"):
                    mint.clean_lean_inputs(self.root, self.lib)
                link.unlink()

    def test_existing_directory_dotdot_and_file_link_chains_remain_bound(self):
        installation = self.lib.parent.parent
        internal = installation / "lib/internal.dylib"
        internal.write_bytes(b"captured native library input")
        (installation / "lib/subdirectory").mkdir()
        link = installation / "lib/native-link"
        for target in ("subdirectory/../internal.dylib", "../lib/internal.dylib",
                       str(internal)):
            with self.subTest(target=target):
                link.symlink_to(target)
                self.assertEqual(link.read_bytes(), internal.read_bytes())
                value = mint.clean_lean_inputs(self.root, self.lib)
                self.assertIn("lib/native-link", [row["path"] for row in value["installation_entries"]])
                chain = installation / "lib/native-chain"
                chain.symlink_to("native-link")
                self.assertEqual(chain.read_bytes(), internal.read_bytes())
                mint.clean_lean_inputs(self.root, self.lib)
                chain.unlink()
                link.unlink()

    def test_link_escape_at_first_snapshot_cannot_hide_target_bytes(self):
        inside = self.lib.parent.parent / "native-input"
        inside.write_bytes(b"bound input")
        outside = self.root / "outside-input"
        outside.write_bytes(b"unbound input")
        link = self.lib.parent.parent / "native-link"
        link.symlink_to(inside)
        real = mint.tree_records
        calls = 0
        def swap_at_snapshot(*args):
            nonlocal calls
            calls += 1
            if calls == 1:
                link.unlink()
                link.symlink_to(outside)
            return real(*args)
        with mock.patch.object(mint, "tree_records", side_effect=swap_at_snapshot):
            with self.assertRaisesRegex(mint.WorkflowError, "unbound linked input"):
                mint.clean_lean_inputs(self.root, self.lib)

    def test_direct_selection_retarget_after_second_snapshot_refuses(self):
        installation = self.lib.parent.parent
        physical = self.root / "installation-A"
        other = self.root / "installation-B"
        installation.rename(physical)
        shutil.copytree(physical, other)
        installation.symlink_to(physical, target_is_directory=True)
        real = mint.tree_records
        calls = 0
        def retarget_at_end(*args):
            nonlocal calls
            calls += 1
            value = real(*args)
            if calls == 2:
                installation.unlink()
                installation.symlink_to(other, target_is_directory=True)
            return value
        with mock.patch.object(mint, "tree_records", side_effect=retarget_at_end):
            with self.assertRaisesRegex(mint.WorkflowError, "selection changed during capture"):
                mint.clean_lean_inputs(self.root, self.lib)

    def test_unchanged_elan_link_cannot_hide_physical_directory_replacement(self):
        installation = self.lib.parent.parent
        physical = self.root / "installation-A"
        other = self.root / "installation-B"
        backup = self.root / "installation-A-retained"
        installation.rename(physical)
        shutil.copytree(physical, other)
        changed = other / "lib/lean/Init.olean"
        changed.write_bytes(changed.read_bytes() + b"different physical library body")
        installation.symlink_to(physical, target_is_directory=True)
        original_link = os.readlink(installation)
        real = mint.tree_records
        calls = 0
        def replace_after_capture(*args):
            nonlocal calls
            calls += 1
            value = real(*args)
            if calls == 2:
                physical.rename(backup)
                other.rename(physical)
            return value
        with mock.patch.object(mint, "tree_records", side_effect=replace_after_capture):
            with self.assertRaisesRegex(mint.WorkflowError, "selection changed during capture"):
                mint.clean_lean_inputs(self.root, self.lib)
        self.assertEqual(os.readlink(installation), original_link)
        self.assertNotEqual((backup / "lib/lean/Init.olean").read_bytes(),
                            (self.lib / "Init.olean").read_bytes())

    def test_scalar_alias_and_original_record_byte_mutation_refuse(self):
        value = mint.clean_lean_inputs(self.root, self.lib)
        path = self.root / "record.json"
        path.write_text(json.dumps(value))
        original_sha = mint.sha256_file(path)
        self.assertEqual(mint.verify_clean_lean_inputs(self.root, path, self.lib, original_sha), value)
        self.assertIs(type(value["oracle_identity"][1]), int)
        self.assertIn(value["oracle_identity"][1], (0, 1))
        value["oracle_identity"][1] = bool(value["oracle_identity"][1])
        path.write_text(json.dumps(value))
        with self.assertRaisesRegex(mint.WorkflowError, "manifest bytes changed"):
            mint.verify_clean_lean_inputs(self.root, path, self.lib, original_sha)
        with self.assertRaisesRegex(mint.WorkflowError, "Oracle changed"):
            mint.verify_clean_lean_inputs(self.root, path, self.lib, mint.sha256_file(path))

    def test_coherent_other_receipt_cannot_change_callers_selector(self):
        other_root = self.root / "other"
        other = fixture(other_root)
        receipt = self.root / "other-record.json"
        receipt.write_text(json.dumps(mint.clean_lean_inputs(self.root, other)))
        # Even a valid self-consistent B record and its real raw hash cannot
        # redirect the independently selected A used by the actual child.
        with self.assertRaisesRegex(mint.WorkflowError, "Oracle changed"):
            mint.verify_clean_lean_inputs(self.root, receipt, self.lib, mint.sha256_file(receipt))

    def test_real_closed_environment_is_equal_for_pinned_ddc_and_selfhost(self):
        source = (ROOT / "scripts/mint_and_prove_seed.sh").read_text()
        function = "run_clean() {" + source.split("run_clean() {", 1)[1].split("\n}", 1)[0] + "\n}"
        query = "import json,os; print(json.dumps({k:os.environ.get(k) for k in ['CLEAN_OLEAN_PINNED_LEAN_LIB','CLEAN_OLEAN_REQUIRE_PINNED_LEAN','ELAN_HOME','LEAN_TOOLCHAIN_BIN','UNDECLARED_TEST_INPUT']}))"
        setup = {"WORK": str(self.root / "work"), "MKDIR_BIN": "/bin/mkdir", "ENV_BIN": "/usr/bin/env",
                 "PYTHON_BIN": sys.executable, "HELPER": str(ROOT / "scripts/mint_seed_support.py"),
                 "CARGO_HOME_SHARED": str(self.root / "cargo"), "SOURCE_DATE_EPOCH": "123",
                 "NATIVE_LIBRARY_PATH": "", "SEED_DYLIB_PATH": "", "CLEAN_LEAN_LIB": str(self.lib)}
        script = "\n".join(f"{key}={shlex.quote(value)}" for key, value in setup.items()) + "\n" + function
        for name in ("pinned", "ddc", "proof"):
            script += f"\nrun_clean /usr/bin:/bin {name} {shlex.quote(sys.executable)} -I -S -c {shlex.quote(query)}\n"
        result = subprocess.run(["/bin/bash", "-eu", "-c", script], capture_output=True, text=True,
                                env={**os.environ, "ELAN_HOME": "/wrong/ambient", "LEAN_TOOLCHAIN_BIN": "/wrong/4.8",
                                     "UNDECLARED_TEST_INPUT": "must not enter"}, check=True)
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        expected = {"CLEAN_OLEAN_PINNED_LEAN_LIB": str(self.lib), "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1",
                    "ELAN_HOME": None, "LEAN_TOOLCHAIN_BIN": None, "UNDECLARED_TEST_INPUT": None}
        self.assertEqual(rows, [expected] * 3)

    def test_ambient_selector_is_refused_before_any_mint_work(self):
        result = subprocess.run(["bash", str(ROOT / "scripts/mint_and_prove_seed.sh"),
                                 "--clean-lean-lib", str(self.lib), "--check-only"],
                                env={**os.environ, "CLEAN_OLEAN_PINNED_LEAN_LIB": str(self.lib)},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("undeclared ambient Clean Lean selectors", result.stderr)

    def test_native_authority_needs_actual_bound_closure_not_scalar_names(self):
        spec = importlib.util.spec_from_file_location("mint_lean_authority_test", ROOT / "scripts/recreate_bootstrap.py")
        owner = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = owner
        spec.loader.exec_module(owner)
        config = self.root / "bootstrap.toml"
        config.write_text('[build]\nsubmodules=false\n[llvm]\ndownload-ci-llvm=false\n')
        value = mint.clean_lean_inputs(self.root, self.lib)
        context = mint.mint_configuration_context(self.root, config, "test-host", clean_lean_lib=self.lib)
        declared = value["environment"]
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.dict(os.environ, declared, clear=True))
            stack.enter_context(mock.patch.object(owner.platform, "system", return_value="Linux"))
            stack.enter_context(mock.patch.object(owner, "bind_native_build_tools", return_value=[]))
            stack.enter_context(mock.patch.object(owner, "bootstrap_cargo_authority", return_value=({"unbound_config_paths": []}, [])))
            self.assertEqual(owner.capture_build_authority(self.root, "test-host", None,
                            declared_environment=declared)["status"], "rejected")
            valid = owner.capture_build_authority(self.root, "test-host", None,
                            declared_environment=declared, mint_configuration=context)
            self.assertEqual(valid["status"], "ready", valid["errors"])
            corrupted = json.loads(json.dumps(context))
            corrupted["clean_lean_inputs"]["oracle_identity"][1] = bool(
                corrupted["clean_lean_inputs"]["oracle_identity"][1])
            alias = owner.capture_build_authority(self.root, "test-host", None,
                            declared_environment=declared, mint_configuration=corrupted)
            self.assertEqual(alias["status"], "rejected", alias)
            corrupt_before = json.loads(json.dumps(valid))
            corrupt_before["clean_lean_inputs"]["oracle_identity"][1] = bool(
                corrupt_before["clean_lean_inputs"]["oracle_identity"][1])
            self.assertEqual(owner._bind_build_authority(corrupt_before, valid)["status"], "rejected")
            (self.lib / "Init.olean").write_bytes((self.lib / "Init.olean").read_bytes() + b"mutation")
            changed = owner.capture_build_authority(self.root, "test-host", None,
                            declared_environment=declared, mint_configuration=context)
            self.assertEqual(changed["status"], "rejected", changed)


if __name__ == "__main__":
    unittest.main()
