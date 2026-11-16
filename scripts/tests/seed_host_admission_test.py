#!/usr/bin/env python3
"""Inert host-admission controls: no compiler, build, mint, or publisher runs."""

from __future__ import annotations

import copy
import contextlib
import hashlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts import check_seed_freshness as freshness
from scripts import mint_seed_support as support
from scripts import recreate_bootstrap as recreate

LINUX = "aarch64-unknown-linux-gnu"
MAC = "aarch64-apple-darwin"
SOURCE = {"commit": "a" * 40, "commit_date": "2026-09-30"}
VERSION = "0.10.0"


def cohort(host: str) -> dict[str, str]:
    pin = {}
    for component in ("compiler", "rustfmt"):
        pin.update({
            f"{component}_git_commit_hash": SOURCE["commit"],
            f"{component}_date": SOURCE["commit_date"],
            f"{component}_version": f"{VERSION}-trust",
            f"{component}_channel_manifest_hash": hashlib.sha256(b"manifest").hexdigest(),
        })
    for component in support.SEED_COMPONENTS:
        suffix = "" if component == "trust-src" else f"-{host}"
        pin[f"dist/{SOURCE['commit_date']}/{component}-{VERSION}-trust{suffix}.tar.xz"] = hashlib.sha256(b"archive").hexdigest()
    return pin


def records(host: str):
    receipt = {
        "schema": support.RECEIPT_SCHEMA,
        "source_commit": SOURCE["commit"], "source_commit_date": SOURCE["commit_date"],
        "source_version": VERSION, "host": host, "self_host_proof": "pass",
    }
    surface = {"schema": "trust-self-host-seed-surface-v1", "source_version": VERSION, "host": host}
    return receipt, surface


class HostInventoryTests(unittest.TestCase):
    def test_native_default_reuses_linux_and_mac_detector(self):
        for system, machine, expected in (("Linux", "aarch64", LINUX), ("Darwin", "arm64", MAC)):
            with mock.patch.object(support.platform, "system", return_value=system), mock.patch.object(support.platform, "machine", return_value=machine), mock.patch.object(support.platform, "libc_ver", return_value=("glibc", "2.39")):
                self.assertEqual(freshness.native_payload_host(), expected)

    def test_plain_require_payloads_uses_native_host_without_an_opt_in_flag(self):
        for native, payload_host, expected in ((LINUX, MAC, 1), (LINUX, LINUX, 0), (MAC, MAC, 0)):
            with self.subTest(native=native, payload_host=payload_host), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / "src").mkdir()
                (root / "src/rust-compat-version").write_text("1.99.0\n")
                pin = cohort(payload_host)
                (root / "src/stage0").write_text("".join(f"{key}={value}\n" for key, value in pin.items()))
                for relative in pin:
                    if relative.startswith("dist/"):
                        path = root / "bootstrap/trust-stage0" / relative
                        path.parent.mkdir(parents=True, exist_ok=True)
                        path.write_bytes(b"archive")
                (path.parent / "channel-rust-trust.toml").write_bytes(b"manifest")
                output = io.StringIO()
                with mock.patch.object(freshness, "ROOT", root), mock.patch.object(freshness, "native_payload_host", return_value=native) as detection, mock.patch.object(freshness, "probe_materialized_stage0", return_value=([], [])), mock.patch.object(freshness, "probe_configured_seed", return_value=([], [])), mock.patch.object(sys, "argv", ["check_seed_freshness.py", "--require-payloads"]), contextlib.redirect_stdout(output):
                    self.assertEqual(freshness.main(), expected, output.getvalue())
                    detection.assert_called_once_with()
                if expected:
                    self.assertIn("missing required trustc archive", output.getvalue())
                    self.assertIn(LINUX, output.getvalue())

    def test_unknown_native_host_fails_closed(self):
        with mock.patch.object(freshness, "native_payload_host", side_effect=RuntimeError("unsupported")):
            errors = freshness.validate_materialized_payloads(cohort(LINUX))
        self.assertEqual(len(errors), 1)
        self.assertIn("cannot determine the native seed host", errors[0])

    def test_complete_native_mac_and_linux(self):
        for host in (MAC, LINUX):
            with self.subTest(host=host):
                self.assertEqual(freshness.validate_payload_inventory(cohort(host), host), [])

    def test_mac_only_is_not_linux(self):
        errors = freshness.validate_payload_inventory(cohort(MAC), LINUX)
        self.assertEqual(len(errors), 8)
        self.assertTrue(all(LINUX in error for error in errors))

    def test_mixed_hosts_do_not_form_a_cohort(self):
        pin = cohort(LINUX)
        key = next(key for key in pin if "/trustc-" in key)
        pin[key.replace(LINUX, MAC)] = pin.pop(key)
        self.assertEqual(len(freshness.validate_payload_inventory(pin, LINUX)), 1)

    def test_source_archive_must_be_host_neutral(self):
        pin = cohort(LINUX)
        key = next(key for key in pin if "/trust-src-" in key)
        pin[key.replace(".tar.xz", f"-{LINUX}.tar.xz")] = pin.pop(key)
        self.assertEqual(len(freshness.validate_payload_inventory(pin, LINUX)), 1)

    def test_wrong_version_and_missing_component_refused(self):
        for component in support.SEED_COMPONENTS:
            pin = cohort(LINUX)
            key = next(key for key in pin if f"/{component}-{VERSION}-" in key)
            del pin[key]
            with self.subTest(component=component):
                self.assertEqual(len(freshness.validate_payload_inventory(pin, LINUX)), 1)

    def test_declared_rustfmt_version_is_used(self):
        pin = cohort(LINUX)
        pin["rustfmt_version"] = "0.9.0-trust"
        self.assertEqual(len(freshness.validate_payload_inventory(pin, LINUX)), 1)

    def test_materialized_bytes_are_still_hashed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pin = cohort(LINUX)
            for key in pin:
                if key.startswith("dist/"):
                    path = root / "bootstrap/trust-stage0" / key
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(b"archive")
            manifest = root / "bootstrap/trust-stage0/dist" / SOURCE["commit_date"] / "channel-rust-trust.toml"
            manifest.write_bytes(b"manifest")
            with mock.patch.object(freshness, "ROOT", root):
                self.assertEqual(freshness.validate_materialized_payloads(pin, LINUX), [])
                path.write_bytes(b"changed archive")
                self.assertTrue(any("SHA-256 mismatch" in error for error in freshness.validate_materialized_payloads(pin, LINUX)))
                manifest.write_bytes(b"changed manifest")
                self.assertTrue(any("channel-rust-trust.toml digest" in error for error in freshness.validate_materialized_payloads(pin, LINUX)))

    def test_generic_inventory_api_remains_available(self):
        self.assertEqual(freshness.validate_payload_inventory(cohort(MAC)), [])


class HostIdentityTests(unittest.TestCase):
    def test_mint_is_native_only(self):
        for host in (MAC, LINUX):
            with mock.patch.object(support, "detected_host", return_value=host):
                self.assertEqual(support.native_host(host), host)
                self.assertEqual(support.native_host(), host)
                other = MAC if host == LINUX else LINUX
                with self.assertRaisesRegex(support.WorkflowError, "cross-host"):
                    support.native_host(other)

    def test_compiler_reported_host_retained_and_required(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "bin").mkdir()
            (root / "lib").mkdir()
            (root / "bin/trustc").write_bytes(b"inert compiler fixture")
            (root / "lib/librustc_driver-fixture.so").write_bytes(b"inert driver fixture")
            for host in (MAC, LINUX, ""):
                output = f"commit-hash: {SOURCE['commit']}\nhost: {host}\n"
                with mock.patch.object(support.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, output)):
                    if host:
                        self.assertEqual(support.compiler_identity(root, "fixture")["host"], host)
                    else:
                        with self.assertRaises(support.WorkflowError):
                            support.compiler_identity(root, "fixture")

    def test_extracted_pin_wrong_host_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            stage = root / LINUX / "stage0"
            stage.mkdir(parents=True)
            (stage / ".rustc-stamp").write_text(support.stage0_extraction_stamp(cohort(LINUX)))
            identity = {"host": MAC, "commit": SOURCE["commit"], "date": SOURCE["commit_date"]}
            # The runtime closure is bound before the compiler is run
            # (scripts/tests/mint_seed_linux_closure_test.py); on Linux the inert fixture has
            # no ELF to bind, so it stands in here: this test is the host check after it.
            with mock.patch.object(support, "read_stage0_pin", return_value=cohort(LINUX)), \
                    mock.patch.object(support, "foreign_load_commands", return_value={"unresolved": []}) as closure, \
                    mock.patch.object(support, "compiler_identity", return_value=identity):
                with self.assertRaisesRegex(support.WorkflowError, "reports host 'aarch64-apple-darwin', not "):
                    support.pinned_stage0_identity(root, root, LINUX)
            closure.assert_called_once_with(stage, [])

    def test_ddc_wrong_host_refused_before_relation_classification(self):
        with mock.patch.object(support, "read_stage0_pin", return_value=cohort(LINUX)), mock.patch.object(support, "compiler_identity", return_value={"host": MAC}):
            with self.assertRaisesRegex(support.WorkflowError, "DDC seed reports host"):
                support.ddc_seed_identity(Path("."), Path("."), LINUX)

    def test_recreator_passes_requested_host(self):
        # validate_seed runs the checker through _run_seed_checker (native
        # custody), not recreate.subprocess.run: patch the seam the command
        # actually crosses.
        with mock.patch.object(recreate, "_run_seed_checker",
                               return_value=subprocess.CompletedProcess([], 0)) as run:
            self.assertTrue(recreate.validate_seed(Path("/fixture"), LINUX))
            self.assertEqual(run.call_args.args[0][-2:], ["--host", LINUX])
            self.assertEqual(run.call_args.kwargs["cwd"], "/fixture")


class RepinTupleTests(unittest.TestCase):
    def test_exact_linux_and_mac_tuples(self):
        for host in (MAC, LINUX):
            receipt, surface = records(host)
            self.assertEqual(len(support.validate_repin_tuple(cohort(host), SOURCE, VERSION, host, receipt, surface)), 9)

    def test_every_receipt_and_surface_identity_is_bound(self):
        for record_kind in ("receipt", "surface"):
            receipt, surface = records(LINUX)
            original = receipt if record_kind == "receipt" else surface
            for key in original:
                wrong = copy.deepcopy(original)
                wrong[key] = "wrong"
                args = (wrong, surface) if record_kind == "receipt" else (receipt, wrong)
                with self.subTest(record=record_kind, key=key), self.assertRaises(support.WorkflowError):
                    support.validate_repin_tuple(cohort(LINUX), SOURCE, VERSION, LINUX, *args)

    def test_every_generated_pin_scalar_is_bound(self):
        receipt, surface = records(LINUX)
        for key in cohort(LINUX):
            if key.startswith("dist/"):
                continue
            pin = cohort(LINUX)
            pin[key] = "wrong"
            with self.subTest(key=key), self.assertRaises(support.WorkflowError):
                support.validate_repin_tuple(pin, SOURCE, VERSION, LINUX, receipt, surface)

    def test_mac_archives_cannot_receive_linux_ledger_label(self):
        receipt, surface = records(LINUX)
        with self.assertRaisesRegex(support.WorkflowError, "exact host archive"):
            support.validate_repin_tuple(cohort(MAC), SOURCE, VERSION, LINUX, receipt, surface)

    def test_duplicate_receipt_identity_is_rejected(self):
        with self.assertRaisesRegex(support.WorkflowError, "duplicate"):
            support.parse_receipt(f"host={MAC}\nhost={LINUX}\n")

    def test_repin_rehashes_prepared_bytes_before_any_commit(self):
        for mutation in (None, "archive", "manifest", "receipt-host", "control"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                prepared = root / "prepared"
                payload_root = prepared / "bootstrap/trust-stage0"
                (root / "src").mkdir()
                (root / "src/version").write_text(VERSION + "\n")
                (root / "src/stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n")
                pin = cohort(LINUX)
                for relative in pin:
                    if relative.startswith("dist/"):
                        archive = payload_root / relative
                        archive.parent.mkdir(parents=True, exist_ok=True)
                        archive.write_bytes(b"archive")
                manifest = payload_root / "dist" / SOURCE["commit_date"] / "channel-rust-trust.toml"
                manifest.write_bytes(b"manifest")
                (prepared / "src-stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n" + "".join(f"{key}={value}\n" for key, value in pin.items()))
                ledger = root / "bootstrap/trust-stage0/seed-ledger.toml"
                ledger.parent.mkdir(parents=True)
                # A single-host ledger that records the cut host: a re-pin refuses a
                # committed ledger that does not say which hosts it records.
                ledger.write_text(f'[release]\nrepo = "fixture/trust"\nhost_triple = "{LINUX}"\n')
                receipt, surface = records(LINUX)
                receipt.update({"ddc_verdict": "identical", "ddc_seed_relation": "same-lineage",
                    "pinned_seed_commit": "b" * 40, "pinned_seed_date": "2026-07-13",
                    "ddc_seed_commit": "c" * 40, "ddc_seed_lineage": "trust",
                    "stage2_tree_sha256_pinned_seed": "d" * 64,
                    "stage2_tree_sha256_ddc_seed": "d" * 64, "lineage_disjoint_anchor": "none"})
                receipt.update({"pinned_seed_compiler_sha256": "1" * 64,
                    "pinned_seed_driver_sha256": "2" * 64, "ddc_seed_date": "2026-07-12",
                    "ddc_seed_compiler_sha256": "3" * 64, "ddc_seed_driver_sha256": "4" * 64,
                    "ddc_build_driver": "the pinned seed's cargo, in both builds",
                    "ddc_scope": "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std"})
                surface["tool_versions"] = {name: "fixture" for name in ("trustc", "targo", "trustfmt")}
                surface["entrypoint_sha256"] = {name: "5" * 64 for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")}
                surface["tree"] = {"sha256": "6" * 64}
                if mutation == "archive":
                    archive.write_bytes(b"corrupt")
                elif mutation == "manifest":
                    manifest.write_bytes(b"corrupt")
                elif mutation == "receipt-host":
                    receipt["host"] = MAC
                elif mutation == "control":
                    receipt["ddc_seed_relation"] = "reproducibility-control"
                receipt_path, surface_path = root / "receipt", root / "surface.json"
                receipt_path.write_text("".join(f"{key}={value}\n" for key, value in receipt.items()) + f"compiler_file={'7' * 64} bin/trustc\n")
                surface_path.write_text(json.dumps(surface))
                with mock.patch.object(support, "repository_state", return_value=SOURCE), mock.patch.object(support, "read_stage0_pin", return_value={"compiler_git_commit_hash": "b" * 40, "compiler_date": "2026-07-13"}), mock.patch.object(support, "check_repin_date"), mock.patch.object(support, "repin_files", return_value=({}, [])), mock.patch.object(support, "create_repin_commit", return_value="e" * 40) as commit, mock.patch.object(support.subprocess, "run", side_effect=AssertionError("no process may execute")):
                    args = (root, prepared, SOURCE["commit"], LINUX, "seed/fixture", "Fixture <fixture@example.invalid>", receipt_path, surface_path, root)
                    if mutation is None:
                        self.assertEqual(support.repin(*args)[0], "e" * 40)
                        commit.assert_called_once()
                    else:
                        with self.assertRaises(support.WorkflowError):
                            support.repin(*args)
                        commit.assert_not_called()


if __name__ == "__main__":
    unittest.main()
