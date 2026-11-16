#!/usr/bin/env python3
"""Real inert archive/cohort controls; no native build or seed authority."""

from __future__ import annotations

import copy
import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import seed_initialization_cohort as cohort

HOST, MAC, COMMIT, DATE, VERSION = "aarch64-unknown-linux-gnu", "aarch64-apple-darwin", "a" * 40, "2026-07-13", "1.99.0-trust"


def sha(payload):
    return hashlib.sha256(payload).hexdigest()


def archive(path, payload, *, escaping=False):
    top = path.name.removesuffix(".tar.xz")
    with tarfile.open(path, "w:xz") as bundle:
        for name, data in (("install.sh", b"inert installer"), ("version", b"1.99.0"),
                           ("git-commit-hash", COMMIT.encode()), ("inert-payload", payload)):
            item = tarfile.TarInfo(top + "/" + name)
            item.size = len(data)
            item.mode = 0o644
            bundle.addfile(item, io.BytesIO(data))
        if escaping:
            link = tarfile.TarInfo(top + "/outbound")
            link.type, link.linkname = tarfile.SYMTYPE, "../../outside"
            bundle.addfile(link)
    return sha(path.read_bytes())


class CohortControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.native = self.root / "native"
        self.legacy = self.root / "legacy"
        self.legacy.mkdir()
        self.receipt = self.root / "LEGACY-ADMISSION"
        self.manifest = self.root / "legacy-channel.toml"
        self.out = self.root / "cohort"
        self.pins, self.native_pins = {}, {"dist_server": "file://repo"}
        old_manifest = {"date": DATE, "pkg": {"trust": {"version": VERSION, "git_commit_hash": COMMIT}}}
        native_manifest = copy.deepcopy(old_manifest)
        for role in ("compiler", "rustfmt"):
            identity = {f"{role}_git_commit_hash": COMMIT, f"{role}_date": DATE, f"{role}_version": VERSION}
            self.pins.update(identity)
            self.native_pins.update(identity)
        for component in cohort.ledger.COMPONENTS:
            package = cohort.PACKAGES.get(component, component)
            old_entry = {"version": VERSION, "git_commit_hash": COMMIT, "target": {}}
            new_entry = copy.deepcopy(old_entry)
            for host, directory, pins, manifest_entry, server, prefix in (
                (MAC, self.legacy, self.pins, old_entry, cohort.SERVER, "old"),
                (HOST, self.native / "bootstrap/trust-stage0/dist" / DATE, self.native_pins, new_entry, "file://repo", "new")):
                directory.mkdir(parents=True, exist_ok=True)
                suffix, target = ("", "*") if component == "trust-src" else ("-" + host, host)
                name = component + "-" + VERSION + suffix + ".tar.xz"
                relative = "dist/" + DATE + "/" + name
                digest = archive(directory / name, (prefix + component).encode())
                pins[relative] = digest
                manifest_entry["target"][target] = {"available": True, "xz_url": server + "/" + relative, "xz_hash": digest}
            old_manifest["pkg"][package] = old_entry
            native_manifest["pkg"][package] = new_entry
        self.manifest.write_text(cohort.prepare.dump_toml(old_manifest))
        native_channel = self.native / "bootstrap/trust-stage0/dist" / DATE / "channel-rust-trust.toml"
        native_channel.write_text(cohort.prepare.dump_toml(native_manifest))
        for role in ("compiler", "rustfmt"):
            self.pins[role + "_channel_manifest_hash"] = sha(self.manifest.read_bytes())
            self.native_pins[role + "_channel_manifest_hash"] = sha(native_channel.read_bytes())
        old_stage0 = "".join(k + "=" + v + "\n" for k, v in self.pins.items())
        self.write_native_pins()
        old_ledger = ('scope = "internal"\npromotion_decision = "admit-internal"\n'
                      + "checksums = " + json.dumps(["sha256:" + v for k, v in self.pins.items() if k.startswith("dist/")])
                      + '\n[release]\nhost_triple = "' + MAC + '"\n[release.reported_product_identities]\n'
                      + '\n'.join(k + ' = "original reported fixture"' for k in ("trustc", "targo", "trustfmt")) + "\n")
        self.receipt.write_text(json.dumps({"schema": "trust.legacy-seed-admission.v1", "ledger": old_ledger, "stage0": old_stage0}))
        self.shared = self.legacy / ("trust-src-" + VERSION + ".tar.xz")
        self.admission = {"source_commit": COMMIT, "source_date": DATE, "source_version": "1.99.0",
                          "std_source_archive_sha256": sha(self.shared.read_bytes()),
                          "legacy_admission": {"host": MAC, "commit": "b" * 40, "ledger_sha256": sha(old_ledger.encode()),
                                               "stage0_sha256": sha(old_stage0.encode())}}
        self.addCleanup(mock.patch.stopall)
        mock.patch.object(cohort.initialization, "policy", return_value=self.admission).start()
        mock.patch.object(cohort.ledger, "initialization_module", return_value=cohort.initialization).start()

    def write_native_pins(self):
        (self.native / "src-stage0").write_text("".join(k + "=" + v + "\n" for k, v in self.native_pins.items()))

    def assemble(self):
        return cohort.assemble(self.native, HOST, self.receipt, self.legacy, self.manifest, self.shared, self.out)

    def test_real_dual_host_union_preserves_all_original_bytes_and_displaces_repacked_source(self):
        result = self.assemble()
        self.assertEqual(len(result["payloads"]), 17)
        shared = "dist/" + DATE + "/" + self.shared.name
        self.assertEqual((self.out / "bootstrap/trust-stage0" / shared).read_bytes(), self.shared.read_bytes())
        self.assertNotEqual(result["displaced_native_source_sha256"], result["shared_source"]["sha256"])
        for relative in result["legacy"]["record"]["payloads"]:
            self.assertEqual((self.out / "bootstrap/trust-stage0" / relative).read_bytes(), (self.legacy / Path(relative).name).read_bytes())
        self.assertFalse(result["admitted_root_seed"])
        self.assertFalse(result["counts_as_trust_stage0_evidence"])
        self.assertFalse((self.out / "bootstrap/trust-stage0/SEED-LEDGER.toml").exists())

    def test_legacy_archive_tamper_refused_before_output(self):
        next(p for p in self.legacy.iterdir() if p.name.startswith("targo-")).write_bytes(b"tamper")
        with self.assertRaisesRegex(ValueError, "checksum"):
            self.assemble()
        self.assertFalse(self.out.exists())

    def test_legacy_text_cannot_acquire_new_evidence(self):
        raw = json.loads(self.receipt.read_text())
        raw["ledger"] += "# altered\n"
        self.receipt.write_text(json.dumps(raw))
        with self.assertRaisesRegex(ValueError, "exact original bytes"):
            self.assemble()

    def test_shared_source_substitution_is_refused(self):
        self.shared.write_bytes(b"substitute")
        with self.assertRaisesRegex(ValueError, "checksum"):
            self.assemble()

    def test_native_pin_must_authenticate_real_prepared_channel(self):
        self.native_pins["compiler_channel_manifest_hash"] = "f" * 64
        self.write_native_pins()
        with self.assertRaisesRegex(ValueError, "prepared pin"):
            self.assemble()

    def test_native_host_or_source_cannot_change(self):
        self.native_pins["compiler_git_commit_hash"] = "c" * 40
        self.write_native_pins()
        with self.assertRaisesRegex(ValueError, "source or host"):
            self.assemble()

    def test_manifest_extra_payload_or_wrong_component_refused(self):
        manifest = {"pkg": {"unknown": {"target": {HOST: {"available": True, "xz_url": cohort.SERVER + "/dist/inert.tar.xz", "xz_hash": "a" * 64}}}}}
        with self.assertRaisesRegex(ValueError, "component, host or archive"):
            cohort.manifest_payloads(manifest, self.pins, {})

    def test_original_manifest_bytes_are_pinned(self):
        self.manifest.write_text(self.manifest.read_text() + "# changed\n")
        with self.assertRaisesRegex(ValueError, "exact original pin"):
            self.assemble()

    def test_nonboolean_availability_is_refused(self):
        manifest = {"pkg": {"trust-src": {"target": {"*": {"available": "true"}}}}}
        with self.assertRaisesRegex(ValueError, "availability is not boolean"):
            cohort.manifest_payloads(manifest, self.pins, {})

    def test_native_metadata_change_during_copy_never_emits_success(self):
        real = cohort.support.copy_authenticated
        def copying(source, destination):
            real(source, destination)
            if source.name.startswith("targo-"):
                channel = self.native / "bootstrap/trust-stage0/dist" / DATE / "channel-rust-trust.toml"
                channel.write_text(channel.read_text() + "# changed during copy\n")
        with mock.patch.object(cohort.support, "copy_authenticated", side_effect=copying):
            with self.assertRaisesRegex(ValueError, "metadata changed"):
                self.assemble()
        self.assertFalse((self.out / "cohort-payloads.json").exists())

    def test_output_is_never_overwritten(self):
        self.out.mkdir()
        marker = self.out / "retained"
        marker.write_bytes(b"retain")
        with self.assertRaisesRegex(ValueError, "fresh"):
            self.assemble()
        self.assertEqual(marker.read_bytes(), b"retain")

    def test_real_archive_link_escape_is_refused(self):
        path = self.root / "inert.tar.xz"
        digest = archive(path, b"fixture", escaping=True)
        with self.assertRaisesRegex(cohort.support.WorkflowError, "root"):
            cohort.archive_capture(path, digest, COMMIT)


if __name__ == "__main__":
    unittest.main()
