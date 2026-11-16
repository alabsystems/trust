#!/usr/bin/env python3
"""Native-root input and admission controls; no compiler build or seed credit."""

from __future__ import annotations

import copy
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import initialize_linux_root_seed as initializer
from scripts import mint_seed_support as support
from scripts import seed_host_ledger as ledger

init = initializer.initialization
HOST, MAC = "aarch64-unknown-linux-gnu", "aarch64-apple-darwin"


def digest(payload):
    return hashlib.sha256(payload).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True) + "\n").encode()


def fixture():
    admission = init.policy(ledger.read_proof_file)
    pins = {}
    for name in ("compiler", "rustfmt"):
        pins.update({f"{name}_git_commit_hash": admission["source_commit"],
                     f"{name}_date": admission["source_date"], f"{name}_version": admission["source_version"] + "-trust",
                     f"{name}_channel_manifest_hash": "a" * 64})
    for host in (HOST, MAC):
        for component in ledger.COMPONENTS:
            suffix = "" if component == "trust-src" else "-" + host
            relative = f"dist/{admission['source_date']}/{component}-{admission['source_version']}-trust{suffix}.tar.xz"
            pins[relative] = digest(relative.encode())
    pins[f"dist/{admission['source_date']}/trust-src-{admission['source_version']}-trust.tar.xz"] = admission["std_source_archive_sha256"]
    files = {"bin/trustc": digest(b"inert trustc"), "lib/librustc_driver-inert.so": digest(b"inert driver"),
             f"lib/rustlib/{HOST}/lib/libstd-inert.rlib": digest(b"inert std")}
    manifest = {"schema": "trust-stage2-tree-v1", "records": [
        {"path": path, "kind": "file", "sha256": sha, "mode": 0o755} for path, sha in sorted(files.items())]}
    manifest["sha256"] = support.records_sha256(manifest["records"])
    receipt = {name: "a" * 64 for name in init.DIGEST_FIELDS}
    receipt.update(schema=init.RECEIPT_SCHEMA, kind="genesis-root", host=HOST,
                   source_commit=admission["source_commit"], source_commit_date=admission["source_date"],
                   source_version=admission["source_version"], predecessor="absent", orchestration_commit="f" * 40,
                   external_root_admission="external-bootstrap-root-only", external_root_counts_as_trust_stage0_evidence="false",
                   ddc_seed_admission="external-bootstrap-root-only", ddc_seed_counts_as_trust_stage0_evidence="false",
                   ddc_seed_relation="trust-lineage-disjoint-only", ddc_lineage_caveat=init.DDC_CAVEAT,
                   ddc_build_driver="self-hosted candidate's Targo, in both builds", ddc_scope=init.DDC_SCOPE,
                   ddc_verdict="identical", self_host_proof="pass", full_tools="pass", archives_carry_compared="pass",
                   full_tools_contract=init.HISTORICAL_CONTRACT, current_toolchain_qualification="false",
                   archive_rebuild="pass", native_runtime="pass", native_runtime_unresolved="0",
                   stage2_tree_sha256_self_host=manifest["sha256"], stage2_tree_sha256_ddc_seed=manifest["sha256"],
                   self_host_build_path="/inert/same-build", ddc_build_path="/inert/same-build",
                   compared_files="3", archive_compared_files="3", native_runtime_observations="1")
    evidence = {
        "source-closure.json": {"schema": "trust.genesis-source-closure.v1", "source_commit": admission["source_commit"],
                                "repositories": [{"path": p, "commit": c, "tracked_files": 1,
                                                   "tracked_bytes_sha256": "a" * 64}
                                                  for p, c in {".": admission["source_commit"], **admission["providers"]}.items()]},
        "inputs-before.json": {"schema": "inert-inputs", "files": 1},
        "inputs-after.json": {"schema": "inert-inputs", "files": 1},
        "full-tools.json": {"schema": "trust.genesis-native-tools.v1", "host": HOST, "passed": True,
                            "contract": init.HISTORICAL_CONTRACT, "source_commit": admission["source_commit"],
                            "current_toolchain_qualification": False, "supports_modern_native_lane": False,
                            "tools": {p: files["bin/trustc"] for p in init.FULL_TOOLS}},
        "archive-comparison.json": {"schema": "trust.genesis-archive-comparison.v1", "host": HOST,
                                    "passed": True, "files": files},
        "archive-rebuild.json": {"schema": "trust.genesis-archive-rebuild.v1", "host": HOST, "passed": True,
                                 "source_commit": admission["source_commit"], "stage2_tree_sha256": manifest["sha256"]},
        "native-runtime.json": {"checked": True, "format": "elf", "host": HOST, "unresolved": [],
                                "observations": {"/inert/elf": "1" * 64}},
    }
    payloads = {name: encoded(value) for name, value in evidence.items()}
    for role, name, prefix in (("genesis", "external-root.json", "external_root"), ("ddc", "ddc-root.json", "ddc_seed")):
        channel = "\n".join(f'[pkg.{c}.target.{HOST}]\navailable = true\nxz_hash = "{digest(c.encode())}"'
                            for c in ("rustc", "cargo", "rust-std")).encode()
        channel_name = "genesis-channel.toml" if role == "genesis" else "ddc-channel.toml"
        payloads[channel_name] = channel
        admission["external_roots"][role]["manifest_sha256"] = digest(channel)
        receipt[prefix + "_commit"] = admission["external_roots"][role]["commit"]
        payloads[name] = encoded({"admission": "external-bootstrap-root-only", "counts_as_trust_stage0_evidence": False,
                                  "identity": {"lineage": "stock", "host": HOST, "commit": receipt[prefix + "_commit"],
                                               "compiler_sha256": receipt[prefix + "_compiler_sha256"],
                                               "driver_sha256": receipt[prefix + "_driver_sha256"]},
                                  "components": [{"component": c, "archive_sha256": digest(c.encode()),
                                                  "payloads": [{"path": "inert"}]} for c in ("rustc", "cargo", "rust-std")]})
    for name, field in init.EVIDENCE.items():
        receipt[field] = digest(payloads[name])
    payloads["stage2-self-host.json"] = payloads["stage2-ddc.json"] = encoded(manifest)
    surface = {"schema": "trust-self-host-seed-surface-v1", "host": HOST, "source_version": admission["source_version"],
               "entrypoint_sha256": {name: files["bin/trustc"] for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")},
               "tool_versions": {name: "inert-native-fixture" for name in ("trustc", "targo", "trustfmt")},
               "tree": {"sha256": "a" * 64}}
    return admission, pins, receipt, payloads, surface, files


def receipt_bytes(receipt, files):
    return ("".join(f"{k}={v}\n" for k, v in receipt.items())
            + "".join(f"compiler_file={sha} {p}\n" for p, sha in files.items())).encode()


class AdmissionTests(unittest.TestCase):
    def setUp(self):
        self.admission, self.pins, self.receipt, self.payloads, self.surface, self.files = fixture()
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.addCleanup(mock.patch.stopall)
        mock.patch.object(ledger, "initialization_module", return_value=init).start()
        mock.patch.object(init, "policy", return_value=self.admission).start()

    def write(self):
        prefix = self.root / "host-proofs" / HOST
        (prefix / "initialization").mkdir(parents=True, exist_ok=True)
        for name, value in self.payloads.items():
            (prefix / "initialization" / name).write_bytes(value)
        raw = receipt_bytes(self.receipt, self.files)
        (prefix / "GENESIS-ROOT").write_bytes(raw)
        (prefix / "seed-surface.json").write_bytes(encoded(self.surface))
        record = ledger.make_genesis_host_record(self.pins, HOST, raw, encoded(self.surface))
        (prefix / "host-record.json").write_bytes(ledger.record_bytes(record))
        return record

    def test_complete_custody_is_genesis_not_an_invented_native_mint(self):
        record = self.write()
        raw = receipt_bytes(self.receipt, self.files)
        init.capture_evidence(self.root, HOST, self.receipt, raw, ledger.read_proof, self.admission)
        with self.assertRaisesRegex(ValueError, "admission is pending"):
            ledger.capture_host_record(self.root, self.pins, HOST, record)
        self.assertEqual(record["root_initialization"]["predecessor"], "absent")
        self.assertNotIn("mint", record)
        with self.assertRaises(ValueError):
            ledger.make_host_record(self.pins, HOST, receipt_bytes(self.receipt, self.files), encoded(self.surface))

    def test_prepared_root_uses_actual_host_dispatch_and_cannot_skip_pending_producer(self):
        self.write()
        seed = self.root / "bootstrap/trust-stage0"
        seed.mkdir(parents=True)
        shutil.move(str(self.root / "host-proofs"), seed / "host-proofs")
        (self.root / "src").mkdir()
        (self.root / "src/stage0").write_text("".join(k + "=" + v + "\n" for k, v in self.pins.items()))
        with mock.patch.object(initializer.ledger, "pinned_hosts", return_value=[HOST]), \
                mock.patch.object(initializer.ledger, "initialization_module", return_value=init), \
                self.assertRaisesRegex(ValueError, "admission is pending"):
            initializer.prepared_admission(self.root, HOST, self.admission, {}, {})

    def test_actual_linux_optional_loader_absence_is_recorded_without_digest_credit(self):
        runtime = json.loads(self.payloads["native-runtime.json"])
        runtime["observations"]["/etc/ld.so.preload"] = None
        self.payloads["native-runtime.json"] = encoded(runtime)
        self.receipt["native_runtime_receipt_sha256"] = digest(self.payloads["native-runtime.json"])
        self.receipt["native_runtime_observations"] = "2"
        init.validate_evidence(self.payloads, self.receipt, self.files, self.admission)
        runtime["observations"]["/inert/elf"] = None
        self.payloads["native-runtime.json"] = encoded(runtime)
        with self.assertRaisesRegex(ValueError, "native runtime evidence"):
            init.validate_evidence(self.payloads, self.receipt, self.files, self.admission)

    def test_missing_tampered_symlink_evidence_is_refused(self):
        for name in self.payloads:
            for failure in ("missing", "tampered", "symlink"):
                with self.subTest(name=name, failure=failure):
                    record = self.write()
                    path = self.root / "host-proofs" / HOST / "initialization" / name
                    path.unlink()
                    if failure == "tampered":
                        path.write_bytes(b"changed")
                    if failure == "symlink":
                        path.symlink_to("../GENESIS-ROOT")
                    with self.assertRaises((ValueError, OSError)):
                        ledger.capture_host_record(self.root, self.pins, HOST, record)
                    if path.is_symlink():
                        path.unlink()

    def test_admission_cannot_skip_phases_invent_a_seed_or_broaden_diversity(self):
        changes = {"pinned_seed_commit": "6" * 40, "predecessor": "6986546e", "source_commit": "6" * 40,
                   "external_root_counts_as_trust_stage0_evidence": "true", "ddc_seed_commit": "6" * 40,
                   "ddc_seed_relation": "lineage-disjoint", "ddc_lineage_caveat": "Thompson defeated",
                   "full_tools": "pending", "self_host_proof": "pending", "archive_rebuild": "pending",
                   "full_tools_contract": "current-native-floor", "current_toolchain_qualification": "true",
                   "native_runtime_observations": "0", "compared_files": "0", "ddc_build_path": "/another-build",
                   "inputs_after_sha256": "f" * 64, "stage2_tree_sha256_ddc_seed": "f" * 64}
        for name, value in changes.items():
            bad = {**self.receipt, name: value}
            with self.subTest(name=name), self.assertRaises(ValueError):
                ledger.make_genesis_host_record(self.pins, HOST, receipt_bytes(bad, self.files), encoded(self.surface))

    def test_retained_metadata_cannot_hide_zero_tools_unresolved_runtime_or_foreign_rebuild(self):
        changes = {"full-tools.json": lambda d: d.update(tools={}),
                   "native-runtime.json": lambda d: d.update(unresolved=["missing.so"]),
                   "archive-rebuild.json": lambda d: d.update(host=MAC),
                   "archive-comparison.json": lambda d: d.update(files={"bin/trustc": "1" * 64}),
                   "external-root.json": lambda d: d.update(counts_as_trust_stage0_evidence=True)}
        original_receipt, original_payloads = copy.deepcopy(self.receipt), copy.deepcopy(self.payloads)
        for name, mutate in changes.items():
            self.receipt, self.payloads = copy.deepcopy(original_receipt), copy.deepcopy(original_payloads)
            document = json.loads(self.payloads[name])
            mutate(document)
            self.payloads[name] = encoded(document)
            self.receipt[init.EVIDENCE[name]] = digest(self.payloads[name])
            record = self.write()
            with self.subTest(name=name), self.assertRaises(ValueError):
                ledger.capture_host_record(self.root, self.pins, HOST, record)

    def test_compared_files_and_tree_records_must_match_exactly(self):
        record = self.write()
        raw = receipt_bytes(self.receipt, self.files) + b"compiler_file=" + b"1" * 64 + b" bin/trustc\n"
        (self.root / "host-proofs" / HOST / "GENESIS-ROOT").write_bytes(raw)
        with self.assertRaises(ValueError):
            ledger.capture_host_record(self.root, self.pins, HOST, record)

    def test_unknown_kind_foreign_host_and_fabricated_surface_fail(self):
        record = self.write()
        for bad in ({**record, "schema": "unknown"}, {**record, "admission_kind": "mint"},
                    {**record, "entrypoint_sha256": {"trustc": "f" * 64}}):
            with self.assertRaises(ValueError):
                ledger.capture_host_record(self.root, self.pins, HOST, bad)
        with self.assertRaises(ValueError):
            ledger.make_genesis_host_record(self.pins, MAC, receipt_bytes(self.receipt, self.files), encoded(self.surface))

    def test_actual_archive_bytes_join_the_compared_compiler_std_and_every_tool(self):
        seed = self.root
        tools = set(init.FULL_TOOLS)
        assignments = {"targo": {"bin/targo", "bin/cargo"}, "targo-trust": {"bin/targo-trust"},
                       "trustfmt": {"bin/trustfmt", "bin/targo-fmt"},
                       "tippy": {"bin/tippy", "bin/targo-tippy", "bin/tippy-driver"},
                       "trust-analyzer": {"bin/trust-analyzer"}}
        assignments["trustc"] = tools - set().union(*assignments.values())
        assignments["trustc-dev"] = {"lib/librustc_driver-inert.so"}
        assignments["trust-std"] = {f"lib/rustlib/{HOST}/lib/libstd-inert.rlib"}
        assignments["trust-src"] = set()
        def archive(component, changed=None):
            suffix = "" if component == "trust-src" else "-" + HOST
            version = self.admission["source_version"] + "-trust"
            top = component + "-" + version + suffix
            relative = f"dist/{self.admission['source_date']}/{top}.tar.xz"
            path = seed / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            with tarfile.open(path, "w:xz") as bundle:
                rows = {"install.sh": b"#!/bin/sh\n", "version": version.encode(),
                        "git-commit-hash": self.admission["source_commit"].encode()}
                for p in assignments[component]:
                    body = b"inert driver" if "librustc_driver" in p else b"inert std" if "libstd-" in p else b"inert trustc"
                    rows[component + "/" + p] = b"tampered payload" if p == changed else body
                for name, body in rows.items():
                    member = tarfile.TarInfo(top + "/" + name)
                    member.size = len(body)
                    bundle.addfile(member, io.BytesIO(body))
            self.pins[relative] = digest(path.read_bytes())
            return relative
        for component in ledger.COMPONENTS:
            archive(component)
        self.admission["std_source_archive_sha256"] = self.pins[next(k for k in self.pins if "/trust-src-" in k)]
        self.write()
        init.check_archive_joins(seed, self.pins, HOST, self.receipt, self.surface, ledger.read_proof)
        # Re-pin a changed archive to its own valid hash: the semantic byte
        # joins, rather than just the archive checksum, must reject each case.
        for component, path in (("trustc", "bin/trustc"), ("trustc", "bin/ay"),
                                ("trustc-dev", "lib/librustc_driver-inert.so"),
                                ("trust-std", f"lib/rustlib/{HOST}/lib/libstd-inert.rlib")):
            archive(component, path)
            with self.subTest(path=path), self.assertRaises(ValueError):
                init.check_archive_joins(seed, self.pins, HOST, self.receipt, self.surface, ledger.read_proof)
            archive(component)
        wrong = copy.deepcopy(self.surface)
        wrong["entrypoint_sha256"]["trustc"] = "f" * 64
        with self.assertRaises(ValueError):
            init.check_archive_joins(seed, self.pins, HOST, self.receipt, wrong, ledger.read_proof)


class LegacyTests(unittest.TestCase):
    def test_original_bytes_are_preserved_without_upgrade_or_changed_archives(self):
        admission = init.policy(ledger.read_proof_file)
        original = admission["legacy_admission"]["commit"]
        stage0 = subprocess.check_output(["/usr/bin/git", "-C", str(ROOT), "show", original + ":src/stage0"])
        raw_ledger = subprocess.check_output(["/usr/bin/git", "-C", str(ROOT), "show", original + ":bootstrap/trust-stage0/seed-ledger.toml"])
        pins = dict(line.split("=", 1) for line in stage0.decode().splitlines() if "=" in line and not line.startswith("#"))
        receipt = encoded({"schema": "trust.legacy-seed-admission.v1", "ledger": raw_ledger.decode(), "stage0": stage0.decode()})
        record = ledger.make_legacy_host_record(pins, MAC, receipt)
        self.assertEqual(record["legacy_admission"]["original_ledger_sha256"], admission["legacy_admission"]["ledger_sha256"])
        self.assertFalse(record["legacy_admission"]["counts_as_native_mint_evidence"])
        self.assertFalse(record["legacy_admission"]["counts_as_root_initialization_evidence"])
        self.assertNotIn("mint", record)
        self.assertNotIn("entrypoint_sha256", record)
        for wrong in (HOST,):
            with self.assertRaises(ValueError):
                ledger.make_legacy_host_record(pins, wrong, receipt)
        changed = dict(pins)
        changed[next(k for k in pins if k.startswith("dist/"))] = "f" * 64
        with self.assertRaises(ValueError):
            ledger.make_legacy_host_record(changed, MAC, receipt)
        for name in ("ledger", "stage0"):
            document = json.loads(receipt)
            document[name] += "\n"
            with self.assertRaises(ValueError):
                ledger.make_legacy_host_record(pins, MAC, encoded(document))


class InputTests(unittest.TestCase):
    def native_pack_fixture(self, root):
        stage2 = root / "stage2"
        for relative in (*init.FULL_TOOLS, "lib/librustc_driver-inert.so", f"lib/rustlib/{HOST}/lib/libstd-inert.rlib",
                         "share/inert-unpackaged-metadata"):
            path = stage2 / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(("inert nonexecuted fixture " + relative).encode())
            path.chmod(0o755 if relative in init.FULL_TOOLS else 0o644)
        (stage2 / "lib/driver-alias.so").symlink_to("librustc_driver-inert.so")
        (stage2 / "bin/internal-driver-alias").symlink_to("../lib/librustc_driver-inert.so")
        os.link(stage2 / "lib/librustc_driver-inert.so", stage2 / "bin/internal-hard-driver")
        return stage2, support.stage2_manifest(stage2)

    def write_native_pack(self, archive, stage2, *, changed=None, extra=None, omit_snapshots=False):
        with tarfile.open(archive, "w:xz") as bundle:
            for entry in ("bin", "lib", "libexec"):
                def filter_member(row):
                    if omit_snapshots and any(row.name == p or row.name.startswith(p + "/") for p in init.SOURCE_SNAPSHOTS):
                        return None
                    if changed == ("missing", row.name):
                        return None
                    if changed == ("mode", row.name):
                        row.mode ^= 0o111
                    if changed == ("link", row.name):
                        row.linkname = "../../outside"
                    return row
                bundle.add(stage2 / entry, arcname=entry, filter=filter_member)
            if extra:
                row = tarfile.TarInfo(extra)
                row.size = 7
                bundle.addfile(row, io.BytesIO(b"changed"))

    def test_full18_native_pack_joins_exact_surface_projection_and_link_topology(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            stage2, manifest = self.native_pack_fixture(root)
            archive = root / "native.tar.xz"
            self.write_native_pack(archive, stage2)
            files = init.native_pack_payloads(archive, support.sha256_file(archive), encoded(manifest), HOST)
            self.assertTrue(set(init.FULL_TOOLS).issubset(files))
            self.assertNotIn("share/inert-unpackaged-metadata", files)
            for changed in (("missing", "bin/rustdoc"), ("mode", "bin/trustc"), ("link", "lib/driver-alias.so")):
                self.write_native_pack(archive, stage2, changed=changed)
                with self.subTest(changed=changed), self.assertRaises((ValueError, support.WorkflowError)):
                    init.native_pack_payloads(archive, support.sha256_file(archive), encoded(manifest), HOST)
            for extra in ("bin/trustc", "../escaping"):
                self.write_native_pack(archive, stage2, extra=extra)
                with self.subTest(extra=extra), self.assertRaises((ValueError, support.WorkflowError)):
                    init.native_pack_payloads(archive, support.sha256_file(archive), encoded(manifest), HOST)
            (stage2 / "bin/trustc").write_bytes(b"repinned tampered compiler")
            self.write_native_pack(archive, stage2)
            with self.assertRaises(ValueError):
                init.native_pack_payloads(archive, support.sha256_file(archive), encoded(manifest), HOST)

    def test_exact_bootstrap_source_links_are_retained_but_not_runtime_payloads(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            stage2, _ = self.native_pack_fixture(root)
            source = root / "source"
            source.mkdir()
            for prefix in init.SOURCE_SNAPSHOTS:
                directory = stage2 / prefix
                directory.mkdir()
                (directory / "rust").symlink_to(source, target_is_directory=True)
            manifest = support.stage2_manifest(stage2)
            projected, omitted = init.native_projection(manifest, source)
            self.assertEqual(len(omitted), 4)
            self.assertTrue(all(row not in projected for row in omitted))
            archive = root / "native.tar.xz"
            self.write_native_pack(archive, stage2, omit_snapshots=True)
            files = init.native_pack_payloads(archive, support.sha256_file(archive), encoded(manifest), HOST)
            self.assertTrue(set(init.FULL_TOOLS).issubset(files))
            self.write_native_pack(archive, stage2)
            with self.assertRaisesRegex(ValueError, "unobserved"):
                init.native_pack_payloads(archive, support.sha256_file(archive), encoded(manifest), HOST)

    def test_source_snapshot_exclusion_cannot_hide_another_target_or_extra_payload(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            stage2, _ = self.native_pack_fixture(root)
            prefix = stage2 / init.SOURCE_SNAPSHOTS[0]
            prefix.mkdir()
            (prefix / "rust").symlink_to(root, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "another authenticated source"):
                init.native_projection(support.stage2_manifest(stage2), stage2)
            (prefix / "hidden-runtime-library").write_bytes(b"cannot hide this")
            with self.assertRaisesRegex(ValueError, "exact bootstrap"):
                init.native_projection(support.stage2_manifest(stage2), root)

    def test_native_pack_cannot_hide_missing_fulltool_or_outbound_source_link(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            stage2, manifest = self.native_pack_fixture(root)
            archive = root / "native.tar.xz"
            (stage2 / "lib/outbound-source").symlink_to("/outside/source")
            self.write_native_pack(archive, stage2)
            with self.assertRaises((ValueError, support.WorkflowError)):
                init.native_pack_payloads(archive, support.sha256_file(archive), encoded(support.stage2_manifest(stage2)), HOST)
            (stage2 / "lib/outbound-source").unlink()
            (stage2 / "bin/internal-driver-alias").unlink()
            (stage2 / "bin/internal-driver-alias").symlink_to("../../outside/source")
            self.write_native_pack(archive, stage2)
            with self.assertRaises((ValueError, support.WorkflowError)):
                init.native_pack_payloads(archive, support.sha256_file(archive), encoded(support.stage2_manifest(stage2)), HOST)
            (stage2 / "bin/internal-driver-alias").unlink()
            (stage2 / "bin/trustd").unlink()
            self.write_native_pack(archive, stage2)
            with self.assertRaisesRegex(ValueError, "omits a required tool"):
                init.native_pack_payloads(archive, support.sha256_file(archive), encoded(support.stage2_manifest(stage2)), HOST)

    def test_real_directory_bearing_stage2_manifest_uses_the_ordinary_schema(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for path in ("bin/trustc", "lib/librustc_driver-inert.so", f"lib/rustlib/{HOST}/lib/libstd-inert.rlib"):
                named = root / path
                named.parent.mkdir(parents=True, exist_ok=True)
                named.write_bytes(b"inert compiler/std fixture, never executed")
            manifest = support.stage2_manifest(root)
            self.assertTrue(any(row["kind"] == "directory" for row in manifest["records"]))
            self.assertEqual(init.tree_manifest(encoded(manifest), HOST), manifest)

    def test_archive_bytes_installed_payload_and_platform_are_all_bound(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            seed = root / "seed"
            (seed / "bin").mkdir(parents=True)
            (seed / "bin/rustc").write_bytes(b"inert external compiler")
            archive = root / f"rustc-nightly-{HOST}.tar.xz"
            with tarfile.open(archive, "w:xz") as bundle:
                member = tarfile.TarInfo(f"{archive.name[:-7]}/rustc/bin/rustc")
                member.size = len(b"inert external compiler")
                bundle.addfile(member, io.BytesIO(b"inert external compiler"))
            sha = digest(archive.read_bytes())
            self.assertEqual(len(initializer.bind_archive(archive, sha, seed, "rustc", HOST)["payloads"]), 1)
            with self.assertRaises(ValueError):
                initializer.bind_archive(archive, "f" * 64, seed, "rustc", HOST)
            with self.assertRaises(ValueError):
                initializer.bind_archive(archive, sha, seed, "rustc", MAC)
            (seed / "bin/rustc").write_bytes(b"tampered compiler")
            with self.assertRaises(ValueError):
                initializer.bind_archive(archive, sha, seed, "rustc", HOST)
            (seed / "bin/rustc").unlink()
            with self.assertRaises((OSError, ValueError)):
                initializer.bind_archive(archive, sha, seed, "rustc", HOST)

    def test_source_snapshot_rejects_wrong_commit_dirty_bytes_and_skip_bits(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def git(*args):
                return subprocess.check_output(["/usr/bin/git", "-C", str(root), *args], stderr=subprocess.DEVNULL).decode().strip()
            git("init", "-q")
            git("config", "user.name", "Inert control")
            git("config", "user.email", "inert@example.invalid")
            (root / "source").write_text("original\n")
            git("add", "source")
            git("commit", "-qm", "inert source control")
            commit = git("rev-parse", "HEAD")
            self.assertEqual(len(initializer.source_snapshot(root, commit)["repositories"]), 1)
            with self.assertRaises(ValueError):
                initializer.source_snapshot(root, "f" * 40)
            (root / "source").write_text("changed\n")
            with self.assertRaises(ValueError):
                initializer.source_snapshot(root, commit)
            (root / "source").write_text("original\n")
            git("update-index", "--skip-worktree", "source")
            with self.assertRaises(ValueError):
                initializer.source_snapshot(root, commit)

    def test_cli_missing_inputs_refuses_and_writes_no_root_receipt(self):
        args = ["--source-root", "/missing-source", "--std-source-archive", "/missing-source-archive"]
        for role in ("genesis", "ddc"):
            for field in ("manifest", "archives", "sysroot"):
                args += [f"--{role}-{field}", "/missing-input"]
        with mock.patch("builtins.print"):
            self.assertEqual(initializer.main(args), 1)

    @unittest.skipUnless(sys.platform == "linux", "native glibc loader observation")
    def test_external_elf_closure_preserves_external_only_classification(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "bin").mkdir()
            for name in ("rustc", "cargo"):
                shutil.copy2("/usr/bin/true", root / "bin" / name)
            host = support.native_host()
            runtime = initializer.linux.external_bootstrap_closure(root, host)
            self.assertFalse(runtime["counts_as_trust_stage0_evidence"])
            self.assertEqual(runtime["admission"], "external-bootstrap-root-only")
            self.assertTrue(runtime["observations"])
            initializer.linux.unchanged(runtime)
            with self.assertRaises(ValueError):
                initializer.linux.closure(root, host, [])


if __name__ == "__main__":
    unittest.main()
