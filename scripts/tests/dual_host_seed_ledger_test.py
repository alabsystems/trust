#!/usr/bin/env python3
"""Inert dual-host admission controls; no compiler, Git, cache, or publisher runs."""

from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor. This test imports tomllib (3.11+) at its top.
# `python3 dual_host_seed_ledger_test.py` on a machine whose python3 is older (3.9 on macOS
# CommandLineTools) re-execs here under the newest >=3.11 on PATH
# (scripts/tests/python_floor_test.py holds every such script to this).
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("dual_host_seed_ledger_test.py requires Python 3.11+ (tomllib); none found on PATH")

import copy
import hashlib
import importlib.util
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path
from unittest import mock

# The ledger refuses a seed proof root that is not its own resolved path
# (seed_host_ledger.read_proof: "seed proof root or one of its parents contains
# a symlink"), and macOS temporary directories live under the /var ->
# /private/var link: until 2026-10-14 five tests here failed on macOS on that
# refusal, before what each of them tests was reached. Hand the ledger resolved
# temporary roots, as the recreator's tests do.
tempfile.tempdir = os.path.realpath(tempfile.gettempdir())

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts import mint_seed_support as support
from scripts import recreate_bootstrap as recreate
from scripts import seed_host_ledger as host_ledger


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


prepare = load("dual_host_prepare", ROOT / "src/tools/trust-stage0-dist/prepare.py")
MAC, LINUX = "aarch64-apple-darwin", "aarch64-unknown-linux-gnu"
COMMIT, DATE, VERSION = "a" * 40, "2026-09-30", "0.10.0"
CURRENT = 'scope="internal"\npromotion_decision="admit-internal"\nsignatures=["placeholder:internal-admission-only"]\n[release]\nrepo="fixture/trust"\nvisibility="private"\n'


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def cohort(hosts=(MAC, LINUX)) -> dict[str, str]:
    pins = {"dist_server": "file://{trust-root}/bootstrap/trust-stage0"}
    for name in ("compiler", "rustfmt"):
        pins.update({f"{name}_git_commit_hash": COMMIT, f"{name}_date": DATE,
                     f"{name}_version": VERSION + "-trust",
                     f"{name}_channel_manifest_hash": digest(b"manifest")})
    for host in hosts:
        for name in host_ledger.COMPONENTS:
            suffix = "" if name == "trust-src" else f"-{host}"
            relative = f"dist/{DATE}/{name}-{VERSION}-trust{suffix}.tar.xz"
            pins[relative] = digest(relative.encode())
    return pins


def proofs(host: str):
    receipt = {
        "schema": "trust-seed-mint-v1", "source_commit": COMMIT,
        "source_commit_date": DATE, "source_version": VERSION, "host": host,
        "pinned_seed_commit": "b" * 40, "pinned_seed_date": "2026-07-13",
        "pinned_seed_compiler_sha256": "1" * 64, "pinned_seed_driver_sha256": "2" * 64,
        "ddc_seed_relation": "pin-ancestor", "ddc_seed_commit": "c" * 40,
        "ddc_seed_date": "2026-07-12", "ddc_seed_lineage": "trust",
        "ddc_seed_compiler_sha256": "3" * 64, "ddc_seed_driver_sha256": "4" * 64,
        "ddc_build_driver": "the pinned seed's cargo, in both builds",
        "ddc_scope": "<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std",
        "stage2_tree_sha256_pinned_seed": digest(host.encode()),
        "stage2_tree_sha256_ddc_seed": digest(host.encode()), "ddc_verdict": "identical",
        "lineage_disjoint_anchor": "none", "self_host_proof": "pass",
    }
    surface = {
        "schema": "trust-self-host-seed-surface-v1", "source_version": VERSION, "host": host,
        "tool_versions": {name: f"inert-{host}-{name}" for name in ("trustc", "targo", "trustfmt")},
        "entrypoint_sha256": {name: digest((host + name).encode()) for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")},
        "tree": {"sha256": digest((host + "installed-tree").encode())},
    }
    return receipt, surface


def proof_bytes(host: str):
    receipt, surface = proofs(host)
    text = "".join(f"{key}={value}\n" for key, value in receipt.items())
    text += f"compiler_file={digest(host.encode())} bin/trustc\n"
    return text.encode(), (json.dumps(surface, sort_keys=True) + "\n").encode()


def write_proofs(seed: Path, host: str, payloads=None):
    payloads = payloads or proof_bytes(host)
    for relative, payload in zip(host_ledger.proof_paths(host), payloads):
        path = seed / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)
    # A record binds only its own host's archives and the shared source, so the
    # host's own cohort gives the same record as any cohort that includes it.
    record = host_ledger.make_host_record(cohort((host,)), host, *payloads)
    (seed / host_ledger.record_path(host)).write_bytes(host_ledger.record_bytes(record))


def stage0_text(pins: dict[str, str]) -> str:
    return "".join(f"{key}={value}\n" for key, value in pins.items())


def fixture(root: Path, hosts=(MAC, LINUX), legacy=False):
    pins = cohort(hosts)
    seed = root / "bootstrap/trust-stage0"
    (root / "src").mkdir(parents=True)
    (root / "src/stage0").write_text(stage0_text(pins))
    (root / "src/version").write_text(VERSION + "\n")
    (root / "scripts").mkdir()
    (root / "scripts/check_seed_freshness.py").write_text("# inert mocked freshness check\n")
    for relative in pins:
        if relative.startswith("dist/"):
            path = seed / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(relative.encode())
    (seed / f"dist/{DATE}/channel-rust-trust.toml").write_bytes(b"manifest")
    records = {}
    for host in hosts:
        write_proofs(seed, host)
        records[host] = host_ledger.make_host_record(pins, host, *proof_bytes(host))
    receipt, surface = proofs(hosts[0])
    options = {} if legacy else {"host_records": records}
    ledger, _ = support.render_seed_ledger(CURRENT, pins, stage0_text(pins), hosts[0], surface["tool_versions"], receipt, **options)
    (seed / "seed-ledger.toml").write_text(ledger)
    return pins, records


def rewrite_ledger(root: Path, mutation):
    path = root / "bootstrap/trust-stage0/seed-ledger.toml"
    document = tomllib.loads(path.read_text())
    mutation(document)
    path.write_text(prepare.dump_toml(document))


def capture(root: Path, host: str, module=recreate):
    def compiler(_root, selected_host, _pins, _members, identities):
        expected = proofs(selected_host)[1]["tool_versions"]
        return {"status": "validated" if identities == expected else "rejected",
                "host": selected_host, "errors": [] if identities == expected else ["wrong selected product identities"]}
    bindings = {f"bin/{name}": {"member_sha256": value} for name, value in proofs(host)[1]["entrypoint_sha256"].items()}
    with mock.patch.object(module.subprocess, "run", return_value=subprocess.CompletedProcess([], 0)), mock.patch.object(module, "_capture_seed_archive_members", return_value=([], bindings)), mock.patch.object(module, "_capture_seed_compiler_identity", side_effect=compiler):
        return module.capture_validated_seed_lineage(root, host)


class ReceiptBindingTests(unittest.TestCase):
    def test_exact_records_cover_both_hosts_and_shared_source(self):
        pins = cohort()
        self.assertEqual(host_ledger.pinned_hosts(pins), sorted([MAC, LINUX]))
        for host in (MAC, LINUX):
            record = host_ledger.make_host_record(pins, host, *proof_bytes(host))
            self.assertEqual(len(record["payloads"]), 9)
            self.assertEqual(record["receipt_sha256"], digest(proof_bytes(host)[0]))

    def test_foreign_archive_only_has_no_native_receipt(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp)
            with self.assertRaises(OSError):
                host_ledger.collect_host_records(seed, cohort(), MAC, *proof_bytes(MAC))

    def test_complete_collection_keeps_exact_foreign_proof_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp)
            write_proofs(seed, LINUX)
            records, payloads = host_ledger.collect_host_records(seed, cohort(), MAC, *proof_bytes(MAC))
            self.assertEqual(set(records), {MAC, LINUX})
            self.assertEqual(payloads[host_ledger.proof_paths(LINUX)[0]], proof_bytes(LINUX)[0])

    def test_foreign_native_record_cannot_be_rebound_to_new_archive_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp)
            write_proofs(seed, MAC)
            pins = cohort()
            key = next(key for key in pins if "/trustc-" in key and MAC in key)
            pins[key] = "f" * 64
            with self.assertRaisesRegex(ValueError, "rebound"):
                host_ledger.collect_host_records(seed, pins, LINUX, *proof_bytes(LINUX))

    def test_receipt_tuple_and_ddc_negatives(self):
        mutations = {
            "schema": "other", "source_commit": "d" * 40, "source_commit_date": "2026-07-13",
            "source_version": "1.99.0", "host": MAC, "self_host_proof": "pending",
            "ddc_verdict": "DIFFERENT", "ddc_seed_relation": "reproducibility-control",
            "ddc_seed_lineage": "stock", "ddc_seed_commit": "b" * 40,
            "ddc_build_driver": "ambient", "ddc_scope": "cross-target only",
            "pinned_seed_compiler_sha256": "bad", "ddc_seed_driver_sha256": "bad",
            "stage2_tree_sha256_ddc_seed": "f" * 64, "lineage_disjoint_anchor": "bad",
        }
        for key, value in mutations.items():
            receipt, surface = proofs(LINUX)
            receipt[key] = value
            text = "".join(f"{name}={item}\n" for name, item in receipt.items()) + f"compiler_file={'1' * 64} bin/trustc\n"
            with self.subTest(key=key), self.assertRaises(ValueError):
                host_ledger.make_host_record(cohort(), LINUX, text.encode(), json.dumps(surface).encode())

    def test_diverse_relation_requires_its_own_anchor(self):
        receipt, _ = proofs(LINUX)
        receipt.update(ddc_seed_relation="lineage-disjoint", ddc_seed_lineage="stock", lineage_disjoint_anchor=COMMIT)
        host_ledger.validate_receipt(receipt, cohort(), LINUX)
        receipt["lineage_disjoint_anchor"] = "none"
        with self.assertRaises(ValueError):
            host_ledger.validate_receipt(receipt, cohort(), LINUX)

    def test_native_surface_must_match_actual_archive_entrypoint_digests(self):
        record = host_ledger.make_host_record(cohort(), LINUX, *proof_bytes(LINUX))
        bindings = {f"bin/{name}": {"member_sha256": value} for name, value in record["entrypoint_sha256"].items()}
        host_ledger.check_entrypoint_bindings(record, bindings)
        for name in record["entrypoint_sha256"]:
            wrong = copy.deepcopy(bindings)
            wrong[f"bin/{name}"]["member_sha256"] = "f" * 64
            with self.subTest(name=name), self.assertRaises(ValueError):
                host_ledger.check_entrypoint_bindings(record, wrong)

    def test_surface_host_and_native_entrypoints_are_required(self):
        for key, value in (("host", MAC), ("source_version", "1.99.0"), ("entrypoint_sha256", {}), ("tree", {}), ("tool_versions", {"trustc": "inert"})):
            _, surface = proofs(LINUX)
            surface[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                host_ledger.make_host_record(cohort(), LINUX, proof_bytes(LINUX)[0], json.dumps(surface).encode())

    def test_duplicate_receipt_and_surface_fields_refused(self):
        receipt, surface = proof_bytes(LINUX)
        for bad_receipt, bad_surface in ((receipt + b"host=aarch64-unknown-linux-gnu\n", surface), (receipt, b'{"host":"a","host":"b"}')):
            with self.assertRaises(ValueError):
                host_ledger.make_host_record(cohort(), LINUX, bad_receipt, bad_surface)

    def test_missing_or_escaping_compared_file_refused(self):
        receipt, surface = proof_bytes(LINUX)
        prefix = receipt[:receipt.index(b"compiler_file=")]
        for row in (b"", b"compiler_file=" + b"1" * 64 + b" ../outside\n"):
            with self.assertRaises(ValueError):
                host_ledger.make_host_record(cohort(), LINUX, prefix + row, surface)

    def test_exact_retained_metadata_bound_and_one_byte_short(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp)
            write_proofs(seed, MAC)
            pins = cohort()
            total = sum(sum(map(len, proof_bytes(host))) + len(host_ledger.record_bytes(host_ledger.make_host_record(pins, host, *proof_bytes(host)))) for host in (MAC, LINUX))
            with mock.patch.object(host_ledger, "MAX_TOTAL_PROOF_BYTES", total):
                _, retained = host_ledger.collect_host_records(seed, pins, LINUX, *proof_bytes(LINUX))
                self.assertEqual(sum(map(len, retained.values())), total)
            with mock.patch.object(host_ledger, "MAX_TOTAL_PROOF_BYTES", total - 1), self.assertRaisesRegex(ValueError, "aggregate"):
                host_ledger.collect_host_records(seed, pins, LINUX, *proof_bytes(LINUX))

    def test_native_host_count_is_bounded(self):
        hosts = tuple(f"host{index}-unknown-linux-gnu" for index in range(host_ledger.MAX_HOSTS + 1))
        with self.assertRaisesRegex(ValueError, "host count"):
            host_ledger.pinned_hosts(cohort(hosts))

    def test_bound_excessive_receipt_before_decoding(self):
        with self.assertRaisesRegex(ValueError, "bounded"):
            host_ledger.parse_receipt(b"x" * (host_ledger.MAX_PROOF_BYTES + 1))

    def test_symlink_receipts_and_parent_escape_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            seed = Path(tmp)
            write_proofs(seed, LINUX)
            receipt = seed / host_ledger.proof_paths(LINUX)[0]
            target = seed / "copied-receipt"
            receipt.rename(target)
            receipt.symlink_to(target)
            with self.assertRaises(ValueError):
                host_ledger.read_proof(seed, host_ledger.proof_paths(LINUX)[0])
            receipt.unlink()
            target.rename(receipt)
            parent = seed / "host-proofs" / LINUX
            moved = seed / "moved"
            parent.rename(moved)
            parent.symlink_to(moved, target_is_directory=True)
            with self.assertRaises(ValueError):
                host_ledger.read_proof(seed, host_ledger.proof_paths(LINUX)[0])

    def test_incomplete_or_noncohort_host_inventory_refused(self):
        for changed in ("missing", "extra", "wrong-version"):
            pins = cohort()
            key = next(key for key in pins if "/trustc-" in key and LINUX in key)
            if changed == "missing":
                del pins[key]
            elif changed == "extra":
                pins[f"dist/{DATE}/ambient-0.10.0-trust-{LINUX}.tar.xz"] = "1" * 64
            else:
                pins[key.replace("0.10.0", "1.99.0")] = pins.pop(key)
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                host_ledger.pinned_hosts(pins)


class LedgerAdmissionTests(unittest.TestCase):
    def test_dual_host_admission_selects_own_native_products(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            for host in (MAC, LINUX):
                result = capture(root, host)
                self.assertEqual(result["status"], "validated", result["errors"])
                self.assertEqual(result["compiler"]["host"], host)
                self.assertEqual(result["authority"]["seed_ledger"]["host_records"]["selected_host"], host)
                # A ledger of mint records keeps the authority it had before the
                # fixed-point kind existed (and so its receipts): no validator
                # digest beside the helper's unless a record is that kind.
                self.assertEqual(set(result["authority"]["seed_ledger"]["host_records"]),
                                 {"helper_sha256", "selected_host", "records", "record_metadata_sha256"})

    def test_legacy_single_host_own_host_remains_valid(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root, (MAC,), legacy=True)
            self.assertEqual(capture(root, MAC)["status"], "validated")

    def test_a_legacy_single_host_ledger_never_admits_a_linux_host(self):
        # The single-host format carries no host record, so nothing in it says which
        # evidence admitted the seed: a Linux seed is admitted only through its own
        # host record (where a fixed point is graded below every release), even when
        # the legacy ledger names that host itself.
        for host in sorted(recreate.LINUX_SEED_HOSTS):
            with self.subTest(host=host):
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    fixture(root, (host,), legacy=True)
                    self.assertNotIn("hosts", tomllib.loads(
                        (root / "bootstrap/trust-stage0/seed-ledger.toml").read_text())["release"])
                    result = capture(root, host)
                    self.assertEqual(result["status"], "rejected")
                    self.assertIn(
                        "seed admission ledger is in the single-host format (no [release.hosts]), which admits "
                        f"no Linux host: {host}'s seed is admitted only through its own "
                        f'[release.hosts."{host}"] host record (docs/PLAN.md PKG-S6)', result["errors"])
                    self.assertNotIn("host_records", result["authority"]["seed_ledger"])
                    built = {"status": "trust_from_trust",
                             "validated_seed": {**result, "materialization_status": "fresh-from-validated-archives"}}
                    self.assertEqual(recreate._classify_receipt_status("immutable_release", built), "rejected")
                # Not vacuous: the same cohort, ledgered with its own host record, is admitted.
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    fixture(root, (host,))
                    self.assertEqual(capture(root, host)["status"], "validated")

    def test_legacy_mac_authority_cannot_be_borrowed_for_linux(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root, legacy=True)
            result = capture(root, LINUX)
            self.assertEqual(result["status"], "rejected")
            self.assertTrue(any("host_triple" in error for error in result["errors"]))

    def test_unknown_empty_and_ambiguous_host_tables_refused(self):
        mutations = {
            "missing": lambda d: d["release"]["hosts"].pop(LINUX),
            "empty": lambda d: d["release"].update(hosts={}),
            "wrong-schema": lambda d: d["release"]["hosts"][LINUX].update(schema="other"),
            "borrow-mac": lambda d: d["release"]["hosts"].update({LINUX: copy.deepcopy(d["release"]["hosts"][MAC])}),
            "global-host": lambda d: d["release"].update(host_triple=LINUX),
            "global-mint": lambda d: d["release"].update(mint={"self_host_proof": "pass"}),
            "extra-fields": lambda d: d["release"]["hosts"][LINUX].update(unsupported="yes"),
        }
        for name, mutation in mutations.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                fixture(root)
                rewrite_ledger(root, mutation)
                self.assertEqual(capture(root, LINUX)["status"], "rejected")

    def test_proof_bytes_and_archive_mutations_change_authority_and_refuse(self):
        for selected in (MAC, LINUX):
            for changed_host in (MAC, LINUX):
                for kind in ("receipt", "surface", "archive", "metadata"):
                    with self.subTest(selected=selected, changed_host=changed_host, kind=kind), tempfile.TemporaryDirectory() as tmp:
                        root = Path(tmp)
                        pins, _ = fixture(root)
                        before = capture(root, selected)
                        seed = root / "bootstrap/trust-stage0"
                        if kind == "archive":
                            relative = next(key for key in pins if "/trustc-" in key and changed_host in key)
                        elif kind == "metadata":
                            relative = host_ledger.record_path(changed_host)
                        else:
                            relative = host_ledger.proof_paths(changed_host)[kind == "surface"]
                        path = seed / relative
                        path.write_bytes(path.read_bytes() + b" ")
                        after = capture(root, selected)
                        self.assertEqual(after["status"], "validated" if kind == "metadata" else "rejected")
                        self.assertNotEqual(before["authority_sha256"], after["authority_sha256"])

    def test_public_signature_refusal_remains_mandatory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            def public(document):
                document.update(scope="public", promotion_decision="promote", signatures=["plausible-but-unverified-signature"])
                document["release"]["visibility"] = "public"
            rewrite_ledger(root, public)
            result = capture(root, LINUX)
            self.assertEqual(result["status"], "rejected")
            self.assertIn("public seed promotion lacks an implemented pinned-key cryptographic verifier", result["errors"])

    def test_single_host_compatibility_fields_must_agree(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root, (MAC,))
            rewrite_ledger(root, lambda d: d["release"]["mint"].update(ddc_seed_commit="f" * 40))
            self.assertEqual(capture(root, MAC)["status"], "rejected")

    def test_lineage_anchor_selects_native_host_without_other_host_fallback(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            with mock.patch.object(support, "detected_host", return_value=LINUX):
                self.assertEqual(support.committed_seed_mint(root), {key: proofs(LINUX)[0][key] for key in host_ledger.MINT_FIELDS})
            with mock.patch.object(support, "detected_host", return_value="x86_64-unknown-linux-gnu"), self.assertRaises(support.WorkflowError):
                support.committed_seed_mint(root)


class ProducerIntegrationTests(unittest.TestCase):
    def test_merged_repin_captures_all_host_bytes_before_commit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pins, _ = fixture(root)
            prepared = root / "prepared"
            seed = prepared / "bootstrap/trust-stage0"
            for relative in pins:
                if relative.startswith("dist/"):
                    path = seed / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(relative.encode())
            (seed / f"dist/{DATE}/channel-rust-trust.toml").write_bytes(b"manifest")
            write_proofs(seed, MAC)
            (prepared / "src-stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n" + stage0_text(pins))
            (root / "src/stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n")
            receipt, surface = root / "native-receipt", root / "native-surface"
            receipt.write_bytes(proof_bytes(LINUX)[0])
            surface.write_bytes(proof_bytes(LINUX)[1])
            captured = {}
            def commit(_root, _parent, _branch, writes, *_rest):
                captured.update(writes)
                return "e" * 40
            with mock.patch.object(support, "repository_state", return_value={"commit": COMMIT, "commit_date": DATE}), mock.patch.object(support, "read_stage0_pin", return_value={"compiler_git_commit_hash": "b" * 40, "compiler_date": "2026-07-13"}), mock.patch.object(support, "check_repin_date"), mock.patch.object(support, "repin_files", return_value=({}, [])), mock.patch.object(support, "create_repin_commit", side_effect=commit), mock.patch.object(support.subprocess, "run", side_effect=AssertionError("no process may execute")):
                result = support.repin(root, prepared, COMMIT, LINUX, "seed/inert", "Inert <inert@example.invalid>", receipt, surface, root)
            self.assertEqual(result[0], "e" * 40)
            ledger = tomllib.loads(captured["bootstrap/trust-stage0/seed-ledger.toml"].decode())
            self.assertEqual(set(ledger["release"]["hosts"]), {MAC, LINUX})
            self.assertNotIn("host_triple", ledger["release"])
            for host in (MAC, LINUX):
                record = ledger["release"]["hosts"][host]
                for relative, expected in zip(host_ledger.proof_paths(host), proof_bytes(host)):
                    self.assertEqual(captured["bootstrap/trust-stage0/" + relative], expected)
                self.assertEqual(record["receipt_sha256"], digest(proof_bytes(host)[0]))
            self.assertNotEqual(receipt.read_bytes(), proof_bytes(LINUX)[0])

    def test_repin_refuses_wrong_previous_pin_before_creating_any_commit(self):
        for field, wrong in (("compiler_git_commit_hash", "f" * 40), ("compiler_date", "2026-07-12")):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                pins, _ = fixture(root)
                (root / "src-stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n" + stage0_text(pins))
                (root / "src/stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n")
                seed = root / "bootstrap/trust-stage0"
                receipt, surface = (seed / relative for relative in host_ledger.proof_paths(LINUX))
                previous = {"compiler_git_commit_hash": "b" * 40, "compiler_date": "2026-07-13"}
                previous[field] = wrong
                with mock.patch.object(support, "repository_state", return_value={"commit": COMMIT, "commit_date": DATE}), mock.patch.object(support, "read_stage0_pin", return_value=previous), mock.patch.object(support, "check_repin_date"), mock.patch.object(support, "create_repin_commit") as commit, mock.patch.object(support.subprocess, "run", side_effect=AssertionError("no process may execute")):
                    with self.assertRaisesRegex(support.WorkflowError, "previous src/stage0"):
                        support.repin(root, root, COMMIT, LINUX, "seed/inert", "Inert <inert@example.invalid>", receipt, surface, root)
                commit.assert_not_called()


# sha256 of render_seed_ledger's text for these fixtures (the hosts of the cohort,
# and whether host records are passed) as the renderer of 43bf99fe41 wrote it,
# before title_hosts and mint_switch_line existed. With both off, not one byte moves.
PRE_KEYWORD_LEDGER_SHA256 = {
    ((MAC,), False): "55130f02518fef9d9d75784e374517621830be5e65d8cbedcf34936104558e3e",
    ((MAC,), True): "34df534e647efa491cf4c580a294b220ff0c7ca844d8a8fa10766140f11e6712",
    ((MAC, LINUX), False): "3e016f5679a5345c49c4a745f10a51f1941ccf00c2150de06a7c6f2ec3547af9",
    ((MAC, LINUX), True): "a1bac06b973fb2b02cef03a27ba8eddc85bb01ba815e812c8a68181df40953e0",
}
MINT_COMMENT = [
    "# Each host binds its own completed native mint receipt, installed",
    "# surface, and exact archives. Foreign cross artifacts alone do not admit a host.",
]


def disclosure() -> dict[str, str]:
    """A root_disclosure table with the literals scripts/seed_fixed_point.py admits."""
    fp = host_ledger.fixed_point_module()
    return {**dict(fp.DISCLOSURE), "stock_built_ancestor": fp.STOCK_ANCESTOR,
            "stock_built_ancestor_commit": fp.STOCK_ANCESTOR_COMMIT, "root_commit": fp.ROOT_COMMIT,
            "producer_stage0_commit": fp.CHAIN_COMMITS[-1], "cross_check_stage0_commit": fp.CHAIN_COMMITS[2]}


def fixed_point_table(record: dict) -> dict:
    """A host record shaped as the fixed-point kind tables it (render-only: the
    renderer and the ledger readers here read tables, they do not admit them)."""
    table = {key: value for key, value in record.items() if key not in ("mint", "pinned_seed_date")}
    table.update(schema=host_ledger.FIXED_POINT_SCHEMA, admission_kind=host_ledger.fixed_point_module().KIND,
                 receipt_path=f"host-proofs/{record['host']}/SEED-FIXED-POINT", evidence_sha256="e" * 64,
                 root_disclosure=disclosure())
    return table


def render(hosts, records=None, **keywords) -> str:
    pins = cohort(hosts)
    receipt, surface = proofs(hosts[0])
    text, _ = support.render_seed_ledger(CURRENT, pins, stage0_text(pins), hosts[0], surface["tool_versions"],
                                         receipt, **({} if records is None else {"host_records": records}),
                                         **keywords)
    return text


class LedgerRenderingTests(unittest.TestCase):
    def test_both_keywords_off_keep_the_pre_change_text(self):
        for (hosts, with_records), expected in PRE_KEYWORD_LEDGER_SHA256.items():
            records = ({host: host_ledger.make_host_record(cohort(hosts), host, *proof_bytes(host)) for host in hosts}
                       if with_records else None)
            for keywords in ({}, {"title_hosts": False, "mint_switch_line": False}):
                with self.subTest(hosts=hosts, records=with_records, keywords=keywords):
                    self.assertEqual(digest(render(hosts, records, **keywords).encode()), expected)

    def test_the_committed_darwin_ledger_renders_byte_for_byte(self):
        # The real pin: the committed ledger is what this renderer makes of its own
        # inputs, with the new keywords off (and so it was before they existed).
        seed = ROOT / "bootstrap/trust-stage0"
        ledger = (seed / "seed-ledger.toml").read_text()
        text = (ROOT / "src/stage0").read_text()
        stage0 = {}
        for line in text.splitlines():
            key, separator, value = line.strip().partition("=")
            if separator and not key.startswith("#"):
                stage0[key] = value
        parsed = tomllib.loads(ledger)
        records = {host: json.loads((seed / host_ledger.record_path(host)).read_text())
                   for host in parsed["release"]["hosts"]}
        # Darwin's table, by name: whatever other host the ledger records, this
        # pin's Darwin record is its mint record, and it renders the ledger.
        self.assertEqual(records[MAC]["schema"], host_ledger.SCHEMA, "this pin's Darwin record is a mint record")
        receipt = support.parse_receipt((seed / host_ledger.proof_paths(MAC)[0]).read_text())
        if all(record["schema"] == host_ledger.SCHEMA for record in records.values()):
            # No record of another kind: with the new keywords off, not one byte moves.
            variants = ({}, {"title_hosts": False, "mint_switch_line": False})
        else:
            # A ledger that also records another kind (a Linux fixed point) is what
            # the re-pin renders with the keywords its own text shows.
            variants = ({"title_hosts": parsed["release"]["title"].endswith(f"{', '.join(sorted(records))})"),
                         "mint_switch_line": "aterm_seed_pin_switch" in parsed},)
        for keywords in variants:
            with self.subTest(keywords=keywords):
                rendered, _ = support.render_seed_ledger(ledger, stage0, text, MAC,
                                                         dict(records[MAC]["reported_product_identities"]), receipt,
                                                         host_records=records, **keywords)
                self.assertEqual(rendered, ledger)

    def test_a_fixed_point_record_changes_the_comment_and_the_title_can_name_every_host(self):
        pins = cohort()
        records = {MAC: host_ledger.make_host_record(pins, MAC, *proof_bytes(MAC)),
                   LINUX: fixed_point_table(host_ledger.make_host_record(pins, LINUX, *proof_bytes(LINUX)))}
        text = render((MAC, LINUX), records)
        lines = text.splitlines()
        for line in MINT_COMMENT:
            self.assertNotIn(line, lines)
        position = lines.index(support.NON_MINT_HOSTS_COMMENT[0])
        self.assertEqual(lines[position:position + len(support.NON_MINT_HOSTS_COMMENT)],
                         list(support.NON_MINT_HOSTS_COMMENT))
        for words in ("no mint", "no pinned predecessor", "no diverse double"):
            self.assertIn(words, " ".join(support.NON_MINT_HOSTS_COMMENT).replace("\n", " "))
        title = f"Trust stage0 seed {DATE} ({VERSION}-trust, "
        self.assertEqual(tomllib.loads(text)["release"]["title"], title + f"{MAC})")
        named = tomllib.loads(render((MAC, LINUX), records, title_hosts=True))
        self.assertEqual(named["release"]["title"], title + f"{MAC}, {LINUX})")
        self.assertEqual(named["release"]["hosts"][LINUX]["root_disclosure"], disclosure())
        # Every record a mint record: today's comment, whatever the title says.
        mints = {host: host_ledger.make_host_record(pins, host, *proof_bytes(host)) for host in (MAC, LINUX)}
        minted = render((MAC, LINUX), mints, title_hosts=True).splitlines()
        self.assertEqual(minted[minted.index(MINT_COMMENT[0]):minted.index(MINT_COMMENT[0]) + 2], MINT_COMMENT)
        self.assertNotIn(support.NON_MINT_HOSTS_COMMENT[0], minted)

    def test_the_mint_switch_line_is_text_for_aterm_and_no_table(self):
        pins = cohort()
        records = {MAC: host_ledger.make_host_record(pins, MAC, *proof_bytes(MAC)),
                   LINUX: fixed_point_table(host_ledger.make_host_record(pins, LINUX, *proof_bytes(LINUX)))}
        without = render((MAC, LINUX), records)
        self.assertEqual([line for line in without.splitlines() if line.startswith("[release.mint]")], [])
        text = render((MAC, LINUX), records, title_hosts=True, mint_switch_line=True)
        lines = text.splitlines()
        # Exactly one line aterm's lineage_switch.rs matches, top-level and before [release].
        switch = [number for number, line in enumerate(lines) if line.startswith("[release.mint]")]
        self.assertEqual(len(switch), 1)
        self.assertLess(switch[0], lines.index("[release]"))
        self.assertIn("lineage_switch.rs", "\n".join(lines[:switch[0]]))
        parsed = tomllib.loads(text)
        self.assertNotIn("mint", parsed["release"])
        self.assertTrue(parsed["aterm_seed_pin_switch"].startswith("[release.mint]"))
        for host in (MAC, LINUX):
            self.assertIs(host_ledger.select_host_record(parsed["release"], host), parsed["release"]["hosts"][host])
        # Without the line the text is the same but for it (and the blank line after it).
        plain = render((MAC, LINUX), records, title_hosts=True)
        self.assertEqual(plain.count("\n[release]\n"), 1)
        self.assertEqual(text, plain.replace("\n[release]\n",
                                             "\n" + "\n".join(support.MINT_SWITCH_LINES) + "\n\n[release]\n"))
        # A ledger that keeps its [release.mint] table (one host) gets no second line.
        one = {MAC: host_ledger.make_host_record(cohort((MAC,)), MAC, *proof_bytes(MAC))}
        with self.assertRaisesRegex(support.WorkflowError, r"already has a \[release.mint\] table"):
            render((MAC,), one, mint_switch_line=True)
        with self.assertRaisesRegex(support.WorkflowError, r"already has a \[release.mint\] table"):
            render((MAC,), mint_switch_line=True)


class RecordedHostTests(unittest.TestCase):
    def test_a_cut_names_every_recorded_host_it_drops(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            self.assertEqual(set(support.committed_host_records(root)), {MAC, LINUX})
            with self.assertRaisesRegex(support.WorkflowError,
                                        f"this re-pin would drop {LINUX}: .* pass --drop-host {LINUX}"):
                support.recorded_hosts(root, MAC, [])
            self.assertEqual(support.recorded_hosts(root, MAC, [LINUX]), [LINUX])
            self.assertEqual(support.recorded_hosts(root, LINUX, [MAC]), [MAC])
            for drops, message in (
                ([LINUX, LINUX], "is given more than once"),
                (["x86_64-unknown-linux-gnu"], "names a host the committed seed ledger does not record"),
                ([MAC, LINUX], f"--drop-host {MAC} names a host this cut keeps"),
                (["not a triple"], "host triple is not canonical"),
            ):
                with self.subTest(drops=drops), self.assertRaisesRegex(support.WorkflowError, message):
                    support.recorded_hosts(root, MAC, drops)
            # The CLI: refused (exit 1, the reason on stderr), then accepted when typed.
            run = lambda *extra: subprocess.run(
                [sys.executable, "-I", "-S", "-B", str(ROOT / "scripts/mint_seed_support.py"), "recorded-hosts",
                 "--root", str(root), "--host", MAC, *extra], capture_output=True, text=True, timeout=60)
            refused = run()
            self.assertEqual(refused.returncode, 1)
            self.assertIn(f"would drop {LINUX}", refused.stderr)
            typed = run("--drop-host", LINUX)
            self.assertEqual((typed.returncode, typed.stdout.strip()),
                             (0, f"re-pin drops recorded host(s) {LINUX} (typed --drop-host)"))

    def test_a_legacy_single_host_ledger_records_its_host_triple(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root, (MAC,), legacy=True)
            self.assertEqual(support.committed_host_records(root), {MAC: {}})
            self.assertEqual(support.recorded_hosts(root, MAC, []), [])
            with self.assertRaisesRegex(support.WorkflowError, f"would drop {MAC}"):
                support.recorded_hosts(root, LINUX, [])
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(support.committed_host_records(Path(tmp)), {})

    def test_a_host_whose_record_discloses_an_unpinned_root_cannot_be_cut_by_the_mint(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            rewrite_ledger(root, lambda d: d["release"]["hosts"][LINUX].update(root_disclosure=disclosure()))
            with self.assertRaisesRegex(support.WorkflowError, f"{LINUX}'s committed host record carries "
                                        "root_disclosure"):
                support.recorded_hosts(root, LINUX, [MAC])
            # A cut of the other host drops it only when told to.
            with self.assertRaisesRegex(support.WorkflowError, f"would drop {LINUX}"):
                support.recorded_hosts(root, MAC, [])
            self.assertEqual(support.recorded_hosts(root, MAC, [LINUX]), [LINUX])

    def test_a_ledger_that_does_not_say_its_hosts_is_refused_not_read_as_recording_none(self):
        # Only an absent ledger records no host. One that is there and does not say
        # which hosts it records would otherwise let a cut drop what it holds.
        head = 'scope = "internal"\npromotion_decision = "admit-internal"\n'
        for label, text, message in (
            ("an empty file", "", r"has no \[release\] table"),
            ("no [release] table", head, r"has no \[release\] table"),
            ("[release] that is not a table", head + 'release = "x"\n', r"has no \[release\] table"),
            ("an empty [release.hosts] beside a host_triple",
             head + f'[release]\nhost_triple = "{MAC}"\n[release.hosts]\n', r"\[release.hosts\] is empty"),
            ("[release.hosts] that is not a table", head + '[release]\nhosts = "x"\n',
             r"\[release.hosts\] is not a table of host tables"),
            ("a host entry that is not a table", head + '[release.hosts]\nx = 1\n',
             r"\[release.hosts\] is not a table of host tables"),
            ("a legacy ledger without a host_triple", head + '[release]\nrepo = "fixture/trust"\n',
             "its host_triple is None, not a host triple"),
            ("a legacy host_triple that is not a string", head + "[release]\nhost_triple = 7\n",
             "its host_triple is 7, not a host triple"),
            ("an empty legacy host_triple", head + '[release]\nhost_triple = ""\n',
             "its host_triple is '', not a host triple"),
        ):
            with self.subTest(label), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                ledger = root / "bootstrap/trust-stage0/seed-ledger.toml"
                ledger.parent.mkdir(parents=True)
                ledger.write_text(text)
                with self.assertRaisesRegex(support.WorkflowError, message) as refused:
                    support.committed_host_records(root)
                self.assertIn("so which hosts it records is unknown. Nothing was built or changed",
                              str(refused.exception))
                for host in (MAC, LINUX):
                    with self.assertRaisesRegex(support.WorkflowError, message):
                        support.recorded_hosts(root, host, [])

    def test_a_successor_keeps_the_committed_disclosure_table_exactly(self):
        table = disclosure()
        committed = {LINUX: {"schema": host_ledger.FIXED_POINT_SCHEMA, "host": LINUX,
                             "admission_kind": host_ledger.fixed_point_module().KIND, "root_disclosure": table}}
        support.check_disclosed_successors(committed, {LINUX: {"root_disclosure": dict(table)}})
        for key, value in (("root", "pinned"), ("predecessor_pin", "1" * 40), ("root_commit", "2" * 40)):
            with self.subTest(key=key), self.assertRaisesRegex(
                    support.WorkflowError, f"{LINUX}'s committed host record carries root_disclosure"):
                support.check_disclosed_successors(committed, {LINUX: {"root_disclosure": {**table, key: value}}})
        with self.assertRaisesRegex(support.WorkflowError, "does not carry the same table"):
            support.check_disclosed_successors(committed, {LINUX: {"root_disclosure": {**table, "extra": "x"}}})
        with self.assertRaisesRegex(support.WorkflowError, "does not carry the same table"):
            support.check_disclosed_successors(committed, {LINUX: {}})

    def test_a_fixed_point_record_without_its_table_has_no_successor(self):
        # The kind is the record's schema or admission_kind as much as its table: a
        # committed fixed point that lost the table is refused, not read as a mint.
        self.assertEqual(support.FIXED_POINT_HOST_SCHEMA, host_ledger.FIXED_POINT_SCHEMA)
        self.assertEqual(support.FIXED_POINT_ADMISSION_KIND, host_ledger.fixed_point_module().KIND)
        mint_successor = {LINUX: {"schema": host_ledger.SCHEMA, "host": LINUX, "mint": {}}}
        for label, committed in (
            ("by its schema", {"schema": host_ledger.FIXED_POINT_SCHEMA, "host": LINUX}),
            ("by its admission kind", {"schema": host_ledger.SCHEMA, "host": LINUX,
                                       "admission_kind": host_ledger.fixed_point_module().KIND}),
            ("with a disclosure that is not a table", {"schema": host_ledger.FIXED_POINT_SCHEMA, "host": LINUX,
                                                       "root_disclosure": "unpinned-host-chain"}),
        ):
            for successor in (mint_successor, {LINUX: {}}):
                with self.subTest(label, successor=successor), self.assertRaisesRegex(
                        support.WorkflowError, f"{LINUX}'s committed host record is the fixed-point kind .* "
                        "carries no root_disclosure table"):
                    support.check_disclosed_successors({LINUX: committed}, successor)
        # A mint record, and a legacy host with no table, have no disclosure to keep.
        support.check_disclosed_successors({LINUX: {"schema": host_ledger.SCHEMA, "host": LINUX}}, mint_successor)
        support.check_disclosed_successors({LINUX: {}}, mint_successor)
        # And the early check refuses a cut of such a host from the committed ledger.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            rewrite_ledger(root, lambda d: d["release"]["hosts"][LINUX].update(
                schema=host_ledger.FIXED_POINT_SCHEMA))
            with self.assertRaisesRegex(support.WorkflowError, "is the fixed-point kind"):
                support.recorded_hosts(root, LINUX, [MAC])


class RepinRecordedHostTests(unittest.TestCase):
    def prepared(self, root: Path, hosts, foreign=()) -> Path:
        prepared = root / "prepared"
        seed = prepared / "bootstrap/trust-stage0"
        pins = cohort(hosts)
        for relative in pins:
            if relative.startswith("dist/"):
                path = seed / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(relative.encode())
        (seed / f"dist/{DATE}/channel-rust-trust.toml").write_bytes(b"manifest")
        for host in foreign:
            write_proofs(seed, host)
        (prepared / "src-stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n" + stage0_text(pins))
        (root / "src/stage0").write_text(support.STAGE0_GENERATED_MARKER + "\n")
        return prepared

    def repin(self, root: Path, prepared: Path, native: str, **keywords):
        receipt, surface = root / "native-receipt", root / "native-surface"
        receipt.write_bytes(proof_bytes(native)[0])
        surface.write_bytes(proof_bytes(native)[1])
        captured = {}

        def commit(_root, _parent, _branch, writes, _removals, message, *_rest):
            captured.update(writes)
            captured["message"] = message
            return "e" * 40
        with mock.patch.object(support, "repository_state", return_value={"commit": COMMIT, "commit_date": DATE}), \
                mock.patch.object(support, "read_stage0_pin", return_value={"compiler_git_commit_hash": "b" * 40,
                                                                            "compiler_date": "2026-07-13"}), \
                mock.patch.object(support, "check_repin_date"), \
                mock.patch.object(support, "repin_files", return_value=({}, [])), \
                mock.patch.object(support, "create_repin_commit", side_effect=commit) as created, \
                mock.patch.object(support.subprocess, "run", side_effect=AssertionError("no process may execute")):
            try:
                support.repin(root, prepared, COMMIT, native, "seed/inert", "Inert <inert@example.invalid>",
                              receipt, surface, root, **keywords)
            finally:
                self.calls = created.call_count
        return captured

    def test_repin_drops_a_recorded_host_only_when_told(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            prepared = self.prepared(root, (MAC,))
            with self.assertRaisesRegex(support.WorkflowError, f"this re-pin would drop {LINUX}"):
                self.repin(root, prepared, MAC)
            self.assertEqual(self.calls, 0)
            captured = self.repin(root, prepared, MAC, drop_hosts=[LINUX])
            self.assertEqual(self.calls, 1)
            ledger = tomllib.loads(captured["bootstrap/trust-stage0/seed-ledger.toml"].decode())
            self.assertEqual(set(ledger["release"]["hosts"]), {MAC})
            self.assertIn(f"* dropped recorded host(s), by a typed --drop-host: {LINUX}", captured["message"])
            for drops, message in (([MAC], "names a host this cut keeps"),
                                   (["x86_64-unknown-linux-gnu"], "does not record")):
                with self.subTest(drops=drops), self.assertRaisesRegex(support.WorkflowError, message):
                    self.repin(root, prepared, MAC, drop_hosts=drops)
                self.assertEqual(self.calls, 0)
            # A cut that keeps every recorded host says nothing of drops.
            kept = self.repin(root, self.prepared(root, (MAC, LINUX), foreign=(LINUX,)), MAC)
            self.assertNotIn("dropped recorded host", kept["message"])

    def test_the_repin_command_line_passes_each_drop_host_to_the_repin(self):
        # The mint script passes its --drop-host values to the helper's command line;
        # that command line must hand every one of them, in order, to repin().
        argv = ["repin", "--root", "r", "--prepared", "p", "--commit", COMMIT, "--host", MAC, "--branch", "b",
                "--identity", "Inert <inert@example.invalid>", "--receipt", "rc", "--surface", "s", "--work", "w"]
        for drops in ([], [LINUX], [LINUX, "x86_64-unknown-linux-gnu"]):
            with self.subTest(drops=drops), \
                    mock.patch.object(support, "repin", return_value=("c" * 40, "t", "d" * 64)) as repin, \
                    mock.patch("sys.stdout", io.StringIO()):
                self.assertEqual(support.main([*argv, *(f"--drop-host={host}" for host in drops)]), 0)
                repin.assert_called_once()
                self.assertEqual(list(repin.call_args.kwargs["drop_hosts"]), drops)

    def test_repin_refuses_a_successor_that_loses_the_disclosure(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            rewrite_ledger(root, lambda d: d["release"]["hosts"][LINUX].update(root_disclosure=disclosure()))
            for native, foreign in ((MAC, LINUX), (LINUX, MAC)):
                with self.subTest(native=native):
                    prepared = self.prepared(root, (MAC, LINUX), foreign=(foreign,))
                    with self.assertRaisesRegex(support.WorkflowError,
                                                f"{LINUX}'s committed host record carries root_disclosure"):
                        self.repin(root, prepared, native)
                    self.assertEqual(self.calls, 0)
                    shutil.rmtree(prepared)
            # Dropping it instead is a typed choice, and is then carried out.
            captured = self.repin(root, self.prepared(root, (MAC,)), MAC, drop_hosts=[LINUX])
            self.assertEqual(set(tomllib.loads(captured["bootstrap/trust-stage0/seed-ledger.toml"].decode())
                                 ["release"]["hosts"]), {MAC})


class FixedPointAncestryTests(unittest.TestCase):
    def test_pin_ancestry_names_a_fixed_points_producers(self):
        fp = host_ledger.fixed_point_module()
        producers = {fp.ROOT_COMMIT, fp.CHAIN_COMMITS[-1], fp.CHAIN_COMMITS[2]}
        self.assertEqual(support.FIXED_POINT_PRODUCER_FIELDS,
                         tuple(key for key in fp.DISCLOSED if key in support.FIXED_POINT_PRODUCER_FIELDS))
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixture(root)
            quiet = subprocess.CompletedProcess([], 0, stdout="", stderr="")
            with mock.patch.object(support, "git_command", return_value=quiet), \
                    mock.patch.object(support, "committed_seed_mint", return_value={}):
                before = support.pin_ancestry(root)
                self.assertEqual(before, {"b" * 40})
                rewrite_ledger(root, lambda d: d["release"]["hosts"][LINUX].update(root_disclosure=disclosure()))
                self.assertEqual(support.pin_ancestry(root), {"b" * 40} | producers)


class ManifestMergeTests(unittest.TestCase):
    def manifest(self, host):
        return {"date": DATE, "pkg": {"trust": {"version": VERSION + "-trust", "git_commit_hash": COMMIT},
            "trustc": {"version": VERSION + "-trust", "git_commit_hash": COMMIT, "target": {host: {"available": True, "xz_url": f"inert://{host}", "xz_hash": digest(host.encode())}}}}}

    def merge(self, new, old):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "manifest.toml"
            path.write_text(prepare.dump_toml(old))
            return prepare.merge_existing_manifest_targets(new, path)

    def test_identical_source_union_and_fresh_shared_target_order(self):
        new, old = self.manifest(LINUX), self.manifest(MAC)
        self.assertEqual(self.merge(new, old), 1)
        self.assertEqual(set(new["pkg"]["trustc"]["target"]), {MAC, LINUX})
        new, old = self.manifest(MAC), self.manifest(MAC)
        new["pkg"]["trustc"]["target"][MAC]["xz_hash"] = "f" * 64
        self.assertEqual(self.merge(new, old), 0)
        self.assertEqual(new["pkg"]["trustc"]["target"][MAC]["xz_hash"], "f" * 64)

    def test_missing_and_mismatched_release_identity_refused(self):
        for side in ("new", "old"):
            for field in ("date", "git_commit_hash", "version"):
                for missing in (False, True):
                    new, old = self.manifest(LINUX), self.manifest(MAC)
                    changed = new if side == "new" else old
                    table = changed if field == "date" else changed["pkg"]["trust"]
                    if missing:
                        del table[field]
                    else:
                        table[field] = "different"
                    with self.subTest(side=side, field=field, missing=missing), self.assertRaises(ValueError):
                        self.merge(new, old)

    def test_component_version_and_commit_mismatch_refused(self):
        for field in ("version", "git_commit_hash"):
            new, old = self.manifest(LINUX), self.manifest(MAC)
            old["pkg"]["trustc"][field] = "other"
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.merge(new, old)


if __name__ == "__main__":
    unittest.main()
