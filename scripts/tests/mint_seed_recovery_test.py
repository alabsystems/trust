#!/usr/bin/env python3
"""Retained-mint boundaries with inert files and a nonexecuting verifier seam."""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("mint_recovery_tests", ROOT / "scripts/mint_seed_recovery.py")
recovery = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(recovery)
REAL = recovery.load_support()
PRODUCER = REAL.stage_evidence_owner()
COMMIT = "a" * 40
HOST = "aarch64-apple-darwin"
VERSION = "0.2.0"


def put(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(value if isinstance(value, bytes) else value.encode())
    return path


def write(path, value):
    return put(path, json.dumps(value, indent=2) + "\n")


class Fixture:
    def __init__(self, base):
        base = base.resolve()
        self.base = base
        self.root = base / "product"
        self.evidence = base / "evidence"
        self.build = self.root / "build" / f"pack-mint-{VERSION}-{HOST}-{COMMIT[:12]}"
        self.stage = self.build / HOST / "stage2"
        self.work = self.root / "build/.mint-and-prove.fixture"
        self.cargo = self.work / "cargo-home"
        self.config = put(self.root / "bootstrap.toml", "[build]\nextended = true\n")
        self.marker = put(self.root / "source.txt", "frozen compiler input\n")
        self.lean_file = put(base / "lean/lib/lean/fixture", "inert Lean input\n")
        self.helper = put(base / "native/helper", "inert native helper, never executed\n")
        self.helper.chmod(0o755)
        self.oracle = base / "oracle"
        put(self.oracle / "bin/rustc", "inert oracle compiler\n")
        put(self.oracle / "lib/driver", "inert oracle driver\n")
        self.source = {"commit": COMMIT, "source_date_epoch": 1000, "commit_date": "2026-10-03"}
        attributes = dict(vars(REAL))
        attributes.update(repository_state=lambda root: self.source,
                          canonical_version=lambda root: VERSION,
                          configuration_closure=self.configuration,
                          clean_lean_inputs=self.lean)
        self.support = SimpleNamespace(**attributes)
        self.calls = []
        self.verdict = True
        self.owner = SimpleNamespace(capture_source_lineage=self.lineage,
                                     verify_stage_tool_provenance=self.verify)
        self.engine = {"commit": "e" * 40, "root": str(ROOT)}
        pin = ["compiler_git_commit_hash=" + "b" * 40, "compiler_date=2026-10-01",
               "compiler_version=0.1.0-trust", "dist_server=file://{trust-root}/bootstrap/trust-stage0",
               "artifacts_server=file://{trust-root}/bootstrap/trust-stage0/artifacts",
               "artifacts_with_llvm_assertions_server=file://{trust-root}/bootstrap/trust-stage0/artifacts-with-llvm-assertions",
               "compiler_channel_manifest_hash=" + "d" * 64, "compiler_dist_channel=trust",
               "git_merge_commit_email=trust@fixture.invalid", "min_stage0_rustc_version=1.100.0",
               "nightly_branch=main", "rustfmt_channel_manifest_hash=" + "d" * 64,
               "rustfmt_date=2026-10-01", "rustfmt_dist_channel=trust",
               "rustfmt_git_commit_hash=" + "b" * 40, "rustfmt_version=0.1.0-trust"]
        payloads = []
        for component in REAL.SEED_COMPONENTS:
            relative = f"bootstrap/trust-stage0/dist/2026-10-01/{component}.tar.xz"
            path = put(self.root / relative, "inert pinned " + component)
            h = recovery.digest(path)
            pin.append(f"dist/2026-10-01/{component}.tar.xz={h}")
            payloads.append({"path": relative, "actual_sha256": h, "pinned_sha256": h, "matches_pin": True})
        stage0 = put(self.root / "src/stage0", "\n".join(pin) + "\n")
        channel = put(self.root / "bootstrap/trust-stage0/channel.toml", "inert pinned channel")
        put(self.stage / "bin/trustc", "inert retained compiler")
        put(self.stage / "bin/targo", "inert retained frontend")
        producer = put(self.build / HOST / "stage3-tools-bin" / HOST / "targo", "inert retained frontend")
        compared = REAL.stage2_manifest(self.stage)
        self.ddc_dir = self.evidence / "ddc-equality-evidence"
        oracle = {"commit": "c" * 40, "host": HOST, "relation": "lineage-disjoint", "sysroot": str(self.oracle),
                  "compiler": "bin/rustc", "compiler_sha256": recovery.digest(self.oracle / "bin/rustc"),
                  "driver": "lib/driver", "driver_sha256": recovery.digest(self.oracle / "lib/driver")}
        for name, value in (("stage2-pinned-seed.json", compared), ("stage2-ddc-seed.json", compared),
                            ("ddc-seed.json", oracle), ("ddc-seed-post-build.json", oracle)):
            write(self.ddc_dir / name, value)
        self.ddc_observation = {"state": "actual_canonical_DDC_equality_observed", "source": COMMIT,
                                "stage2_tree_sha256": compared["sha256"], "oracle_commit": oracle["commit"],
                                "relation": oracle["relation"], "captured_manifests": [
                                    {"file": str(self.work / p.name), "sha256": recovery.digest(p)}
                                    for p in sorted(self.ddc_dir.iterdir())]}
        write(self.ddc_dir / "observation.json", self.ddc_observation)
        safe = {"schema": "trust-sanitized-path-v2", "profile": REAL.SANITIZED_PATH_PROFILE,
                "host": HOST, "python": str(self.helper), "admitted": {
                    name: REAL.sanitized_tool_identity(self.helper) for name in REAL.build_helper_names(HOST)}}
        self.safe_file = write(self.evidence / "safe-path-v3-initial.json", safe)
        env = {"CARGO_HOME": str(self.cargo), "CARGO_NET_OFFLINE": "true", "GIT_CONFIG_NOSYSTEM": "1",
               "GIT_CONFIG_GLOBAL": os.devnull, "RUSTUP_HOME": str(self.work / "environment-mint/rustup-home"),
               "SOURCE_DATE_EPOCH": "1000", **self.lean()["environment"]}
        lineage = self.lineage(self.root)
        lineage.update(pre_build_closure_sha256=lineage["closure_sha256"],
                       post_build_closure_sha256=lineage["closure_sha256"], stable_across_build=True)
        self.provenance = {"schema": "trust.stage-tool-provenance.v2", "status": "internal-release-ready", "errors": [],
                           "writer": "scripts/mint_and_prove_seed.sh", "stage": 2, "host": HOST,
                           "compiler": {"source_commit": COMMIT}, "source_lineage": lineage,
                           "tools": [{"name": "targo", "path": str((self.stage / "bin/targo").relative_to(self.root)),
                                      "sha256": recovery.digest(self.stage / "bin/targo"),
                                      "producer_path": str(producer.relative_to(self.root)), "producer_sha256": recovery.digest(producer)}],
                           "bootstrap_lineage": {"config_path": "bootstrap.toml", "mint_configuration": {
                               "host": HOST, "xpy_config_overrides": {"build.jobs": 12},
                               "configuration_closure": self.configuration(), "clean_lean_inputs": self.lean()},
                               "validated_seed": {"authority": {"pins": PRODUCER.parse_stage0_pins(self.root)[0], "payloads": payloads,
                                   "src_stage0": {"path": "src/stage0", "sha256": recovery.digest(stage0)},
                                   "channel_manifest": {"path": str(channel.relative_to(self.root)), "sha256": recovery.digest(channel)}}}},
                           "build_authority": {"cargo_environment": {"cargo_home": str(self.cargo)},
                               "declared_rustup_home": {"selected_local_path": env["RUSTUP_HOME"], "entries": [], "errors": []},
                               "clean_lean_inputs": self.lean(),
                               "declared_environment_sha256": {k: hashlib.sha256(v.encode()).hexdigest() for k, v in env.items()}}}
        self.save_provenance()
        write(self.evidence / "mint-result.json", {"source": COMMIT, "source_after": COMMIT, "exit": 1,
            "command": ["bash", str(self.root / "scripts/mint_and_prove_seed.sh"), "--host", HOST, "--jobs", "12",
                        "--ddc-seed", str(self.oracle), "--cargo-home", str(base / "immutable-cargo"),
                        "--clean-lean-lib", str(self.lean_file.parent)]})
        packages = []
        for i, component in enumerate(REAL.SEED_COMPONENTS):
            prefix = f"{component}-{VERSION}-trust{'' if component == 'trust-src' else '-'+HOST}.tar."
            gz = put(self.build / "dist" / (prefix + "gz"), "retained gz " + component)
            xz = put(self.build / "dist" / (prefix + "xz"), "retained xz " + component)
            packages.append(f'[pkg.p{i}.target."{HOST}"]\nurl="https://trust.invalid/{gz.name}"\nhash="{recovery.digest(gz)}"\nxz_url="https://trust.invalid/{xz.name}"\nxz_hash="{recovery.digest(xz)}"\n')
        put(self.build / "dist/channel-rust-trust.toml", "\n".join(packages))
        put(self.build / "dist/channel-rust-trust-date.txt", "2026-10-03")
        put(self.build / "dist/channel-rust-trust-git-commit-hash.txt", COMMIT)

    def configuration(self, *args):
        return {"fingerprint": recovery.digest(self.config), "files": ["bootstrap.toml"]}

    def lean(self, *args):
        return {"library_path": str(self.lean_file.parent), "fingerprint": recovery.digest(self.lean_file),
                "physical_installation": str(self.lean_file.parents[2]),
                "environment": {"CLEAN_OLEAN_PINNED_LEAN_LIB": str(self.lean_file.parent), "CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"}}

    def lineage(self, *args):
        value = recovery.digest(self.marker)
        return {"status": "immutable_release", "errors": [], "closure_sha256": value,
                "repositories": [{"path": ".", "head": COMMIT, "working_tree_snapshot_sha256": value}]}

    def save_provenance(self):
        captured = write(self.evidence / "canonical-stage-provenance-before-selfhost.json", self.provenance)
        put(self.stage / "tool-provenance.json", captured.read_bytes())
        write(self.evidence / "state.json", {"source": COMMIT,
              "canonical_stage_provenance": {"sha256": recovery.digest(captured)},
              "native_profile": {"source": COMMIT, "sha256": recovery.digest(self.safe_file)},
              "ddc": {"stage2_tree_sha256": self.ddc_observation["stage2_tree_sha256"],
                      "oracle_commit": "c" * 40, "relation": "lineage-disjoint"}})

    def inspect(self):
        return recovery.validate(self.root, self.build, self.evidence, support=self.support,
                                 owner=self.owner, engine=self.engine)

    def verify(self, root, host, stage, **kwargs):
        self.calls.append((root, host, stage, kwargs, dict(os.environ)))
        return self.verdict


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="retained-mint-inert-")
        self.addCleanup(temp.cleanup)
        self.f = Fixture(Path(temp.name))
        no_process = mock.patch.object(subprocess, "Popen", side_effect=AssertionError("inert controls cannot execute tools"))
        no_process.start()
        self.addCleanup(no_process.stop)

    def refuses(self, text):
        with self.assertRaisesRegex((recovery.RecoveryError, REAL.WorkflowError), text):
            self.f.inspect()
        self.assertFalse(self.f.work.exists())

    def test_inspect_records_phase_split_without_creating_operational_state(self):
        r = self.f.inspect()
        self.assertEqual(r["state"], "inspected")
        self.assertFalse(r["qualification"])
        self.assertFalse(r["strict_native_verifier_passed"])
        self.assertFalse(r["original_private_cargo_retained"])
        self.assertEqual(r["original_jobs"], 12)
        self.assertEqual(len(r["dist_sha256"]), 21)
        self.assertFalse(self.f.work.exists())
        self.assertEqual(self.f.calls, [])

    def test_prepare_restores_exact_bytes_and_delegates_full_strict_original_context(self):
        record = self.f.inspect()
        before = (self.f.stage / "tool-provenance.json").read_bytes()
        environment = dict(os.environ)
        r = recovery.prepare(record, support=self.f.support, owner=self.f.owner)
        self.assertEqual(dict(os.environ), environment)
        self.assertEqual(Path(r["path_manifest"]).read_bytes(), self.f.safe_file.read_bytes())
        for name in ("stage2-pinned-seed.json", "stage2-ddc-seed.json", "ddc-seed.json"):
            self.assertEqual((self.f.work / name).read_bytes(), (self.f.ddc_dir / name).read_bytes())
        self.assertEqual(r["ddc_seed"], str(self.f.oracle))
        self.assertTrue(r["strict_native_verifier_passed"])
        self.assertFalse(r["qualification"])
        self.assertFalse(self.f.cargo.exists())
        self.assertFalse((self.f.work / "mint-stage-observation.json").exists())
        self.assertEqual((self.f.stage / "tool-provenance.json").read_bytes(), before)
        root, host, stage, kwargs, env = self.f.calls[0]
        self.assertEqual((root, host, stage), (self.f.root, HOST, 2))
        self.assertTrue(kwargs["require_immutable_lineage"])
        self.assertTrue(kwargs["require_llvm_identity"])
        self.assertEqual(kwargs["mint_configuration"]["xpy_config_overrides"]["build.jobs"], 12)
        self.assertEqual(env["PATH"], str(self.f.work / "safe-bin"))
        self.assertEqual(env["CARGO_NET_OFFLINE"], "true")
        self.assertEqual(set((self.f.work / "safe-bin").iterdir()),
                         {self.f.work / "safe-bin" / n for n in REAL.build_helper_names(HOST)})

    def test_verifier_refusal_never_emits_prepared_or_final_authority(self):
        record = self.f.inspect()
        self.f.verdict = False
        with self.assertRaisesRegex(recovery.RecoveryError, "strict stage provenance verifier refused"):
            recovery.prepare(record, support=self.f.support, owner=self.f.owner)
        self.assertEqual(record["state"], "inspected")
        self.assertFalse(record["strict_native_verifier_passed"])
        self.assertFalse((self.f.build / "trust-seed-mint").exists())
        with self.assertRaisesRegex(recovery.RecoveryError, "WORK must be absent"):
            self.f.inspect()

    def test_duplicate_and_nonfinite_json_refuse(self):
        p = self.f.evidence / "mint-result.json"
        put(p, '{"exit":1,"exit":1}')
        self.refuses("duplicate JSON key")
        put(p, '{"exit":NaN}')
        self.refuses("nonfinite JSON")

    def test_terminal_success_or_foreign_source_cannot_authorize_recovery(self):
        p = self.f.evidence / "mint-result.json"
        original = recovery.document(p)
        for field, value, message in (("exit", 0, "terminal exit1"), ("exit", True, "terminal exit1"),
                                       ("source_after", "f" * 40, "source differs")):
            with self.subTest(field=field, value=value):
                write(p, {**original, field: value})
                self.refuses(message)

    def test_tampered_stage_capture_or_current_receipt_refuse(self):
        p = self.f.stage / "tool-provenance.json"
        put(p, p.read_bytes() + b" ")
        self.refuses("in-stage provenance changed")
        self.f.save_provenance()
        p = self.f.evidence / "canonical-stage-provenance-before-selfhost.json"
        put(p, p.read_bytes() + b" ")
        self.refuses("capture changed")

    def test_changed_source_config_lean_helper_and_tool_are_independent_refusals(self):
        for p, message in ((self.f.marker, "recursive source"), (self.f.config, "config closure"),
                           (self.f.lean_file, "Lean closure"), (self.f.helper, "native helper changed"),
                           (self.f.stage / "bin/targo", "stage tool/producer changed")):
            with self.subTest(path=p):
                original = p.read_bytes()
                put(p, original + b"tampered")
                self.refuses(message)
                put(p, original)
                if p == self.f.helper:
                    # Restoring bytes changes metadata too: restore the fixture's
                    # genuinely saved identity before the next independent case.
                    s = recovery.document(self.f.safe_file)
                    s["admitted"] = {n: REAL.sanitized_tool_identity(p) for n in REAL.build_helper_names(HOST)}
                    write(self.f.safe_file, s)
                    self.f.save_provenance()

    def test_original_seed_missing_tampered_or_duplicated_refuses(self):
        payload = self.f.provenance["bootstrap_lineage"]["validated_seed"]["authority"]["payloads"][0]
        p = self.f.root / payload["path"]
        put(p, "tampered archive")
        self.refuses("original seed archive changed")
        p.unlink()
        with self.assertRaises(OSError):
            self.f.inspect()

    def test_ddc_missing_tampered_or_different_canonical_records_refuse(self):
        p = self.f.ddc_dir / "stage2-ddc-seed.json"
        original = p.read_bytes()
        put(p, original + b" ")
        self.refuses("DDC evidence changed")
        put(p, original)
        p.unlink()
        with self.assertRaises(OSError):
            self.f.inspect()

    def test_changed_compared_entry_or_oracle_bytes_refuse(self):
        p = self.f.stage / "bin/trustc"
        original = p.read_bytes()
        put(p, "different compiler")
        self.refuses("stage2 changed")
        put(p, original)
        put(self.f.oracle / "lib/driver", "different oracle driver")
        self.refuses("oracle bytes changed")

    def test_canonical_ddc_population_validation_cannot_be_replaced_by_a_file_hash(self):
        p = self.f.ddc_dir / "stage2-ddc-seed.json"
        row = recovery.document(p)
        row["records"].append(row["records"][-1])
        row["sha256"] = REAL.records_sha256(row["records"])
        write(p, row)
        observation = recovery.document(self.f.ddc_dir / "observation.json")
        for item in observation["captured_manifests"]:
            if Path(item["file"]).name == p.name:
                item["sha256"] = recovery.digest(p)
        write(self.f.ddc_dir / "observation.json", observation)
        self.refuses("repeats stage2 record")

    def test_oracle_prepost_identity_and_observed_tree_cannot_be_assumed(self):
        p = self.f.ddc_dir / "ddc-seed-post-build.json"
        row = recovery.document(p)
        row["commit"] = "f" * 40
        write(p, row)
        observation = recovery.document(self.f.ddc_dir / "observation.json")
        for item in observation["captured_manifests"]:
            if Path(item["file"]).name == p.name:
                item["sha256"] = recovery.digest(p)
        write(self.f.ddc_dir / "observation.json", observation)
        self.refuses("oracle changed during build")

    def test_helper_inventory_and_saved_physical_metadata_are_both_required(self):
        row = recovery.document(self.f.safe_file)
        name = next(iter(row["admitted"]))
        original = dict(row["admitted"][name])
        del row["admitted"][name]
        write(self.f.safe_file, row)
        self.f.save_provenance()
        self.refuses("helper profile or inventory differs")
        row["admitted"][name] = {**original, "inode": original["inode"] + 1}
        write(self.f.safe_file, row)
        self.f.save_provenance()
        self.refuses("native helper changed")

    def test_seed_archive_inventory_must_be_unique_even_with_identical_valid_digests(self):
        rows = self.f.provenance["bootstrap_lineage"]["validated_seed"]["authority"]["payloads"]
        rows[-1] = dict(rows[0])
        self.f.save_provenance()
        self.refuses("payload pin is duplicated")

    def test_real_producer_keeps_sixteen_scalars_separate_from_nine_archive_pins(self):
        scalars, payloads = PRODUCER.parse_stage0_pins(self.f.root)
        self.assertEqual((len(scalars), len(payloads)), (16, 9))
        self.assertEqual(REAL.read_stage0_pin(self.f.root), {**scalars, **payloads})
        authority = self.f.provenance["bootstrap_lineage"]["validated_seed"]["authority"]
        self.assertEqual(authority["pins"], scalars)
        self.assertFalse(any(key.startswith("dist/") for key in authority["pins"]))
        self.assertEqual(self.f.inspect()["state"], "inspected")

    def test_scalar_pin_identity_mismatch_refuses(self):
        authority = self.f.provenance["bootstrap_lineage"]["validated_seed"]["authority"]
        authority["pins"]["compiler_git_commit_hash"] = "f" * 40
        self.f.save_provenance()
        self.refuses("stage0 scalar pin map changed")

    def test_current_archive_pin_must_match_retained_payload_digest(self):
        authority = self.f.provenance["bootstrap_lineage"]["validated_seed"]["authority"]
        p = self.f.root / "src/stage0"
        row = authority["payloads"][0]
        text = p.read_text().replace(row["pinned_sha256"], "f" * 64, 1)
        p.write_text(text)
        authority["src_stage0"]["sha256"] = recovery.digest(p)
        self.f.save_provenance()
        self.refuses("stage0 payload pin map changed")

    def test_unrepresented_archive_pin_cannot_hide_in_scalar_partition(self):
        authority = self.f.provenance["bootstrap_lineage"]["validated_seed"]["authority"]
        p = self.f.root / "src/stage0"
        p.write_text(p.read_text() + "dist/2026-10-01/unrepresented.tar.xz=" + "f" * 64 + "\n")
        authority["src_stage0"]["sha256"] = recovery.digest(p)
        self.f.save_provenance()
        self.refuses("stage0 payload pin inventory changed")

    def test_saved_helper_manifest_must_match_original_admission_anchor(self):
        put(self.f.safe_file, self.f.safe_file.read_bytes() + b" ")
        self.refuses("original admitted hash")

    def test_self_consistent_new_ddc_tree_cannot_replace_original_cut_anchor(self):
        row = recovery.document(self.f.ddc_dir / "stage2-pinned-seed.json")
        extra = put(self.f.stage / "extra", "uncompared addition")
        row["records"].append({"path": "extra", "kind": "file", "mode": 0o644,
                               "bytes": extra.stat().st_size, "sha256": recovery.digest(extra)})
        row["sha256"] = REAL.records_sha256(row["records"])
        observation = recovery.document(self.f.ddc_dir / "observation.json")
        observation["stage2_tree_sha256"] = row["sha256"]
        for name in ("stage2-pinned-seed.json", "stage2-ddc-seed.json"):
            write(self.f.ddc_dir / name, row)
            for item in observation["captured_manifests"]:
                if Path(item["file"]).name == name:
                    item["sha256"] = recovery.digest(self.f.ddc_dir / name)
        write(self.f.ddc_dir / "observation.json", observation)
        self.refuses("DDC tree differs from original cut")

    def test_self_consistent_oracle_relation_downgrade_cannot_replace_original_cut(self):
        observation = recovery.document(self.f.ddc_dir / "observation.json")
        observation["relation"] = "same-lineage"
        for name in ("ddc-seed.json", "ddc-seed-post-build.json"):
            p = self.f.ddc_dir / name
            row = recovery.document(p)
            row["relation"] = "same-lineage"
            write(p, row)
            for item in observation["captured_manifests"]:
                if Path(item["file"]).name == name:
                    item["sha256"] = recovery.digest(p)
        write(self.f.ddc_dir / "observation.json", observation)
        self.refuses("DDC oracle relation/identity differs from original cut")

    def test_named_file_replacement_during_hash_is_refused(self):
        original = put(self.f.base / "racing-input", "old bytes")
        replacement = put(self.f.base / "replacement", "new bytes")
        actual_digest = hashlib.file_digest

        def replace_after_read(stream, algorithm):
            result = actual_digest(stream, algorithm)
            os.replace(replacement, original)
            return result

        with mock.patch.object(recovery.hashlib, "file_digest", side_effect=replace_after_read):
            with self.assertRaisesRegex(recovery.RecoveryError, "file replaced"):
                recovery.digest(original)

    def test_original_jobs_or_environment_cannot_be_relabelled(self):
        p = self.f.evidence / "mint-result.json"
        row = recovery.document(p)
        row["command"][row["command"].index("--jobs") + 1] = "20"
        write(p, row)
        self.refuses("original jobs differ")
        row["command"][row["command"].index("--jobs") + 1] = "12"
        write(p, row)
        self.f.provenance["build_authority"]["declared_environment_sha256"]["CARGO_NET_OFFLINE"] = "f" * 64
        self.f.save_provenance()
        self.refuses("closed environment")

    def test_unexpected_dist_file_and_channel_hash_refuse(self):
        p = put(self.f.build / "dist/extra.tar.xz", "unexpected")
        self.refuses("dist inventory differs")
        p.unlink()
        p = self.f.build / "dist/channel-rust-trust.toml"
        text = p.read_text()
        p.write_text(text.replace('hash="', 'hash="f', 1))
        self.refuses("archive/channel hash differs")

    def test_foreign_work_and_conflicting_proof_output_refuse(self):
        self.f.provenance["build_authority"]["cargo_environment"]["cargo_home"] = str(self.f.base / "foreign/cargo-home")
        self.f.save_provenance()
        self.refuses("foreign retained operational")
        self.f.provenance["build_authority"]["cargo_environment"]["cargo_home"] = str(self.f.cargo)
        self.f.save_provenance()
        p = self.f.root / "build" / f"self-host-proof-{VERSION}-{HOST}-{COMMIT[:12]}"
        p.mkdir()
        self.refuses("conflicting final/proof")

    def test_rebind_races_and_saved_helper_manifest_changes_refuse(self):
        record = self.f.inspect()
        put(self.f.safe_file, self.f.safe_file.read_bytes() + b" ")
        with self.assertRaisesRegex(recovery.RecoveryError, "saved helper manifest changed"):
            recovery.prepare(record, support=self.f.support, owner=self.f.owner)
        self.assertFalse(self.f.work.exists())

    def test_symlink_and_parent_escape_do_not_become_input_authority(self):
        p = self.f.evidence / "mint-result.json"
        original = p.read_bytes()
        other = put(self.f.base / "terminal-copy", original)
        p.unlink()
        p.symlink_to(other)
        self.refuses("invalid or oversize file")
        for path in ("../foreign", "/absolute", "a/../foreign", "./alias"):
            with self.subTest(path=path), self.assertRaises(recovery.RecoveryError):
                recovery.inside(self.f.root, path)

    def test_record_creation_is_exclusive(self):
        p = self.f.evidence / "new-record.json"
        recovery.write_record(p, {"state": "inspected", "qualification": False})
        original = p.read_bytes()
        with self.assertRaisesRegex(recovery.RecoveryError, "record exists"):
            recovery.write_record(p, {"qualification": True})
        self.assertEqual(p.read_bytes(), original)


class AuditFixture(Fixture):
    """The retained-WORK producer shape: raw failed history, not an accepted receipt."""
    def __init__(self, base):
        super().__init__(base)
        self.work.mkdir()
        for name in ("home", "tmp", "rustup-home", "xdg-config"):
            (self.work / "environment-mint" / name).mkdir(parents=True)
        (self.work / "safe-bin").mkdir()
        safe = recovery.document(self.safe_file)
        for name, row in safe["admitted"].items():
            (self.work / "safe-bin" / name).symlink_to(row["path"])
        put(self.work / "safe-path.json", self.safe_file.read_bytes())
        for path in self.ddc_dir.glob("*.json"):
            if path.name != "observation.json":
                put(self.work / path.name, path.read_bytes())
        donor = self.base / "immutable-cargo"; donor.mkdir()
        cargo = REAL.cargo_home_inputs(donor, self.cargo)
        write(self.work / "cargo-home-inputs.json", cargo)
        write(self.work / "bootstrap-config-closure.json", self.configuration())
        write(self.work / "clean-lean-inputs.json", self.lean())
        write(self.work / "mint-toolchain-inputs.json", REAL.mint_tool_manifest(self.root, self.config))
        for name in ("native-library-inputs.json", "seed-dylib-inputs.json"):
            write(self.work / name, REAL.native_library_manifest([]))
        write(self.work / "pinned-seed.json", {"compiler_commit": "b" * 40, "host": HOST})
        terminal = recovery.document(self.evidence / "mint-result.json")
        terminal["command"].extend(["--config", str(self.config)])
        host, jobs, work, cargo, env, oracle, source = recovery.declared_environment(self.root, self.provenance, terminal)
        env["SOURCE_DATE_EPOCH"] = "1000"
        before = {"schema": REAL.MINT_OBSERVATION_SCHEMA, "host": host,
                  "build_root": self.build.relative_to(self.root).as_posix(), "config_path": "bootstrap.toml",
                  "config_closure_sha256": self.configuration()["fingerprint"],
                  "mint_configuration": self.provenance["bootstrap_lineage"]["mint_configuration"],
                  "declared_environment": {key: env[key] for key in REAL.MINT_ENVIRONMENT if key in env},
                  "source_lineage": self.lineage(), "bootstrap_lineage": self.provenance["bootstrap_lineage"],
                  "build_authority": self.provenance["build_authority"], "llvm_before": {"mode": "in-tree", "output": {"present": False}}}
        write(self.work / "mint-stage-observation.json", before)
        self.provenance.update(status="rejected", errors=["unmapped public stage tool rust-lld"])
        write(self.stage / "tool-provenance.json", self.provenance)
        self.raw_mint = self.base / "actual-mint-result.json"
        write(self.raw_mint, {"source": COMMIT, "exit": 1, "source_config_operator_unchanged": True,
                              "phases": [{"phase": "canonical-preflight", "exit": 0},
                                         {"phase": "canonical-mint", "exit": 1, "argv": terminal["command"]}]})
        self.raw_controller = self.base / "actual-controller-result.json"
        write(self.raw_controller, {"source": COMMIT, "admission_exit": 1, "child_result": str(self.raw_mint),
                                    "managed_inputs_unchanged": True})
        self.refresh_capture()

    def refresh_capture(self):
        originals = [self.stage / "tool-provenance.json", self.raw_mint, self.raw_controller]
        originals.extend(self.work / name for name in recovery.AUDIT_INPUTS)
        rows = []
        for index, original in enumerate(originals):
            copied = self.evidence / f"raw-{index}.json"
            put(copied, original.read_bytes())
            rows.append({"original": str(original), "retained": str(copied),
                         "sha256": recovery.digest(copied), "bytes": copied.stat().st_size})
        write(self.evidence / "RETAINED.json", {"schema": "trust.failed-mint-retained-evidence.v1",
              "source": COMMIT, "actual_exit": 1, "original_work": str(self.work), "files": rows})

    def inspect_audit(self):
        return recovery.validate_at_provenance(self.root, self.build, self.evidence,
                        support=self.support, owner=self.owner, engine=self.engine)


class RetainedAuditTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="retained-audit-inert-")
        self.addCleanup(temp.cleanup)
        self.f = AuditFixture(Path(temp.name))
        self.no_process = mock.patch.object(subprocess, "Popen", side_effect=AssertionError("no native execution in inert controls"))
        self.no_process.start(); self.addCleanup(self.no_process.stop)

    def refuses(self, text):
        with self.assertRaisesRegex((recovery.RecoveryError, REAL.WorkflowError), text):
            self.f.inspect_audit()

    def test_real_retained_history_shape_is_inspected_without_reaudit_or_writes(self):
        before = {p: p.read_bytes() for p in self.f.work.glob("*.json")}
        record = self.f.inspect_audit()
        self.assertEqual(record["mode"], recovery.AUDIT_MODE)
        self.assertEqual(record["original_jobs"], 12)
        self.assertTrue(record["original_work_retained"])
        self.assertTrue(record["original_private_cargo_retained"])
        self.assertFalse(record["qualification"])
        self.assertFalse(record["strict_native_verifier_passed"])
        self.assertEqual(before, {p: p.read_bytes() for p in self.f.work.glob("*.json")})
        self.assertEqual(self.f.calls, [])

    def test_tampered_original_or_copy_and_duplicate_history_refuse(self):
        original = self.f.work / "safe-path.json"
        original.write_bytes(original.read_bytes() + b" ")
        self.refuses("original/copy changed")
        self.f.refresh_capture()
        capture = recovery.document(self.f.evidence / "RETAINED.json")
        capture["files"].append(capture["files"][0])
        write(self.f.evidence / "RETAINED.json", capture)
        self.refuses("duplicate")

    def test_missing_observation_or_foreign_work_refuses(self):
        capture = recovery.document(self.f.evidence / "RETAINED.json")
        capture["files"] = [row for row in capture["files"] if Path(row["original"]).name != "mint-stage-observation.json"]
        write(self.f.evidence / "RETAINED.json", capture)
        self.refuses("missing retained original")

    def test_coherent_failure_relabel_cannot_admit_a_successful_history(self):
        terminal = recovery.document(self.f.raw_mint); terminal["exit"] = 0
        write(self.f.raw_mint, terminal); self.f.refresh_capture()
        self.refuses("failure or input history differs")

    def test_boolean_phase_exit_is_not_a_terminal_integer_failure(self):
        terminal = recovery.document(self.f.raw_mint)
        terminal["phases"][-1]["exit"] = True
        write(self.f.raw_mint, terminal); self.f.refresh_capture()
        self.refuses("did not reach the canonical mint")

    def test_scalar_pin_changes_refuse(self):
        path = self.f.root / "src/stage0"
        path.write_text(path.read_text().replace("compiler_version=0.1.0-trust", "compiler_version=0.2.0-trust"))
        self.refuses("scalar pins changed")

    def test_incomplete_ddc_manifest_refuses(self):
        write(self.f.work / "stage2-ddc-seed.json", {"not": "DDC"}); self.f.refresh_capture()
        self.refuses("stage2")

    def test_seed_payload_mutation_refuses(self):
        row = self.f.provenance["bootstrap_lineage"]["validated_seed"]["authority"]["payloads"][0]
        (self.f.root / row["path"]).write_bytes(b"changed pinned seed archive")
        self.refuses("stage0 payload changed")

    def test_current_oracle_mutation_refuses(self):
        (self.f.oracle / "bin/rustc").write_bytes(b"changed oracle compiler")
        self.refuses("current DDC oracle changed")

    def test_archive_channel_mismatch_refuses(self):
        path = next((self.f.build / "dist").glob("*.tar.xz"))
        path.write_bytes(path.read_bytes() + b"changed")
        self.refuses("dist/channel hash differs")

    def test_preexisting_llvm_observation_cannot_become_fresh_build_evidence(self):
        path = self.f.work / "mint-stage-observation.json"
        doc = recovery.document(path); doc["llvm_before"]["output"]["present"] = True
        write(path, doc); self.f.refresh_capture()
        self.refuses("absent in-tree LLVM")

    def test_foreign_job_history_cannot_change_the_original_audit_job_count(self):
        doc = recovery.document(self.f.raw_mint)
        argv = doc["phases"][-1]["argv"]; argv[argv.index("--jobs") + 1] = "18"
        write(self.f.raw_mint, doc); self.f.refresh_capture()
        self.refuses("original jobs differ")

    def test_partial_tail_output_never_restarts_that_tail(self):
        put(self.f.work / "seed-inputs.json", "earlier partial continuation")
        self.refuses("conflicting continuation output")

    def test_actual_audit_is_delegated_with_original_jobs_environment_and_distinct_receipt(self):
        record = self.f.inspect_audit()
        rejected = (self.f.stage / "tool-provenance.json").read_bytes()
        before = dict(os.environ)
        output = self.f.evidence / "mint-continuation-inert-stage-provenance.json"
        calls = []
        def finish(root, build, config, host, observation, **kwargs):
            calls.append((root, build, config, host, observation, kwargs, dict(os.environ)))
            accepted = {**self.f.provenance, "status": "internal-release-ready", "errors": []}
            write(kwargs["receipt_path"], accepted)
        self.f.support.finish_mint_stage_evidence = finish
        prepared = recovery.prepare_at_provenance(record, output, support=self.f.support, owner=self.f.owner)
        self.assertTrue(prepared["strict_native_verifier_passed"])
        self.assertFalse(prepared["qualification"])
        self.assertFalse(prepared["cargo_home_absent_for_fresh_inputs"])
        self.assertEqual(dict(os.environ), before)
        self.assertEqual((self.f.stage / "tool-provenance.json").read_bytes(), rejected)
        self.assertEqual(calls[0][5], {"jobs": 12, "receipt_path": output})
        self.assertEqual(calls[0][6]["PATH"], str(self.f.work / "safe-bin"))
        self.assertEqual(calls[0][6]["CARGO_HOME"], str(self.f.cargo))
        self.assertEqual(calls[0][4], self.f.work / "mint-stage-observation.json")

    def test_audit_refusal_preserves_originals_and_never_prepares(self):
        record = self.f.inspect_audit()
        self.f.support.finish_mint_stage_evidence = mock.Mock(side_effect=REAL.WorkflowError("strict audit refused"))
        original = (self.f.stage / "tool-provenance.json").read_bytes()
        with self.assertRaisesRegex(REAL.WorkflowError, "strict audit refused"):
            recovery.prepare_at_provenance(record, self.f.evidence / "mint-continuation-red-stage-provenance.json",
                                           support=self.f.support, owner=self.f.owner)
        self.assertEqual(record["state"], "inspected")
        self.assertEqual((self.f.stage / "tool-provenance.json").read_bytes(), original)
        self.assertTrue(self.f.cargo.is_dir())

    def test_external_audit_cannot_overwrite_or_add_a_receipt_inside_original_mint(self):
        record = self.f.inspect_audit()
        for path in (self.f.stage / "tool-provenance.json", self.f.build / "new-audit.json"):
            with self.assertRaisesRegex(recovery.RecoveryError, "new external receipt"):
                recovery.prepare_at_provenance(record, path, support=self.f.support, owner=self.f.owner)


if __name__ == "__main__":
    unittest.main()
