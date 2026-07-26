#!/usr/bin/env python3

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "compat_check.py"
SPEC = importlib.util.spec_from_file_location("trust_compat_check", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CorpusTests(unittest.TestCase):
    def test_committed_corpus_metadata_matches_exact_bytes_and_entries(self) -> None:
        root = SCRIPT.parent.parent
        crate_list = root / "tests/compat/top_crates.txt"
        metadata = root / "tests/compat/top_crates.meta.json"
        loaded, entries = MODULE.load_corpus(crate_list, metadata)
        self.assertEqual(loaded["entry_count"], 123)
        self.assertEqual(len(entries), 123)
        self.assertEqual(len(entries), len(set(entries)))
        self.assertIn(
            "Each generated top-level fixture has an empty main; proc-macro targets may be "
            "compiled, but the corpus does not inventory or independently attest each macro "
            "invocation.",
            loaded["limitations"],
        )

    def test_invalid_or_duplicate_entries_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "corpus.txt"
            path.write_text("serde\nserde\nnot a crate\n", encoding="utf-8")
            with self.assertRaises(MODULE.GateError):
                MODULE.parse_corpus(path)


class ReceiptHelpersTests(unittest.TestCase):
    @staticmethod
    def full_receipt(*, marker: str = "current", count: int = 2) -> dict:
        entries = [f"crate-{index}" for index in range(count)]
        return {
            "schema": MODULE.RECEIPT_SCHEMA,
            "status": "diagnostic-passed",
            "classification": "diagnostic-only",
            "runner_execution_authenticated": False,
            "release_gate_admissible": False,
            "marker": marker,
            "lane": MODULE.native_compat_lane_claims(),
            "source": {"source_tree_clean": True},
            "tools": {"targo": {}, "trustc": {}},
            "stage_provenance": {"verified_before_and_after_run": True},
            "corpus": {
                "complete": True,
                "entry_count": count,
                "executed_entry_count": count,
                "entries": entries,
            },
            "isolation": {"cache_mode": "isolated"},
            "input_stability": {
                "source_stable": True,
                "corpus_stable": True,
                "tools_stable": True,
                "stage_provenance_stable": True,
            },
            "summary": {"total": count, "passed": count, "failed": 0},
            "results": [
                {"crate": crate, "status": "passed"}
                for crate in entries
            ],
        }

    def test_atomic_json_uses_durable_unique_same_directory_replace(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            receipt = root / "evidence" / "compat.json"
            colliding = receipt.parent / f".{receipt.name}.collision.tmp"
            receipt.parent.mkdir()
            collision_target = receipt.parent / "collision-target"
            collision_target.write_text("do not overwrite\n", encoding="utf-8")
            colliding.symlink_to(collision_target)
            real_fsync = MODULE.os.fsync
            with mock.patch.object(
                MODULE.secrets,
                "token_hex",
                side_effect=["collision", "unique"],
            ), mock.patch.object(MODULE.os, "fsync", wraps=real_fsync) as fsync:
                published = MODULE.atomic_json(receipt, {"status": "diagnostic"})
            self.assertEqual(published, receipt)
            self.assertEqual(
                json.loads(receipt.read_text(encoding="utf-8")),
                {"status": "diagnostic"},
            )
            self.assertTrue(colliding.is_symlink())
            self.assertEqual(collision_target.read_text(encoding="utf-8"), "do not overwrite\n")
            self.assertFalse((receipt.parent / f".{receipt.name}.unique.tmp").exists())
            self.assertGreaterEqual(fsync.call_count, 2, "file and directory must both be fsynced")

    def test_atomic_json_rejects_symlink_destination_and_unsafe_parents(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            target = root / "target.json"
            target.write_text("authority\n", encoding="utf-8")
            linked_destination = root / "linked.json"
            linked_destination.symlink_to(target)
            with self.assertRaisesRegex(MODULE.GateError, "destination is a symlink"):
                MODULE.atomic_json(linked_destination, {"status": "failed"})
            self.assertEqual(target.read_text(encoding="utf-8"), "authority\n")

            directory_destination = root / "directory.json"
            directory_destination.mkdir()
            with self.assertRaisesRegex(MODULE.GateError, "not a regular file"):
                MODULE.atomic_json(directory_destination, {"status": "failed"})

            real_parent = root / "real-parent"
            real_parent.mkdir()
            linked_parent = root / "linked-parent"
            linked_parent.symlink_to(real_parent, target_is_directory=True)
            with self.assertRaisesRegex(MODULE.GateError, "symlink or non-directory"):
                MODULE.atomic_json(linked_parent / "receipt.json", {"status": "failed"})
            self.assertFalse((real_parent / "receipt.json").exists())

            file_parent = root / "file-parent"
            file_parent.write_text("not a directory\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.GateError, "symlink or non-directory"):
                MODULE.atomic_json(file_parent / "receipt.json", {"status": "failed"})

    def test_serialization_failure_does_not_touch_destination_or_parent(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            parent = root / "not-created"
            with self.assertRaisesRegex(MODULE.GateError, "not strict JSON"):
                MODULE.atomic_json(parent / "receipt.json", {"bad": object()})
            self.assertFalse(parent.exists())

    def test_nonpassing_reruns_preserve_full_authority_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            authority = root / "compat.json"
            MODULE.publish_compatibility_receipt(
                authority, self.full_receipt(marker="established")
            )
            established = authority.read_bytes()
            for status in (
                "diagnostic-partial-passed",
                "diagnostic-failed",
                "diagnostic-rejected",
            ):
                with self.subTest(status=status):
                    attempt = {
                        "schema": MODULE.RECEIPT_SCHEMA,
                        "status": status,
                        "marker": status,
                    }
                    published, full_pass = MODULE.publish_compatibility_receipt(
                        authority, attempt
                    )
                    self.assertFalse(full_pass)
                    self.assertEqual(authority.read_bytes(), established)
                    self.assertEqual(published, MODULE.nonpassing_attempt_path(authority))
                    self.assertEqual(
                        json.loads(published.read_text(encoding="utf-8"))["status"],
                        status,
                    )

    def test_incomplete_status_passed_attempt_cannot_replace_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            authority = root / "compat.json"
            MODULE.publish_compatibility_receipt(authority, self.full_receipt())
            established = authority.read_bytes()
            malformed_pass = {
                "schema": MODULE.RECEIPT_SCHEMA,
                "status": "diagnostic-passed",
            }
            published, full_pass = MODULE.publish_compatibility_receipt(
                authority, malformed_pass
            )
            self.assertFalse(full_pass)
            self.assertEqual(authority.read_bytes(), established)
            self.assertEqual(published, MODULE.nonpassing_attempt_path(authority))

    def test_result_identities_must_be_an_exact_corpus_bijection(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            authority = root / "compat.json"
            MODULE.publish_compatibility_receipt(
                authority, self.full_receipt(marker="established")
            )
            established = authority.read_bytes()
            attempts = []

            repeated = self.full_receipt(marker="repeated")
            repeated["results"] = [repeated["results"][0], repeated["results"][0]]
            attempts.append(repeated)

            reordered = self.full_receipt(marker="reordered")
            reordered["results"].reverse()
            attempts.append(reordered)

            duplicate_corpus = self.full_receipt(marker="duplicate-corpus")
            first = duplicate_corpus["corpus"]["entries"][0]
            duplicate_corpus["corpus"]["entries"] = [first, first]
            attempts.append(duplicate_corpus)

            for attempt in attempts:
                with self.subTest(marker=attempt["marker"]):
                    published, full_pass = MODULE.publish_compatibility_receipt(
                        authority, attempt
                    )
                    self.assertFalse(full_pass)
                    self.assertEqual(authority.read_bytes(), established)
                    self.assertEqual(published, MODULE.nonpassing_attempt_path(authority))

    def test_inflated_proc_macro_lane_cannot_replace_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            authority = root / "compat.json"
            established = self.full_receipt(marker="established")
            MODULE.publish_compatibility_receipt(authority, established)
            established_bytes = authority.read_bytes()
            inflated = self.full_receipt(marker="inflated")
            inflated["lane"]["covers"].append("native proc-macro compilation and execution")
            published, full_pass = MODULE.publish_compatibility_receipt(authority, inflated)
            self.assertFalse(full_pass)
            self.assertEqual(authority.read_bytes(), established_bytes)
            self.assertEqual(published, MODULE.nonpassing_attempt_path(authority))

    def test_unserializable_attempt_cannot_touch_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            authority = root / "compat.json"
            MODULE.publish_compatibility_receipt(authority, self.full_receipt())
            established = authority.read_bytes()
            with self.assertRaisesRegex(MODULE.GateError, "not strict JSON"):
                MODULE.publish_compatibility_receipt(
                    authority,
                    {
                        "schema": MODULE.RECEIPT_SCHEMA,
                        "status": "rejected",
                        "bad": object(),
                    },
                )
            self.assertEqual(authority.read_bytes(), established)
            self.assertFalse(MODULE.nonpassing_attempt_path(authority).exists())

    def test_later_full_pass_may_replace_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            authority = root / "compat.json"
            MODULE.publish_compatibility_receipt(
                authority, self.full_receipt(marker="old")
            )
            published, full_pass = MODULE.publish_compatibility_receipt(
                authority, self.full_receipt(marker="new")
            )
            self.assertTrue(full_pass)
            self.assertEqual(published, authority)
            self.assertEqual(json.loads(authority.read_text(encoding="utf-8"))["marker"], "new")

    def test_main_rejected_attempt_preserves_existing_authority(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            authority = root / "compat.json"
            MODULE.publish_compatibility_receipt(
                authority, self.full_receipt(marker="established")
            )
            established = authority.read_bytes()
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                exit_code = MODULE.main(
                    [
                        "--repo-root",
                        str(root),
                        "--cache-mode",
                        "run",
                        "--receipt",
                        str(authority),
                    ]
                )
            self.assertEqual(exit_code, 2)
            self.assertIn("complete diagnostic receipt left untouched", stderr.getvalue())
            self.assertEqual(authority.read_bytes(), established)
            diagnostic = MODULE.nonpassing_attempt_path(authority)
            self.assertEqual(
                json.loads(diagnostic.read_text(encoding="utf-8"))["status"],
                "diagnostic-rejected",
            )

    def test_unauthenticated_runner_can_never_emit_release_authority(self) -> None:
        receipt = self.full_receipt()
        self.assertTrue(MODULE.is_complete_passing_diagnostic(receipt))
        self.assertFalse(MODULE.is_full_passing_receipt(receipt))
        forged = dict(receipt)
        forged["runner_execution_authenticated"] = True
        forged["release_gate_admissible"] = True
        self.assertFalse(MODULE.is_full_passing_receipt(forged))
        self.assertFalse(MODULE.is_complete_passing_diagnostic(forged))

    def test_strict_json_rejects_duplicate_keys_at_any_depth(self) -> None:
        with self.assertRaisesRegex(MODULE.GateError, "duplicate object key 'x'"):
            MODULE.strict_json_loads('{"outer":{"x":1,"x":2}}', "fixture")

    @unittest.skipUnless(MODULE.os.name == "posix", "controlled Git is POSIX-only")
    def test_git_identity_ignores_fake_path_and_repo_local_fsmonitor(self) -> None:
        with tempfile.TemporaryDirectory() as repository_dir, tempfile.TemporaryDirectory() as fake_dir:
            root = Path(repository_dir).resolve()
            git = MODULE.controlled_git_executable()
            fixed_env = MODULE.provenance_git_environment()

            def fixture_git(*args: str) -> None:
                completed = MODULE.subprocess.run(
                    [str(git), "-C", str(root), *args],
                    env=fixed_env,
                    stdout=MODULE.subprocess.PIPE,
                    stderr=MODULE.subprocess.PIPE,
                    check=False,
                )
                self.assertEqual(
                    completed.returncode,
                    0,
                    completed.stderr.decode("utf-8", "replace"),
                )

            fixture_git("init", "--quiet")
            (root / "tracked.txt").write_text("fixture\n", encoding="utf-8")
            fixture_git("add", "tracked.txt")
            fixture_git(
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "fixture",
            )
            monitor_marker = root / ".git" / "fsmonitor-invoked"
            monitor = root / ".git" / "malicious-fsmonitor"
            monitor.write_text(
                f"#!/bin/sh\n: > '{monitor_marker}'\nprintf '0\\n'\n",
                encoding="utf-8",
            )
            monitor.chmod(0o755)
            fixture_git("config", "--local", "core.fsmonitor", str(monitor))
            fixture_git("config", "--local", "core.trustctime", "false")
            fixture_git("config", "--local", "core.checkStat", "minimal")
            fixture_git("config", "--local", "core.ignoreStat", "true")
            fixture_git(
                "config", "--local", "core.worktree", "/definitely/not/the/repository"
            )

            fake_marker = Path(fake_dir) / "fake-git-invoked"
            fake_git = Path(fake_dir) / "git"
            fake_git.write_text(
                f"#!/bin/sh\n: > '{fake_marker}'\nexit 99\n", encoding="utf-8"
            )
            fake_git.chmod(0o755)
            with mock.patch.dict(MODULE.os.environ, {"PATH": fake_dir}, clear=False):
                identity = MODULE.git_identity(root)

            self.assertRegex(identity["head"], r"^[0-9a-f]{40}$")
            self.assertFalse(fake_marker.exists())
            self.assertFalse(monitor_marker.exists())

            (root / ".gitignore").write_text("*\n", encoding="utf-8")
            (root / "hidden.txt").write_text("hidden\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.GateError, "untracked .gitignore authority"):
                MODULE.git_identity(root)

            (root / ".gitignore").unlink()
            (root / "hidden.txt").unlink()
            if MODULE.sys.platform == "darwin":
                (root / ".GITIGNORE").write_text("*\n", encoding="utf-8")
                (root / "hidden.txt").write_text("hidden\n", encoding="utf-8")
                if (root / ".gitignore").exists():
                    with self.assertRaisesRegex(
                        MODULE.GateError, "untracked .gitignore authority"
                    ):
                        MODULE.git_identity(root)
                (root / ".GITIGNORE").unlink()
                (root / "hidden.txt").unlink()
            (root / ".git" / "info" / "exclude").write_text(
                " #secret\n", encoding="utf-8"
            )
            (root / " #secret").write_text("hidden\n", encoding="utf-8")
            with self.assertRaisesRegex(MODULE.GateError, "material uncommitted rules"):
                MODULE.git_identity(root)

    @unittest.skipUnless(MODULE.os.name == "posix", "controlled Git is POSIX-only")
    def test_git_identity_recurses_into_gitlinks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            nested = root / "nested"
            git = MODULE.controlled_git_executable()
            fixed_env = MODULE.provenance_git_environment()

            def run_git(repo: Path, *args: str, capture: bool = False):
                completed = MODULE.subprocess.run(
                    [str(git), "-C", str(repo), *args],
                    env=fixed_env,
                    stdout=MODULE.subprocess.PIPE,
                    stderr=MODULE.subprocess.PIPE,
                    check=False,
                )
                self.assertEqual(
                    completed.returncode,
                    0,
                    completed.stderr.decode("utf-8", "replace"),
                )
                return completed.stdout if capture else None

            run_git(root, "init", "--quiet")
            (root / "tracked.txt").write_text("root\n", encoding="utf-8")
            run_git(root, "add", "tracked.txt")
            run_git(
                root,
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "root fixture",
            )
            run_git(root, "init", "--quiet", str(nested))
            (nested / "tracked.txt").write_text("nested\n", encoding="utf-8")
            run_git(nested, "add", "tracked.txt")
            run_git(
                nested,
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "nested fixture",
            )
            nested_head = run_git(
                nested, "rev-parse", "--verify", "HEAD^{commit}", capture=True
            )
            assert nested_head is not None
            cache_info = f"160000,{nested_head.decode('ascii').strip()},nested"
            run_git(root, "update-index", "--add", "--cacheinfo", cache_info)
            run_git(
                root,
                "-c",
                "user.name=Trust Tests",
                "-c",
                "user.email=trust-tests@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "gitlink fixture",
            )

            identity = MODULE.git_identity(root)
            self.assertEqual(identity["recursive_submodules"][0]["path"], "nested")
            (nested / ".gitignore").write_text("*\n", encoding="utf-8")
            (nested / "hidden.txt").write_text("hidden\n", encoding="utf-8")
            with self.assertRaises(MODULE.GateError):
                MODULE.git_identity(root)

    def test_resolved_packages_are_exact_and_sorted(self) -> None:
        packages = MODULE.resolved_packages(
            {
                "packages": [
                    {"name": "z", "version": "1.0.0", "source": "registry+x", "checksum": "b"},
                    {"name": "a", "version": "2.0.0", "source": "registry+x", "checksum": "a"},
                ]
            }
        )
        self.assertEqual([package["name"] for package in packages], ["a", "z"])
        self.assertEqual(packages[0]["checksum"], "a")

    def test_stage_provenance_requires_bootstrap_non_self_proof_disclosure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            sysroot = Path(directory) / "stage2"
            sysroot.mkdir()
            receipt = sysroot / "tool-provenance.json"
            payload = {
                "schema": MODULE.PROVENANCE_SCHEMA,
                "status": "candidate-ready",
                "source_tree_clean": True,
                "trust_from_trust": True,
                "compiler": {
                    "source_commit": "a" * 40,
                    "compiler_sha256": "b" * 64,
                    "sysroot_matches": True,
                },
            }
            receipt.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(MODULE.GateError):
                MODULE.validate_stage_provenance(
                    receipt,
                    root=Path(directory),
                    source_head="a" * 40,
                    sysroot=sysroot,
                    trustc_sha256="b" * 64,
                )

    def test_candidate_provenance_is_never_compatibility_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sysroot = root / "build" / "test-host" / "stage2"
            sysroot.mkdir(parents=True)
            receipt = sysroot / "tool-provenance.json"
            receipt.write_text(
                json.dumps(
                    {
                        "schema": MODULE.PROVENANCE_SCHEMA,
                        "status": "candidate-ready",
                        "stage": 2,
                        "host": "test-host",
                        "path_scope": "repository-root-relative",
                        "tool_binding_status": "ready",
                        "errors": [],
                        "source_tree_clean": True,
                        "trust_from_trust": True,
                        "source_lineage": {
                            "status": "immutable_release",
                            "stable_across_build": True,
                            "errors": [],
                        },
                        "bootstrap_lineage": {
                            "status": "trust_from_trust",
                            "stable_across_build": True,
                            "errors": [],
                        },
                        "build_authority": {
                            "status": "ready",
                            "stable_across_build": True,
                            "errors": [],
                        },
                        "compiler": {
                            "source_commit": "a" * 40,
                            "compiler_sha256": "b" * 64,
                            "sysroot_matches": True,
                        },
                        "bootstrap_compiler_verification": {
                            "mode": "disabled",
                            "flag": "-Ztrust-verify=off",
                            "reason": "bootstrap stability",
                            "counts_as_self_proof": False,
                        },
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(MODULE.GateError, "not immutable"):
                MODULE.validate_stage_provenance(
                    receipt,
                    root=root,
                    source_head="a" * 40,
                    sysroot=sysroot,
                    trustc_sha256="b" * 64,
                )

    def test_partial_or_shared_cache_runs_cannot_exit_as_passing_evidence(self) -> None:
        self.assertEqual(MODULE.evidence_exit_code(complete=True, failed=0), 0)
        self.assertNotEqual(MODULE.evidence_exit_code(complete=False, failed=0), 0)
        with self.assertRaises(MODULE.GateError):
            MODULE.require_evidence_cache_mode("run")

    def test_lane_claims_do_not_inflate_proc_macro_execution(self) -> None:
        lane = MODULE.native_compat_lane_claims()
        self.assertEqual(
            lane["fixture_shape"],
            "generated binary with an empty main and one wildcard dependency",
        )
        self.assertIn(
            "proc-macro package compilation where selected graphs contain proc-macro targets",
            lane["covers"],
        )
        self.assertIn(
            "an inventory or independent attestation of proc-macro invocation",
            lane["does_not_cover"],
        )
        self.assertFalse(
            any("proc-macro compilation and execution" in item for item in lane["covers"])
        )

    def test_registry_metadata_requires_exact_checksums_and_no_git_sources(self) -> None:
        valid = {
            "packages": [
                {
                    "name": "serde",
                    "version": "1.0.0",
                    "source": "registry+https://example.invalid/index",
                    "checksum": "a" * 64,
                }
            ]
        }
        MODULE.validate_resolved_metadata("serde", valid)
        missing_checksum = json.loads(json.dumps(valid))
        missing_checksum["packages"][0]["checksum"] = None
        with self.assertRaises(MODULE.GateError):
            MODULE.validate_resolved_metadata("serde", missing_checksum)
        git_source = json.loads(json.dumps(valid))
        git_source["packages"].append(
            {
                "name": "injected",
                "version": "0.1.0",
                "source": "git+https://example.invalid/repo",
                "checksum": None,
            }
        )
        with self.assertRaises(MODULE.GateError):
            MODULE.validate_resolved_metadata("serde", git_source)

    def test_successful_native_build_requires_unverified_banner(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            targo = root / "targo"
            trustc = root / "trustc"
            metadata = json.dumps(
                {
                    "packages": [
                        {
                            "name": "serde",
                            "version": "1.0.0",
                            "source": "registry+test",
                            "checksum": "a" * 64,
                        }
                    ]
                },
                separators=(",", ":"),
            )
            targo.write_text(
                "#!/bin/sh\n"
                "case \" $* \" in\n"
                "  *' generate-lockfile '*) : > Cargo.lock ;;\n"
                f"  *' metadata '*) printf '%s\\n' '{metadata}' ;;\n"
                "esac\n",
                encoding="utf-8",
            )
            trustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            targo.chmod(0o755)
            trustc.chmod(0o755)
            result = MODULE.run_crate(
                "serde",
                index=1,
                work_root=root / "work",
                cargo_home_root=root / "cargo-home",
                cache_mode="isolated",
                targo=targo,
                trustc=trustc,
            )
            self.assertEqual(result["status"], "failed")
            self.assertIn("mandatory UNVERIFIED banner", result["error"])
            self.assertFalse(result["commands"][-1]["mandatory_unverified_banner_present"])


if __name__ == "__main__":
    unittest.main()
