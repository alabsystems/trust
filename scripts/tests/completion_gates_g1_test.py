#!/usr/bin/env python3
"""Negative controls for the schema-owned G1 Rust checker snapshot protocol."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts/completion_gates/check_g1_rust_input.py"
GOAL = "TRUST-TWO-LANGUAGE-100"
REPOSITORY = "https://github.com/alabsystems/trust"
RUN = "a" * 64
IDENTITY = "b" * 64
FEATURES = sorted({
    "macros", "build_scripts", "inline_asm", "ffi", "dynamic_linking",
    "runtime_startup", "closures", "coroutines", "consts", "statics",
    "intrinsics", "unsafe", "generated_shims",
})
REQUIRED = (
    "pinned_upstream_rust_revision",
    "full_upstream_rust_surface",
    "all_reachable_rust_bodies_inventoried",
    "zero_upstream_rust_semantic_regressions",
    "non_applicable_rust_harness_rows_only",
    "owner_pinned_rust_surface_and_accept_reject_parity",
    "rust_frontend_constructor_totality",
    "rust_macro_build_asm_ffi_dynamic_runtime_surface",
)
VERDICT_KEYS = {
    "schema", "goal_id", "gate", "checker", "repository_id", "acceptance_run_id",
    "checker_sha256", "evidence_sha256", "source_revision", "toolchain_sha256",
    "corpus_manifest_sha256", "subject_graph_sha256", "linked_module_sha256",
    "release_artifact_sha256", "authority_policy_sha256",
    "policy_authorization_sha256", "prior_gates_root", "passed", "checks",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class Fixture:
    def __init__(
        self, *, baseline_status: str = "compatible", active_exception: bool = False,
        object_format: str = "sha1", missing_upstream: bool = False,
        exception_status: str | None = None,
        surface_exception: tuple[str, str] | None = None,
        overrides: dict[str, bytes] | None = None,
    ) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="trust-g1-control-")
        self.root = Path(self.tmp.name)
        init_args = ("init", "-q", "--object-format=sha256") if object_format == "sha256" else ("init", "-q")
        self.git(*init_args)
        self.git("config", "user.email", "g1@example.invalid")
        self.git("config", "user.name", "G1 Test")
        self.write("tests/ui/a.rs", b"fn main() {}\n")
        self.write("tests/ui/b.rs", b"fn main() { let _ = 1; }\n")
        self.git("add", "tests")
        self.git("commit", "-qm", "upstream test tree")
        self.upstream = self.git("rev-parse", "HEAD").strip()
        tree = self.git("rev-parse", f"{self.upstream}^{{tree}}").strip()
        self.tree_sha = sha(self.git_bytes("cat-file", "tree", tree))
        self.test_files = self.git("ls-tree", "-rz", "--name-only", self.upstream,
                                   "--", "tests").split("\0")[:-1]
        if missing_upstream:
            self.upstream = "f" * len(self.upstream)
        baseline = (
            'schema_version = "0.1.0"\n'
            '[upstream]\n'
            'channel = "nightly"\n'
            f'revision = "rust-lang/rust:{self.upstream}"\n'
            'snapshot_date = "2026-09-23"\n'
            '[[entries]]\n'
            'id = "toolchain.rustc"\n'
            f'status = "{baseline_status}"\n'
        )
        self.write("tests/upstream-rust/baseline.toml", baseline.encode())
        self.write("release/trust-version.toml", (
            '[rust_alignment]\n'
            f'revision = "rust-lang/rust:{self.upstream}"\n'
        ).encode())
        ledger = 'schema_version = "0.1.0"\nexceptions = []\n'
        if active_exception:
            exception_status = "active"
        if exception_status is not None:
            ledger = (
                'schema_version = "0.1.0"\n'
                '[[exceptions]]\n'
                'id = "unwaived"\n'
                f'status = "{exception_status}"\n'
                'kind = "expected_fail"\n'
            )
        self.write("tests/upstream-rust/test-exceptions.toml", ledger.encode())
        # The surface-level CompatibilityException ledger (model.rs ExceptionLedger).
        surface = 'schema_version = "0.1.0"\nexceptions = []\n'
        if surface_exception is not None:
            surface_class, surface_status = surface_exception
            surface = (
                'schema_version = "0.1.0"\n'
                '[[exceptions]]\n'
                'id = "surface-waiver"\n'
                'baseline_entry_id = "toolchain.rustc"\n'
                'title = "surface waiver"\n'
                f'class = "{surface_class}"\n'
                f'status = "{surface_status}"\n'
                'owner = "g1"\n'
                'reason = "control"\n'
            )
        self.write("tests/upstream-rust/exceptions.toml", surface.encode())
        # Committed replacements for the default ledgers, keyed by path; each
        # value may name the upstream pin as {upstream}.
        for relative, data in (overrides or {}).items():
            self.write(relative, data.replace(b"{upstream}", self.upstream.encode()))
        self.write("cases/accept.rs", b"fn main() {}\n")
        self.write("cases/reject.rs", b"not rust\n")
        self.git("add", ".")
        self.git("commit", "-qm", "candidate source")
        self.revision = self.git("rev-parse", "HEAD").strip()
        self.entries = [
            {"id": "case.accept", "kind": "rust-source", "admitted": True,
             "source": self.reference("cases/accept.rs"), "expected_outcome": "accept"},
            {"id": "case.reject", "kind": "rust-source", "admitted": False,
             "source": self.reference("cases/reject.rs"), "expected_outcome": "reject"},
        ]
        self.observation = {
            "schema": "trust.two-language.g1.rust-observation/v1",
            "source_revision": self.revision,
            "upstream_revision": self.upstream,
            "admitted_entry_ids": ["case.accept"],
            "upstream_test_files": self.test_files,
            "reachable_bodies": [{"program_id": "program", "body_id": "body.main",
                                  "function_identity_sha256": IDENTITY}],
            "suite_results": [
                {"entry_id": "case.accept", "observed_outcome": "accept"},
                {"entry_id": "case.reject", "observed_outcome": "reject"},
            ],
            "features": [{"id": name, "outcome": "covered"} for name in FEATURES],
            "unmeasured": [],
        }
        self.setup_inputs()

    def close(self) -> None:
        self.tmp.cleanup()

    def git_bytes(self, *args: str) -> bytes:
        result = subprocess.run(["git", *args], cwd=self.root, check=True,
                                capture_output=True)
        return result.stdout

    def git(self, *args: str) -> str:
        return self.git_bytes(*args).decode().strip()

    def write(self, relative: str, data: bytes) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def document(self, relative: str, value: dict) -> dict[str, str]:
        self.write(relative, json.dumps(value, sort_keys=True).encode())
        return self.reference(relative)

    def reference(self, relative: str) -> dict[str, str]:
        return {"path": relative, "sha256": sha((self.root / relative).read_bytes())}

    def setup_inputs(self) -> None:
        feature_ref = self.document("evidence/features.json", {
            "schema": "trust.two-language.language-feature-manifest/v1",
            "lane": "rust", "features": FEATURES,
        })
        suite_ref = self.document("evidence/suite.json", {
            "schema": "trust.two-language.suite-manifest/v1",
            "lane": "rust", "cases": ["case.accept", "case.reject"],
        })
        exception_ref = self.document("evidence/exceptions.json", {
            "schema": "trust.two-language.exception-ledger/v1",
            "lane": "rust", "rows": [],
        })
        admission_ref = self.document("evidence/admission.json", {
            "schema": "trust.two-language.admission-contract/v1",
            "goal_id": GOAL, "repository_id": REPOSITORY,
            "lanes": {
                "rust": {
                    "upstream_repository": "https://github.com/rust-lang/rust",
                    "upstream_revision": self.upstream,
                    "upstream_tree_sha256": self.tree_sha,
                    "feature_manifest": feature_ref, "suite_manifest": suite_ref,
                    "exception_ledger": exception_ref, "entries": self.entries,
                },
                "lean": {}, "mixed": {},
            },
        })
        self.admission_ref = admission_ref
        self.policy = {
            "schema": "trust.two-language.authority-policy/v2",
            "goal_id": GOAL, "repository_id": REPOSITORY,
            "authorized_source_revision": self.revision,
            "authorized_acceptance_run_id": RUN,
            "contracts": {
                "admission": {"id": "trust.two-language.contract.admission", **admission_ref},
                "semantics": {}, "obligations": {}, "proof_authority": {},
                "compatibility_surfaces": {}, "codegen_surface": {},
                "acceptance_environment": {},
            },
        }
        self.document("evidence/policy.json", self.policy)
        self.corpus = {
            "rust": {
                "upstream_revision": self.upstream,
                "admission_policy_sha256": admission_ref["sha256"],
                "entries": self.entries,
            },
        }
        self.document("evidence/corpus.json", self.corpus)
        self.graph = {
            "programs": [{
                "id": "program", "admitted_file_ids": ["case.accept"],
                "bodies": [{"id": "body.main", "language": "rust",
                            "function_identity_sha256": IDENTITY}],
            }],
        }
        self.document("evidence/graph.json", self.graph)
        for name in ("toolchain", "release", "policy-auth"):
            self.document(f"evidence/{name}.json", {})
        self.write("evidence/linked.bin", b"linked-ir")
        self.document("evidence/observation.json", self.observation)
        self.write("checker.py", CHECKER.read_bytes())
        self.make_bundle()

    def make_bundle(self) -> None:
        refs = {check_id: self.reference("evidence/observation.json")
                for check_id in REQUIRED}
        refs["pinned_upstream_rust_revision"] = self.reference(
            "tests/upstream-rust/baseline.toml")
        refs["non_applicable_rust_harness_rows_only"] = self.reference(
            "tests/upstream-rust/test-exceptions.toml")
        self.bundle = {
            "schema": "trust.two-language.gate-evidence/v1",
            "gate": "G1", "checker": "trust.two-language.g1.rust-input/v2",
            "artifacts": refs,
        }
        self.document("evidence/bundle.json", self.bundle)

    def run(
        self, *, extra: list[str] | None = None, env_extra: dict[str, str] | None = None,
    ) -> tuple[int, dict, str]:
        files = {
            "--verify-evidence": "evidence/bundle.json",
            "--toolchain-manifest": "evidence/toolchain.json",
            "--corpus-manifest": "evidence/corpus.json",
            "--subject-graph": "evidence/graph.json",
            "--linked-module": "evidence/linked.bin",
            "--release-artifact": "evidence/release.json",
            "--authority-policy": "evidence/policy.json",
            "--policy-authorization": "evidence/policy-auth.json",
        }
        names = {
            "--verify-evidence": "--evidence-sha256",
            "--toolchain-manifest": "--toolchain-sha256",
            "--corpus-manifest": "--corpus-manifest-sha256",
            "--subject-graph": "--subject-graph-sha256",
            "--linked-module": "--linked-module-sha256",
            "--release-artifact": "--release-artifact-sha256",
            "--authority-policy": "--authority-policy-sha256",
            "--policy-authorization": "--policy-authorization-sha256",
        }
        command = [sys.executable, "-I", str(self.root / "checker.py"),
                   "--root", str(self.root), "--acceptance-run-id", RUN,
                   "--source-revision", self.revision,
                   "--checker-sha256", sha((self.root / "checker.py").read_bytes())]
        for flag, relative in files.items():
            command.extend([flag, str(self.root / relative), names[flag],
                            sha((self.root / relative).read_bytes())])
        command.extend(extra or [])
        env = {"HOME": str(self.root), "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
               "PATH": "/usr/bin:/bin", "PYTHONHASHSEED": "0", "TZ": "UTC"}
        env.update(env_extra or {})
        result = subprocess.run(command, cwd=self.root, env=env, check=False,
                                capture_output=True, text=True, timeout=30)
        return result.returncode, json.loads(result.stdout), result.stderr


class G1CheckerTest(unittest.TestCase):
    def setUp(self) -> None:
        self.fx = Fixture()

    def tearDown(self) -> None:
        self.fx.close()

    def assert_red(
        self, *, diagnostic: str | None = None, env_extra: dict[str, str] | None = None,
    ) -> dict[str, bool]:
        code, verdict, stderr = self.fx.run(env_extra=env_extra)
        self.assertEqual(code, 1, stderr)
        self.assertFalse(verdict["passed"])
        self.assertEqual(set(verdict), VERDICT_KEYS)
        self.assertEqual(tuple(row["id"] for row in verdict["checks"]), REQUIRED)
        if diagnostic:
            self.assertIn(diagnostic, stderr)
        return {row["id"]: row["passed"] for row in verdict["checks"]}

    def test_exact_structural_observation_cannot_mint_g1_pass(self) -> None:
        checks = self.assert_red(diagnostic="self-authored")
        self.assertTrue(checks["pinned_upstream_rust_revision"])
        self.assertTrue(checks["non_applicable_rust_harness_rows_only"])
        self.assertFalse(any(checks[name] for name in REQUIRED if name not in (
            "pinned_upstream_rust_revision", "non_applicable_rust_harness_rows_only")))

    def test_sha256_git_revision_and_blob_oids_are_accepted(self) -> None:
        self.fx.close()
        self.fx = Fixture(object_format="sha256")
        self.assertEqual(len(self.fx.revision), 64)
        self.assertEqual(len(self.fx.upstream), 64)
        checks = self.assert_red(diagnostic="self-authored")
        self.assertTrue(checks["pinned_upstream_rust_revision"])
        self.assertTrue(checks["non_applicable_rust_harness_rows_only"])

    def test_missing_pinned_upstream_object_is_explicit_refusal(self) -> None:
        self.fx.close()
        self.fx = Fixture(missing_upstream=True)
        checks = self.assert_red(diagnostic="pinned upstream Rust commit object is unavailable locally")
        self.assertFalse(checks["pinned_upstream_rust_revision"])

    def test_missing_pinned_test_file_refuses_observation(self) -> None:
        self.fx.observation["upstream_test_files"].pop()
        self.fx.document("evidence/observation.json", self.fx.observation)
        self.fx.make_bundle()
        checks = self.assert_red(diagnostic="omit or add pinned Git-tree files")
        self.assertFalse(checks["full_upstream_rust_surface"])

    def test_missing_recorded_rust_body_refuses_observation(self) -> None:
        self.fx.observation["reachable_bodies"] = []
        self.fx.document("evidence/observation.json", self.fx.observation)
        self.fx.make_bundle()
        self.assert_red(diagnostic="differ from subject-graph rows")

    def test_missing_owner_feature_refuses_observation(self) -> None:
        self.fx.observation["features"].pop()
        self.fx.document("evidence/observation.json", self.fx.observation)
        self.fx.make_bundle()
        self.assert_red(diagnostic="omit or add owner features")

    def test_unknown_outcome_and_self_authored_counter_refuse(self) -> None:
        self.fx.observation["suite_results"][0]["observed_outcome"] = "unknown"
        self.fx.document("evidence/observation.json", self.fx.observation)
        self.fx.make_bundle()
        self.assert_red(diagnostic="unknown or partial outcome")
        self.fx.observation["suite_results"][0]["observed_outcome"] = "accept"
        self.fx.observation["passed_count"] = 2
        self.fx.document("evidence/observation.json", self.fx.observation)
        self.fx.make_bundle()
        self.assert_red(diagnostic="expected exactly")

    def test_corpus_denominator_cannot_omit_owner_entry(self) -> None:
        self.fx.corpus["rust"]["entries"] = self.fx.entries[:1]
        self.fx.document("evidence/corpus.json", self.fx.corpus)
        checks = self.assert_red(diagnostic="differs from owner admission")
        self.assertFalse(checks["pinned_upstream_rust_revision"])

    def test_tree_digest_must_bind_actual_pinned_git_tree(self) -> None:
        admission = json.loads((self.fx.root / "evidence/admission.json").read_text())
        admission["lanes"]["rust"]["upstream_tree_sha256"] = "0" * 64
        ref = self.fx.document("evidence/admission.json", admission)
        self.fx.policy["contracts"]["admission"]["sha256"] = ref["sha256"]
        self.fx.document("evidence/policy.json", self.fx.policy)
        self.fx.corpus["rust"]["admission_policy_sha256"] = ref["sha256"]
        self.fx.document("evidence/corpus.json", self.fx.corpus)
        self.assert_red(diagnostic="differs from the pinned Git tree object")

    def test_dirty_tracked_baseline_is_not_the_pin(self) -> None:
        path = self.fx.root / "tests/upstream-rust/baseline.toml"
        path.write_bytes(path.read_bytes().replace(b"compatible", b"unknown"))
        self.fx.make_bundle()
        self.assert_red(diagnostic="on-disk bytes differ from accepted revision")

    def test_observation_digest_must_match_bundle(self) -> None:
        self.fx.observation["unmeasured"] = ["foreign-calls"]
        self.fx.document("evidence/observation.json", self.fx.observation)
        self.assert_red(diagnostic="SHA-256 mismatch")

    def test_policy_run_identity_must_match(self) -> None:
        self.fx.policy["authorized_acceptance_run_id"] = "c" * 64
        self.fx.document("evidence/policy.json", self.fx.policy)
        self.assert_red(diagnostic="wrong schema, repository, source, or run identity")

    def test_active_test_exception_refuses(self) -> None:
        self.fx.close()
        self.fx = Fixture(active_exception=True)
        checks = self.assert_red(diagnostic="active upstream Rust test exception")
        self.assertFalse(checks["non_applicable_rust_harness_rows_only"])

    def substitute_clean_ledger(self) -> tuple[str, str]:
        """Commit a clean test-exception ledger, then rewind HEAD past it.

        Returns (HEAD, substitute commit). The worktree keeps the clean bytes,
        so only the Git object HEAD names still holds the active row.
        """
        ledger = "tests/upstream-rust/test-exceptions.toml"
        clean = b'schema_version = "0.1.0"\nexceptions = []\n'
        head = self.fx.revision
        self.fx.write(ledger, clean)
        self.fx.git("add", ledger)
        self.fx.git("commit", "-qm", "substitute")
        substitute = self.fx.git("rev-parse", "HEAD")
        self.fx.git("reset", "-q", "--hard", "HEAD~1")
        self.fx.write(ledger, clean)
        return head, substitute

    def test_replace_ref_substituting_the_ledger_is_refused_by_name(self) -> None:
        # Measured green lie: refs/replace/<HEAD> pointing at a commit whose
        # ledger is clean made the non-applicable row pass while HEAD was
        # unchanged and status clean, though HEAD's ledger holds an active row.
        self.fx.close()
        self.fx = Fixture(active_exception=True)
        head, substitute = self.substitute_clean_ledger()
        ledger = "tests/upstream-rust/test-exceptions.toml"
        blob = self.fx.git("hash-object", ledger)
        self.fx.git("update-index", "--cacheinfo", f"100644,{blob},{ledger}")
        self.fx.git("update-ref", f"refs/replace/{head}", substitute)
        self.fx.make_bundle()
        self.assertEqual(self.fx.git("rev-parse", "HEAD"), head)
        self.assertEqual(self.fx.git("status", "--porcelain", "--untracked-files=no"), "")
        checks = self.assert_red(diagnostic="refs/replace/* object substitutions")
        self.assertFalse(checks["non_applicable_rust_harness_rows_only"])
        self.assertFalse(checks["pinned_upstream_rust_revision"])

    def test_git_environment_cannot_redirect_the_tree_read(self) -> None:
        # A GIT_DIR naming another repository (here a bare clone carrying the
        # replacement) must not reach the checker's Git calls.
        self.fx.close()
        self.fx = Fixture(active_exception=True)
        head, substitute = self.substitute_clean_ledger()
        with tempfile.TemporaryDirectory(prefix="trust-g1-shadow-") as tmp:
            shadow = Path(tmp) / "shadow.git"
            subprocess.run(["git", "clone", "-q", "--bare", str(self.fx.root), str(shadow)],
                           check=True, capture_output=True)
            branch = subprocess.run(["git", "-C", str(shadow), "symbolic-ref", "HEAD"],
                                    check=True, capture_output=True, text=True).stdout.strip()
            for argv in (("update-ref", branch, head),
                         ("update-ref", f"refs/replace/{head}", substitute)):
                subprocess.run(["git", "-C", str(shadow), *argv], check=True, capture_output=True)
            self.fx.make_bundle()
            checks = self.assert_red(diagnostic="on-disk bytes differ from accepted revision",
                                     env_extra={"GIT_DIR": str(shadow)})
        self.assertFalse(checks["non_applicable_rust_harness_rows_only"])

    def test_every_git_call_is_hardened_and_git_env_free(self) -> None:
        spec = importlib.util.spec_from_file_location("g1_checker_git", CHECKER)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        holder = mock.Mock(root=self.fx.root)
        seen = []

        def fake_run(argv, **kwargs):
            seen.append((argv, kwargs.get("env")))
            return subprocess.CompletedProcess(argv, 0, b"", b"")

        with mock.patch.dict(os.environ, {"GIT_DIR": "/nonexistent", "GIT_CONFIG_COUNT": "0"}), \
                mock.patch.object(module.subprocess, "run", side_effect=fake_run):
            module.Context.git(holder, "rev-parse", "HEAD")
        argv, env = seen[0]
        self.assertEqual(argv[:5], ["git", "--no-replace-objects", "--no-optional-locks",
                                    "-c", "core.fsmonitor=false"])
        self.assertIsNotNone(env)
        # Every caller GIT_* variable is gone; only the neutralizers remain.
        self.assertEqual({key: value for key, value in env.items() if key.startswith("GIT_")}, {
            "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_ATTR_NOSYSTEM": "1", "GIT_NO_LAZY_FETCH": "1",
        })
        self.assertEqual(env.get("XDG_CONFIG_HOME"), os.devnull)

    def marker_program(self, directory: Path) -> tuple[Path, Path]:
        marker = directory / "marker"
        program = directory / "program.sh"
        program.write_text(f"#!/bin/sh\necho ran \"$@\" >> '{marker}'\nexit 1\n")
        program.chmod(0o755)
        return program, marker

    def test_promisor_remote_program_does_not_run_on_a_direct_g1_run(self) -> None:
        # Measured: with a repo-local promisor remote whose uploadpack names a
        # program, G1's own `cat-file -t <missing upstream>` started a lazy
        # fetch that ran it -- even with GIT_NO_LAZY_FETCH=1 exported, which
        # the GIT_* strip dropped. The checker ran directly, not via the runner.
        self.fx.close()
        self.fx = Fixture(missing_upstream=True)
        with tempfile.TemporaryDirectory(prefix="trust-g1-promisor-") as tmp:
            program, marker = self.marker_program(Path(tmp))
            other = Path(tmp) / "other.git"
            subprocess.run(["git", "init", "-q", "--bare", str(other)], check=True,
                           capture_output=True)
            for key, value in (("core.repositoryformatversion", "1"),
                               ("extensions.partialClone", "origin"),
                               ("remote.origin.url", str(other)),
                               ("remote.origin.promisor", "true"),
                               ("remote.origin.uploadpack", str(program))):
                self.fx.git("config", key, value)
            for env_extra in (None, {"GIT_NO_LAZY_FETCH": "1"}):
                checks = self.assert_red(
                    diagnostic="pinned upstream Rust commit object is unavailable locally",
                    env_extra=env_extra,
                )
                self.assertFalse(checks["pinned_upstream_rust_revision"])
                self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "")

    def test_fsmonitor_hook_does_not_run_through_g1_git(self) -> None:
        # No G1 command reads the index today, so the full run is a control;
        # the direct Context.git call proves an index read through G1's Git
        # wrapper cannot reach a repo-local core.fsmonitor hook either.
        with tempfile.TemporaryDirectory(prefix="trust-g1-fsmonitor-") as tmp:
            program, marker = self.marker_program(Path(tmp))
            self.fx.git("config", "core.fsmonitor", str(program))
            self.assert_red(diagnostic="self-authored")
            self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "")
            spec = importlib.util.spec_from_file_location("g1_checker_fsmonitor", CHECKER)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            holder = mock.Mock(root=self.fx.root)
            module.Context.git(holder, "status", "--porcelain")
            self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "")

    def test_active_surface_exception_refuses_regardless_of_class(self) -> None:
        # Measured green lie: an active platform_gap row in exceptions.toml left
        # the non-applicable row green.
        for surface_class in ("platform_gap", "intentional_divergence"):
            self.fx.close()
            self.fx = Fixture(surface_exception=(surface_class, "active"))
            checks = self.assert_red(diagnostic="active upstream Rust surface exception")
            self.assertFalse(checks["non_applicable_rust_harness_rows_only"])
            self.assertTrue(checks["pinned_upstream_rust_revision"])

    def test_unknown_surface_exception_status_refuses(self) -> None:
        self.fx.close()
        self.fx = Fixture(surface_exception=("platform_gap", "superseded"))
        checks = self.assert_red(diagnostic="unknown upstream Rust surface-exception status")
        self.assertFalse(checks["non_applicable_rust_harness_rows_only"])

    def test_expired_surface_exception_is_not_retired(self) -> None:
        self.fx.close()
        self.fx = Fixture(surface_exception=("platform_gap", "expired"))
        checks = self.assert_red(diagnostic="expired upstream Rust surface exception")
        self.assertFalse(checks["non_applicable_rust_harness_rows_only"])

    def test_retired_surface_exception_is_bound_into_row_artifacts(self) -> None:
        self.fx.close()
        self.fx = Fixture(surface_exception=("platform_gap", "resolved"))
        code, verdict, stderr = self.fx.run()
        self.assertEqual(code, 1, stderr)
        row = next(row for row in verdict["checks"]
                   if row["id"] == "non_applicable_rust_harness_rows_only")
        self.assertTrue(row["passed"], stderr)
        self.assertIn(self.fx.reference("tests/upstream-rust/exceptions.toml"), row["artifacts"])

    def test_test_exception_status_outside_the_rust_model_refuses(self) -> None:
        # `superseded` is a Lean-ledger status; model.rs ExceptionStatus has
        # only active/expired/resolved, and an expired row stays refused.
        for status, diagnostic in (
            ("superseded", "unknown upstream Rust test-exception status"),
            ("expired", "expired upstream Rust test exception"),
        ):
            self.fx.close()
            self.fx = Fixture(exception_status=status)
            checks = self.assert_red(diagnostic=diagnostic)
            self.assertFalse(checks["non_applicable_rust_harness_rows_only"])

    def test_unknown_baseline_status_refuses_full_surface(self) -> None:
        self.fx.close()
        self.fx = Fixture(baseline_status="unknown")
        checks = self.assert_red(diagnostic="unknown or non-compatible surfaces")
        self.assertTrue(checks["pinned_upstream_rust_revision"])

    def test_bundle_unknown_id_and_g8_inputs_refuse(self) -> None:
        self.fx.bundle["artifacts"]["unknown"] = self.fx.reference("evidence/observation.json")
        self.fx.document("evidence/bundle.json", self.fx.bundle)
        self.assert_red(diagnostic="G1 evidence artifacts")
        self.fx.make_bundle()
        code, verdict, stderr = self.fx.run(extra=["--receipt", str(self.fx.root / "receipt.json")])
        self.assertEqual(code, 1, stderr)
        self.assertFalse(verdict["passed"])
        self.assertIn("G8-only", stderr)

    def assert_ledger_refused(
        self, relative: str, data: bytes, row: str, diagnostic: str,
    ) -> dict[str, bool]:
        self.fx.close()
        self.fx = Fixture(overrides={relative: data})
        checks = self.assert_red(diagnostic=diagnostic)
        self.assertFalse(checks[row], relative)
        return checks

    def test_non_toml_line_break_in_a_comment_cannot_hide_a_ledger_key(self) -> None:
        # Measured green lie: str.splitlines broke a comment at U+2028, so G1
        # read `status = "resolved"` plus a [[shadow]] table swallowing the
        # real key, while tomllib (and the toml crate) read one comment line
        # and status = "active". The same trick pinned another revision in
        # baseline.toml / trust-version.toml while G1 read the owner's pin.
        # A lone CR and FF/VT/FS are not TOML line ends at all.
        diagnostic = "non-TOML line break"
        other = "rust-lang/rust:" + "0" * 40
        for sep in ("\u2028", "\u2029", "\x85", "\r", "\x0c", "\x0b", "\x1c"):
            with self.subTest(sep=repr(sep)):
                self.assert_ledger_refused(
                    "tests/upstream-rust/test-exceptions.toml",
                    ('schema_version = "0.1.0"\n[[exceptions]]\nid = "unwaived"\n'
                     'kind = "expected_fail"\n'
                     f'# c{sep}status = "resolved"{sep}[[shadow]]\n'
                     'status = "active"\n').encode(),
                    "non_applicable_rust_harness_rows_only", diagnostic,
                )
                self.assert_ledger_refused(
                    "tests/upstream-rust/exceptions.toml",
                    ('schema_version = "0.1.0"\n[[exceptions]]\nid = "surface-waiver"\n'
                     'class = "platform_gap"\n'
                     f'# c{sep}status = "resolved"{sep}[[shadow]]\n'
                     'status = "active"\n').encode(),
                    "non_applicable_rust_harness_rows_only", diagnostic,
                )
                self.assert_ledger_refused(
                    "tests/upstream-rust/baseline.toml",
                    ('schema_version = "0.1.0"\n[upstream]\nchannel = "nightly"\n'
                     'snapshot_date = "2026-09-23"\n'
                     f'# c{sep}revision = "rust-lang/rust:{{upstream}}"{sep}[shadow]\n'
                     f'revision = "{other}"\n'
                     '[[entries]]\nid = "toolchain.rustc"\nstatus = "compatible"\n').encode(),
                    "pinned_upstream_rust_revision", diagnostic,
                )
                self.assert_ledger_refused(
                    "release/trust-version.toml",
                    ('[rust_alignment]\n'
                     f'# c{sep}revision = "rust-lang/rust:{{upstream}}"{sep}[shadow]\n'
                     f'revision = "{other}"\n').encode(),
                    "pinned_upstream_rust_revision", diagnostic,
                )

    def test_crlf_ledger_lines_still_parse(self) -> None:
        # Control: CRLF is a TOML line end, so a CRLF ledger keeps both rows.
        crlf = b'schema_version = "0.1.0"\r\nexceptions = []\r\n'
        self.fx.close()
        self.fx = Fixture(overrides={"tests/upstream-rust/test-exceptions.toml": crlf,
                                     "tests/upstream-rust/exceptions.toml": crlf})
        checks = self.assert_red(diagnostic="self-authored")
        self.assertTrue(checks["non_applicable_rust_harness_rows_only"])
        self.assertTrue(checks["pinned_upstream_rust_revision"])

    def test_deeply_nested_ledger_array_is_a_refusal_not_a_crash(self) -> None:
        # Measured: ~1200 nested arrays raised RecursionError past main()'s
        # handlers, so the checker printed no JSON verdict at all.
        depth = 1200
        self.assert_ledger_refused(
            "tests/upstream-rust/test-exceptions.toml",
            ('schema_version = "0.1.0"\n'
             f'deep = {"[" * depth}{"]" * depth}\n'
             'exceptions = []\n').encode(),
            "non_applicable_rust_harness_rows_only", "TOML array nesting exceeds",
        )

    def test_overlong_ledger_integer_is_a_refusal_not_a_crash(self) -> None:
        # Measured: a 5000-digit integer made int() raise ValueError under the
        # int max-str-digits limit (3.11+), so no JSON verdict was printed;
        # interpreters without the limit accepted it. TOML integers are i64.
        for raw, diagnostic in (
            ("1" + "0" * 4999, "value outside the supported TOML subset"),
            (str(2 ** 63), "TOML integer outside the 64-bit range"),
            (str(-(2 ** 63) - 1), "TOML integer outside the 64-bit range"),
        ):
            with self.subTest(raw=raw[:24]):
                self.assert_ledger_refused(
                    "tests/upstream-rust/test-exceptions.toml",
                    f'schema_version = "0.1.0"\nbig = {raw}\nexceptions = []\n'.encode(),
                    "non_applicable_rust_harness_rows_only", diagnostic,
                )

    def test_real_pinned_toml_ledgers_fit_the_refusing_subset(self) -> None:
        spec = importlib.util.spec_from_file_location("g1_checker_subset", CHECKER)
        self.assertIsNotNone(spec)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        baseline = module.toml_subset(
            (ROOT / "tests/upstream-rust/baseline.toml").read_bytes(), "baseline"
        )
        exceptions = module.toml_subset(
            (ROOT / "tests/upstream-rust/test-exceptions.toml").read_bytes(), "exceptions"
        )
        surface = module.toml_subset(
            (ROOT / "tests/upstream-rust/exceptions.toml").read_bytes(), "surface"
        )
        version = module.toml_subset(
            (ROOT / "release/trust-version.toml").read_bytes(), "version"
        )
        self.assertTrue(version["rust_alignment"]["revision"].startswith("rust-lang/rust:"))
        self.assertTrue(baseline["entries"])
        self.assertIsInstance(exceptions.get("exceptions", []), list)
        self.assertEqual(surface.get("schema_version"), "0.1.0")
        self.assertIsInstance(surface.get("exceptions", []), list)
        self.assertTrue(all(row.get("status") in module.EXCEPTION_STATUSES
                            for row in surface.get("exceptions", [])))


class G1RunnerIntegrationTest(unittest.TestCase):
    def test_signed_runner_executes_real_g1_and_invalid_owner_key_blocks_it(self) -> None:
        from scripts.tests import two_language_completion_gate_test as runner_test

        source = runner_test.checker_source

        def with_real_g1(gate_id: str) -> str:
            return CHECKER.read_text(encoding="utf-8") if gate_id == "G1" else source(gate_id)

        with tempfile.TemporaryDirectory(prefix="trust-g1-signed-runner-") as tmp:
            with mock.patch.object(runner_test, "checker_source", side_effect=with_real_g1):
                fixture = runner_test.GreenReceipt(Path(tmp))
            checker_path = fixture.root / runner_test.gate.CHECKER_PATHS["G1"]
            self.assertEqual(checker_path.read_bytes(), CHECKER.read_bytes())
            policy = json.loads(fixture.policy.read_text(encoding="utf-8"))
            self.assertEqual(policy["authorized_checkers"]["G1"]["sha256"], sha(CHECKER.read_bytes()))

            evidence = json.loads(fixture.evidence_path("G1").read_text(encoding="utf-8"))
            evidence["schema"] = "trust.two-language.gate-evidence/v1"
            fixture.rewrite_evidence("G1", evidence)
            signed = runner_test.gate.validate_receipt(
                fixture.path, fixture.root, fixture.owner_public
            )
            self.assertFalse(signed["accepted"])
            self.assertFalse(signed["gate_results"]["G1"])
            self.assertTrue(any(
                "owner Rust upstream repository is not rust-lang/rust" in error
                for error in signed["errors"]
            ), signed["errors"])
            self.assertFalse(any(
                "policy_authorization" in error for error in signed["errors"]
            ), signed["errors"])

            wrong_private = Path(tmp) / "wrong-owner"
            subprocess.run(
                [str(runner_test.gate.SSH_KEYGEN), "-q", "-t", "ed25519", "-N", "",
                 "-f", str(wrong_private)],
                check=True, capture_output=True,
            )
            invalid = runner_test.gate.validate_receipt(
                fixture.path, fixture.root, Path(f"{wrong_private}.pub")
            )
            self.assertFalse(invalid["accepted"])
            self.assertTrue(any(
                "policy_authorization" in error for error in invalid["errors"]
            ), invalid["errors"])
            self.assertFalse(any(
                "owner Rust upstream repository is not rust-lang/rust" in error
                for error in invalid["errors"]
            ), invalid["errors"])


if __name__ == "__main__":
    unittest.main()
