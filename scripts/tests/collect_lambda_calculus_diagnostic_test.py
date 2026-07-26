#!/usr/bin/env python3
"""Fake-tool tests for the one-crate downstream diagnostic collector."""

from __future__ import annotations

import gzip
import hashlib
import importlib.util
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import textwrap
import time
import unittest
from pathlib import Path
from unittest import mock


REPO = Path(__file__).resolve().parents[2]
COLLECTOR = REPO / "scripts/collect_lambda_calculus_diagnostic.py"
FIXTURE = REPO / "crates/trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0"
OFFICIAL_ARCHIVE_SHA256 = "168030aef659e9a35ba517952982bb0212fda53d531837e3f18c399f9d28dba8"
OFFICIAL_ARCHIVE_URL = (
    "https://static.crates.io/crates/lambda_calculus/lambda_calculus-3.5.0.crate"
)


def load_collector_module() -> object:
    name = "trust_lambda_calculus_diagnostic_under_test"
    specification = importlib.util.spec_from_file_location(name, COLLECTOR)
    if specification is None or specification.loader is None:
        raise AssertionError(f"could not load collector module from {COLLECTOR}")
    module = importlib.util.module_from_spec(specification)
    sys.modules[name] = module
    specification.loader.exec_module(module)
    return module


COLLECTOR_MODULE = load_collector_module()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def executable(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents, encoding="utf-8")
    path.chmod(0o755)


def write_deterministic_source_archive(source: Path, archive: Path) -> None:
    """Create the fake repo's explicit, collector-pinned published archive authority."""
    with archive.open("xb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
            with tarfile.open(fileobj=compressed, mode="w") as package:
                for path in sorted(candidate for candidate in source.rglob("*") if candidate.is_file()):
                    relative = path.relative_to(source).as_posix()
                    contents = path.read_bytes()
                    member = tarfile.TarInfo(f"lambda_calculus-3.5.0/{relative}")
                    member.size = len(contents)
                    member.mode = 0o644
                    member.mtime = 0
                    member.uid = 0
                    member.gid = 0
                    member.uname = ""
                    member.gname = ""
                    package.addfile(member, io.BytesIO(contents))


def source_tree_pin(source: Path) -> dict[str, object]:
    rows = []
    for path in sorted(candidate for candidate in source.rglob("*") if candidate.is_file()):
        contents = path.read_bytes()
        rows.append(
            {
                "path": path.relative_to(source).as_posix(),
                "size": len(contents),
                "sha256": hashlib.sha256(contents).hexdigest(),
            }
        )
    manifest = (
        json.dumps(rows, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n"
    ).encode()
    return {
        "bytes": sum(row["size"] for row in rows),
        "file_count": len(rows),
        "manifest_encoding": "canonical-json-file-rows-v1",
        "manifest_sha256": hashlib.sha256(manifest).hexdigest(),
    }


class DiagnosticFixture:
    def __init__(self, parent: Path, mode: str = "ok") -> None:
        parent = parent.resolve()
        self.repo = parent / "repo"
        self.output = parent / "accepted.json"
        self.repo.mkdir()
        (self.repo / "scripts/tests").mkdir(parents=True)
        fixture = self.repo / "crates/trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0"
        fixture.mkdir(parents=True)
        shutil.copy2(FIXTURE / "regenerate.sh", fixture / "regenerate.sh")
        (fixture / "metadata").mkdir()
        shutil.copy2(FIXTURE / "PROVENANCE.md", fixture / "PROVENANCE.md")
        shutil.copytree(FIXTURE / "SOURCE", fixture / "SOURCE")

        # Integration tests never depend on crates.io availability.  Their copied
        # collector has an explicit test-only checksum/URL authority, while still
        # exercising the production rule that the caller cannot supply the pin.
        self.source_archive = parent / "lambda_calculus-3.5.0.fixture.crate"
        write_deterministic_source_archive(fixture / "SOURCE", self.source_archive)
        fixture_archive_sha256 = sha256(self.source_archive)
        fixture_archive_url = "https://fixture.invalid/lambda_calculus-3.5.0.crate"
        collector_text = COLLECTOR.read_text(encoding="utf-8")
        self._assert_replacement_count(collector_text, OFFICIAL_ARCHIVE_SHA256, 1)
        self._assert_replacement_count(collector_text, OFFICIAL_ARCHIVE_URL, 1)
        collector_text = collector_text.replace(OFFICIAL_ARCHIVE_SHA256, fixture_archive_sha256)
        collector_text = collector_text.replace(OFFICIAL_ARCHIVE_URL, fixture_archive_url)
        (self.repo / "scripts/collect_lambda_calculus_diagnostic.py").write_text(
            collector_text, encoding="utf-8"
        )

        selection = json.loads(
            (FIXTURE / "metadata/source-selection.json").read_text(encoding="utf-8")
        )
        selection["archive"] = {
            "sha256": fixture_archive_sha256,
            "url": fixture_archive_url,
        }
        (fixture / "metadata/source-selection.json").write_text(
            json.dumps(selection, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )
        (self.repo / ".gitignore").write_text("build/\n", encoding="utf-8")
        verifier_exit = 1 if mode == "provenance_failure" else 0
        executable(
            self.repo / "scripts/recreate_bootstrap.py",
            "#!/usr/bin/env python3\n"
            "import sys\n"
            f"print('fixture provenance verifier')\nraise SystemExit({verifier_exit})\n",
        )
        self._git("init", "-q")
        self._git("config", "user.name", "Diagnostic Fixture")
        self._git("config", "user.email", "fixture@example.invalid")
        self._git("add", ".")
        self._git("-c", "commit.gpgsign=false", "commit", "-qm", "fixture")
        self.head = self._git("rev-parse", "HEAD").stdout.strip()
        self.stage = self.repo / "build/test-host/stage2"
        self.bin = self.stage / "bin"
        self.bin.mkdir(parents=True)
        self.identities = self._write_tools(mode)
        self._write_provenance(mode)

    @staticmethod
    def _assert_replacement_count(text: str, needle: str, expected: int) -> None:
        actual = text.count(needle)
        if actual != expected:
            raise AssertionError(f"expected {expected} collector pin occurrence(s), found {actual}")

    def _git(self, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["/usr/bin/git", "-C", str(self.repo), *arguments],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def _write_tools(self, mode: str) -> dict[str, str]:
        trustc_identity = textwrap.dedent(
            f"""\
            rustc 1.99.0-test ({self.head[:9]}) (trustc)
            binary: trustc
            commit-hash: {self.head}
            host: test-host
            release: 1.99.0-test
            """
        ).rstrip()
        targo_identity = textwrap.dedent(
            f"""\
            targo 1.99.0-test ({self.head[:9]})
            binary: targo
            commit-hash: {self.head}
            host: test-host
            release: 1.99.0-test
            """
        ).rstrip()
        extension_identity = textwrap.dedent(
            f"""\
            targo-trust 0.1.0-test
            trust.identity=targo trust
            trust-repo-commit-hash: {self.head}
            """
        ).rstrip()
        daemon_identity = textwrap.dedent(
            f"""\
            trustd 0.1.0-test
            trust.identity=trustd
            trust.protocol=1
            trust-repo-commit-hash: {self.head}
            """
        ).rstrip()

        fake_trustc = textwrap.dedent(
            f'''\
            #!/usr/bin/python3
            import json, pathlib, sys
            MODE = {mode!r}
            IDENTITY = {trustc_identity!r}
            if "-vV" in sys.argv:
                print(IDENTITY)
                raise SystemExit(0)
            dump_arg = next(arg for arg in sys.argv if arg.startswith("-Ztrust-dump=mir:"))
            dump = pathlib.Path(dump_arg.split("=", 1)[1])
            dump.mkdir(parents=True, exist_ok=True)
            if MODE == "compile_failure":
                print("synthetic compiler failure", file=sys.stderr)
                raise SystemExit(7)
            documents = {{
                "term__core.json": {{"def_path": "lambda_calculus::term::core", "body": {{}}}},
                "data__encoded.json": {{"def_path": "lambda_calculus::data::encoded", "body": {{}}}},
            }}
            if MODE == "malformed_dump":
                documents["term__core.json"] = None
            for name, document in documents.items():
                path = dump / name
                path.write_text("{{malformed" if document is None else json.dumps(document))
            output = pathlib.Path(sys.argv[sys.argv.index("-o") + 1])
            output.write_bytes(b"fixture rlib")
            print("fixture compiler stdout")
            print("fixture compiler diagnostic", file=sys.stderr)
            '''
        )
        executable(self.bin / "trustc", fake_trustc)

        fake_targo = textwrap.dedent(
            f'''\
            #!/usr/bin/python3
            import json, pathlib, sys
            MODE = {mode!r}
            IDENTITY = {targo_identity!r}
            if "-vV" in sys.argv:
                print(IDENTITY)
                raise SystemExit(0)
            if sys.argv[1:3] != ["trust", "prove"]:
                raise SystemExit(9)
            dump = pathlib.Path(sys.argv[sys.argv.index("--dump-dir") + 1])
            total = len(list(dump.glob("*.json")))
            if MODE == "wrong_denominator":
                total += 1
            budget = int(next(arg.split("=", 1)[1] for arg in sys.argv
                              if arg.startswith("--budget-secs=")))
            inhabited = int(MODE == "overlapping_proven_declined")
            declined = int(MODE == "overlapping_proven_declined")
            scorecard = {{
                "total": total,
                "inhabited": inhabited,
                "type_grounded_not_inhabited": 0,
                "not_grounded": total - inhabited,
                "fully_faithful": 0,
                "fully_faithful_via_trustir": int(MODE == "bad_fully_faithful_partition"),
                "fully_faithful_mirsem_fallback": 0,
                "safety_vc_faithful": 0,
                "safety_vc_faithful_overflow": 0,
                "safety_vc_faithful_usub": 0,
                "safety_vc_faithful_signed_overflow": 0,
                "safety_vc_faithful_bounds": 0,
                "safety_vc_faithful_div": int(MODE == "bad_safety_subtype"),
                "safety_vc_faithful_rem": 0,
                "safety_vc_faithful_negation": 0,
                "safety_vc_faithful_shift": 0,
                "declined": declined,
                "declined_paths": (["lambda_calculus::term::core"] if declined else []),
                "kernel_rejected": int(MODE == "kernel_rejection"),
                "proven": (["lambda_calculus::term::core"] if inhabited else []),
                "rejections": (["fixture rejection"] if MODE == "kernel_rejection" else []),
                "bridge_agreement": {{"status": "fixture-agreed"}},
                "total_obligations": total,
                "postcondition_obligations": 0,
                "safety_obligations": total,
                "safety_discharged": 0,
                "loop_headers_detected": 0,
                "loop_headers_recognized": 0,
            }}
            print(json.dumps({{
                "schema": "trust.prove-scorecard.v1",
                "status": ("rejected" if MODE == "kernel_rejection" else "measured"),
                "claim_boundary": "fixture",
                "budget_secs_per_function": budget,
                "scorecard": scorecard,
                "bridge_gate_error": None,
            }}))
            raise SystemExit(1 if MODE == "prove_failure" else 0)
            '''
        )
        executable(self.bin / "targo", fake_targo)
        executable(
            self.bin / "targo-trust",
            "#!/usr/bin/python3\n"
            f"print({extension_identity!r})\n",
        )
        executable(
            self.bin / "trustd",
            "#!/usr/bin/python3\n"
            f"print({daemon_identity!r})\n",
        )
        return {
            "trustc": trustc_identity,
            "targo": targo_identity,
            "targo-trust": extension_identity,
            "trustd": daemon_identity,
        }

    def _write_provenance(self, mode: str) -> None:
        rows = []
        for name in ("targo", "targo-trust", "trustd"):
            rows.append(
                {
                    "name": name,
                    "path": f"build/test-host/stage2/bin/{name}",
                    "sha256": sha256(self.bin / name),
                    "status": "bound",
                    "version_probe_ok": True,
                    "version": self.identities[name].splitlines()[0],
                }
            )
        if mode == "missing_trustd_binding":
            rows = [row for row in rows if row["name"] != "trustd"]
        repository_row = {
            "path": ".",
            "head": self.head,
            "has_staged_changes": False,
            "has_unstaged_changes": False,
            "untracked_files": [],
            "conflict_paths": [],
            "assume_unchanged_paths": [],
            "skip_worktree_paths": [],
            "fsmonitor_valid_paths": [],
            "working_tree_mismatch_paths": [],
        }
        receipt = {
            "schema": "trust.stage-tool-provenance.v2",
            "status": "internal-release-ready",
            "stage": 2,
            "host": "test-host",
            "stage_root": "build/test-host/stage2",
            "path_scope": "repository-root-relative",
            "source_tree_clean": True,
            "tool_binding_status": "ready",
            "errors": [],
            "trust_from_trust": True,
            "source_lineage": {
                "schema": "trust.source-lineage.v1",
                "status": "immutable_release",
                "source_tree_clean": True,
                "stable_across_build": True,
                "errors": [],
                "repositories": [repository_row],
            },
            "compiler": {
                "path": "build/test-host/stage2/bin/trustc",
                "compiler_sha256": sha256(self.bin / "trustc"),
                "source_commit": self.head,
                "compiler_verbose": self.identities["trustc"],
            },
            "tools": rows,
        }
        (self.stage / "tool-provenance.json").write_text(
            json.dumps(receipt, sort_keys=True), encoding="utf-8"
        )

    def run(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(self.repo / "scripts/collect_lambda_calculus_diagnostic.py"),
                "--repo-root",
                str(self.repo),
                "--stage2-root",
                str(self.stage),
                "--output",
                str(self.output),
                "--source-archive",
                str(self.source_archive),
                "--source-fetch-timeout-secs",
                "20",
                "--prove-budget-secs",
                "1",
                "--compile-timeout-secs",
                "20",
                "--prove-timeout-secs",
                "20",
                "--provenance-timeout-secs",
                "20",
                "--max-output-bytes",
                "1048576",
            ],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )


class LambdaCalculusDiagnosticTest(unittest.TestCase):
    def test_run_capture_enforces_output_bound_while_child_is_live(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            scratch = Path(temporary).resolve()
            started = time.monotonic()
            with self.assertRaisesRegex(
                COLLECTOR_MODULE.EvidenceError,
                "stdout exceeds the 4096-byte limit",
            ):
                COLLECTOR_MODULE.run_capture(
                    [
                        sys.executable,
                        "-c",
                        "import os; chunk=b'x'*65536\nwhile True: os.write(1, chunk)",
                    ],
                    cwd=scratch,
                    environment=dict(os.environ),
                    scratch=scratch,
                    label="unbounded-output",
                    timeout=20,
                    max_output_bytes=4096,
                )
            self.assertLess(time.monotonic() - started, 5)
            self.assertFalse(list(scratch.glob("unbounded-output.*")))

    def test_dirfd_publication_rejects_ancestor_swap_after_anchor(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            ancestor = root / "anchored"
            parent = ancestor / "evidence"
            parent.mkdir(parents=True)
            output = parent / "receipt.json"
            old = b'{"accepted":"previous"}\n'
            output.write_bytes(old)

            displaced = root / "anchored-before-swap"
            outside = root / "attacker-controlled"
            (outside / "evidence").mkdir(parents=True)
            with COLLECTOR_MODULE.AnchoredOutput(output) as target:
                previous = target.snapshot()
                ancestor.rename(displaced)
                ancestor.symlink_to(outside, target_is_directory=True)

                with self.assertRaisesRegex(
                    COLLECTOR_MODULE.EvidenceError,
                    "output ancestor changed concurrently",
                ):
                    target.publish(b'{"accepted":"replacement"}\n', previous)

            self.assertEqual((displaced / "evidence/receipt.json").read_bytes(), old)
            self.assertFalse((outside / "evidence/receipt.json").exists())

    def test_publication_linearization_does_not_overwrite_a_racing_leaf(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            output = root / "receipt.json"
            old = b'{"accepted":"previous"}\n'
            raced = b'{"writer":"raced"}\n'
            output.write_bytes(old)

            with COLLECTOR_MODULE.AnchoredOutput(output) as target:
                previous = target.snapshot()
                original_rename = COLLECTOR_MODULE.os.rename

                def race_before_capture(*args: object, **kwargs: object) -> None:
                    output.write_bytes(raced)
                    original_rename(*args, **kwargs)

                with mock.patch.object(
                    COLLECTOR_MODULE.os,
                    "rename",
                    side_effect=race_before_capture,
                ):
                    with self.assertRaisesRegex(
                        COLLECTOR_MODULE.EvidenceError,
                        "changed at publication linearization",
                    ):
                        target.publish(b'{"accepted":"replacement"}\n', previous)

            self.assertEqual(output.read_bytes(), raced)
            self.assertFalse(list(root.glob(".trust-receipt-*")))

    def test_success_binds_full_core_transcript_scorecard_and_claim_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            fixture.output.write_bytes(b'{"old":true}\n')
            result = fixture.run()
            self.assertEqual(result.returncode, 0, result.stderr)
            receipt = json.loads(fixture.output.read_text(encoding="utf-8"))
            self.assertEqual(receipt["schema"], "trust.lambda-calculus-downstream-diagnostic.v1")
            self.assertIs(receipt["runner_execution_authenticated"], False)
            self.assertIs(receipt["release_gate_admissible"], False)
            self.assertEqual(receipt["runner_authority"]["scope"], "diagnostic-only")
            self.assertEqual(
                receipt["claim_boundary"]["kind"],
                "one-published-crate-non-representative-diagnostic",
            )
            self.assertEqual(receipt["claim_boundary"]["projects_sampled"], 1)
            self.assertIn("not proof of downstream ecosystem coverage", receipt["claim_boundary"]["non_claims"])
            self.assertEqual(receipt["git"]["head"], fixture.head)
            self.assertIn("core.fsmonitor=false", receipt["git"]["git_config_overrides"])
            self.assertEqual(receipt["stage2"]["provenance"]["document"]["status"], "internal-release-ready")
            self.assertEqual(receipt["collector_python"]["sha256"], sha256(Path(sys.executable).resolve()))
            self.assertEqual(set(receipt["stage2"]["tools"]), {"trustc", "targo", "targo-trust", "trustd"})
            self.assertEqual(receipt["source"]["manifest"]["count"], 46)
            self.assertEqual(receipt["source"]["published_archive"]["status"], "verified")
            self.assertEqual(
                receipt["source"]["published_archive"]["observed_sha256"],
                sha256(fixture.source_archive),
            )
            self.assertEqual(
                receipt["source"]["archive_acquisition"]["kind"],
                "caller-supplied-archive-with-collector-owned-checksum-pin",
            )
            self.assertTrue(receipt["source"]["archive_rechecked_after_measurement"])
            self.assertEqual(receipt["regeneration"]["full_dump_manifest"]["count"], 2)
            self.assertEqual(receipt["regeneration"]["core_dump_manifest"]["count"], 1)
            self.assertEqual(receipt["proof"]["scorecard"]["scorecard"]["total"], 1)
            proof_stdout = receipt["proof"]["capture"]["stdout"]
            self.assertEqual(
                proof_stdout["sha256"],
                hashlib.sha256(proof_stdout["utf8"].encode()).hexdigest(),
            )
            self.assertIn("fixture compiler diagnostic", receipt["regeneration"]["compiler"]["stderr"]["utf8"])
            self.assertEqual(receipt["commands"]["proof"][0], str(fixture.bin / "targo"))

    def test_compiler_failure_preserves_previous_accepted_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary), "compile_failure")
            old = b'{"accepted":"previous"}\n'
            fixture.output.write_bytes(old)
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(fixture.output.read_bytes(), old)
            self.assertIn("FAILED CLOSED", result.stderr)

    def test_proof_denominator_mismatch_preserves_previous_accepted_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary), "wrong_denominator")
            old = b'{"accepted":"previous"}\n'
            fixture.output.write_bytes(old)
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(fixture.output.read_bytes(), old)
            self.assertIn("denominator", result.stderr)

    def test_missing_trustd_provenance_binding_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary), "missing_trustd_binding")
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(fixture.output.exists())
            self.assertIn("trustd", result.stderr)

    def test_source_tree_drift_is_rejected_before_tools_run(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            source = fixture.repo / "crates/trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0/SOURCE/src/lib.rs"
            source.write_text(source.read_text(encoding="utf-8") + "\n", encoding="utf-8")
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(fixture.output.exists())
            self.assertTrue("not clean" in result.stderr or "pinned" in result.stderr)

    def test_clean_modified_source_and_matching_tracked_manifest_is_not_published_source(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            fixture_dir = (
                fixture.repo
                / "crates/trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0"
            )
            source = fixture_dir / "SOURCE"
            lib = source / "src/lib.rs"
            lib.write_text(lib.read_text(encoding="utf-8") + "\n// locally modified\n", encoding="utf-8")
            selection_path = fixture_dir / "metadata/source-selection.json"
            selection = json.loads(selection_path.read_text(encoding="utf-8"))
            selection["source_tree"].update(source_tree_pin(source))
            selection_path.write_text(
                json.dumps(selection, sort_keys=True, indent=2) + "\n", encoding="utf-8"
            )
            fixture._git("add", str(lib.relative_to(fixture.repo)), str(selection_path.relative_to(fixture.repo)))
            fixture._git("-c", "commit.gpgsign=false", "commit", "-qm", "forge adjacent source pin")

            result = fixture.run()

            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(fixture.output.exists())
            self.assertIn("does not exactly match", result.stderr)

    def test_supplied_archive_must_match_collector_owned_checksum_pin(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            fixture.source_archive.write_bytes(b"not the pinned archive")

            result = fixture.run()

            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(fixture.output.exists())
            self.assertIn("collector-owned crates.io checksum pin", result.stderr)

    def test_oversized_supplied_archive_is_rejected_before_hashing(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            with fixture.source_archive.open("wb") as archive:
                archive.truncate(COLLECTOR_MODULE.MAX_ARCHIVE_BYTES + 1)

            result = fixture.run()

            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(fixture.output.exists())
            self.assertIn("outside 1..=", result.stderr)

    def test_fully_faithful_witness_partition_is_enforced(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary), "bad_fully_faithful_partition")
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("fully-faithful witness partition", result.stderr)

    def test_safety_faithfulness_subtype_is_bounded_by_parent(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary), "bad_safety_subtype")
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("safety_vc_faithful_div", result.stderr)

    def test_proven_and_declined_paths_must_be_disjoint(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary), "overlapping_proven_declined")
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("both proven and declined", result.stderr)

    def test_regenerate_output_root_is_non_destructive(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            fixture_dir = fixture.repo / "crates/trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0"
            legacy = fixture_dir / "legacy.json"
            legacy.write_bytes(b'{"tracked":"sentinel"}\n')
            scratch = Path(temporary) / "scratch-output"
            result = subprocess.run(
                [
                    str(fixture_dir / "regenerate.sh"),
                    "--trustc",
                    str(fixture.bin / "trustc"),
                    "--output-root",
                    str(scratch),
                ],
                env={**os.environ, "RUSTFLAGS": "--cfg hostile", "TRUST_DUMP_MIR": "/hostile"},
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(legacy.read_bytes(), b'{"tracked":"sentinel"}\n')
            self.assertEqual(len(list((scratch / "full").glob("*.json"))), 2)
            self.assertEqual(len(list((scratch / "core").glob("*.json"))), 1)
            compiler_environment = (scratch / "compiler.env").read_text(encoding="utf-8")
            self.assertNotIn("RUSTFLAGS", compiler_environment)
            self.assertNotIn("TRUST_DUMP_MIR", compiler_environment)

    def test_regenerate_rejects_ambient_compiler_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            fixture_dir = fixture.repo / "crates/trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0"
            result = subprocess.run(
                [
                    str(fixture_dir / "regenerate.sh"),
                    "--output-root",
                    str(Path(temporary) / "scratch-output"),
                ],
                env={**os.environ, "TRUSTC": "/tmp/ambient-trustc"},
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("ambient TRUSTC is not an authority", result.stderr)

    def test_unignored_in_repository_receipt_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            fixture.output = fixture.repo / "receipt.json"
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(fixture.output.exists())
            self.assertIn("must be Git-ignored", result.stderr)

    def test_tracked_in_repository_output_is_never_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            fixture.output = fixture.repo / ".gitignore"
            original = fixture.output.read_bytes()
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(fixture.output.read_bytes(), original)
            self.assertIn("output is tracked", result.stderr)

    def test_ignored_output_cannot_escape_through_ancestor_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            outside = Path(temporary) / "outside"
            outside.mkdir()
            escape = fixture.repo / "build/escape"
            escape.symlink_to(outside, target_is_directory=True)
            fixture.output = escape / "receipt.json"
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse((outside / "receipt.json").exists())
            self.assertIn("output ancestor must be a real non-symlink directory", result.stderr)

    def test_material_local_exclude_cannot_hide_output_or_source_drift(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            exclude = Path(fixture._git("rev-parse", "--git-path", "info/exclude").stdout.strip())
            if not exclude.is_absolute():
                exclude = fixture.repo / exclude
            exclude.write_text("private-evidence/\n", encoding="utf-8")
            fixture.output = fixture.repo / "private-evidence/receipt.json"
            result = fixture.run()
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(fixture.output.exists())
            self.assertIn("info/exclude contains material rules", result.stderr)

    def test_repo_local_fsmonitor_command_is_not_execution_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            marker = Path(temporary) / "fsmonitor-executed"
            monitor = Path(temporary) / "hostile-fsmonitor"
            executable(
                monitor,
                f"#!/bin/sh\ntouch {str(marker)!r}\nprintf '\\n'\nexit 0\n",
            )
            fixture._git("config", "core.fsmonitor", str(monitor))
            result = fixture.run()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(marker.exists(), "repo-local core.fsmonitor must be disabled")

    def test_ignored_in_repository_receipt_does_not_dirty_exact_head(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            fixture = DiagnosticFixture(Path(temporary))
            fixture.output = fixture.repo / "build/evidence/receipt.json"
            result = fixture.run()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(fixture.output.is_file())
            status = fixture._git(
                "status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"
            ).stdout
            self.assertEqual(status, "")


if __name__ == "__main__":
    unittest.main()
