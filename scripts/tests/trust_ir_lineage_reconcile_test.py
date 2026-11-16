#!/usr/bin/env python3
"""Regression tests for the consumer-side Trust-IR artifact-set reconciler."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import trust_ir_lineage_reconcile as lineage  # noqa: E402


DOMAIN = "trust.thir-lower.artifact.v1"
CRATE = "probe"
LINEAGE = "sha256:" + "a" * 64


def digest(domain: str, payload: bytes) -> str:
    domain_bytes = domain.encode("utf-8")
    framed = (
        b"trust-ir.sha256-domain.v1\0"
        + len(domain_bytes).to_bytes(8, "big")
        + domain_bytes
        + len(payload).to_bytes(8, "big")
        + payload
    )
    return "sha256:" + hashlib.sha256(framed).hexdigest()


class LineagePublicationTest(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.dump = Path(temporary.name)
        self.binary = self.dump / f"{CRATE}.trust-ir.bin"
        self.text = self.dump / f"{CRATE}.trust-ir.txt"
        self.binary.write_bytes(b"TRUST_IR binary fixture")
        # WS5.2: the name is the link-time symbol; the def path is the display path.
        self.text.write_text(
            'rustcc fn @_RNvCs0_5probe1f(functy.0) {\n    ; #display-path: "probe::f"\n}\n',
            encoding="utf-8",
        )
        self.flip_log = self.dump / "flip.log"
        self.flip_log.write_text(
            f"INFO trust-ir-flip: compiled from trust-ir, did=probe::f, "
            f"asserts=0, lineage={LINEAGE}\n",
            encoding="utf-8",
        )
        self.publication = {
            "schema": "trust.thir-lower.artifact-set.v1",
            "digest_algorithm": "sha256-domain-v1",
            "digest_domain": DOMAIN,
            "commit_marker": True,
            "artifacts": [self.artifact(self.binary), self.artifact(self.text)],
        }

    def artifact(self, path: Path, domain: str = DOMAIN) -> dict:
        payload = path.read_bytes()
        return {"name": path.name, "bytes": len(payload), "digest": digest(domain, payload)}

    def reconcile(self, coverage_crate: str = CRATE) -> lineage.Reconciliation:
        coverage = {
            "schema": "trust.thir-lower.crate-module.coverage.v2",
            "crate": coverage_crate,
            "bodies": [
                {"def_path": "probe::f", "kind": "fn", "lineage": LINEAGE, "func_id": 0}
            ],
            "publication": self.publication,
        }
        (self.dump / f"{CRATE}.coverage.json").write_text(
            json.dumps(coverage), encoding="utf-8"
        )
        return lineage.reconcile(self.dump, self.flip_log)

    def test_valid_producer_shape_with_one_flip(self) -> None:
        result = self.reconcile()
        self.assertEqual(result.failures, [])
        self.assertEqual((result.artifacts, result.rows, result.flipped), (2, 1, 1))
        completed = subprocess.run(
            [
                sys.executable,
                str(SCRIPTS / "trust_ir_lineage_reconcile.py"),
                "--dump",
                str(self.dump),
                "--flip-log",
                str(self.flip_log),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)

    def test_unrelated_only_manifest_does_not_attest_a_matching_flip(self) -> None:
        unrelated = self.dump / "unrelated.dat"
        unrelated.write_bytes(b"unrelated but correctly hashed")
        self.publication["artifacts"] = [self.artifact(unrelated)]
        self.binary.unlink()
        result = self.reconcile()
        self.assertEqual(result.flipped, 1)
        self.assertTrue(result.failures, result)
        self.assertTrue(any(self.binary.name in failure for failure in result.failures))
        self.assertTrue(any(self.text.name in failure for failure in result.failures))
        completed = subprocess.run(
            [
                sys.executable,
                str(SCRIPTS / "trust_ir_lineage_reconcile.py"),
                "--dump",
                str(self.dump),
                "--flip-log",
                str(self.flip_log),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 1, completed.stdout)

    def test_each_required_role_must_be_listed_even_if_file_exists(self) -> None:
        required = self.publication["artifacts"]
        for omitted in required:
            with self.subTest(omitted=omitted["name"]):
                self.publication["artifacts"] = [
                    row for row in required if row["name"] != omitted["name"]
                ]
                result = self.reconcile()
                self.assertTrue(
                    any(omitted["name"] in failure for failure in result.failures),
                    result.failures,
                )

    def test_duplicate_and_extra_artifacts_are_rejected(self) -> None:
        required = self.publication["artifacts"]
        unrelated = self.dump / "unrelated.dat"
        unrelated.write_bytes(b"unrelated")
        for added in (required[0], self.artifact(unrelated)):
            with self.subTest(added=added["name"]):
                self.publication["artifacts"] = [*required, added]
                self.assertTrue(self.reconcile().failures)

    def test_substituted_binary_path_is_rejected(self) -> None:
        substitute = self.dump / "other.trust-ir.bin"
        substitute.write_bytes(self.binary.read_bytes())
        self.publication["artifacts"][0] = self.artifact(substitute)
        result = self.reconcile()
        self.assertTrue(result.failures)
        self.assertTrue(any(self.binary.name in failure for failure in result.failures))

    def test_each_required_hash_is_recomputed(self) -> None:
        required = self.publication["artifacts"]
        for index in range(2):
            with self.subTest(artifact=required[index]["name"]):
                self.publication["artifacts"] = [dict(row) for row in required]
                self.publication["artifacts"][index]["digest"] = "sha256:" + "0" * 64
                result = self.reconcile()
                self.assertTrue(
                    any("DIGEST MISMATCH" in failure for failure in result.failures),
                    result.failures,
                )

    def test_digest_domain_is_the_producer_domain(self) -> None:
        other_domain = "attacker-selected-domain"
        self.publication["digest_domain"] = other_domain
        self.publication["artifacts"] = [
            self.artifact(self.binary, other_domain), self.artifact(self.text, other_domain)
        ]
        result = self.reconcile()
        self.assertTrue(any("digest domain" in failure for failure in result.failures))

    def test_coverage_crate_must_match_the_marker_path(self) -> None:
        result = self.reconcile(coverage_crate="other")
        self.assertTrue(any("commit marker path" in failure for failure in result.failures))

    def test_address_fidelity_reads_the_display_path_not_the_symbol(self) -> None:
        """WS5.2: a row addresses the function whose DISPLAY PATH is its def path.

        Negative twins: a function whose display path names another body, and one
        whose def path survives only as the NAME (the pre-WS5.2 spelling), both fail D.
        """
        for text in (
            'rustcc fn @_RNvCs0_5probe1f(functy.0) {\n    ; #display-path: "probe::g"\n}\n',
            "fn @probe::f() {\n}\n",
        ):
            with self.subTest(text=text):
                self.text.write_text(text, encoding="utf-8")
                self.publication["artifacts"] = [
                    self.artifact(self.binary),
                    self.artifact(self.text),
                ]
                result = self.reconcile()
                self.assertTrue(
                    any("display path" in failure for failure in result.failures),
                    result.failures,
                )

    def test_rust_debug_unquote_inverts_the_display_path_escaping(self) -> None:
        self.assertEqual(lineage.rust_debug_unquote('"a::b<\\"c\\">"'), 'a::b<"c">')
        self.assertEqual(lineage.rust_debug_unquote('"\\u{e9}t\\\\"'), "\u00e9t\\")
        self.assertIsNone(lineage.rust_debug_unquote('"dangling\\"'))
        self.assertIsNone(lineage.rust_debug_unquote("unquoted"))

    def test_malformed_artifact_name_is_reported(self) -> None:
        self.publication["artifacts"][0]["name"] = [self.binary.name]
        result = self.reconcile()
        self.assertTrue(result.failures)


if __name__ == "__main__":
    unittest.main()
