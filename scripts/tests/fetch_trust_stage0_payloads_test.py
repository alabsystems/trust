#!/usr/bin/env python3
"""Focused tests for scripts/fetch_trust_stage0_payloads.py."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
HELPER = REPO_ROOT / "scripts" / "fetch_trust_stage0_payloads.py"
PAYLOAD_REL = "dist/2026-05-04/trustc-1.96.0-trust-aarch64-test.tar.xz"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_stage0(root: Path, digest: str) -> None:
    (root / "src").mkdir(parents=True)
    (root / "src" / "stage0").write_text(
        "\n".join(
            [
                "dist_server=file://{trust-root}/bootstrap/trust-stage0",
                "compiler_date=2026-05-04",
                f"{PAYLOAD_REL}={digest}",
                "",
            ]
        ),
        encoding="utf-8",
    )


def write_manifest(root: Path, url: str, digest: str) -> None:
    manifest = root / "bootstrap" / "trust-stage0" / "dist" / "channel-rust-trust.toml"
    manifest.parent.mkdir(parents=True)
    manifest.write_text(
        "\n".join(
            [
                'manifest-version = "2"',
                'date = "2026-05-04"',
                "",
                "[pkg]",
                "[pkg.trustc]",
                'version = "1.96.0-trust"',
                "[pkg.trustc.target]",
                "[pkg.trustc.target.aarch64-test]",
                "available = true",
                f'xz_url = "{url}"',
                f'xz_hash = "{digest}"',
                "",
            ]
        ),
        encoding="utf-8",
    )


def run_helper(root: Path, *args: str) -> tuple[int, dict[str, object]]:
    completed = subprocess.run(
        [sys.executable, str(HELPER), "--repo-root", str(root), "--json", *args],
        check=False,
        text=True,
        capture_output=True,
    )
    if completed.stdout:
        payload = json.loads(completed.stdout)
    else:
        raise AssertionError(f"helper produced no JSON\nstderr={completed.stderr}")
    return completed.returncode, payload


def test_declared_file_source_is_fetchable_and_only_writes_with_fetch() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        source = root / "declared" / Path(PAYLOAD_REL).name
        source.parent.mkdir(parents=True)
        source_bytes = b"trust-stage0-payload"
        source.write_bytes(source_bytes)
        digest = sha256(source_bytes)
        write_stage0(root, digest)
        write_manifest(root, source.as_uri(), digest)
        target = root / "bootstrap" / "trust-stage0" / PAYLOAD_REL

        code, report = run_helper(root)
        assert code == 0, report
        assert report["status"] == "fetchable", report
        assert not target.exists()

        code, report = run_helper(root, "--fetch")
        assert code == 0, report
        assert report["status"] == "ready", report
        assert target.read_bytes() == source_bytes


def test_missing_repo_local_manifest_url_stays_blocked() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        digest = sha256(b"missing")
        write_stage0(root, digest)
        write_manifest(
            root,
            "file://{trust-root}/bootstrap/trust-stage0/" + PAYLOAD_REL,
            digest,
        )

        code, report = run_helper(root)
        assert code == 1, report
        assert report["status"] == "blocked", report
        payload = report["payloads"][0]
        assert payload["status"] == "blocked", payload
        assert payload["declared_sources"][0]["status"] == "missing-local-file", payload


def test_fetched_payload_must_match_stage0_checksum() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        source = root / "declared" / Path(PAYLOAD_REL).name
        source.parent.mkdir(parents=True)
        source.write_bytes(b"actual")
        expected = sha256(b"expected")
        write_stage0(root, expected)
        write_manifest(root, source.as_uri(), expected)
        target = root / "bootstrap" / "trust-stage0" / PAYLOAD_REL

        code, report = run_helper(root, "--fetch")
        assert code == 1, report
        assert report["status"] == "blocked", report
        assert report["payloads"][0]["status"] == "download-checksum-mismatch", report
        assert not target.exists()


def main() -> int:
    tests = [
        test_declared_file_source_is_fetchable_and_only_writes_with_fetch,
        test_missing_repo_local_manifest_url_stays_blocked,
        test_fetched_payload_must_match_stage0_checksum,
    ]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
