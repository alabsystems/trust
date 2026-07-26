#!/usr/bin/env python3
"""Focused adversarial tests for the self-host seed minting workflow."""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
import stat
import sys
import tarfile
import tempfile
import tomllib
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from scripts import mint_seed_support as support


VERSION = "1.99.0"
HOST = "aarch64-apple-darwin"
COMMIT = "a" * 40


def add_bytes(bundle: tarfile.TarFile, name: str, value: bytes, mode: int = 0o644) -> None:
    member = tarfile.TarInfo(name)
    member.size = len(value)
    member.mode = mode
    bundle.addfile(member, io.BytesIO(value))


def write_archive(
    path: Path,
    component: str,
    *,
    commit: str = COMMIT,
    extra: list[tarfile.TarInfo] | None = None,
) -> None:
    top = path.name.removesuffix(".tar.xz")
    with tarfile.open(path, "w:xz") as bundle:
        directory = tarfile.TarInfo(top)
        directory.type = tarfile.DIRTYPE
        directory.mode = 0o755
        bundle.addfile(directory)
        add_bytes(bundle, f"{top}/install.sh", b"#!/bin/sh\nexit 0\n", 0o755)
        add_bytes(bundle, f"{top}/version", f"{VERSION} fixture\n".encode())
        add_bytes(bundle, f"{top}/git-commit-hash", f"{commit}\n".encode())
        for member in extra or []:
            bundle.addfile(member)


def write_component_set(dist: Path, *, commit: str = COMMIT) -> None:
    for component in support.COMPONENTS:
        path = dist / f"{component}-{VERSION}-trust-{HOST}.tar.xz"
        write_archive(path, component, commit=commit)


def expect_error(fragment: str, function: object, *args: object, **kwargs: object) -> None:
    try:
        function(*args, **kwargs)  # type: ignore[operator]
    except support.WorkflowError as exc:
        assert fragment in str(exc), (fragment, str(exc))
    else:
        raise AssertionError(f"expected WorkflowError containing {fragment!r}")


def test_canonical_metadata() -> None:
    assert support.canonical_version_value("1.99.0") == "1.99.0"
    assert support.canonical_version_value("1.99.0-trust.1+build.7")
    expect_error("canonical SemVer", support.canonical_version_value, "01.99.0")
    expect_error("canonical SemVer", support.canonical_version_value, "1.99")
    assert support.detected_host("Darwin", "arm64") == HOST
    assert support.detected_host("Darwin", "AMD64") == "x86_64-apple-darwin"
    with mock.patch.object(support.platform, "libc_ver", return_value=("glibc", "2.39")):
        assert support.detected_host("Linux", "aarch64") == "aarch64-unknown-linux-gnu"
    assert (
        support.detected_host("Linux", "x86_64", "musl")
        == "x86_64-unknown-linux-musl"
    )


def test_bootstrap_config_closure_binds_recursive_includes() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        source = root / "config.toml"
        child = root / "config.d" / "native.toml"
        child.parent.mkdir()
        source.write_text('include = ["config.d/native.toml"]\n[build]\njobs = 4\n')
        child.write_text('[llvm]\ndownload-ci-llvm = false\n')

        first = support.configuration_closure(root, source)
        assert len(first["files"]) == 2
        child.write_text('[llvm]\ndownload-ci-llvm = true\n')
        second = support.configuration_closure(root, source)
        assert first["fingerprint"] != second["fingerprint"]

        child.write_text('include = ["../config.toml"]\n')
        expect_error("include cycle", support.configuration_closure, root, source)

        outside = root.parent / f"{root.name}-outside.toml"
        try:
            outside.write_text("[build]\n")
            source.write_text(f'include = ["../{outside.name}"]\n')
            expect_error("escapes", support.configuration_closure, root, source)
        finally:
            outside.unlink(missing_ok=True)


def test_exact_artifacts_are_commit_bound_and_hashed() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        dist = root / "dist"
        work = root / "work"
        dist.mkdir()
        work.mkdir()
        write_component_set(dist)
        # This would have won the former `ls | head` selection on some hosts.
        stale = dist / f"trustc-0.1.0-trust-{HOST}.tar.xz"
        write_archive(stale, "trustc", commit="b" * 40)
        manifest_path = work / "inputs.json"

        manifest = support.stage_artifacts(
            dist, work, VERSION, HOST, COMMIT, manifest_path
        )

        assert manifest_path.exists()
        assert manifest["source_commit"] == COMMIT
        assert [item["component"] for item in manifest["artifacts"]] == list(
            support.COMPONENTS
        )
        for item in manifest["artifacts"]:
            expected = dist / item["filename"]
            assert item["sha256"] == hashlib.sha256(expected.read_bytes()).hexdigest()
            assert item["filename"].startswith(f"{item['component']}-{VERSION}-trust-")
        assert stale.name not in manifest_path.read_text()


def test_near_match_cannot_substitute_for_exact_artifact() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        dist = root / "dist"
        work = root / "work"
        dist.mkdir()
        work.mkdir()
        write_component_set(dist)
        exact = dist / f"trustc-{VERSION}-trust-{HOST}.tar.xz"
        exact.unlink()
        write_archive(dist / f"trustc-{VERSION}-trust-other-host.tar.xz", "trustc")
        expect_error(
            "exact trustc dist artifact",
            support.stage_artifacts,
            dist,
            work,
            VERSION,
            HOST,
            COMMIT,
            work / "inputs.json",
        )


def test_explicit_native_library_inputs_are_content_bound() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp).resolve()
        library = directory / "libz3.dylib"
        library.write_bytes(b"first native library")
        (directory / "unrelated.txt").write_text("ignored")
        first = support.native_library_manifest([directory])
        assert len(first["files"]) == 1
        assert first["files"][0]["name"] == "libz3.dylib"
        library.write_bytes(b"second native library")
        second = support.native_library_manifest([directory])
        assert first["fingerprint"] != second["fingerprint"]


def test_archive_commit_must_equal_head() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        dist = root / "dist"
        work = root / "work"
        dist.mkdir()
        work.mkdir()
        write_component_set(dist, commit="b" * 40)
        expect_error(
            "not minted from current HEAD",
            support.stage_artifacts,
            dist,
            work,
            VERSION,
            HOST,
            COMMIT,
            work / "inputs.json",
        )


def test_archive_path_traversal_is_rejected() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        dist = root / "dist"
        work = root / "work"
        dist.mkdir()
        work.mkdir()
        write_component_set(dist)
        path = dist / f"trust-std-{VERSION}-trust-{HOST}.tar.xz"
        traversal = tarfile.TarInfo(
            f"trust-std-{VERSION}-trust-{HOST}/../../outside"
        )
        traversal.size = 0
        write_archive(path, "trust-std", extra=[traversal])
        expect_error(
            "escapes its extraction root",
            support.stage_artifacts,
            dist,
            work,
            VERSION,
            HOST,
            COMMIT,
            work / "inputs.json",
        )


def test_archive_escaping_symlink_is_rejected() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        dist = root / "dist"
        work = root / "work"
        dist.mkdir()
        work.mkdir()
        write_component_set(dist)
        path = dist / f"trust-std-{VERSION}-trust-{HOST}.tar.xz"
        top = path.name.removesuffix(".tar.xz")
        link = tarfile.TarInfo(f"{top}/bin/escape")
        link.type = tarfile.SYMTYPE
        link.linkname = "../../../outside"
        write_archive(path, "trust-std", extra=[link])
        expect_error(
            "link escapes its extraction root",
            support.stage_artifacts,
            dist,
            work,
            VERSION,
            HOST,
            COMMIT,
            work / "inputs.json",
        )


def test_symlinked_dist_artifact_is_rejected() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        dist = root / "dist"
        work = root / "work"
        elsewhere = root / "elsewhere.tar.xz"
        dist.mkdir()
        work.mkdir()
        write_component_set(dist)
        exact = dist / f"trust-std-{VERSION}-trust-{HOST}.tar.xz"
        exact.rename(elsewhere)
        exact.symlink_to(elsewhere)
        expect_error(
            "non-symlink regular file",
            support.stage_artifacts,
            dist,
            work,
            VERSION,
            HOST,
            COMMIT,
            work / "inputs.json",
        )


def test_sanitized_path_excludes_all_ambient_rust_frontends() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        source = root / "source"
        output = root / "safe"
        source.mkdir()
        for name in ("git", "sh", "cc", "rustc", "cargo", "cargo-clippy", "trustc", "targo"):
            path = source / name
            path.write_text("#!/bin/sh\nexit 0\n")
            path.chmod(0o755)
        report = support.create_sanitized_path(str(source), output)
        assert (output / "git").is_symlink()
        assert (output / "sh").is_symlink()
        assert (output / "cc").is_symlink()
        for name in ("rustc", "cargo", "cargo-clippy", "trustc", "targo"):
            assert not (output / name).exists()
        excluded = "\n".join(report["excluded_rust_family"])
        assert "rustc" in excluded and "cargo" in excluded and "trustc" in excluded
        manifest = root / "path.json"
        support.write_json_exclusive(manifest, report)
        support.revalidate_sanitized_path(output, manifest)
        (source / "cc").write_text("#!/bin/sh\nexit 17\n# changed size\n")
        expect_error(
            "sanitized PATH target changed",
            support.revalidate_sanitized_path,
            output,
            manifest,
        )


def test_work_directory_publish_is_new_only_and_cleanup_is_scoped() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "build").mkdir()
        work = support.make_work_directory(root)
        candidate = work / "seed"
        candidate.mkdir()
        (candidate / "proof").write_text("exact")
        final = root / "build" / "published-seed"

        support.publish_directory(root, candidate, final, "test seed")
        assert (final / "proof").read_text() == "exact"
        assert not candidate.exists()
        support.cleanup_work_directory(root, work)
        assert not work.exists()

        outside = root / "outside"
        outside.mkdir()
        expect_error(
            "non-workflow temporary directory",
            support.cleanup_work_directory,
            root,
            outside,
        )


def test_seed_config_is_private_override_not_checkout_copy() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        source = root / "config.toml"
        seed = root / "seed"
        output = root / "private" / "bootstrap.seed.toml"
        fail_tool = root / "private" / "bin" / "unavailable-tippy"
        source.write_text('[build]\nrustc = "/stock/rustc"\n')
        (seed / "bin").mkdir(parents=True)
        for name in ("trustc", "targo", "cargo", "trustdoc", "trustfmt"):
            path = seed / "bin" / name
            path.write_text("#!/bin/sh\nexit 0\n")
            path.chmod(0o755)

        support.write_seed_config(source, output, seed, fail_tool)

        text = output.read_text()
        assert f"include = [{json.dumps(str(source.resolve()))}]" in text
        assert str(seed / "bin" / "trustc") in text
        assert "/stock/rustc" not in text
        parsed = tomllib.loads(text)
        assert parsed["build"]["rustc"] == str(seed / "bin" / "trustc")
        assert parsed["build"]["cargo"] == str(seed / "bin" / "cargo")
        assert parsed["build"]["submodules"] is False
        assert parsed["rust"]["channel"] == "trust"
        assert parsed["rust"]["download-rustc"] is False
        assert parsed["llvm"]["download-ci-llvm"] is False
        assert stat.S_IMODE(output.stat().st_mode) == 0o600
        assert fail_tool.read_text().startswith("#!/bin/sh")


def test_supervisor_propagates_status_and_enforces_timeout() -> None:
    assert support.supervise([sys.executable, "-c", "raise SystemExit(7)"], 5) == 7
    diagnostics = io.StringIO()
    with contextlib.redirect_stderr(diagnostics):
        assert (
            support.supervise(
                [sys.executable, "-c", "import time; time.sleep(30)"], 1
            )
            == 124
        )
    assert "exceeded 1 seconds" in diagnostics.getvalue()
    diagnostics = io.StringIO()
    spawn_orphan = (
        "import subprocess,sys; "
        "subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'])"
    )
    with contextlib.redirect_stderr(diagnostics):
        assert support.supervise([sys.executable, "-c", spawn_orphan], 5) == 125
    assert "left descendant processes" in diagnostics.getvalue()


def test_workflow_shell_keeps_command_policy_and_claim_boundary() -> None:
    script = Path(__file__).resolve().parents[1] / "mint_and_prove_seed.sh"
    text = script.read_text()
    assert text.count("$ROOT/x.py") == 2
    assert text.count("--set build.submodules=false") == 2
    assert "bootstrap.seed.toml" in text
    assert "not a kernel" in text.lower()
    assert "ls " not in text and "head -" not in text


def main() -> int:
    tests = [
        value
        for name, value in sorted(globals().items())
        if name.startswith("test_") and callable(value)
    ]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
