#!/bin/sh
""":"
# Trust: python floor. POSIX sh runs this block when the file is EXECUTED and
# re-execs under a >=3.11 interpreter; Python reads it as a string.
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "mint_and_prove_seed_test.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 mint_and_prove_seed_test.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("mint_and_prove_seed_test.py requires Python 3.11+ (tomllib); none found on PATH")

__doc__ = """Focused adversarial tests for the self-host seed minting workflow."""

import contextlib
import copy
import hashlib
import io
import json
import os
import shlex
import stat
import subprocess
import sys
import tarfile
import tempfile
import unittest
import tomllib
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT))

from scripts import mint_seed_support as support
from scripts.tests.mint_clean_lean_inputs_test import fixture as clean_lean_fixture


VERSION = "1.99.0"
HOST = "aarch64-apple-darwin"
COMMIT = "a" * 40
SHA256_RE = support.SHA256_RE


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


def test_the_cargo_home_input_gives_only_the_offline_trees_and_is_content_bound() -> None:
    # Measured 2026-10-09: with a fresh cargo home the first real cut stopped at
    # "Building bootstrap" (no matching package named `cc` ... offline mode).
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        given = root / "given-cargo-home"
        for relative, value in (
            ("registry/index/index.crates.io-x/.cache/cc", b"index entry"),
            ("registry/cache/index.crates.io-x/cc-1.2.0.crate", b"crate bytes"),
            ("git/db/trust-cg-0123/HEAD", b"ref: refs/heads/main\n"),
            ("registry/src/index.crates.io-x/cc-1.2.0/lib.rs", b"extracted, not an input"),
            ("git/checkouts/trust-cg-0123/abc/lib.rs", b"checkout, not an input"),
            ("bin/rustc", b"#!/bin/sh\n# a rustup proxy\n"),
            ("config.toml", b"[build]\nrustc = \"/elsewhere/rustc\"\n"),
        ):
            path = given / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
        private = root / "work" / "cargo-home"
        manifest = support.cargo_home_inputs(given, private)
        assert sorted(manifest["trees"]) == ["git/db", "registry/cache", "registry/index"]
        assert (private / "registry/cache/index.crates.io-x/cc-1.2.0.crate").read_bytes() == b"crate bytes"
        assert (private / "git/db/trust-cg-0123/HEAD").is_file()
        for absent in ("bin", "config.toml", "registry/src", "git/checkouts"):
            assert not (private / absent).exists(), absent
        expect_error("already exists", support.cargo_home_inputs, given, private)
        record = root / "cargo-home-inputs.json"
        support.write_json_exclusive(record, manifest)
        support.verify_cargo_home_source(record)
        (given / "registry/cache/index.crates.io-x/cc-1.2.0.crate").write_bytes(b"other crate bytes")
        expect_error("changed during the workflow", support.verify_cargo_home_source, record)
        # Its content is what the manifest binds.
        again = support.cargo_home_inputs(given, root / "work" / "cargo-home-2")
        assert again["fingerprint"] != manifest["fingerprint"]
        # No input: an empty private cargo home, said so.
        none = support.cargo_home_inputs(None, root / "work" / "cargo-home-3")
        assert none["source"] is None and none["trees"] == {}
        assert list((root / "work" / "cargo-home-3").iterdir()) == []


def test_a_seed_foreign_library_must_come_from_a_declared_directory() -> None:
    # Measured 2026-10-09: the 2026-07-13 seed's cargo names Homebrew's
    # libgit2.1.9.dylib by absolute path, and under the cut it mapped Homebrew's
    # libgit2 1.9.7 (and, through it, libssh2, llhttp, openssl@3).
    clang = Path("/usr/bin/clang")
    if sys.platform != "darwin" or not clang.is_file():
        print("SKIP test_a_seed_foreign_library_must_come_from_a_declared_directory (macOS only)")
        return
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        sources = root / "src"
        sources.mkdir()
        (sources / "foo.c").write_text("int foo(void) { return 7; }\n")
        (sources / "own.c").write_text("int own(void) { return 1; }\n")
        (sources / "tool.c").write_text(
            "int foo(void); int own(void); int main(void) { return foo() + own() - 8; }\n")
        foreign = "/opt/trust-fixture-foreign/lib/libfoo.1.dylib"
        provided = root / "compat"
        provided.mkdir()
        sysroot = root / "seed"
        (sysroot / "bin").mkdir(parents=True)
        (sysroot / "lib").mkdir()

        def cc(*arguments: str) -> None:
            subprocess.run([str(clang), *arguments], check=True, capture_output=True)

        cc("-dynamiclib", str(sources / "foo.c"), "-o", str(provided / "libfoo.1.dylib"),
           "-install_name", foreign)
        cc("-dynamiclib", str(sources / "own.c"), "-o", str(sysroot / "lib" / "libown.dylib"),
           "-install_name", "@rpath/libown.dylib")
        cc(str(sources / "tool.c"), "-o", str(sysroot / "bin" / "tool"),
           str(provided / "libfoo.1.dylib"), str(sysroot / "lib" / "libown.dylib"),
           "-Wl,-rpath,@executable_path/../lib")
        (sysroot / "bin" / "script").write_text("#!/bin/sh\nexit 0\n")
        expect_error(f"bin/tool -> {foreign}", support.foreign_load_commands, sysroot, [])
        expect_error("no --seed-dylib-path provides", support.foreign_load_commands,
                     sysroot, [root / "elsewhere"])
        loads = support.foreign_load_commands(sysroot, [provided])
        assert loads["checked"] is True
        assert [(row["binary"], row["load"]) for row in loads["foreign"]] == [("bin/tool", foreign)]
        assert loads["foreign"][0]["provider_sha256"] == hashlib.sha256(
            (provided / "libfoo.1.dylib").read_bytes()).hexdigest()


def test_the_double_compile_runs_in_one_environment_with_one_cargo_home() -> None:
    text = (Path(__file__).resolve().parents[1] / "mint_and_prove_seed.sh").read_text()
    # Both builds of the double compile: the same HOME, TMPDIR and cargo home.
    assert 'xpy "$SAFE_BIN" ddc' not in text
    assert 'xpy "$SAFE_BIN" mint "$DDC_CONFIG" "$MINT_BUILD" build compiler/rustc library/std' in text
    assert 'CARGO_HOME="$CARGO_HOME_SHARED"' in text
    assert '"$environment_root/cargo-home"' not in text
    assert "CARGO_NET_OFFLINE=true" in text
    # The declared seed dylib directories, first on DYLD_LIBRARY_PATH; both seeds checked.
    assert 'DYLD_LIBRARY_PATH="$SEED_DYLIB_PATH"' in text
    # Continuation adds another pinned-stage0 probe. Check every real probe's
    # expanded argv instead of counting a fixed number of textual occurrences.
    probes = []
    for line in text.replace("\\\n", " ").splitlines():
        if any(f'"$HELPER" {verb} ' in line for verb in ("ddc-seed", "pinned-stage0")):
            command = line.strip()
            if command.startswith("DDC_LINE=$("):
                command = command.removeprefix("DDC_LINE=$(").removesuffix(")")
            probes.append(command)
    assert probes
    with tempfile.TemporaryDirectory() as tmp:
        capture = Path(tmp) / "probe-argv.jsonl"
        harness = (
            'ROOT=/product; HOST=aarch64-apple-darwin; DDC_SEED=/oracle; WORK=/work; '
            'MINT_BUILD=/mint; HELPER=/helper; PYTHON_BIN=record_probe\n'
            'PINNED_OBSERVATION=/work/pinned-seed-recovery.json\n'
            'SEED_DYLIB_ARGS=(--seed-dylib-path "/provider one" --seed-dylib-path "/provider two")\n'
            'record_probe() { "$REAL_PYTHON" -c '
            + shlex.quote("import json,os,sys; f=open(os.environ['PROBE_CAPTURE'],'a'); "
                          "f.write(json.dumps(sys.argv[1:])+'\\n'); f.close()")
            + ' "$@"; }\n' + "\n".join(probes)
        )
        subprocess.run(["/bin/bash", "-eu", "-c", harness], check=True,
                       env={"PATH": os.defpath, "REAL_PYTHON": sys.executable,
                            "PROBE_CAPTURE": str(capture)})
        captured = [json.loads(line) for line in capture.read_text().splitlines()]
        assert {argv[3] for argv in captured} == {"ddc-seed", "pinned-stage0"}
        assert {argv[argv.index("--output") + 1] for argv in captured if "--output" in argv} == {
            "/work/pinned-seed.json", "/work/pinned-seed-recovery.json", "/work/ddc-seed.json", "/work/ddc-seed-post-build.json",
        }
        assert any(argv[3] == "ddc-seed" and "--output" not in argv for argv in captured)
        for argv in captured:
            providers = [argv[i + 1] for i, value in enumerate(argv) if value == "--seed-dylib-path"]
            assert providers == ["/provider one", "/provider two"], argv
    assert "verify-cargo-home-inputs" in text and "--cargo-home-manifest" in text


def test_the_build_manifest_tool_is_found_where_bootstrap_installs_it() -> None:
    # BuildManifest's stage1 compiler produces output stage2. Session adds
    # one and the requested target triple to the tool installation directory.
    with tempfile.TemporaryDirectory() as tmp:
        build = Path(tmp).resolve() / "pack-mint-x"
        installed = build / HOST / "stage3-tools-bin" / HOST / "build-manifest"
        installed.parent.mkdir(parents=True)
        installed.write_text("#!/bin/sh\nexit 0\n")
        installed.chmod(0o755)
        assert support.find_build_manifest_tool(build, HOST) == installed


def test_build_manifest_tool_does_not_fall_back_to_a_decoy_producer() -> None:
    for relative in (
        Path("stage3-tools-bin/build-manifest"),
        Path("stage2-tools-bin") / HOST / "build-manifest",
        Path("stage4-tools-bin") / HOST / "build-manifest",
        Path("stage3-tools-bin/x86_64-unknown-linux-gnu/build-manifest"),
    ):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp).resolve()
            decoy = build / HOST / relative
            decoy.parent.mkdir(parents=True)
            decoy.write_text("#!/bin/sh\nexit 99\n")
            decoy.chmod(0o755)
            expect_error("build-manifest", support.find_build_manifest_tool, build, HOST)


def test_build_manifest_tool_uses_its_recipe_stage_with_stale_outputs_present() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        build = Path(tmp).resolve()
        installed = build / HOST / "stage3-tools-bin" / HOST / "build-manifest"
        installed.parent.mkdir(parents=True)
        installed.write_text("#!/bin/sh\nexit 0\n")
        installed.chmod(0o755)
        decoys = [
            build / HOST / "stage3-tools-bin" / "build-manifest",
            build / HOST / "stage9-tools-bin" / HOST / "build-manifest",
            build / HOST / "stage2-tools-bin" / HOST / "build-manifest",
        ]
        for decoy in decoys:
            decoy.parent.mkdir(parents=True, exist_ok=True)
            decoy.write_text("#!/bin/sh\nexit 99\n")
            decoy.chmod(0o755)
        def identity(path):
            data = path.read_bytes()
            info = path.lstat()
            return data, (info.st_dev, info.st_ino, info.st_mode, info.st_nlink,
                          info.st_size, info.st_mtime_ns, info.st_ctime_ns)

        before = {path: identity(path) for path in decoys}
        assert support.find_build_manifest_tool(build, HOST) == installed
        assert {path: identity(path) for path in decoys} == before


def test_build_manifest_tool_requires_a_regular_executable_at_the_canonical_path() -> None:
    for kind in ("missing", "directory", "not-executable", "symlink", "dangling-symlink"):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp).resolve()
            installed = build / HOST / "stage3-tools-bin" / HOST / "build-manifest"
            installed.parent.mkdir(parents=True)
            if kind == "directory":
                installed.mkdir()
            elif kind == "not-executable":
                installed.write_text("#!/bin/sh\nexit 0\n")
                installed.chmod(0o644)
            elif kind in ("symlink", "dangling-symlink"):
                target = build / "elsewhere"
                if kind == "symlink":
                    target.write_text("#!/bin/sh\nexit 0\n")
                    target.chmod(0o755)
                installed.symlink_to(target)
            expect_error("build-manifest", support.find_build_manifest_tool, build, HOST)


def test_build_manifest_tool_refuses_a_noncanonical_host() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        expect_error("host triple is not canonical", support.find_build_manifest_tool,
                     Path(tmp), "../" + HOST)


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
        for name in (*support.build_helper_names(HOST), "rustc", "cargo", "cargo-clippy", "trustc", "targo"):
            path = source / name
            path.write_text("#!/bin/sh\nexit 0\n")
            path.chmod(0o755)
        # An unrelated, unreadable executable is outside the declared inputs.
        sudo = source / "sudo"
        sudo.write_text("#!/bin/sh\nexit 0\n")
        sudo.chmod(0o111)
        report = support.create_sanitized_path(str(source), output, HOST, source / "python3")
        assert (output / "git").is_symlink()
        assert (output / "sh").is_symlink()
        assert (output / "cc").is_symlink()
        for name in ("rustc", "cargo", "cargo-clippy", "trustc", "targo"):
            assert not (output / name).exists()
        assert set(report["admitted"]) == set(support.build_helper_names(HOST))
        assert not (output / "sudo").exists()
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
        assert support.supervise([sys.executable, "-c", spawn_orphan], 5, grace_seconds=1) == 125
    assert "left descendant processes" in diagnostics.getvalue()


def test_supervisor_lets_descendants_exit_by_themselves() -> None:
    # A Pool's resource tracker exits only once it reads EOF on a pipe its
    # parent held, so it is still running the instant the parent exits.
    pool = (
        "from multiprocessing import Pool\n"
        "if __name__ == '__main__':\n"
        "    pool = Pool(2)\n"
        "    pool.map(abs, [1, -2])\n"
        "    pool.close()\n"
        "    pool.join()\n"
        "    raise SystemExit(3)\n"
    )
    outlive = (
        "import subprocess,sys; "
        "subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(1)'])"
    )
    for program, status in ((pool, 3), (outlive, 0)):
        diagnostics = io.StringIO()
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / "child.py"
            script.write_text(program)
            with contextlib.redirect_stderr(diagnostics):
                assert support.supervise([sys.executable, str(script)], 30) == status
        assert "left descendant processes" not in diagnostics.getvalue()


PIN = "1" * 40
DDC = "2" * 40
CUT = "3" * 40
STAGE0_HEAD = """dist_server=file://{trust-root}/bootstrap/trust-stage0
compiler_dist_channel=trust

min_stage0_rustc_version=1.96.0

# The configuration above this comment is editable, and can be changed
# by forks of the repository if they have alternate values.
#
"""


def stage0_text(commit: str, date: str, version: str, digest: str) -> str:
    return STAGE0_HEAD + "\n".join(
        [
            "# The section below was generated by src/tools/trust-stage0-dist/prepare.py",
            "# from a repo-local dist snapshot.",
            "",
            f"compiler_channel_manifest_hash={'c' * 64}",
            f"compiler_git_commit_hash={commit}",
            f"compiler_date={date}",
            f"compiler_version={version}",
            f"rustfmt_channel_manifest_hash={'c' * 64}",
            f"rustfmt_git_commit_hash={commit}",
            f"rustfmt_date={date}",
            f"rustfmt_version={version}",
            "",
            f"dist/{date}/trustc-{version}-{HOST}.tar.xz={digest}",
            "",
        ]
    )


def fake_sysroot(path: Path, *, commit: str, date: str, binary: str = "trustc", trust_line: bool = True) -> Path:
    (path / "bin").mkdir(parents=True)
    (path / "lib").mkdir()
    compiler = path / "bin" / binary
    compiler.write_text(
        "#!/bin/sh\n"
        f"echo 'rustc 1.99.0-dev ({commit[:9]} {date})'\n"
        f"echo 'binary: {binary}'\n"
        f"echo 'commit-hash: {commit}'\n"
        f"echo 'commit-date: {date}'\n"
        f"echo 'host: {HOST}'\n"
        "echo 'release: 1.99.0-dev'\n"
        + ("echo 'trust: 0.10.0+gabc'\n" if trust_line else "")
    )
    compiler.chmod(0o755)
    (path / "lib" / "librustc_driver-0123.dylib").write_bytes(f"driver {commit}".encode())
    return path


def test_pack_cut_refuses_every_configured_stage0_tool() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        defaults = root / "src" / "bootstrap" / "defaults"
        defaults.mkdir(parents=True)
        (defaults / "bootstrap.compiler.toml").write_text("[rust]\nincremental = true\n")
        source = root / "bootstrap.toml"
        source.write_text('profile = "compiler"\n[build]\nextended = true\n')
        support.require_pinned_seed_config(root, source)
        for key in support.STAGE0_SELECTORS:
            source.write_text(f'[build]\n{key} = "/elsewhere/{key}"\n')
            expect_error(f"build.{key}", support.require_pinned_seed_config, root, source)
        # An include cannot smuggle one in either.
        (root / "seed.toml").write_text('[build]\nrustc = "/pkg/store/trust/9192/bin/trustc"\n')
        source.write_text('include = ["seed.toml"]\n')
        expect_error("build.rustc", support.require_pinned_seed_config, root, source)
        # Nor a profile: bootstrap merges src/bootstrap/defaults/bootstrap.<profile>.toml
        # last, filling what is unset, including a profile named by an include.
        (defaults / "bootstrap.dist.toml").write_text('[build]\ncargo = "/elsewhere/cargo"\n')
        source.write_text('profile = "user"\n')  # bootstrap's alias for dist
        expect_error("build.cargo", support.require_pinned_seed_config, root, source)
        (root / "seed.toml").write_text('profile = "dist"\n')
        source.write_text('include = ["seed.toml"]\n')
        expect_error("build.cargo", support.require_pinned_seed_config, root, source)
        source.write_text('profile = "../../../seed"\n')
        expect_error("plain profile name", support.require_pinned_seed_config, root, source)
        # The root file's own value wins over an include's, as in bootstrap.
        (root / "seed.toml").write_text('[build]\nrustc = "/included"\n')
        source.write_text('include = ["seed.toml"]\n[build]\nrustc = "/root"\n')
        assert support.effective_build_table(root, source)["rustc"] == "/root"
        inventory = {}
        assert support.effective_build_table(root, source, inputs=inventory)["rustc"] == "/root"
        assert inventory == {
            path: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (source, root / "seed.toml")
        }
        # Each key's origin is the file whose value won (LAND-GATE-11 names it).
        (root / "seed.toml").write_text('[build]\nrustc = "/included"\ncargo = "/included"\n')
        origins = {}
        table = support.effective_build_table(root, source, origins=origins)
        assert (table["rustc"], table["cargo"]) == ("/root", "/included")
        assert origins == {"rustc": source, "cargo": root / "seed.toml"}
        # Profile includes use the same merge order as ordinary config includes.
        source.write_text('profile = "dist"\n')
        (defaults / "bootstrap.dist.toml").write_text('include = ["extra.toml"]\n')
        (defaults / "extra.toml").write_text('[build]\ncargo = "/profile/include"\n')
        inventory = {}
        origins = {}
        assert support.effective_build_table(
            root, source, inputs=inventory, origins=origins)["cargo"] == "/profile/include"
        assert set(inventory) == {source, defaults / "bootstrap.dist.toml", defaults / "extra.toml"}
        assert origins == {"cargo": defaults / "extra.toml"}
        expect_error("build.cargo", support.require_pinned_seed_config, root, source)
        # Confined unless asked otherwise: the freshness gate reads any config bootstrap would.
        outside = Path(tempfile.mkdtemp()).resolve()
        try:
            (outside / "bootstrap.toml").write_text('[build]\nrustc = "/x"\n')
            expect_error("escapes", support.effective_build_table, root, outside / "bootstrap.toml")
            assert support.effective_build_table(root, outside / "bootstrap.toml", confine=False)["rustc"] == "/x"
        finally:
            import shutil
            shutil.rmtree(outside)


def test_the_pin_and_the_repin_date_guard() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        pin = support.read_stage0_pin(root)
        assert pin["compiler_git_commit_hash"] == PIN
        assert pin["dist_server"] == "file://{trust-root}/bootstrap/trust-stage0"
        support.check_repin_date(root, "2026-09-29")
        support.check_repin_date(root, "2026-07-13")
        expect_error("canonical YYYY-MM-DD", support.check_repin_date, root, "2026-02-30")


def test_ddc_seed_identity_names_its_relation_to_the_pin() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        git(root, "init", "-q", "-b", "main")
        git(root, "config", "user.name", "Fixture")
        git(root, "config", "user.email", "fixture@example.com")
        (root / "src").mkdir()
        earlier, builder = "4" * 40, "5" * 40
        (root / "src" / "stage0").write_text(stage0_text(earlier, "2026-06-01", "1.98.0-trust", "d" * 64))
        git(root, "add", "-A")
        git(root, "commit", "-q", "-m", "an earlier pin")
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
        ledger.parent.mkdir(parents=True)
        ledger.write_text(
            f'scope = "internal"\n[release]\nrepo = "owner/trust"\n[release.mint]\npinned_seed_commit = "{builder}"\n'
        )
        git(root, "add", "-A")
        git(root, "commit", "-q", "-m", "the pin")

        def relation(name: str, **kwargs: object) -> dict[str, object]:
            return support.ddc_seed_identity(root, fake_sysroot(root / "seeds" / name, **kwargs))

        independent = relation("9178", commit=DDC, date="2026-09-15")
        assert independent["relation"] == "same-lineage" and independent["lineage"] == "trust"
        assert independent["commit"] == DDC and independent["date"] == "2026-09-15"
        assert SHA256_RE.fullmatch(independent["driver_sha256"])
        control = relation("july", commit=PIN, date="2026-07-13", trust_line=False)
        assert control["relation"] == "reproducibility-control"
        stock = relation("stock", commit=DDC, date="2026-09-01", binary="rustc", trust_line=False)
        assert stock["lineage"] == "stock" and stock["relation"] == "lineage-disjoint"
        # The stock oracle is a rustup toolchain's own sysroot: admitted as the DDC seed
        # only (STOCK-AS-ORACLE), never a genesis adapter, never anywhere else.
        oracle = fake_sysroot(
            root / "home" / ".rustup" / "toolchains" / f"1.97.1-{HOST}",
            commit="6" * 40, date="2026-08-01", binary="rustc", trust_line=False,
        )
        assert support.ddc_seed_identity(root, oracle)["relation"] == "lineage-disjoint"
        expect_error("forbidden stock-toolchain tree", support.canonical_directory, oracle, "a tool root")
        expect_error("forbidden stock-toolchain tree", support.compiler_identity, oracle, "atpkg trust pack")
        adapter = fake_sysroot(
            root / "build" / HOST / "genesis-stage0", commit="7" * 40, date="2026-08-01", trust_line=False
        )
        expect_error("forbidden stock-toolchain tree", support.ddc_seed_identity, root, adapter)
        expect_error("forbidden stock-toolchain tree", support.ddc_seed_identity, root, oracle / "lib")
        # An earlier pin, and the seed the ledger says built the pin, are the pin's ancestors.
        assert relation("june", commit=earlier, date="2026-06-01")["relation"] == "pin-ancestor"
        assert relation("builder", commit=builder, date="2026-07-01")["relation"] == "pin-ancestor"
        assert set(support.DDC_RELATIONS) == {
            "lineage-disjoint", "same-lineage", "pin-ancestor", "reproducibility-control"
        }
        assert [name for name, text in support.DDC_RELATIONS.items() if text.startswith("diverse")] == [
            "lineage-disjoint"
        ]


def test_the_receipt_carries_the_relation_and_the_latest_disjoint_anchor() -> None:
    manifest = {"sha256": "f" * 64, "records": [{"path": "bin/trustc", "kind": "file", "sha256": "a" * 64}]}
    seed = {"host": HOST, "commit": PIN, "date": "2026-07-13", "compiler_sha256": "b" * 64, "driver_sha256": "c" * 64}

    def receipt(relation: str, previous: str = "") -> dict[str, str]:
        text = support.render_receipt(
            source={"commit": CUT, "commit_date": "2026-09-29"},
            version="0.10.0",
            host=HOST,
            pinned=seed,
            ddc={**seed, "commit": DDC, "lineage": "trust", "relation": relation},
            pinned_manifest=manifest,
            ddc_manifest_sha256="f" * 64,
            previous_anchor=previous,
        )
        return support.parse_receipt(text)

    assert receipt("lineage-disjoint", "9" * 40)["lineage_disjoint_anchor"] == CUT
    assert receipt("pin-ancestor", "9" * 40)["lineage_disjoint_anchor"] == "9" * 40
    same = receipt("same-lineage")
    assert same["lineage_disjoint_anchor"] == "none" and same["ddc_seed_relation"] == "same-lineage"
    assert "ddc_kind" not in same
    expect_error("unknown DDC seed relation", receipt, "ddc")


def test_the_default_ddc_seed_is_the_newest_pack_that_is_not_the_pin() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        store = root / "store"
        fake_sysroot(store / "9178", commit=DDC, date="2026-09-15")
        fake_sysroot(store / "9300", commit=PIN, date="2026-07-13")  # the pin, as a pack
        (store / "current").symlink_to(store / "9300")
        assert support.default_ddc_seed(root, store) == store / "9178"
        fake_sysroot(store / "9192", commit="5" * 40, date="2026-09-17")
        assert support.default_ddc_seed(root, store) == store / "9192"
        expect_error("no --ddc-seed given", support.default_ddc_seed, root, root / "no-store")


def test_default_ddc_seed_discovers_physical_noindex_packs_at_the_default_store() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        store = root / "Library/Application Support/aterm/pkg/store/trust"
        old = fake_sysroot(store / "15698.noindex", commit=DDC, date="2026-09-15")
        pin = fake_sysroot(store / "16387.noindex", commit=PIN, date="2026-07-13")
        (store / "15698").symlink_to(old)
        (store / "16387").symlink_to(pin)
        (store / "current").symlink_to(pin)
        with mock.patch.object(support.Path, "home", return_value=root), \
                mock.patch.object(support.platform, "system", return_value="Darwin"), \
                mock.patch.object(support, "compiler_identity", wraps=support.compiler_identity) as identity:
            assert support.default_ddc_seed(root) == old
        assert [call.args[0] for call in identity.call_args_list] == [pin, old]


def test_default_ddc_seed_orders_mixed_layouts_and_deduplicates_build_numbers() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        store = root / "store"
        old = fake_sysroot(store / "9999.noindex", commit=DDC, date="2026-09-15")
        legacy = fake_sysroot(store / "10000", commit="5" * 40, date="2026-09-17")
        newest = fake_sysroot(store / "20000.noindex", commit=PIN, date="2026-07-13")
        assert support.default_ddc_seed(root, store) == legacy  # numeric, not lexical order
        canonical = fake_sysroot(store / "10000.noindex", commit=PIN, date="2026-07-13")
        fake_sysroot(store / "09999", commit="6" * 40, date="2026-09-18")
        with mock.patch.object(support, "compiler_identity", wraps=support.compiler_identity) as identity:
            assert support.default_ddc_seed(root, store) == old
        assert [call.args[0] for call in identity.call_args_list] == [newest, canonical, old]


def test_default_ddc_seed_ignores_alias_directories_and_nonsense_pack_names() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        store = root / "store"
        eligible = fake_sysroot(store / "100.noindex", commit=DDC, date="2026-09-15")
        outside = fake_sysroot(root / "outside", commit="5" * 40, date="2026-09-17")
        for name in ("999999.noindex", "999998", "current"):
            (store / name).symlink_to(outside)
        for name in ("latest.noindex", "200.noindex.old", "3.0.noindex", "²", "².noindex"):
            fake_sysroot(store / name, commit="6" * 40, date="2026-09-18")
        (store / "999997.noindex").write_text("not a directory")
        with mock.patch.object(support, "compiler_identity", wraps=support.compiler_identity) as identity:
            assert support.default_ddc_seed(root, store) == eligible
        assert [call.args[0] for call in identity.call_args_list] == [eligible]
        alias_store = root / "store-alias"
        alias_store.symlink_to(store)
        expect_error("non-symlink directory", support.default_ddc_seed, root, alias_store)


def test_default_ddc_seed_rejects_failed_identities_and_never_uses_a_duplicate_alias() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        store = root / "store"
        eligible = fake_sysroot(store / "100.noindex", commit=DDC, date="2026-09-15")
        fake_sysroot(store / "200", commit="5" * 40, date="2026-09-17")
        broken = fake_sysroot(store / "200.noindex", commit="6" * 40, date="2026-09-18")
        (broken / "bin/trustc").write_text("#!/bin/sh\necho 'not compiler identity'\n")
        with mock.patch.object(support, "compiler_identity", wraps=support.compiler_identity) as identity:
            assert support.default_ddc_seed(root, store) == eligible
        assert [call.args[0] for call in identity.call_args_list] == [broken, eligible]
        (eligible / "lib/librustc_driver-0123.dylib").unlink()
        expect_error("no --ddc-seed given", support.default_ddc_seed, root, store)
        empty = root / "empty-store"
        empty.mkdir()
        expect_error("no --ddc-seed given", support.default_ddc_seed, root, empty)


def test_the_extracted_stage0_must_be_the_pin() -> None:
    with mock.patch.object(support.platform, "system", return_value="Darwin"), \
            tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        build = root / "build" / "pack-mint-x"
        stage0 = fake_sysroot(build / HOST / "stage0", commit=PIN, date="2026-07-13", trust_line=False)
        expected_stamp = support.stage0_extraction_stamp(support.read_stage0_pin(root))
        (stage0 / ".rustc-stamp").write_text(expected_stamp)
        assert support.pinned_stage0_identity(root, build, HOST)["commit"] == PIN
        (stage0 / ".rustc-stamp").write_text("trust-stage0-extraction-v1:" + "0" * 64)
        expect_error("not the pin's", support.pinned_stage0_identity, root, build, HOST)
        (stage0 / ".rustc-stamp").write_text("2026-06-01")
        expect_error("not the pin's", support.pinned_stage0_identity, root, build, HOST)
        other = root / "build" / "pack-mint-y"
        fake_sysroot(other / HOST / "stage0", commit=DDC, date="2026-07-13")
        (other / HOST / "stage0" / ".rustc-stamp").write_text(expected_stamp)
        expect_error("not the src/stage0 pin", support.pinned_stage0_identity, root, other, HOST)


def test_ddc_stage_reuses_one_path_and_restores_the_pinned_build() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        build = root / "build" / "pack-mint-0.10.0-host-abc"
        (build / HOST / "llvm" / "build" / "lib").mkdir(parents=True)
        (build / HOST / "llvm" / "build" / "lib" / "libLLVM.a").write_bytes(b"llvm")
        (build / HOST / "stage2" / "bin").mkdir(parents=True)
        (build / HOST / "stage2" / "bin" / "trustc").write_bytes(b"pinned")
        support.ddc_stage(root, build, HOST)
        pinned = build.with_name(build.name + ".pinned")
        assert (pinned / HOST / "stage2" / "bin" / "trustc").read_bytes() == b"pinned"
        assert (build / HOST / "llvm" / "build" / "lib" / "libLLVM.a").read_bytes() == b"llvm"
        assert not (build / HOST / "stage2").exists()
        expect_error("was not restored", support.ddc_stage, root, build, HOST)
        (build / HOST / "stage2" / "bin").mkdir(parents=True)
        (build / HOST / "stage2" / "bin" / "trustc").write_bytes(b"ddc")
        support.ddc_restore(root, build)
        assert (build / HOST / "stage2" / "bin" / "trustc").read_bytes() == b"pinned"
        assert not pinned.exists()
        support.ddc_restore(root, build)  # idempotent: nothing staged
        expect_error("pack-mint-", support.ddc_stage, root, root / "build" / "dev", HOST)


def test_ddc_compare_requires_identical_stage2_trees() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        trees = {}
        for name in ("pinned", "ddc"):
            stage2 = root / name / "stage2"
            (stage2 / "bin").mkdir(parents=True)
            (stage2 / "lib" / "rustlib").mkdir(parents=True)
            (stage2 / "bin" / "trustc").write_bytes(b"compiler")
            (stage2 / "lib" / "librustc_driver-1.dylib").write_bytes(b"driver")
            trees[name] = stage2
        manifests = {}
        for name, stage2 in trees.items():
            manifests[name] = root / f"{name}.json"
            support.write_json_exclusive(manifests[name], support.stage2_manifest(stage2))
        digest = support.ddc_compare(manifests["pinned"], manifests["ddc"])
        assert SHA256_RE.fullmatch(digest)
        support.verify_stage2_unchanged(manifests["pinned"], trees["pinned"])

        (trees["ddc"] / "lib" / "librustc_driver-1.dylib").write_bytes(b"DRIVER")
        (trees["ddc"] / "lib" / "extra.rlib").write_bytes(b"x")
        changed = root / "changed.json"
        support.write_json_exclusive(changed, support.stage2_manifest(trees["ddc"]))
        expect_error("differs: lib/librustc_driver-1.dylib", support.ddc_compare, manifests["pinned"], changed)
        expect_error("only from the DDC seed: lib/extra.rlib", support.ddc_compare, manifests["pinned"], changed)

        (trees["pinned"] / "bin" / "trustc").write_bytes(b"swapped after the DDC")
        expect_error("changed after the DDC", support.verify_stage2_unchanged, manifests["pinned"], trees["pinned"])


def test_links_are_compared_and_kept_and_the_archives_carry_the_compared_bytes() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        stage2 = root / "stage2"
        std = stage2 / "lib" / "rustlib" / HOST / "lib"
        std.mkdir(parents=True)
        (stage2 / "bin").mkdir()
        (stage2 / "bin" / "trustc").write_bytes(b"compiler")
        (stage2 / "bin" / "rustc").symlink_to("trustc")
        (stage2 / "lib" / "librustc_driver-1.dylib").write_bytes(b"driver")
        (std / "libstd-1.rlib").write_bytes(b"std")
        (stage2 / "lib" / "rustlib" / "src").mkdir()
        (stage2 / "lib" / "rustlib" / "src" / "rust").symlink_to(root)  # bootstrap's live source link
        manifest = root / "stage2.json"
        support.write_json_exclusive(manifest, support.stage2_manifest(stage2))
        support.verify_stage2_unchanged(manifest, stage2)

        # The receipt names the link a seal keeps, and not the one it replaces.
        records = support.load_json(manifest, "manifest")["records"]
        seed = {"host": HOST, "commit": PIN, "date": "2026-07-13", "compiler_sha256": "b" * 64, "driver_sha256": "c" * 64}
        text = support.render_receipt(
            source={"commit": CUT, "commit_date": "2026-09-29"},
            version="0.10.0",
            host=HOST,
            pinned=seed,
            ddc={**seed, "commit": DDC, "lineage": "trust", "relation": "same-lineage"},
            pinned_manifest={"sha256": "f" * 64, "records": records},
            ddc_manifest_sha256="f" * 64,
        )
        assert "compiler_link=trustc bin/rustc\n" in text
        assert "lib/rustlib/src/rust" not in text
        assert support.parse_receipt(text)["ddc_seed_relation"] == "same-lineage"
        assert not support.confined_link({"path": "lib/a", "target": "../../outside"})
        assert support.confined_link({"path": "lib/rustlib/a", "target": "../b"})

        # A compared link repointed after the DDC, or a directory swapped for a link, is caught.
        (stage2 / "bin" / "rustc").unlink()
        (stage2 / "bin" / "rustc").symlink_to("/elsewhere/rustc")
        expect_error("changed after the DDC compared it: bin/rustc", support.verify_stage2_unchanged, manifest, stage2)
        (stage2 / "bin" / "rustc").unlink()
        (stage2 / "bin" / "rustc").symlink_to("trustc")
        support.verify_stage2_unchanged(manifest, stage2)

        # The installed archives: every compared file they ship is the compared bytes.
        installed = root / "seed"
        (installed / "bin").mkdir(parents=True)
        (installed / "lib" / "rustlib" / HOST / "lib").mkdir(parents=True)
        (installed / "bin" / "trustc").write_bytes(b"compiler")
        (installed / "bin" / "targo").write_bytes(b"not compared")
        (installed / "lib" / "librustc_driver-1.dylib").write_bytes(b"driver")
        (installed / "lib" / "rustlib" / HOST / "lib" / "libstd-1.rlib").write_bytes(b"std")
        assert support.verify_archives_carry_compared(installed, manifest, HOST) == 3
        (installed / "lib" / "librustc_driver-1.dylib").write_bytes(b"another driver")
        expect_error(
            "ship lib/librustc_driver-1.dylib with other bytes",
            support.verify_archives_carry_compared, installed, manifest, HOST,
        )
        (installed / "lib" / "librustc_driver-1.dylib").write_bytes(b"driver")
        (installed / "lib" / "rustlib" / HOST / "lib" / "libstd-1.rlib").unlink()
        expect_error("no compared copy of std", support.verify_archives_carry_compared, installed, manifest, HOST)


def _stage2_record_fixture(root: Path) -> tuple[Path, dict[str, object]]:
    stage2 = root / "stage2"
    std = stage2 / "lib" / "rustlib" / HOST / "lib"
    std.mkdir(parents=True)
    (stage2 / "bin").mkdir()
    (stage2 / "bin" / "trustc").write_bytes(b"compiler")
    (stage2 / "lib" / "librustc_driver-1.dylib").write_bytes(b"driver")
    (std / "libstd-1.rlib").write_bytes(b"std")
    (stage2 / "bin" / "rustc").symlink_to("trustc")
    # Capturing an external source link remains valid: the record binds the link.
    (stage2 / "source").symlink_to(root)
    return stage2, support.stage2_manifest(stage2)


def _reject_stage2_record_fixture(
    root: Path, stage2: Path, manifest: dict[str, object] | str, fragment: str,
) -> None:
    bad = root / "bad.json"
    bad.write_text(manifest if isinstance(manifest, str) else json.dumps(manifest))
    good = root / "good.json"
    support.write_json_exclusive(good, support.stage2_manifest(stage2))
    expect_error(fragment, support.ddc_compare, bad, bad)
    expect_error(fragment, support.ddc_compare, bad, good)
    expect_error(fragment, support.ddc_compare, good, bad)
    expect_error(fragment, support.verify_stage2_unchanged, bad, stage2)
    expect_error(fragment, support.verify_archives_carry_compared, stage2, bad, HOST)
    for index, (left, right) in enumerate(((bad, good), (good, bad))):
        evidence = root / f"evidence-{index}"
        expect_error(fragment, support.ddc_evidence, left, right, stage2, stage2, evidence)
        assert not evidence.exists(), "malformed evidence must refuse before any copy"


def test_stage2_manifest_readers_validate_record_shapes_and_tree_digests() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        for name in ("digest", "truncated", "schema", "duplicates", "mode", "bytes", "file-hash", "kind", "fields"):
            case = root / name
            case.mkdir()
            stage2, manifest = _stage2_record_fixture(case)
            bad = copy.deepcopy(manifest)
            file = next(record for record in bad["records"] if record["kind"] == "file")
            if name == "digest":
                bad["sha256"] = "f" * 64
                fragment = "digest does not match its records"
            elif name == "truncated":
                bad["records"].pop()
                fragment = "digest does not match its records"
            elif name == "schema":
                bad["schema"] = "unknown-stage-tree"
                fragment = "invalid stage2 manifest schema"
            else:
                if name == "duplicates":
                    bad["records"].append(copy.deepcopy(file))
                    fragment = "repeats stage2 record path"
                elif name == "mode":
                    file["mode"] = True
                    fragment = "invalid stage2 record mode"
                elif name == "bytes":
                    file["bytes"] = True
                    fragment = "invalid stage2 file metadata"
                elif name == "file-hash":
                    file["sha256"] = "not-a-file-digest"
                    fragment = "invalid stage2 file metadata"
                elif name == "kind":
                    file["kind"] = "socket"
                    fragment = "invalid stage2 record"
                else:
                    file["unchecked"] = "ignored metadata"
                    fragment = "invalid stage2 record"
                bad["sha256"] = support.records_sha256(bad["records"])
            _reject_stage2_record_fixture(case, stage2, bad, fragment)


def test_stage2_manifest_paths_are_confined_and_have_directory_parents() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        paths = ("../escape", "bin/../../escape", "bin//trustc", "bin/./trustc", ".", "")
        for index, relative in enumerate((*paths, str(root / "absolute"))):
            case = root / str(index)
            case.mkdir()
            stage2, bad = _stage2_record_fixture(case)
            file = next(record for record in bad["records"] if record["kind"] == "file")
            file["path"] = relative
            bad["sha256"] = support.records_sha256(bad["records"])
            _reject_stage2_record_fixture(case, stage2, bad, "stage2 record path")
        for parent_kind in ("missing", "file", "symlink"):
            case = root / parent_kind
            case.mkdir()
            stage2, bad = _stage2_record_fixture(case)
            bad["records"] = [record for record in bad["records"] if record["path"] != "bin"]
            if parent_kind == "file":
                bad["records"].append({"path": "bin", "kind": "file", "mode": 0o644,
                                       "bytes": 0, "sha256": hashlib.sha256(b"").hexdigest()})
            elif parent_kind == "symlink":
                bad["records"].append({"path": "bin", "kind": "symlink", "target": str(root)})
            bad["sha256"] = support.records_sha256(bad["records"])
            _reject_stage2_record_fixture(case, stage2, bad, "without its directory")


def test_stage2_manifest_json_keys_are_unambiguous() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        for name, old, replacement in (
            ("tree", '"schema":', '"schema": "ignored-first-value", "schema":'),
            ("record", '"kind":', '"kind": "ignored-first-value", "kind":'),
        ):
            case = root / name
            case.mkdir()
            stage2, manifest = _stage2_record_fixture(case)
            ambiguous = json.dumps(manifest).replace(old, replacement, 1)
            _reject_stage2_record_fixture(case, stage2, ambiguous, "repeats JSON key")


def test_stage2_manifest_validation_keeps_empty_captures_and_receipt_refusals() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        stage2 = root / "stage2"
        stage2.mkdir()
        manifest = root / "empty.json"
        support.write_json_exclusive(manifest, support.stage2_manifest(stage2))
        assert support.ddc_compare(manifest, manifest) == hashlib.sha256(b"").hexdigest()
        support.verify_stage2_unchanged(manifest, stage2)
        expect_error("no compared copy of", support.verify_archives_carry_compared, stage2, manifest, HOST)
        invalid = root / "invalid.json"
        value = support.stage2_manifest(stage2)
        value["sha256"] = "f" * 64
        support.write_json_exclusive(invalid, value)
        pinned_seed = root / "pinned-seed.json"
        ddc_seed = root / "ddc-seed.json"
        identity = {"host": HOST, "commit": PIN, "date": "2026-07-13",
                    "compiler_sha256": "b" * 64, "driver_sha256": "c" * 64}
        support.write_json_exclusive(pinned_seed, identity)
        support.write_json_exclusive(ddc_seed, {**identity, "commit": DDC,
                                              "lineage": "trust", "relation": "same-lineage"})
        output = root / "receipt"
        arguments = ["write-receipt", "--root", str(root), "--version", "0.10.0", "--host", HOST,
                     "--pinned-seed", str(pinned_seed), "--ddc-seed", str(ddc_seed),
                     "--pinned-manifest", str(invalid), "--ddc-manifest", str(invalid), "--output", str(output)]
        with contextlib.redirect_stderr(io.StringIO()) as errors, \
                mock.patch.object(support, "repository_state", return_value={"commit": CUT, "commit_date": "2026-09-29"}), \
                mock.patch.object(support, "committed_seed_mint", return_value={}):
            assert support.main(arguments) == 1
        assert "digest does not match its records" in errors.getvalue()
        assert not output.exists()


def test_ddc_config_compiles_with_the_ddc_seed_and_drives_with_the_pinned_cargo() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        source = root / "bootstrap.toml"
        source.write_text('profile = "compiler"\n')
        seed = fake_sysroot(root / "store" / "9178", commit=DDC, date="2026-09-15")
        (seed / "bin" / "trustdoc").write_text("#!/bin/sh\n")
        cargo = root / "build" / "pack-mint-x.pinned" / HOST / "stage0" / "bin" / "cargo"
        cargo.parent.mkdir(parents=True)
        cargo.write_text("#!/bin/sh\n")
        output = root / "work" / "bootstrap.ddc.toml"
        support.write_ddc_config(source, output, seed / "bin" / "trustc", cargo, root / "work" / "bin" / "tippy")
        parsed = tomllib.loads(output.read_text())
        assert parsed["include"] == [str(source)]
        assert parsed["build"]["rustc"] == str(seed / "bin" / "trustc")
        assert parsed["build"]["cargo"] == str(cargo)
        assert parsed["build"]["rustdoc"] == str(seed / "bin" / "trustdoc")
        assert parsed["rust"]["download-rustc"] is False
        expect_error("already exists", support.write_ddc_config, source, output, seed / "bin" / "trustc", cargo, root / "t")


def test_dist_components_are_read_from_prepare() -> None:
    components = support.dist_producer_components(REPO_ROOT)
    assert components[:3] == ("trustc", "trustc-dev", "trust-std")
    assert "trust-src" in components and "tippy" in components


def test_the_cut_dists_exactly_the_seed_cohort_the_repin_binds() -> None:
    # Measured 2026-10-15 (a dry run of the re-pin on the m2 cut of 25a12e7777): the
    # cut had asked x.py dist for prepare.py's whole producer list, prepare.py pinned
    # trust-docs and trust-llvm-tools too, and the re-pin refused: "archive is outside
    # the exact seed cohort: dist/2026-10-15/trust-docs-0.10.0-...".
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    import seed_host_ledger

    prepare = support.stage0_preparer(REPO_ROOT)
    components = support.dist_producer_components(REPO_ROOT)
    assert set(components) == set(support.SEED_COMPONENTS), components
    assert set(support.SEED_COMPONENTS) == set(seed_host_ledger.COMPONENTS)
    assert len(components) == len(set(components))
    assert {"trust-docs", "trust-llvm-tools"} <= set(prepare.STAGE0_DIST_PRODUCER_ALIASES)
    assert not {"trust-docs", "trust-llvm-tools"} & set(components), components
    # prepare.py's own order is kept.
    order = [prepare.STAGE0_DIST_PRODUCER_ALIASES.index(component) for component in components]
    assert order == sorted(order), components

    class Narrowed:
        STAGE0_DIST_PRODUCER_ALIASES = tuple(
            alias for alias in prepare.STAGE0_DIST_PRODUCER_ALIASES if alias != "targo-trust"
        )

    with mock.patch.object(support, "stage0_preparer", return_value=Narrowed):
        expect_error("targo-trust", support.dist_producer_components, REPO_ROOT)


def git(root: Path, *arguments: str) -> str:
    return subprocess.run(
        ["git", "-C", str(root), *arguments],
        check=True,
        text=True,
        capture_output=True,
        env={**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"},
    ).stdout.strip()


def test_the_cut_needs_every_gitlink_checked_out_at_its_pin() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        for repo in (root, root / "first-party" / "ty"):
            repo.mkdir(parents=True, exist_ok=True)
            git(repo, "init", "-q", "-b", "main")
            git(repo, "config", "user.name", "Fixture")
            git(repo, "config", "user.email", "fixture@example.com")
        (root / "first-party" / "ty" / "lib.rs").write_text("// ty\n")
        git(root / "first-party" / "ty", "add", "-A")
        git(root / "first-party" / "ty", "commit", "-q", "-m", "ty")
        pinned = git(root / "first-party" / "ty", "rev-parse", "HEAD")
        (root / "README").write_text("superproject\n")
        git(root, "add", "README")
        git(root, "update-index", "--add", "--cacheinfo", f"160000,{pinned},first-party/ty")
        git(root, "update-index", "--add", "--cacheinfo", f"160000,{pinned},first-party/ay")
        git(root, "commit", "-q", "-m", "gitlinks")
        # first-party/ay is recorded but never checked out (an empty directory, as a
        # clone without submodules leaves it): `git status` calls it clean.
        (root / "first-party" / "ay").mkdir()
        assert git(root, "status", "--porcelain", "--ignore-submodules=none", "--untracked-files=all") == ""
        expect_error("checked out at its pinned commit", support.repository_state, root)
        expect_error(": first-party/ay", support.repository_state, root)
        git(root, "update-index", "--force-remove", "first-party/ay")
        git(root, "commit", "-q", "-m", "one gitlink")
        assert support.repository_state(root)["commit"] == git(root, "rev-parse", "HEAD")


def test_repin_is_one_commit_on_top_of_the_cut_and_leaves_the_checkout_alone() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        git(root, "init", "-q", "-b", "main")
        git(root, "config", "user.name", "Fixture")
        git(root, "config", "user.email", "fixture@example.com")
        (root / ".gitignore").write_text("/build\n/bootstrap/trust-stage0/dist/**/*.tar.xz\n")
        (root / "src").mkdir()
        (root / "src" / "stage0").write_text(stage0_text(PIN, "2026-07-13", "1.99.0-trust", "d" * 64))
        seed_root = root / "bootstrap" / "trust-stage0"
        (seed_root / "dist" / "2026-07-13").mkdir(parents=True)
        (seed_root / "dist" / "2026-07-13" / "channel-rust-trust.toml").write_text("old\n")
        (seed_root / "dist" / "README.md").write_text("kept\n")
        (seed_root / "seed-ledger.toml").write_text(
            "# ledger header, kept verbatim\n\n"
            'scope = "internal"\npromotion_decision = "admit-internal"\n'
            'signatures = ["placeholder:internal-admission-only:not-publicly-signed"]\n'
            'checksums = ["sha256:' + "d" * 64 + '"]\n\n'
            '[release]\nrepo = "owner/trust"\ntag = "trust-stage0-2026-07-13"\nvisibility = "private"\n'
            # The host the committed pin records (a single-host ledger): the re-pin
            # keeps it, and refuses a ledger that does not say which hosts it records.
            f'host_triple = "{HOST}"\n'
        )
        (root / "build").mkdir()
        git(root, "add", "-A")
        (root / "src" / "version").write_text("0.10.0\n")
        git(root, "add", "src/version")
        git(root, "commit", "-q", "-m", "cut")
        cut = git(root, "rev-parse", "HEAD")

        date = support.repository_state(root, cut)["commit_date"]
        prepared = root / "build" / "pack-mint-x" / "repin"
        out = prepared / "bootstrap" / "trust-stage0"
        (out / "dist" / date).mkdir(parents=True)
        (out / "dist" / date / "channel-rust-trust.toml").write_text("new\n")
        (out / "dist" / date / f"trustc-0.10.0-trust-{HOST}.tar.xz").write_bytes(b"archive")
        (out / "dist" / "channel-rust-trust.toml").write_text("new\n")
        (out / "trust-stage0-admission.json").write_text("{}\n")
        manifest_digest = hashlib.sha256(b"new\n").hexdigest()
        generated = stage0_text(cut, date, "0.10.0-trust", hashlib.sha256(b"archive").hexdigest()).replace(
            "min_stage0_rustc_version=1.96.0\n", ""
        ).replace("c" * 64, manifest_digest)
        for component in support.SEED_COMPONENTS:
            if component == "trustc":
                continue
            suffix = "" if component == "trust-src" else f"-{HOST}"
            filename = f"{component}-0.10.0-trust{suffix}.tar.xz"
            (out / "dist" / date / filename).write_bytes(b"archive")
            generated += f"dist/{date}/{filename}={hashlib.sha256(b'archive').hexdigest()}\n"
        (prepared / "src-stage0").write_text(generated)
        receipt = root / "build" / "pack-mint-x" / "trust-seed-mint"
        receipt.write_text(
            "# SEED-MINT\n"
            f"schema=trust-seed-mint-v1\nsource_commit={cut}\nsource_commit_date={date}\n"
            f"host={HOST}\nsource_version=0.10.0\n"
            f"pinned_seed_commit={PIN}\npinned_seed_date=2026-07-13\n"
            f"pinned_seed_compiler_sha256={'1' * 64}\npinned_seed_driver_sha256={'2' * 64}\n"
            f"ddc_seed_relation=pin-ancestor\nddc_seed_commit={DDC}\nddc_seed_lineage=trust\n"
            f"ddc_seed_date=2026-07-12\nddc_seed_compiler_sha256={'3' * 64}\nddc_seed_driver_sha256={'4' * 64}\n"
            "ddc_build_driver=the pinned seed's cargo, in both builds\n"
            "ddc_scope=<build>/<host>/stage2 after x.py build --stage 2 compiler/rustc library/std\n"
            f"stage2_tree_sha256_pinned_seed={'f' * 64}\nstage2_tree_sha256_ddc_seed={'f' * 64}\n"
            "ddc_verdict=identical\nlineage_disjoint_anchor=none\nself_host_proof=pass\n"
            f"compiler_file={'a' * 64} bin/trustc\n"
        )
        surface = root / "build" / "surface.json"
        surface.write_text(json.dumps({"schema": "trust-self-host-seed-surface-v1",
            "host": HOST, "source_version": "0.10.0",
            "entrypoint_sha256": {name: "5" * 64 for name in ("trustc", "rustc", "trustdoc", "targo", "cargo", "trustfmt")},
            "tree": {"sha256": "6" * 64}, "tool_versions": {
            "trustc": "rustc 1.99.0-dev (333333333 2026-09-29) (trustc 0.10.0)\nbinary: trustc",
            "targo": "targo 1.99.0-dev",
            "trustfmt": "trustfmt 1.9.0-trust",
        }}))
        work = root / "build" / "work"
        work.mkdir()
        # A reproducibility control compared nothing diverse: it never re-pins.
        control = root / "build" / "control-receipt"
        control.write_text(receipt.read_text().replace("=pin-ancestor", "=reproducibility-control"))
        expect_error(
            "not a reproducibility control",
            support.repin,
            root, prepared, cut, HOST, "seed/repin-x", "Cutter <cutter@example.com>", control, surface, work,
        )
        new_commit, tag, stage0_sha256 = support.repin(
            root, prepared, cut, HOST, "seed/repin-x", "Cutter <cutter@example.com>", receipt, surface, work
        )

        assert git(root, "rev-parse", "HEAD") == cut
        assert git(root, "status", "--porcelain", "--untracked-files=no") == ""
        assert git(root, "rev-parse", "seed/repin-x") == new_commit
        assert git(root, "rev-parse", f"{new_commit}^") == cut
        assert git(root, "log", "-1", "--format=%an <%ae>", new_commit) == "Cutter <cutter@example.com>"
        stage0 = git(root, "show", f"{new_commit}:src/stage0")
        assert "min_stage0_rustc_version=1.96.0" in stage0  # the editable head survives
        assert f"compiler_git_commit_hash={cut}" in stage0
        assert hashlib.sha256((stage0 + "\n").encode()).hexdigest() == stage0_sha256
        files = set(git(root, "ls-tree", "-r", "--name-only", new_commit).splitlines())
        assert f"bootstrap/trust-stage0/dist/{date}/channel-rust-trust.toml" in files
        assert "bootstrap/trust-stage0/dist/2026-07-13/channel-rust-trust.toml" not in files
        assert "bootstrap/trust-stage0/dist/README.md" in files
        assert not any(name.endswith(".tar.xz") for name in files)
        ledger = tomllib.loads(git(root, "show", f"{new_commit}:bootstrap/trust-stage0/seed-ledger.toml"))
        assert git(root, "show", f"{new_commit}:bootstrap/trust-stage0/seed-ledger.toml").startswith(
            "# ledger header, kept verbatim"
        )
        assert ledger["checksums"] == ["sha256:" + hashlib.sha256(b"archive").hexdigest()] * len(support.SEED_COMPONENTS)
        assert ledger["promotion_decision"] == "admit-internal"
        assert ledger["release"]["repo"] == "owner/trust"
        assert ledger["release"]["tag"] == tag == f"trust-stage0-{date}-{cut[:9]}"
        assert ledger["release"]["compiler_git_commit_hash"] == cut
        assert ledger["release"]["reported_product_identities"]["trustc"].endswith("(trustc 0.10.0)")
        assert ledger["release"]["mint"]["ddc_seed_commit"] == DDC
        assert ledger["release"]["mint"]["ddc_seed_relation"] == "pin-ancestor"
        assert ledger["release"]["mint"]["lineage_disjoint_anchor"] == "none"
        message = git(root, "log", "-1", "--format=%B", new_commit)
        assert "pin-ancestor" in message and "not diverse" in message and "diverse double" not in message
        assert f"repin_commit={new_commit}" in receipt.read_text()
        assert f"repin_compiler_git_commit_hash={cut}" in receipt.read_text()

        # A re-pin is never moved: the same branch again is refused.
        expect_error(
            "update-ref",
            support.create_repin_commit,
            root, cut, "seed/repin-x", {}, [], "again\n", "Cutter <cutter@example.com>", work,
        )


LINUX_HOST = "aarch64-unknown-linux-gnu"


def test_repin_files_removes_a_dropped_fixed_point_hosts_proofs() -> None:
    # docs/PLAN.md PKG-S6: a fixed-point host's receipt and evidence directory
    # are re-pin metadata like a mint host's three proof files. A cut that drops
    # the host (a typed --drop-host) removes them; what the cut writes is kept,
    # and so is anything else in the host's directory.
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        git(root, "init", "-q", "-b", "main")
        git(root, "config", "user.name", "Fixture")
        git(root, "config", "user.email", "fixture@example.com")
        (root / ".gitignore").write_text("/bootstrap/trust-stage0/dist/**/*.tar.xz\n")
        proofs = root / "bootstrap" / "trust-stage0" / "host-proofs"
        dropped = [f"{LINUX_HOST}/SEED-FIXED-POINT", f"{LINUX_HOST}/seed-surface.json",
                   f"{LINUX_HOST}/host-record.json", f"{LINUX_HOST}/fixed-point/stage2-producer.json",
                   f"{LINUX_HOST}/fixed-point/run-producer.json"]
        written = [f"{HOST}/SEED-MINT", f"{HOST}/seed-surface.json", f"{HOST}/host-record.json"]
        for relative in (*dropped, *written, f"{LINUX_HOST}/NOTES.md"):
            (proofs / relative).parent.mkdir(parents=True, exist_ok=True)
            (proofs / relative).write_text(f"{relative}\n")
        git(root, "add", "-A")
        git(root, "commit", "-q", "-m", "two hosts recorded")
        prepared = root / "prepared"
        out = prepared / "bootstrap" / "trust-stage0" / "host-proofs"
        for relative in written:
            (out / relative).parent.mkdir(parents=True, exist_ok=True)
            (out / relative).write_text("new\n")
        writes, removals = support.repin_files(root, prepared)
        prefix = "bootstrap/trust-stage0/host-proofs/"
        assert set(writes) == {prefix + relative for relative in written}, writes
        assert sorted(removals) == sorted(prefix + relative for relative in dropped), removals


def test_a_cut_names_each_recorded_host_it_drops_before_it_builds() -> None:
    script = REPO_ROOT / "scripts/mint_and_prove_seed.sh"
    text = script.read_text()
    # The option: repeatable, one host each, never empty.
    for argv, message in ((["--drop-host"], "--drop-host requires a value"),
                          (["--drop-host", ""], "--drop-host requires a host triple")):
        refused = subprocess.run(["/bin/bash", str(script), *argv], capture_output=True, text=True, timeout=60)
        assert refused.returncode == 2 and message in refused.stderr, (argv, refused.stderr)
    assert "--drop-host TRIPLE" in text and "DROP_HOSTS+=(\"$2\")" in text
    # Where: once the host is known, before any build, and before --check-only returns.
    call = '"$PYTHON_BIN" -I -S "$HELPER" recorded-hosts --root "$ROOT" --host "$HOST" \\\n'
    assert text.count(call) == 1
    early = text.index(call)
    assert text.index('case "$HOST" in') < early
    for later in ('"$HELPER" make-work', "CHECK OK: the pin is materialized", '"$ROOT/x.py"', '"$HELPER" repin \\'):
        assert early < text.index(later), later
    # The re-pin is told the same drops.
    assert '--work "$WORK" \\\n        ${DROP_HOST_ARGS[@]+"${DROP_HOST_ARGS[@]}"}\n)' in text
    # macOS /bin/bash 3.2 reads an empty array as unbound under set -u, so a cut
    # with no --drop-host would stop at a bare "${a[@]}": every expansion of
    # these arrays is the ${a[@]+"${a[@]}"} form (the bash here is 5.x, where
    # the snippet run below cannot tell the two apart).
    for name in ("DROP_HOSTS", "DROP_HOST_ARGS"):
        idiom = "${%s[@]+\"${%s[@]}\"}" % (name, name)
        assert text.count(idiom) > 0, name
        assert text.count("${%s[@]" % name) == 2 * text.count(idiom), name
        assert "${%s[*]" % name not in text and "$%s" % name not in text.replace("${", ""), name
    # The early check itself, run as the script runs it (bash, set -eu).
    snippet = text[text.index("DROP_HOST_ARGS=()"):early] + call + '    ${DROP_HOST_ARGS[@]+"${DROP_HOST_ARGS[@]}"}\n'
    assert snippet in text
    header = '[release]\nrepo = "owner/trust"\n'
    darwin = f'[release.hosts."{HOST}"]\nschema = "trust-seed-host-record-v1"\n'
    linux = (f'[release.hosts."{LINUX_HOST}"]\nschema = "trust-seed-fixed-point-host-record-v1"\n'
             f'[release.hosts."{LINUX_HOST}".root_disclosure]\nroot = "unpinned-host-chain"\n')
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        ledger = root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
        ledger.parent.mkdir(parents=True)

        def cut(host: str, *drops: str) -> subprocess.CompletedProcess:
            harness = (
                f"PYTHON_BIN={shlex.quote(sys.executable)}\n"
                f"HELPER={shlex.quote(str(REPO_ROOT / 'scripts/mint_seed_support.py'))}\n"
                f"ROOT={shlex.quote(str(root))}\nHOST={host}\n"
                f"DROP_HOSTS=({' '.join(shlex.quote(drop) for drop in drops)})\n"
                + snippet + "echo REACHED\n"
            )
            return subprocess.run(["/bin/bash", "-eu", "-c", harness], capture_output=True, text=True, timeout=60)

        ledger.write_text(header + darwin)
        # Today's one-host ledger: the check passes, with no drop typed (an empty array under set -u).
        alone = cut(HOST)
        assert (alone.returncode, alone.stdout) == (0, "REACHED\n"), alone.stderr
        ledger.write_text(header + darwin + linux)
        stopped = cut(HOST)
        assert stopped.returncode == 1 and "REACHED" not in stopped.stdout, stopped
        assert f"this re-pin would drop {LINUX_HOST}" in stopped.stderr, stopped.stderr
        typed = cut(HOST, LINUX_HOST)
        assert typed.returncode == 0 and typed.stdout.endswith("REACHED\n"), typed.stderr
        assert f"re-pin drops recorded host(s) {LINUX_HOST}" in typed.stdout
        # The fixed-point host itself cannot be cut by the mint, whatever is dropped.
        linux_cut = cut(LINUX_HOST, HOST)
        assert linux_cut.returncode == 1 and "carries root_disclosure" in linux_cut.stderr, linux_cut.stderr


def test_workflow_shell_keeps_command_policy_and_claim_boundary() -> None:
    script = Path(__file__).resolve().parents[1] / "mint_and_prove_seed.sh"
    text = script.read_text()
    # One x.py launcher carries the flags every build of the cut shares.
    assert text.count("$ROOT/x.py") == 1
    assert text.count("--set build.submodules=false") == 1
    assert "bootstrap.seed.toml" in text
    assert "not a kernel" in text.lower()
    assert "ls " not in text and "head -" not in text
    # The pack cut: pin only, a DDC at one path, a commit-bound re-pin.
    for fragment in (
        "require-pinned-seed",
        "check_seed_freshness.py\" --require-payloads",
        "--ddc-seed",
        "default-ddc-seed",
        "ddc-stage",
        "ddc-restore",
        "ddc-compare",
        "verify-stage2-unchanged",
        "verify-archives-carry-compared",
        "reproducibility-control)",
        "write-receipt",
        "repin",
    ):
        assert fragment in text, fragment


def test_the_cut_lays_out_the_rustc_dev_handoff_prepare_requires() -> None:
    # Measured 2026-10-15 on the m2 cut of 25a12e7777: prepare.py, given the
    # cut's fresh output root, refused with "trustc-dev artifact handoff
    # preflight failed" (no trustc-dev under artifacts/<commit>/ and
    # artifacts-with-llvm-assertions/<commit>/), after the proof rebuild.
    prepare = support.stage0_preparer(REPO_ROOT)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        dist = root / "dist"
        work = root / "work"
        dist.mkdir()
        work.mkdir()
        write_component_set(dist)
        inputs = work / "seed-inputs.json"
        support.stage_artifacts(dist, work, VERSION, HOST, COMMIT, inputs)
        channel = {
            "pkg": {
                component: {
                    "target": {
                        HOST: {
                            "available": True,
                            "xz_url": f"https://trust.invalid/d/{component}-{VERSION}-trust-{HOST}.tar.xz",
                        }
                    }
                }
                for component in ("trustc", "trustc-dev")
            }
        }

        def check(output_root: Path) -> tuple[Path, ...]:
            return prepare.validate_rustc_dev_artifact_handoff(
                channel,
                output_root=output_root,
                git_commit_hash=COMMIT,
                source_channel="trust",
                owned_channel="trust",
            )

        output_root = root / "repin" / "bootstrap" / "trust-stage0"
        try:
            check(output_root)
        except ValueError as exc:
            assert "trustc-dev artifact handoff preflight failed" in str(exc), str(exc)
        else:
            raise AssertionError("prepare.py accepted a seed root with no trustc-dev handoff")

        staged = support.stage_rustc_dev_handoff(REPO_ROOT, inputs, work, output_root)
        admitted = (dist / f"trustc-dev-{VERSION}-trust-{HOST}.tar.xz").read_bytes()
        assert sorted(staged) == sorted(check(output_root)), (staged, check(output_root))
        assert {path.parent.parent.name for path in staged} == set(prepare.STAGE0_ARTIFACT_ROOTS)
        for path in staged:
            assert path.parent.name == COMMIT and not path.is_symlink()
            assert path.read_bytes() == admitted
        expect_error("must be new", support.stage_rustc_dev_handoff, REPO_ROOT, inputs, work, output_root)

        swapped = work / "artifacts" / f"trustc-dev-{VERSION}-trust-{HOST}.tar.xz"
        swapped.write_bytes(admitted + b"swapped after admission")
        other_root = root / "other" / "bootstrap" / "trust-stage0"
        expect_error(
            "changed after admission",
            support.stage_rustc_dev_handoff,
            REPO_ROOT,
            inputs,
            work,
            other_root,
        )
        assert not any(path.is_file() for path in other_root.rglob("*")), list(other_root.rglob("*"))

    script = Path(__file__).resolve().parents[1] / "mint_and_prove_seed.sh"
    lines = script.read_text().splitlines()

    def index(fragment: str) -> int:
        hits = [number for number, line in enumerate(lines) if fragment in line]
        assert len(hits) == 1, (fragment, hits)
        return hits[0]

    admission = index('"$PYTHON_BIN" -I -S "$HELPER" stage-artifacts \\')
    handoff = index('"$PYTHON_BIN" -I -S "$HELPER" rustc-dev-handoff \\')
    prepared = index('"$PYTHON_BIN" -I "$ROOT/src/tools/trust-stage0-dist/prepare.py" \\')
    assert admission < handoff < prepared, (admission, handoff, prepared)
    assert '--output-root "$PREPARED/bootstrap/trust-stage0"' in lines[handoff + 4], lines[handoff + 4]


def assert_metadata_only_ddc_evidence(
    pinned_stage2: Path, independent_stage2: Path, output: Path, difference: str
) -> None:
    manifests = []
    for label, stage2 in (("pinned", pinned_stage2), ("ddc", independent_stage2)):
        manifest = output.parent / f"{label}.json"
        support.write_json_exclusive(manifest, support.stage2_manifest(stage2))
        manifests.append(manifest)
    expect_error("DDC FAILED", support.ddc_compare, *manifests)
    assert support.ddc_evidence(
        *manifests, pinned_stage2, independent_stage2, output
    ) == 1
    assert stat.S_IMODE(output.stat().st_mode) == 0o700
    assert sorted(path.name for path in output.iterdir()) == [
        "differences.txt", "stage2-ddc-seed.json", "stage2-pinned-seed.json"
    ]
    assert (output / "differences.txt").read_text() == difference + "\n"
    for label, manifest in zip(("pinned", "ddc"), manifests):
        assert (output / f"stage2-{label}-seed.json").read_bytes() == manifest.read_bytes()
    # Capturing diagnostics neither changes the comparison nor turns its
    # retained manifests into an agreeing comparison.
    expect_error("DDC FAILED", support.ddc_compare, *manifests)
    expect_error(
        "DDC FAILED", support.ddc_compare,
        output / "stage2-pinned-seed.json", output / "stage2-ddc-seed.json",
    )


def test_ddc_evidence_keeps_symlink_only_mismatches() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        pinned = root / "pinned"
        independent = root / "ddc"
        for stage2, target in ((pinned, "trustc"), (independent, "other-trustc")):
            stage2.mkdir()
            (stage2 / "rustc").symlink_to(target)
        assert_metadata_only_ddc_evidence(
            pinned, independent, root / "evidence", "differs: rustc"
        )


def test_ddc_evidence_keeps_directory_mode_only_mismatches() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        pinned = root / "pinned"
        independent = root / "ddc"
        for stage2, mode in ((pinned, 0o755), (independent, 0o700)):
            (stage2 / "lib").mkdir(parents=True)
            (stage2 / "lib").chmod(mode)
        assert_metadata_only_ddc_evidence(
            pinned, independent, root / "evidence", "differs: lib"
        )


def test_ddc_evidence_keeps_added_empty_directories() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        pinned = root / "pinned"
        independent = root / "ddc"
        pinned.mkdir()
        (independent / "empty").mkdir(parents=True)
        assert_metadata_only_ddc_evidence(
            pinned, independent, root / "evidence", "only from the DDC seed: empty"
        )


def test_ddc_evidence_refuses_foreign_destinations_without_changing_them() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        manifests = []
        trees = []
        for label, target in (("pinned", "trustc"), ("ddc", "other-trustc")):
            stage2 = root / label
            stage2.mkdir()
            (stage2 / "rustc").symlink_to(target)
            manifest = root / f"{label}.json"
            support.write_json_exclusive(manifest, support.stage2_manifest(stage2))
            manifests.append(manifest)
            trees.append(stage2)
        foreign = root / "foreign"
        foreign.mkdir()
        (foreign / "sentinel").write_bytes(b"not this workflow's output")
        for kind in ("empty-directory", "directory", "file", "symlink", "dangling-symlink"):
            output = root / kind
            if kind in ("empty-directory", "directory"):
                output.mkdir()
                if kind == "directory":
                    (output / "sentinel").write_bytes(b"not this workflow's output")
            elif kind == "file":
                output.write_bytes(b"not this workflow's output")
            else:
                output.symlink_to(foreign if kind == "symlink" else root / "missing")
            before = support.tree_records(root, "DDC destination fixture")
            expect_error("already exists", support.ddc_evidence, *manifests, *trees, output)
            assert support.tree_records(root, "DDC destination fixture") == before, kind


def test_ddc_evidence_refuses_a_racing_foreign_destination() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        manifests = []
        trees = []
        for label, target in (("pinned", "trustc"), ("ddc", "other-trustc")):
            stage2 = root / label
            stage2.mkdir()
            (stage2 / "rustc").symlink_to(target)
            manifest = root / f"{label}.json"
            support.write_json_exclusive(manifest, support.stage2_manifest(stage2))
            manifests.append(manifest)
            trees.append(stage2)
        output = root / "evidence"
        mkdir = Path.mkdir
        foreign_records = []

        def claim_first(path: Path, *args: object, **kwargs: object) -> None:
            if path == output and not foreign_records:
                mkdir(path)
                (path / "sentinel").write_bytes(b"claimed by another workflow")
                foreign_records.extend(support.tree_records(root, "DDC destination fixture"))
            mkdir(path, *args, **kwargs)

        with mock.patch.object(Path, "mkdir", claim_first):
            expect_error("already exists", support.ddc_evidence, *manifests, *trees, output)
        assert foreign_records
        assert support.tree_records(root, "DDC destination fixture") == foreign_records


def test_ddc_metadata_evidence_survives_restore_without_waiving_comparison() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        build = root / "build" / "pack-mint-ddc-evidence"
        (build / HOST / "llvm").mkdir(parents=True)
        stage2 = build / HOST / "stage2"
        stage2.mkdir()
        (stage2 / "rustc").symlink_to("trustc")
        support.ddc_stage(root, build, HOST)
        pinned = build.with_name(build.name + ".pinned")
        stage2.mkdir()
        (stage2 / "rustc").symlink_to("other-trustc")
        evidence = pinned / "ddc-evidence"
        assert_metadata_only_ddc_evidence(
            pinned / HOST / "stage2", stage2, evidence, "differs: rustc"
        )
        before = support.tree_records(evidence, "DDC evidence fixture")
        support.ddc_restore(root, build)
        restored = build / "ddc-evidence"
        assert support.tree_records(restored, "DDC evidence fixture") == before
        assert (stage2 / "rustc").readlink() == Path("trustc")
        assert not pinned.exists()
        expect_error(
            "DDC FAILED", support.ddc_compare,
            restored / "stage2-pinned-seed.json", restored / "stage2-ddc-seed.json",
        )


def test_a_failed_ddc_keeps_both_seeds_copies_of_what_differs() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp).resolve()
        trees = {}
        for name in ("pinned", "ddc"):
            stage2 = root / name / "stage2"
            (stage2 / "bin").mkdir(parents=True)
            (stage2 / "lib").mkdir(parents=True)
            (stage2 / "bin" / "trustc").write_bytes(b"compiler")
            (stage2 / "lib" / "libsame.rlib").write_bytes(b"same")
            trees[name] = stage2
        manifests = {}
        for name, stage2 in trees.items():
            manifests[name] = root / f"{name}.json"
            support.write_json_exclusive(manifests[name], support.stage2_manifest(stage2))
        agreeing = root / "agreeing"
        assert support.ddc_evidence(
            manifests["pinned"], manifests["ddc"], trees["pinned"], trees["ddc"], agreeing
        ) == 0
        assert not agreeing.exists()

        (trees["ddc"] / "bin" / "trustc").write_bytes(b"other compiler")
        (trees["ddc"] / "lib" / "libextra.rlib").write_bytes(b"extra")
        changed = root / "changed.json"
        support.write_json_exclusive(changed, support.stage2_manifest(trees["ddc"]))
        evidence = root / "evidence"
        assert support.ddc_evidence(
            manifests["pinned"], changed, trees["pinned"], trees["ddc"], evidence
        ) == 2
        assert stat.S_IMODE(evidence.stat().st_mode) == 0o700
        assert (evidence / "pinned" / "bin" / "trustc").read_bytes() == b"compiler"
        assert (evidence / "ddc" / "bin" / "trustc").read_bytes() == b"other compiler"
        assert (evidence / "ddc" / "lib" / "libextra.rlib").read_bytes() == b"extra"
        assert not (evidence / "pinned" / "lib" / "libextra.rlib").exists()
        assert not (evidence / "pinned" / "lib" / "libsame.rlib").exists()
        assert not (evidence / "ddc" / "lib" / "libsame.rlib").exists()
        assert "differs: bin/trustc" in (evidence / "differences.txt").read_text()
        assert json.loads((evidence / "stage2-ddc-seed.json").read_text()) == json.loads(changed.read_text())
        expect_error(
            "already exists",
            support.ddc_evidence,
            manifests["pinned"],
            changed,
            trees["pinned"],
            trees["ddc"],
            evidence,
        )

    # The evidence is taken while the DDC build still exists, into the pinned
    # build that ddc-restore puts back, and named before the comparison fails.
    lines = (Path(__file__).resolve().parents[1] / "mint_and_prove_seed.sh").read_text().splitlines()

    def index(fragment: str) -> int:
        hits = [number for number, line in enumerate(lines) if fragment in line]
        assert len(hits) == 1, (fragment, hits)
        return hits[0]

    def exact(text: str) -> int:
        hits = [number for number, line in enumerate(lines) if line.strip() == text]
        assert len(hits) == 1, (text, hits)
        return hits[0]

    evidence_line = index('"$HELPER" ddc-evidence')
    restore = exact('"$PYTHON_BIN" -I -S "$HELPER" ddc-restore --root "$ROOT" --build "$MINT_BUILD"')
    compare = index('"$HELPER" ddc-compare')
    assert exact('"$WORK/stage2-ddc-seed.json"') < evidence_line < restore < compare
    assert index('--output "$MINT_BUILD.pinned/ddc-evidence"') > evidence_line
    assert restore < index('"$MINT_BUILD/ddc-evidence"') < compare



# Trust: DDC can disagree only in aliases or empty directories, with no file bytes to copy.
def test_failed_ddc_preserves_evidence_for_nonregular_only_differences() -> None:
    for kind in ("symlink", "directory"):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            trees = {}
            for name in ("pinned", "ddc"):
                stage2 = root / name / "stage2"
                (stage2 / "bin").mkdir(parents=True)
                (stage2 / "bin" / "trustc").write_bytes(b"compiler")
                (stage2 / "bin" / "other").write_bytes(b"other compiler")
                (stage2 / "bin" / "compiler").symlink_to("trustc")
                trees[name] = stage2
            if kind == "symlink":
                (trees["ddc"] / "bin" / "compiler").unlink()
                (trees["ddc"] / "bin" / "compiler").symlink_to("other")
                expected = "differs: bin/compiler\n"
            else:
                (trees["ddc"] / "only-on-ddc").mkdir()
                expected = "only from the DDC seed: only-on-ddc\n"
            manifests = {}
            for name, stage2 in trees.items():
                manifests[name] = root / f"{name}.json"
                support.write_json_exclusive(manifests[name], support.stage2_manifest(stage2))
            evidence = root / "new parent" / "evidence"
            assert support.ddc_evidence(
                manifests["pinned"], manifests["ddc"], trees["pinned"], trees["ddc"], evidence
            ) == 1, kind
            assert stat.S_IMODE(evidence.stat().st_mode) == 0o700
            assert {p.name for p in evidence.iterdir()} == {
                "stage2-pinned-seed.json", "stage2-ddc-seed.json", "differences.txt"
            }, kind
            for name, recorded in (("pinned", "stage2-pinned-seed.json"), ("ddc", "stage2-ddc-seed.json")):
                assert (evidence / recorded).read_bytes() == manifests[name].read_bytes(), kind
            assert (evidence / "differences.txt").read_text() == expected, kind
            expect_error("DDC FAILED", support.ddc_compare, manifests["pinned"], manifests["ddc"])
            expect_error(
                "already exists", support.ddc_evidence,
                manifests["pinned"], manifests["ddc"], trees["pinned"], trees["ddc"], evidence,
            )


def test_full_build_follows_dist_so_stage2_keeps_rustc_dev() -> None:
    # `x.py dist` re-assembles stage2 as Kind::Dist, which prunes the
    # rustc_private crates; only a later Kind::Build Assemble restores them.
    # The DDC compared, and promotion seals, the Kind::Build shape.
    script = Path(__file__).resolve().parents[1] / "mint_and_prove_seed.sh"
    lines = script.read_text().splitlines()

    def index(fragment: str) -> int:
        hits = [number for number, line in enumerate(lines) if fragment in line]
        assert len(hits) == 1, (fragment, hits)
        return hits[0]

    dist = index('"$MINT_BUILD" dist "${DIST_COMPONENTS[@]}"')
    full_line = 'xpy "$SAFE_BIN" mint "$CONFIG_SOURCE" "$MINT_BUILD" build'
    fulls = [number for number, line in enumerate(lines) if line.strip() == full_line]
    assert len(fulls) == 1, fulls
    full = fulls[0]
    manifest_tool = index('"$MINT_BUILD" build src/tools/build-manifest')
    verify = index("verify-stage2-unchanged \\")
    assert dist < full < manifest_tool < verify, (dist, full, manifest_tool, verify)


def test_stage_evidence_brackets_the_actual_mint_build() -> None:
    # A receipt obtained after the build cannot establish its native inputs or
    # that LLVM started empty. The owner must observe before the FIRST build,
    # audit the restored pinned build after DDC/dist, and verify before re-pin.
    text = (REPO_ROOT / "scripts/mint_and_prove_seed.sh").read_text()
    before = text.index('"$HELPER" stage-evidence-before')
    first_build = text.index('xpy "$SAFE_BIN" mint "$CONFIG_SOURCE" "$MINT_BUILD" build compiler/rustc')
    unchanged = text.index('"$HELPER" verify-stage2-unchanged')
    after = text.index('"$HELPER" stage-evidence-after')
    repin = text.index('"$HELPER" repin \\')
    assert before < first_build < unchanged < after < repin


def test_mint_configuration_context_binds_the_actual_xpy_overrides() -> None:
    text = (REPO_ROOT / "scripts/mint_and_prove_seed.sh").read_text()
    xpy = text.split("xpy() {", 1)[1].split("\n}", 1)[0]
    for key, value in support.MINT_XPY_CONFIG_OVERRIDES.items():
        spelling = str(value).lower() if isinstance(value, bool) else value
        assert f"--set {key}={spelling} \\\n" in xpy, (key, xpy)


def test_mint_jobs_retain_admission_and_refuse_invalid_counts() -> None:
    empty = subprocess.run(
        ["/bin/bash", str(REPO_ROOT / "scripts/mint_and_prove_seed.sh"), "--jobs", "", "--check-only"],
        capture_output=True, text=True,
    )
    assert empty.returncode == 2 and "nonempty positive count" in empty.stderr
    assert support.mint_build_jobs(None, {}) is None
    assert support.mint_build_jobs(4, {}) == 4
    admitted = {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "6"}
    assert support.mint_build_jobs(None, admitted) == 6
    assert support.mint_build_jobs(16, admitted) == 6
    assert support.mint_build_jobs(2, admitted) == 2
    for jobs in (0, -1, True, "6", 2**32):
        expect_error("positive", support.mint_build_jobs, jobs, {})
    for share in ("", "0", "-1", "six", "1.5", str(2**32)):
        expect_error("positive", support.mint_build_jobs, None,
                     {"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": share})
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        config = root / "bootstrap.toml"
        config.write_text('[build]\njobs = 64\n')
        first = support.mint_configuration_context(root, config, HOST, jobs=6)
        second = support.mint_configuration_context(root, config, HOST, jobs=4)
        assert first["xpy_config_overrides"]["build.jobs"] == 6
        assert first["fingerprint"] != second["fingerprint"]


def test_actual_mint_xpy_command_carries_jobs_after_environment_scrubbing() -> None:
    text = (REPO_ROOT / "scripts/mint_and_prove_seed.sh").read_text()
    setup = text.split("BUILD_JOB_ARGS=()", 1)[1].split("ENV_BIN=", 1)[0]
    setup = "BUILD_JOB_ARGS=()" + setup
    xpy = "xpy() {" + text.split("xpy() {", 1)[1].split("\n}", 1)[0] + "\n}"
    temporary = tempfile.TemporaryDirectory()
    with contextlib.ExitStack() as stack:
        stack.callback(temporary.cleanup)
        fixture_root = Path(temporary.name).resolve()
        library = clean_lean_fixture(fixture_root)
        lean_manifest = fixture_root / "lean-inputs.json"
        support.write_json_exclusive(lean_manifest, support.clean_lean_inputs(fixture_root, library))
        _check_xpy_jobs(setup, xpy, fixture_root, lean_manifest, library)


def _check_xpy_jobs(setup, xpy, fixture_root, lean_manifest, library):
    for explicit, held, share, expected in (("16", "1", "6", "6"), ("", "", "", None)):
        harness = (
            f"PYTHON_BIN={shlex.quote(sys.executable)}\n"
            f"HELPER={shlex.quote(str(REPO_ROOT / 'scripts/mint_seed_support.py'))}\n"
            f"BUILD_JOBS={shlex.quote(explicit)}\n" + setup +
            f"\nROOT={shlex.quote(str(fixture_root))}\nHOST=test-host\n"
            f"CLEAN_LEAN_MANIFEST={shlex.quote(str(lean_manifest))}\n"
            f"CLEAN_LEAN_LIB={shlex.quote(str(library))}\n"
            f"CLEAN_LEAN_MANIFEST_SHA256={support.sha256_file(lean_manifest)}\n"
            "run_clean() { shift 2; env -i \"$PYTHON_BIN\" -I -S -c "
            "'import json,sys; print(json.dumps(sys.argv[1:]))' \"$@\"; }\n" + xpy +
            "\nxpy /safe-bin mint '/fixture config' /fixture-build build compiler/rustc library/std\n"
        )
        result = subprocess.run(
            ["/bin/bash", "-eu", "-c", harness], capture_output=True, text=True, check=True,
            env={**os.environ, "BUILD_SLOT_HELD": held, "CARGO_BUILD_JOBS": share},
        )
        argv = json.loads(result.stdout)
        if expected is None:
            assert "--jobs" not in argv
        else:
            assert argv.count("--jobs") == 1
            assert argv[argv.index("--jobs") + 1] == expected
        assert argv[-2:] == ["compiler/rustc", "library/std"]


def test_mint_exit_handlers_preserve_failed_evidence() -> None:
    import unittest
    from scripts.tests.mint_failure_evidence_test import FailedMintEvidenceTests

    stream = io.StringIO()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(FailedMintEvidenceTests)
    result = unittest.TextTestRunner(stream=stream).run(suite)
    assert result.wasSuccessful(), stream.getvalue()


def test_retained_audit_shell_reuses_original_manifests_without_copying_inputs() -> None:
    """Execute the production setup block; a writer is a real negative control."""
    text = (REPO_ROOT / "scripts/mint_and_prove_seed.sh").read_text()
    setup = text[text.index('CONFIG_MANIFEST="$WORK/bootstrap-config-closure.json"'):text.index("\nrun_clean() {")]
    with tempfile.TemporaryDirectory(prefix="retained-audit-setup-") as tmp:
        root = Path(tmp)
        work = root / "work"; work.mkdir()
        names = ["bootstrap-config-closure.json", "clean-lean-inputs.json", "native-library-inputs.json",
                 "mint-toolchain-inputs.json", "seed-dylib-inputs.json", "cargo-home-inputs.json", "safe-path.json"]
        for name in names:
            (work / name).write_bytes(b"genuine original " + name.encode())
        original = {name: (work / name).read_bytes() for name in names}
        log = root / "calls"
        helper = root / "helper.py"
        helper.write_text("import hashlib,json,pathlib,sys\n"
                          f"with pathlib.Path({str(log)!r}).open('a') as f: f.write(json.dumps(sys.argv[1:])+'\\n')\n"
                          "if sys.argv[1]=='file-sha256': print(hashlib.sha256(pathlib.Path(sys.argv[2]).read_bytes()).hexdigest())\n"
                          "elif sys.argv[1]!='revalidate-path': raise SystemExit('unexpected original-input writer')\n")
        bindings = {"WORK": work, "ROOT": root, "CONFIG_SOURCE": root / "bootstrap.toml",
                    "CLEAN_LEAN_LIB": root / "lean", "HELPER": helper, "PYTHON_BIN": sys.executable,
                    "CONTINUATION_RECORD": root / "prepared.json"}
        prefix = "\n".join(f"{key}={shlex.quote(str(value))}" for key, value in bindings.items())
        arrays = "\nCANONICAL_LIBRARY_PATHS=(); CANONICAL_SEED_DYLIB_PATHS=(); CARGO_HOME_ARGS=()\n"
        for mode, expected in [(1, 0), (0, 1)]:
            completed = subprocess.run(["/bin/bash", "-eu", "-c", prefix + arrays +
                                       f"RESUME_AT_PROVENANCE={mode}\n" + setup], capture_output=True, text=True)
            assert completed.returncode == expected, completed.stderr
            if mode == 0:
                assert "unexpected original-input writer" in completed.stderr
            assert original == {name: (work / name).read_bytes() for name in names}


def test_external_mint_audit_delegates_both_actual_owner_and_strict_verifier() -> None:
    from types import SimpleNamespace
    with tempfile.TemporaryDirectory(prefix="external-mint-audit-") as tmp:
        root = Path(tmp); build = root / "build/pack-mint-fixture"; config = root / "config.toml"
        environment = {"CARGO_HOME": str(root / "cargo")}
        lean = {"library_path": str(root / "lean"), "environment": {"CLEAN_OLEAN_REQUIRE_PINNED_LEAN": "1"}}
        configuration = {"host": HOST, "xpy_config_overrides": {"build.jobs": 12}}
        before = {"schema": support.MINT_OBSERVATION_SCHEMA, "host": HOST,
                  "build_root": "build/pack-mint-fixture", "config_path": "config.toml",
                  "config_closure_sha256": "f" * 64, "mint_configuration": configuration,
                  "declared_environment": environment, "source_lineage": {"original": "source"},
                  "bootstrap_lineage": {"original": "seed"}, "build_authority": {"original": "native"},
                  "llvm_before": {"original": "LLVM"}}
        observation = root / "before.json"; observation.write_text(json.dumps(before))
        output = root / "evidence/mint-continuation-fixture-stage-provenance.json"
        owner = SimpleNamespace(_repository_relative_path=lambda base, path: path.relative_to(base).as_posix(),
                                audit_stage_tool_provenance=mock.Mock(return_value=True),
                                verify_stage_tool_provenance=mock.Mock(return_value=True))
        with mock.patch.object(support, "mint_evidence_context", return_value=(root, build, config, environment, root / "cargo")), \
                mock.patch.object(support, "mint_clean_lean_environment", return_value=lean), \
                mock.patch.object(support, "mint_configuration_context", return_value=configuration), \
                mock.patch.object(support, "configuration_closure", return_value={"fingerprint": "f" * 64}), \
                mock.patch.object(support, "stage_evidence_owner", return_value=owner):
            support.finish_mint_stage_evidence(root, build, config, HOST, observation, jobs=12, receipt_path=output)
            audit = owner.audit_stage_tool_provenance.call_args
            assert audit.args[3:6] == (before["source_lineage"], before["bootstrap_lineage"], before["build_authority"])
            assert audit.kwargs["receipt_path"] == output and audit.kwargs["mint_configuration"] == configuration
            verify = owner.verify_stage_tool_provenance.call_args
            assert verify.kwargs["receipt_path"] == output
            assert verify.kwargs["require_immutable_lineage"] and verify.kwargs["require_llvm_identity"]
            owner.verify_stage_tool_provenance.return_value = False
            expect_error("immutable-lineage/LLVM re-verification", support.finish_mint_stage_evidence,
                         root, build, config, HOST, observation, jobs=12, receipt_path=output)


def test_preparation_extraction_shares_canonical_bytes_modes_and_links_without_spawning() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "trustc-fixture.tar.xz"
        top = archive.name.removesuffix(".tar.xz")
        link = tarfile.TarInfo(top + "/installer-link"); link.type = tarfile.SYMTYPE; link.linkname = "install.sh"
        hard = tarfile.TarInfo(top + "/installer-copy"); hard.type = tarfile.LNKTYPE; hard.linkname = top + "/install.sh"; hard.mode = 0o755
        write_archive(archive, "trustc", extra=[link, hard])
        before = archive.read_bytes()
        ordinary, retained = root / "ordinary", root / "retained"
        with mock.patch.object(support.subprocess, "Popen", side_effect=AssertionError("no native child")), \
                mock.patch.object(support.subprocess, "run", side_effect=AssertionError("no native child")):
            actual = support.extract_authenticated(archive, ordinary, top, COMMIT)
            other = support.extract_for_preparation(archive, retained, top, COMMIT,
                                                    deadline=support.time.monotonic() + 30)
        assert actual == other
        assert support.tree_records(ordinary, "ordinary fixture") == support.tree_records(retained, "retained fixture")
        assert archive.read_bytes() == before


def test_preparation_extraction_requires_the_existing_finite_unexpired_endpoint() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        for index, end in enumerate((None, True, float("nan"), float("inf"), -float("inf"), 0.0, 10**1000)):
            destination = root / str(index)
            expect_error("extraction", support.extract_for_preparation, archive, destination,
                         "fixture", COMMIT, deadline=end)
            assert not destination.exists()


def test_preparation_extraction_keeps_partial_bytes_at_the_original_deadline() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        destination = root / "retained"; clock = [1.0]; original_write = os.write
        def write_then_expire(fd, value):
            wrote = original_write(fd, value)
            clock[0] = 11.0
            return wrote
        with mock.patch.object(support.time, "monotonic", side_effect=lambda: clock[0]), \
                mock.patch.object(support.os, "write", side_effect=write_then_expire):
            expect_error("original deadline exhausted", support.extract_for_preparation,
                         archive, destination, "fixture", COMMIT, deadline=10.0)
        assert (destination / "fixture/install.sh").read_bytes() == b"#!/bin/sh\nexit 0\n"
        assert not (destination / "fixture/version").exists()


def test_failed_preparation_extraction_retains_custody_while_ordinary_mint_still_cleans() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        before = archive.read_bytes()
        for retaining in (False, True):
            destination = root / str(retaining)
            with mock.patch.object(support.os, "write", side_effect=OSError("original write failure")):
                try:
                    if retaining:
                        support.extract_for_preparation(archive, destination, "fixture", COMMIT,
                                                        deadline=support.time.monotonic() + 30)
                    else:
                        support.extract_authenticated(archive, destination, "fixture", COMMIT)
                except OSError as error:
                    assert str(error) == "original write failure"
                else:
                    raise AssertionError("actual write failure must propagate")
            assert destination.exists() == retaining
            assert archive.read_bytes() == before


def test_preparation_extraction_still_refuses_wrong_commit_and_preexisting_destination() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        destination = root / "retained"
        expect_error("not minted from current HEAD", support.extract_for_preparation, archive,
                     destination, "fixture", "b" * 40, deadline=support.time.monotonic() + 30)
        assert destination.is_dir() and not list(destination.iterdir())
        marker = destination / "original"; marker.write_bytes(b"same original partial data")
        try:
            support.extract_for_preparation(archive, destination, "fixture", COMMIT,
                                            deadline=support.time.monotonic() + 30)
        except FileExistsError:
            pass
        else:
            raise AssertionError("existing output must never become a new attempt")
        assert marker.read_bytes() == b"same original partial data"


def test_preparation_extraction_zero_progress_write_refuses_and_retains_partial_output() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        destination = root / "retained"
        with mock.patch.object(support.os, "write", return_value=0):
            expect_error("short write", support.extract_for_preparation, archive, destination,
                         "fixture", COMMIT, deadline=support.time.monotonic() + 30)
        assert (destination / "fixture/install.sh").is_file()


def test_preparation_descriptor_uses_canonical_extraction_without_changing_or_closing_original() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        ordinary, retained = root / "ordinary", root / "retained"
        total = support.extract_authenticated(archive, ordinary, "fixture", COMMIT)
        fd = os.open(archive, os.O_RDONLY)
        try:
            os.lseek(fd, 17, os.SEEK_SET)
            before, flags = os.fstat(fd), os.get_inheritable(fd)
            with mock.patch.object(support.subprocess, "Popen", side_effect=AssertionError("no child")), \
                    mock.patch.object(support.subprocess, "run", side_effect=AssertionError("no child")):
                assert support.extract_for_preparation_fd(fd, retained, "fixture", COMMIT,
                    deadline=support.time.monotonic() + 30) == total
            assert support.tree_records(ordinary, "ordinary") == support.tree_records(retained, "retained")
            assert os.lseek(fd, 0, os.SEEK_CUR) == 17
            assert os.fstat(fd) == before and os.get_inheritable(fd) == flags
            assert os.pread(fd, 6, 0) == archive.read_bytes()[:6]
        finally:
            os.close(fd)


def test_preparation_descriptor_never_reopens_a_replaced_archive_name() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        fd = os.open(archive, os.O_RDONLY)
        try:
            archive.rename(root / "same-held-archive")
            write_archive(archive, "trustc", commit="b" * 40)
            # The original remains held under another name. Path/source guards
            # belong to the issuer; this only establishes actual input bytes.
            with mock.patch.object(support.os, "open", wraps=os.open) as opened:
                support.extract_for_preparation_fd(fd, root / "retained", "fixture", COMMIT,
                                                   deadline=support.time.monotonic() + 30)
            assert all(Path(call.args[0]) != archive for call in opened.call_args_list)
            assert (root / "retained/fixture/git-commit-hash").read_text().strip() == COMMIT
        finally:
            os.close(fd)


def test_preparation_descriptor_refuses_wrong_access_and_nonregular_inputs_before_output() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        pipe, writer = os.pipe()
        directory = os.open(root, os.O_RDONLY)
        writable = os.open(archive, os.O_RDWR)
        try:
            for index, fd in enumerate((pipe, directory, writable)):
                destination = root / str(index)
                expect_error("archive description", support.extract_for_preparation_fd,
                             fd, destination, "fixture", COMMIT,
                             deadline=support.time.monotonic() + 30)
                assert not destination.exists()
                os.fstat(fd)
        finally:
            for fd in (pipe, writer, directory, writable):
                os.close(fd)


def test_preparation_descriptor_rejects_invalid_original_ends_and_descriptors_before_output() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        fd = os.open(archive, os.O_RDONLY)
        try:
            for index, end in enumerate((None, True, float("nan"), float("inf"), 0.0)):
                destination = root / str(index)
                expect_error("extraction", support.extract_for_preparation_fd, fd, destination,
                             "fixture", COMMIT, deadline=end)
                assert not destination.exists()
            for index, invalid in enumerate((True, -1, 0, "3")):
                destination = root / ("fd" + str(index))
                expect_error("original archive description", support.extract_for_preparation_fd,
                             invalid, destination, "fixture", COMMIT,
                             deadline=support.time.monotonic() + 30)
                assert not destination.exists()
            os.fstat(fd)
        finally:
            os.close(fd)


def test_preparation_descriptor_drift_retains_partial_output_and_original_descriptor() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        fd = os.open(archive, os.O_RDONLY); destination = root / "retained"
        original_write = os.write
        def write_then_change(fd, value):
            count = original_write(fd, value)
            archive.chmod(0o600)
            return count
        try:
            archive.chmod(0o644)
            with mock.patch.object(support.os, "write", side_effect=write_then_change):
                expect_error("original preparation archive description changed", support.extract_for_preparation_fd,
                             fd, destination, "fixture", COMMIT,
                             deadline=support.time.monotonic() + 30)
            assert (destination / "fixture/install.sh").read_bytes() == b"#!/bin/sh\nexit 0\n"
            os.fstat(fd)
        finally:
            os.close(fd)


def test_preparation_descriptor_actual_read_failure_is_not_normalized_or_retried() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp); archive = root / "fixture.tar.xz"; write_archive(archive, "trustc")
        fd = os.open(archive, os.O_RDONLY); destination = root / "retained"
        failure = OSError("actual positional input failure")
        try:
            with mock.patch.object(support.os, "pread", side_effect=failure) as read:
                try:
                    support.extract_for_preparation_fd(fd, destination, "fixture", COMMIT,
                                                       deadline=support.time.monotonic() + 30)
                except OSError as error:
                    assert error is failure
                else:
                    raise AssertionError("actual original read failure must propagate")
                assert read.call_count == 1
            assert destination.is_dir()
            os.fstat(fd)
        finally:
            os.close(fd)


def load_tests(loader, tests, pattern):
    """`land_gate.py validation-tests` loads this module with unittest (the
    landing gate's selector names it, LAND-SELECT-VALIDATION-REACH-1): each
    module-level test_* function is one case, as a direct run runs them."""
    tests.addTests(unittest.FunctionTestCase(value) for name, value in sorted(globals().items())
                   if name.startswith("test_") and callable(value))
    return tests


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
