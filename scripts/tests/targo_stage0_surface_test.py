#!/usr/bin/env python3
"""Focused regressions for the canonical targo/tippy stage0 surface."""

from __future__ import annotations

import ast
import contextlib
import importlib.util
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from pathlib import PurePosixPath


REPO_ROOT = Path(__file__).resolve().parents[2]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


genesis = load_module(
    "trust_create_local_genesis_stage0",
    REPO_ROOT / "scripts" / "create_local_genesis_stage0.py",
)
discover = load_module(
    "trust_discover_stage0_seed",
    REPO_ROOT / "scripts" / "discover_trust_stage0_seed.py",
)
stage0_prepare = load_module(
    "trust_stage0_dist_prepare",
    REPO_ROOT / "src" / "tools" / "trust-stage0-dist" / "prepare.py",
)


def extract_test_archive(archive: tarfile.TarFile, destination: Path) -> None:
    """Safely extract a test-owned archive on Python versions before 3.12."""

    members = archive.getmembers()
    for member in members:
        path = PurePosixPath(member.name)
        assert not path.is_absolute() and ".." not in path.parts
        assert member.isfile() or member.isdir()
    archive.extractall(destination)


def _fake_genesis_rustc(path: Path, *, commit: str, date: str, host: str) -> None:
    genesis.write_executable(
        path,
        "#!/bin/sh\n"
        "cat <<'EOF'\n"
        f"rustc 1.99.0-nightly ({commit[:10]} {date})\n"
        "binary: rustc\n"
        f"commit-hash: {commit}\n"
        f"commit-date: {date}\n"
        f"host: {host}\n"
        "release: 1.99.0-nightly\n"
        "LLVM version: 22.1.8\n"
        "EOF\n",
    )


def _write_genesis_roots(root: Path, host_id: str, **overrides: str) -> None:
    expected = {
        "commit_date": "2026-07-08",
        "commit_hash": "14cae681329a63c622a6e1fbe1d30f9374bc51d8",
        "host": host_id,
        "release": "1.99.0-nightly",
        "rustc_archive_sha256": "a" * 64,
        "rustup_toolchain": "nightly-2026-07-09",
    }
    expected.update(overrides)
    manifest = root / genesis.GENESIS_ROOTS_RELATIVE
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(
        json.dumps(
            {
                "schema": genesis.GENESIS_ROOT_SCHEMA,
                "admission": "external-bootstrap-root-only",
                "counts_as_trust_stage0_evidence": False,
                "channel_manifest": {
                    "date": "2026-07-09",
                    "sha256": "b" * 64,
                    "url": "https://static.rust-lang.org/dist/2026-07-09/channel-rust-nightly.toml",
                },
                "roots": {host_id: expected},
            }
        ),
        encoding="utf-8",
    )


def test_checked_in_genesis_roots_meet_the_current_stage0_floor() -> None:
    """The explicit developer adapter must not select a compiler x.py refuses."""
    pins = genesis.stage0_values(REPO_ROOT / "src" / "stage0")
    floor = tuple(int(part) for part in pins["min_stage0_rustc_version"].split("."))
    document = json.loads((REPO_ROOT / genesis.GENESIS_ROOTS_RELATIVE).read_text())
    assert document["admission"] == "external-bootstrap-root-only"
    assert document["counts_as_trust_stage0_evidence"] is False
    assert document["roots"], "genesis host admission must not pass vacuously"
    for host, entry in document["roots"].items():
        version = tuple(int(part) for part in entry["release"].split("-", 1)[0].split("."))
        assert version >= floor, f"{host}: genesis {version} is below stage0 floor {floor}"
        assert entry["host"] == host
        assert entry["rustup_toolchain"] == "nightly-" + document["channel_manifest"]["date"]


def test_genesis_root_accepts_only_the_full_pinned_rustc_tuple() -> None:
    host = "aarch64-unknown-linux-gnu"
    commit = "14cae681329a63c622a6e1fbe1d30f9374bc51d8"
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        rustc = root / "rustc"
        _fake_genesis_rustc(rustc, commit=commit, date="2026-07-08", host=host)
        _write_genesis_roots(root, host)
        identity = genesis.validate_pinned_genesis_toolchain(root, str(rustc), host)
        assert identity["pin"]["rustup_toolchain"] == "nightly-2026-07-09"
        assert identity["observed"]["commit-hash"] == commit
        assert len(identity["rustc_sha256"]) == 64

        for field, wrong in (
            ("release", "1.98.0-nightly"),
            ("commit_hash", "f10db292a3733b5c67c8da8c7661195ff4b05774"),
            ("commit_date", "2026-07-07"),
            ("host", "x86_64-unknown-linux-gnu"),
        ):
            _write_genesis_roots(root, host, **{field: wrong})
            try:
                genesis.validate_pinned_genesis_toolchain(root, str(rustc), host)
            except SystemExit as error:
                assert "refusing unpinned genesis rustc" in str(error)
            else:
                raise AssertionError(f"genesis gate accepted mismatched {field}")


def test_documented_july_8_channel_mismatch_is_rejected() -> None:
    """nightly-2026-07-08 is f10db292/July 7, not the recorded 14cae root."""
    host = "aarch64-unknown-linux-gnu"
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        rustc = root / "rustc"
        _fake_genesis_rustc(
            rustc,
            commit="f10db292a3733b5c67c8da8c7661195ff4b05774",
            date="2026-07-07",
            host=host,
        )
        _write_genesis_roots(root, host)
        try:
            genesis.validate_pinned_genesis_toolchain(root, str(rustc), host)
        except SystemExit as error:
            message = str(error)
            assert "commit-hash" in message
            assert "commit-date" in message
        else:
            raise AssertionError("July 8 channel mismatch passed the genesis gate")


def test_genesis_linter_versions_use_canonical_identity() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        real = root / "clippy-backend"
        genesis.write_executable(
            real,
            "#!/bin/sh\n"
            'if [ "${1-}" = "clippy" ]; then shift; fi\n'
            '[ "$#" -eq 1 ] || exit 42\n'
            'case "$1" in\n'
            "  --version) printf '%s\\n' 'clippy 0.1-test' 'binary: clippy' ;;\n"
            "  -vV|-Vv) printf '%s\\n' 'rustc 1.96.0' 'binary: rustc' 'host: test-host' ;;\n"
            "  *) exit 42 ;;\n"
            "esac\n",
        )
        for public_name, version_prefix in (
            ("tippy", "clippy"),
            ("targo-tippy", "clippy"),
            ("tippy-driver", None),
        ):
            wrapper = root / public_name
            genesis.write_executable(
                wrapper,
                genesis.wrapper_script(
                    real=str(real),
                    source_name="clippy",
                    trust_name=public_name,
                    version_name="tippy",
                    version_argument_prefix=version_prefix,
                ),
            )
            probes = (
                ("--version",),
                ("-V",),
                ("-vV",),
                ("-Vv",),
                ("--version", "--verbose"),
                ("--verbose", "--version"),
            )
            if public_name == "tippy-driver":
                probes = tuple(probe for probe in probes if probe not in (("-vV",), ("-Vv",)))
            for probe in probes:
                output = subprocess.run(
                    [str(wrapper), *probe],
                    check=True,
                    text=True,
                    stdout=subprocess.PIPE,
                ).stdout
                assert output == f"tippy 0.1-test\nbinary: {public_name}\n"

        for probe in (("-vV",), ("-Vv",)):
            output = subprocess.run(
                [str(root / "tippy-driver"), *probe],
                check=True,
                text=True,
                stdout=subprocess.PIPE,
            ).stdout
            assert output.startswith("rustc 1.96.0\nbinary: rustc\n")

        genesis.write_executable(
            real,
            "#!/bin/sh\nprintf '%s\\n' 'clippy failed-version-probe'\nexit 19\n",
        )
        wrapper = root / "tippy"
        failed = subprocess.run(
            [str(wrapper), "--version"],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
        )
        assert failed.returncode == 19
        assert failed.stdout == "tippy failed-version-probe\n"


def fake_cargo_clippy(path: Path) -> None:
    genesis.write_executable(
        path,
        """#!/bin/sh
printf 'MARKER=%s\\n' "$1"
shift
for arg do
    printf 'ARG=%s\\n' "$arg"
done
""",
    )


def test_genesis_tippy_preserves_direct_options_and_exact_z_namespace() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        real = root / "cargo-clippy"
        fake_cargo_clippy(real)

        tippy = root / "tippy"
        genesis.write_executable(
            tippy,
            genesis.wrapper_script(
                real=str(real),
                source_name="clippy",
                trust_name="tippy",
                argument_prefix=genesis.WRAPPER_ARG_PREFIXES["tippy"],
            ),
        )
        output = subprocess.run(
            [
                str(tippy),
                "--workspace",
                "-Zcrate-attr=doc=trust",
                "-Z",
                "trust-verify-full",
                "input.rs",
            ],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == (
            "MARKER=clippy\n"
            "ARG=--workspace\n"
            "ARG=-Zcrate-attr=doc=trust\n"
            "ARG=input.rs\n"
        )

        targo_tippy = root / "targo-tippy"
        genesis.write_executable(
            targo_tippy,
            genesis.wrapper_script(
                real=str(real),
                source_name="clippy",
                trust_name="targo-tippy",
                argument_prefix=genesis.WRAPPER_ARG_PREFIXES["targo-tippy"],
                argument_marker=genesis.WRAPPER_ARG_MARKERS["targo-tippy"],
            ),
        )
        output = subprocess.run(
            [str(targo_tippy), "tippy", "--workspace"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == "MARKER=clippy\nARG=--workspace\n"

        output = subprocess.run(
            [str(targo_tippy), "--workspace"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == "MARKER=clippy\nARG=--workspace\n"

        tippy_driver = root / "tippy-driver"
        genesis.write_executable(
            tippy_driver,
            genesis.wrapper_script(
                real=str(real),
                source_name="clippy",
                trust_name="tippy-driver",
                argument_rename=genesis.WRAPPER_ARG_RENAMES["tippy-driver"],
            ),
        )
        output = subprocess.run(
            [str(tippy_driver), "--trustc", "--version", "--verbose"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == "MARKER=--rustc\nARG=--version\nARG=--verbose\n"


def test_genesis_wrapper_quotes_backend_paths_as_data() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        # A toolchain may be installed below a user-controlled directory. Its
        # path must remain data in the generated shell adapter: JSON quoting is
        # not shell quoting and would expand both `$HOME` and `$(...)` here.
        real = root / "backend-$(touch PWNED)-$HOME-'quote"
        genesis.write_executable(
            real,
            "#!/bin/sh\n"
            'if [ "${1-}" = "clippy" ]; then shift; fi\n'
            'if [ "${1-}" = "--version" ]; then\n'
            "  printf '%s\\n' 'clippy 0.1-test'\n"
            "else\n"
            "  printf 'ARG=%s\\n' \"$1\"\n"
            "fi\n",
        )
        wrapper = root / "tippy"
        genesis.write_executable(
            wrapper,
            genesis.wrapper_script(
                real=str(real),
                source_name="clippy",
                trust_name="tippy",
                argument_prefix="clippy",
                version_name="tippy",
                version_argument_prefix="clippy",
            ),
        )
        env = {**os.environ, "HOME": str(root / "attacker-home")}
        output = subprocess.run(
            [str(wrapper), "--workspace"],
            cwd=root,
            env=env,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == "ARG=--workspace\n"
        version = subprocess.run(
            [str(wrapper), "--version"],
            cwd=root,
            env=env,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert version == "tippy 0.1-test\n"
        assert not (root / "PWNED").exists()


def test_compiled_genesis_tippy_preserves_direct_options() -> None:
    # The Trust compiler by its own name: a bare `rustc` is the aterm reroute
    # stub (exit 127) or rustup's default. The wrapper is test scaffolding with
    # no proof claim, and strict trustc refuses it (16 errors, measured
    # 2026-09-28), so it is built with verification off.
    trustc = shutil.which("trustc")
    assert trustc is not None, "trustc is required to test the compiled genesis wrapper"
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        real = root / "cargo-clippy"
        fake_cargo_clippy(real)
        wrapper = root / "tippy"
        subprocess.run(
            [
                trustc,
                "-Ztrust-verify=off",
                "-O",
                str(REPO_ROOT / "scripts/win-genesis/genesis_wrapper.rs"),
                "-o",
                str(wrapper),
            ],
            check=True,
        )
        (root / "tippy.wrap").write_text(
            f"mode=wrap\nreal={real}\nprefix=clippy\n", encoding="utf-8"
        )
        output = subprocess.run(
            [
                str(wrapper),
                "--workspace",
                "-Zcrate-attr=doc=trust",
                "-Ztrust-verify=off",
                "input.rs",
            ],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == (
            "MARKER=clippy\n"
            "ARG=--workspace\n"
            "ARG=-Zcrate-attr=doc=trust\n"
            "ARG=input.rs\n"
        )

        targo_tippy = root / "targo-tippy"
        shutil.copy2(wrapper, targo_tippy)
        (root / "targo-tippy.wrap").write_text(
            f"mode=wrap\nreal={real}\nprefix=clippy\nmarker=tippy\n",
            encoding="utf-8",
        )
        output = subprocess.run(
            [str(targo_tippy), "tippy", "--workspace"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == "MARKER=clippy\nARG=--workspace\n"

        output = subprocess.run(
            [str(targo_tippy), "--workspace"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == "MARKER=clippy\nARG=--workspace\n"

        tippy_driver = root / "tippy-driver"
        shutil.copy2(wrapper, tippy_driver)
        (root / "tippy-driver.wrap").write_text(
            f"mode=wrap\nreal={real}\narg_from=--trustc\narg_to=--rustc\n",
            encoding="utf-8",
        )
        output = subprocess.run(
            [str(tippy_driver), "--trustc", "--version", "--verbose"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert output == "MARKER=--rustc\nARG=--version\nARG=--verbose\n"

        genesis.write_executable(
            real,
            "#!/bin/sh\n"
            'if [ "${1-}" = "clippy" ]; then shift; fi\n'
            '[ "$#" -eq 1 ] || exit 42\n'
            'case "$1" in\n'
            "  --version) printf '%s\\n' 'clippy 0.1-test' 'binary: clippy' ;;\n"
            "  -vV|-Vv) printf '%s\\n' 'rustc 1.96.0' 'binary: rustc' 'host: test-host' ;;\n"
            "  *) exit 42 ;;\n"
            "esac\n",
        )
        tippy_driver = root / "tippy-driver"
        shutil.copy2(wrapper, tippy_driver)
        for public_name, version_prefix in (
            ("tippy", "clippy"),
            ("targo-tippy", "clippy"),
            ("tippy-driver", None),
        ):
            sidecar = (
                f"mode=wrap\nreal={real}\nsource=clippy\n"
                f"trust={public_name}\nversion=tippy\n"
            )
            if version_prefix is not None:
                sidecar += f"version_prefix={version_prefix}\n"
            if public_name == "tippy-driver":
                sidecar += "compiler_info=1\n"
            if public_name == "targo-tippy":
                sidecar += "prefix=clippy\nmarker=tippy\n"
            (root / f"{public_name}.wrap").write_text(sidecar, encoding="utf-8")
            probes = (
                ("--version",),
                ("-V",),
                ("-vV",),
                ("-Vv",),
                ("--version", "--verbose"),
                ("--verbose", "--version"),
            )
            if public_name == "tippy-driver":
                probes = tuple(probe for probe in probes if probe not in (("-vV",), ("-Vv",)))
            for probe in probes:
                output = subprocess.run(
                    [str(root / public_name), *probe],
                    check=True,
                    text=True,
                    stdout=subprocess.PIPE,
                ).stdout
                assert output == f"tippy 0.1-test\nbinary: {public_name}\n"

        for probe in (("-vV",), ("-Vv",)):
            output = subprocess.run(
                [str(root / "tippy-driver"), *probe],
                check=True,
                text=True,
                stdout=subprocess.PIPE,
            ).stdout
            assert output.startswith("rustc 1.96.0\nbinary: rustc\n")


def test_stage0_contract_has_only_rustc_and_cargo_compatibility_aliases() -> None:
    assert discover.COMPAT_ALIAS_NAMES == ("rustc", "cargo")
    assert "rustdoc" in discover.FORBIDDEN_STAGE0_BIN_ENTRYPOINTS
    assert "rustfmt" in discover.FORBIDDEN_STAGE0_BIN_ENTRYPOINTS
    assert "rust-analyzer" in discover.FORBIDDEN_STAGE0_BIN_ENTRYPOINTS
    assert "tcargo" in discover.FORBIDDEN_STAGE0_BIN_ENTRYPOINTS
    assert "tcargo-trust" in discover.FORBIDDEN_STAGE0_BIN_ENTRYPOINTS
    assert "tcargo-fmt" in discover.FORBIDDEN_STAGE0_BIN_ENTRYPOINTS
    assert "rust-windbg.cmd" in discover.FORBIDDEN_STAGE0_BIN_ENTRYPOINTS
    assert (
        "rust-analyzer-proc-macro-srv"
        in discover.FORBIDDEN_STAGE0_LIBEXEC_ENTRYPOINTS
    )


def python_dict_keys(path: Path, variable: str) -> set[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        if not any(
            isinstance(target, ast.Name) and target.id == variable
            for target in node.targets
        ):
            continue
        assert isinstance(node.value, ast.Dict), f"{variable} must be a literal dict"
        keys: set[str] = set()
        for key in node.value.keys:
            assert isinstance(key, ast.Constant) and isinstance(key.value, str)
            keys.add(key.value)
        return keys
    raise AssertionError(f"{variable} not found in {path}")


def test_genesis_emitters_have_exact_canonical_public_bin_surface() -> None:
    expected = set(genesis.REQUIRED_BINS)
    retired = {"tcargo", "tcargo-trust", "tcargo-fmt", "cargo-trust"}

    posix_emitted = set(genesis.WRAPPER_SOURCES) | set(genesis.STUB_BINS)
    assert posix_emitted == expected
    assert posix_emitted.isdisjoint(genesis.FORBIDDEN_BINS)
    assert posix_emitted.isdisjoint(retired)

    windows = REPO_ROOT / "scripts" / "win-genesis" / "win_genesis.py"
    windows_emitted = python_dict_keys(windows, "WRAP") | python_dict_keys(
        windows, "STUB"
    )
    assert windows_emitted == expected
    assert windows_emitted.isdisjoint(retired)


def test_archive_contract_accepts_windows_suffixes_and_rejects_retired_aliases() -> None:
    names = [
        "tippy/tippy/bin/tippy.exe",
        "tippy/tippy/bin/targo-tippy.exe",
        "tippy/tippy/bin/tippy-driver.exe",
    ]
    good, bad = discover.inspect_archive_members(
        Path("tippy-1.99.0-x86_64-pc-windows-msvc.tar.xz"), names
    )
    assert set(good) == {"tippy", "targo-tippy", "tippy-driver"}
    assert bad == []

    _, bad = discover.inspect_archive_members(
        Path("tippy-1.99.0-x86_64-pc-windows-msvc.tar.xz"),
        [*names, "tippy/tippy/bin/cargo-clippy.exe"],
    )
    assert "forbidden stage0 archive member bin/cargo-clippy" in bad

    good, bad = discover.inspect_archive_members(
        Path("tcargo-1.96.0-trust-aarch64-apple-darwin.tar.xz"),
        ["tcargo/tcargo/bin/tcargo", "tcargo/tcargo/bin/cargo"],
    )
    assert set(good) == {"targo", "cargo"}
    assert bad == []

    good, bad = discover.inspect_archive_members(
        Path("tcargo-trust-1.96.0-trust-aarch64-apple-darwin.tar.xz"),
        [
            "tcargo-trust/tcargo-trust/bin/tcargo-trust",
            "tcargo-trust/tcargo-trust/bin/cargo-trust",
        ],
    )
    assert good == ["targo-trust"]
    assert bad == []

    good, bad = discover.inspect_archive_members(
        Path("trust-clippy-1.96.0-trust-aarch64-apple-darwin.tar.xz"),
        [
            "trust-clippy/trust-clippy-preview/bin/trust-clippy",
            "trust-clippy/trust-clippy-preview/bin/cargo-clippy",
            "trust-clippy/trust-clippy-preview/bin/trust-clippy-driver",
            "trust-clippy/trust-clippy-preview/bin/clippy-driver",
        ],
    )
    assert set(good) == {"tippy", "targo-tippy", "tippy-driver"}
    assert bad == []


def test_stage0_repack_rejects_conflicting_tippy_aliases() -> None:
    def write_input(path: Path, cargo_clippy: bytes) -> None:
        with tarfile.open(path, "w:xz") as archive:
            for name, data in (
                ("tippy-old/tippy-preview/bin/tippy", b"canonical"),
                ("tippy-old/tippy-preview/bin/cargo-clippy", cargo_clippy),
            ):
                member = tarfile.TarInfo(name)
                member.mode = 0o755
                member.size = len(data)
                archive.addfile(member, io.BytesIO(data))

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        source = root / "tippy-old.tar.xz"
        output = root / "tippy-new.tar.xz"
        write_input(source, b"different retired executable")
        try:
            stage0_prepare.repack_owned_tarball(
                source,
                output,
                old_filename=source.name,
                new_filename=output.name,
                source_channel="nightly",
                owned_channel="trust",
            )
        except ValueError as error:
            message = str(error)
            assert "conflicting archive members" in message
            assert "cargo-clippy" in message
            assert "tippy-new/tippy/bin/tippy" in message
        else:
            raise AssertionError("conflicting Tippy aliases were silently selected by archive order")

        # Historical archives commonly contain byte-identical compatibility
        # copies. Keep admitting those, but emit one canonical executable.
        write_input(source, b"canonical")
        stage0_prepare.repack_owned_tarball(
            source,
            output,
            old_filename=source.name,
            new_filename=output.name,
            source_channel="nightly",
            owned_channel="trust",
        )
        with tarfile.open(output, "r:xz") as archive:
            names = archive.getnames()
        assert names.count("tippy-new/tippy/bin/tippy") == 1
        assert all("cargo-clippy" not in name for name in names)

        # A legacy-only frontend cannot be made into direct `tippy` by changing
        # its tar member name: cargo-clippy drops argv[1] and discovers a legacy
        # driver sibling. That format belongs on bootstrap's semantic adapter
        # path, not the native dist-repack path.
        legacy_only = root / "legacy-only.tar.xz"
        with tarfile.open(legacy_only, "w:xz") as archive:
            data = b"legacy cargo-clippy executable"
            member = tarfile.TarInfo("legacy-only/tippy-preview/bin/cargo-clippy")
            member.mode = 0o755
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
        try:
            stage0_prepare.repack_owned_tarball(
                legacy_only,
                output,
                old_filename="legacy-only.tar.xz",
                new_filename="tippy-new.tar.xz",
                source_channel="nightly",
                owned_channel="trust",
            )
        except ValueError as error:
            message = str(error)
            assert "cannot byte-rename legacy-only Tippy" in message
            assert "legacy bootstrap adapter" in message
        else:
            raise AssertionError("legacy cargo-clippy was unsafely byte-renamed to tippy")


def test_stage0_repack_admits_dist_stock_names_and_refuses_link_entries() -> None:
    """T13c: dist lays `rustc`, `rustdoc` and `cargo` as hard links to the Trust
    tools, and rust-installer's tarballer writes each name as a regular member with
    the same bytes. The seed repack must keep admitting exactly that (one canonical
    member per name, the compatibility names it emits itself), must rewrite each
    component's `manifest.in` so `install.sh` finds every file it lists, and must
    refuse a tar hard-link entry, which is why the tarballer is not taught to write
    one."""

    def member(name: str, data: bytes, mode: int = 0o755) -> tuple[tarfile.TarInfo, bytes]:
        info = tarfile.TarInfo(name)
        info.mode = mode
        info.size = len(data)
        return info, data

    # install.sh's contract, reduced: every `file:` line of a component's manifest.in
    # is copied, and a missing one fails the install.
    installer = b"""#!/bin/sh
set -eu
src_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
dest="$1"
for component in $(cat "$src_dir/components"); do
    while read -r directive; do
        case "$directive" in
            file:*)
                file="${directive#file:}"
                test -f "$src_dir/$component/$file"
                mkdir -p "$dest/$(dirname "$file")"
                cp "$src_dir/$component/$file" "$dest/$file"
                ;;
        esac
    done < "$src_dir/$component/manifest.in"
done
"""

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for component, rows, expected in (
            (
                "trustc",
                (("trustc", b"compiler"), ("rustc", b"compiler"),
                 ("trustdoc", b"doc tool"), ("rustdoc", b"doc tool"),
                 # A retired alias the repack strips, listed by the dist's manifest.
                 ("rust-gdb", b"debugger wrapper")),
                {"trustc": b"compiler", "rustc": b"compiler", "trustdoc": b"doc tool"},
            ),
            (
                "targo",
                (("targo", b"frontend"), ("cargo", b"frontend")),
                {"targo": b"frontend", "cargo": b"frontend"},
            ),
        ):
            old = f"{component}-1.99.0-trust-aarch64-apple-darwin"
            new = f"{component}-1.99.0-owned-aarch64-apple-darwin"
            source = root / f"{old}.tar.xz"
            output = root / f"{new}.tar.xz"
            # rust-installer's manifest.in: one sorted `file:` line per file.
            manifest = "".join(sorted(f"file:bin/{name}\n" for name, _ in rows)).encode()
            with tarfile.open(source, "w:xz") as archive:
                for name, data, mode in (
                    (f"{old}/components", f"{component}\n".encode(), 0o644),
                    (f"{old}/install.sh", installer, 0o755),
                    (f"{old}/{component}/manifest.in", manifest, 0o644),
                ):
                    info, payload = member(name, data, mode)
                    archive.addfile(info, io.BytesIO(payload))
                # The tarballer's order: by reversed path bytes, so a stock name
                # can come before its Trust name.
                for name, data in sorted(rows, key=lambda row: row[0][::-1]):
                    info, payload = member(f"{old}/{component}/bin/{name}", data)
                    archive.addfile(info, io.BytesIO(payload))
            stage0_prepare.repack_owned_tarball(
                source, output, old_filename=source.name, new_filename=output.name,
                source_channel="trust", owned_channel="trust",
            )
            with tarfile.open(output, "r:xz") as archive:
                names = archive.getnames()
                bins = {
                    name.rsplit("/", 1)[1]: archive.extractfile(name).read()
                    for name in names
                    if name.rsplit("/", 2)[-2] == "bin"
                }
                listed = archive.extractfile(f"{new}/{component}/manifest.in").read().decode()
                extracted = root / f"extracted-{component}"
                extract_test_archive(archive, extracted)
            assert len(names) == len(set(names)), names
            assert bins == expected, bins
            # The manifest lists exactly the files the archive carries, once each.
            assert sorted(listed.splitlines()) == sorted(f"file:bin/{name}" for name in expected), listed
            installed = root / f"installed-{component}"
            subprocess.run([str(extracted / new / "install.sh"), str(installed)], check=True)
            assert {
                path.name: path.read_bytes() for path in (installed / "bin").iterdir()
            } == expected

        # A link entry for the stock name is renamed onto its Trust name and then
        # disagrees with the regular member there.
        old = "trustc-1.99.0-trust-aarch64-apple-darwin"
        source = root / f"{old}-linked.tar.xz"
        with tarfile.open(source, "w:xz") as archive:
            info, payload = member(f"{old}/trustc/bin/trustc", b"compiler")
            archive.addfile(info, io.BytesIO(payload))
            link = tarfile.TarInfo(f"{old}/trustc/bin/rustc")
            link.type = tarfile.LNKTYPE
            link.linkname = f"{old}/trustc/bin/trustc"
            link.mode = 0o755
            archive.addfile(link)
        try:
            stage0_prepare.repack_owned_tarball(
                source, root / "trustc-1.99.0-owned-aarch64-apple-darwin.tar.xz",
                old_filename=f"{old}.tar.xz",
                new_filename="trustc-1.99.0-owned-aarch64-apple-darwin.tar.xz",
                source_channel="trust", owned_channel="trust",
            )
        except ValueError as error:
            assert "conflicting archive members" in str(error), error
        else:
            raise AssertionError("a tar hard-link entry for a stock name was admitted")


def test_stage0_repack_keeps_installer_components_aligned() -> None:
    installer = b"""#!/bin/sh
set -eu
src_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
for component in $(cat "$src_dir/components"); do
    test -f "$src_dir/$component/manifest.in"
done
"""

    for preview, canonical in (
        ("tippy-preview", "tippy"),
        ("trustfmt-preview", "trustfmt"),
        ("trust-analyzer-preview", "trust-analyzer"),
    ):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / f"{canonical}-old.tar.xz"
            output = root / f"{canonical}-new.tar.xz"
            old_prefix = source.name.removesuffix(".tar.xz")
            new_prefix = output.name.removesuffix(".tar.xz")
            with tarfile.open(source, "w:xz") as archive:
                for name, data, mode in (
                    (f"{old_prefix}/components", f"{preview}\n".encode(), 0o644),
                    (f"{old_prefix}/install.sh", installer, 0o755),
                    (f"{old_prefix}/{preview}/manifest.in", b"file:bin/tool\n", 0o644),
                    (f"{old_prefix}/{preview}/bin/{canonical}", b"tool", 0o755),
                ):
                    member = tarfile.TarInfo(name)
                    member.mode = mode
                    member.size = len(data)
                    archive.addfile(member, io.BytesIO(data))

            stage0_prepare.repack_owned_tarball(
                source,
                output,
                old_filename=source.name,
                new_filename=output.name,
                source_channel="trust",
                owned_channel="trust",
            )

            extracted = root / "extracted"
            with tarfile.open(output, "r:xz") as archive:
                extract_test_archive(archive, extracted)
            package = extracted / new_prefix
            assert (package / "components").read_text(encoding="utf-8") == f"{canonical}\n"
            assert (package / canonical / "manifest.in").is_file()
            assert not (package / preview).exists()
            subprocess.run([str(package / "install.sh")], check=True)


def test_required_host_archives_prefer_canonical_then_pinned_legacy() -> None:
    date = "2026-06-23"
    version = "1.96.0-trust"
    host = "aarch64-apple-darwin"
    legacy_components = {
        "targo": "tcargo",
        "targo-trust": "tcargo-trust",
        "tippy": "trust-clippy",
    }
    values = {"compiler_date": date, "compiler_version": version}
    for component in discover.HOST_STAGE0_COMPONENTS:
        pinned = legacy_components.get(component, component)
        values[f"dist/{date}/{pinned}-{version}-{host}.tar.xz"] = "0" * 64
    stage0 = discover.Stage0Config("test", values, [], [], [])
    selected = discover.required_host_archive_keys(stage0, host)
    assert all(key in values for key in selected)
    assert any("/tcargo-" in key for key in selected)
    assert any("/tcargo-trust-" in key for key in selected)
    assert any("/trust-clippy-" in key for key in selected)

    canonical_targo = f"dist/{date}/targo-{version}-{host}.tar.xz"
    values[canonical_targo] = "1" * 64
    selected = discover.required_host_archive_keys(stage0, host)
    assert canonical_targo in selected
    assert not any("/tcargo-" in key and "/tcargo-trust-" not in key for key in selected)


def test_sysroot_contract_rejects_forbidden_superset() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        bin_dir = root / "bin"
        libexec_dir = root / "libexec"
        bin_dir.mkdir()
        libexec_dir.mkdir()
        for name in discover.REQUIRED_STAGE0_BIN_ENTRYPOINTS:
            genesis.write_executable(bin_dir / name, "#!/bin/sh\nexit 0\n")
        for name in discover.REQUIRED_STAGE0_LIBEXEC_ENTRYPOINTS:
            genesis.write_executable(libexec_dir / name, "#!/bin/sh\nexit 0\n")

        candidate = discover.CandidateRoot("test", "sysroot", root)
        assert discover.inspect_sysroot(candidate).status == "candidate"

        genesis.write_executable(bin_dir / "cargo-trust", "#!/bin/sh\nexit 0\n")
        result = discover.inspect_sysroot(candidate)
        assert result.status == "rejected"
        assert any("bin/cargo-trust" in finding for finding in result.findings)

        (bin_dir / "cargo-trust").unlink()
        if os.name != "nt":
            (bin_dir / "rust-lldb").symlink_to(root / "missing-rust-lldb")
            result = discover.inspect_sysroot(candidate)
            assert result.status == "rejected"
            assert any("bin/rust-lldb" in finding for finding in result.findings)


_MERGE_AARCH = "aarch64-apple-darwin"
_MERGE_LINUX = "x86_64-unknown-linux-gnu"


def _mk_channel_manifest(*, date: str, commit: str, targets_built: dict) -> dict:
    """A minimal channel manifest: pkg.<component>.target.<triple> is a built
    entry (available + xz_url + xz_hash) or an unbuilt {available = false}."""
    pkg: dict = {"trust": {"version": "1.99.0-trust", "git_commit_hash": commit}}
    for component, triples in targets_built.items():
        target_map: dict = {}
        for triple, built in triples.items():
            if built:
                target_map[triple] = {
                    "available": True,
                    "xz_url": (
                        f"file://{{trust-root}}/bootstrap/trust-stage0/dist/{date}/"
                        f"{component}-1.99.0-trust-{triple}.tar.xz"
                    ),
                    "xz_hash": "a" * 64,
                }
            else:
                target_map[triple] = {"available": False}
        pkg[component] = {"target": target_map}
    return {"date": date, "pkg": pkg}


def _write_manifest(tmp: str, manifest: dict) -> Path:
    path = Path(tmp) / "channel-rust-trust.toml"
    path.write_text(stage0_prepare.dump_toml(manifest), encoding="utf-8")
    return path


def test_stage0_merge_unions_dual_host_manifest_targets() -> None:
    date, commit = "2026-07-12", "f4" + "0" * 38
    comps = ("trustc", "trust-std")
    mac = _mk_channel_manifest(
        date=date, commit=commit,
        targets_built={c: {_MERGE_AARCH: True, _MERGE_LINUX: False} for c in comps},
    )
    linux = _mk_channel_manifest(
        date=date, commit=commit,
        targets_built={c: {_MERGE_AARCH: False, _MERGE_LINUX: True} for c in comps},
    )
    with tempfile.TemporaryDirectory() as tmp:
        adopted = stage0_prepare.merge_existing_manifest_targets(
            linux, _write_manifest(tmp, mac)
        )
    assert adopted == len(comps)  # one aarch64 target adopted per component
    for c in comps:
        targets = linux["pkg"][c]["target"]
        assert stage0_prepare.manifest_target_is_built(targets[_MERGE_AARCH])  # adopted from mac
        assert stage0_prepare.manifest_target_is_built(targets[_MERGE_LINUX])  # this run's own


def test_stage0_merge_keeps_fresh_target_on_shared_triple() -> None:
    date, commit = "2026-07-12", "f4" + "0" * 38
    mac = _mk_channel_manifest(date=date, commit=commit, targets_built={"trustc": {_MERGE_AARCH: True}})
    linux = _mk_channel_manifest(date=date, commit=commit, targets_built={"trustc": {_MERGE_AARCH: True}})
    linux["pkg"]["trustc"]["target"][_MERGE_AARCH]["xz_hash"] = "b" * 64  # this run rebuilt it
    with tempfile.TemporaryDirectory() as tmp:
        adopted = stage0_prepare.merge_existing_manifest_targets(
            linux, _write_manifest(tmp, mac)
        )
    assert adopted == 0  # same triple already built here -> nothing adopted
    assert linux["pkg"]["trustc"]["target"][_MERGE_AARCH]["xz_hash"] == "b" * 64  # fresh kept


def test_stage0_merge_refuses_mismatched_release() -> None:
    commit = "f4" + "0" * 38
    mac = _mk_channel_manifest(date="2026-07-12", commit=commit, targets_built={"trustc": {_MERGE_AARCH: True}})
    linux = _mk_channel_manifest(date="2026-08-01", commit=commit, targets_built={"trustc": {_MERGE_LINUX: True}})
    with tempfile.TemporaryDirectory() as tmp:
        mac_path = _write_manifest(tmp, mac)
        raised = False
        try:
            stage0_prepare.merge_existing_manifest_targets(linux, mac_path)
        except ValueError:
            raised = True
    assert raised, "merge must refuse a different-date (different release) manifest"


# --keep-existing-shared: a second host's prepare.py run over the first host's
# pinned output root. The fixture is the shape of the 82bb867edd pin, reduced:
# one host archive per host (trustc-dev) and the host-independent trust-src.
_KEEP_DATE = "2026-11-07"
_KEEP_COMMIT = "82bb867edd" + "0" * 30
_KEEP_VERSION = "0.13.0-trust"
_KEEP_MAC = "aarch64-apple-darwin"
_KEEP_LINUX = "aarch64-unknown-linux-gnu"
_KEEP_SERVER = "file://{trust-root}/bootstrap/trust-stage0"
_KEEP_SRC = f"trust-src-{_KEEP_VERSION}.tar.xz"
_KEEP_LIB = "trust-src/lib/rustlib/src/rust/library/core/src/lib.rs"
_KEEP_TEMPLATE = REPO_ROOT / "src" / "tools" / "rust-installer" / "install-template.sh"


def _keep_installer(**slots: str) -> bytes:
    """install.sh as rust-installer's generator writes it: install-template.sh with
    its five slots filled, by default with the values of the pinned trust-src."""
    values = {"TEMPLATE_PRODUCT_NAME": "'Trust'", "TEMPLATE_REL_MANIFEST_DIR": "rustlib",
              "TEMPLATE_SUCCESS_MESSAGE": "'trust src installed.'",
              "TEMPLATE_LEGACY_MANIFEST_DIRS": "'rustlib,cargo'", "TEMPLATE_RUST_INSTALLER_VERSION": "'3'",
              **slots}
    text = _KEEP_TEMPLATE.read_text(encoding="utf-8")
    for slot, value in values.items():
        text = text.replace(f"%%{slot}%%", value)
    return text.encode("utf-8")


_KEEP_INSTALLER = _keep_installer()


_ABSENT = object()


def _keep_archive(path: Path, members: dict[str, object]) -> Path:
    """A .tar.xz whose package root is its file name. A member is bytes, None for
    a directory, ("symlink", target), ("hardlink", member name), or ("file", mode,
    bytes)."""
    prefix = stage0_prepare.tarball_prefix(path.name)
    with tarfile.open(path, "w:xz") as archive:
        info = tarfile.TarInfo(prefix)
        info.type, info.mode = tarfile.DIRTYPE, 0o755
        archive.addfile(info)
        for name, data in members.items():
            info = tarfile.TarInfo(f"{prefix}/{name}")
            if data is None:
                info.type, info.mode = tarfile.DIRTYPE, 0o755
                archive.addfile(info)
            elif isinstance(data, tuple) and data[0] == "symlink":
                info.type, info.linkname, info.mode = tarfile.SYMTYPE, data[1], 0o777
                archive.addfile(info)
            elif isinstance(data, tuple) and data[0] == "hardlink":
                info.type, info.linkname, info.mode = tarfile.LNKTYPE, data[1], 0o644
                archive.addfile(info)
            else:
                mode, payload = (data[1], data[2]) if isinstance(data, tuple) else (
                    0o755 if name.endswith("install.sh") else 0o644, data)
                info.mode, info.size = mode, len(payload)
                archive.addfile(info, io.BytesIO(payload))
    return path


def _keep_src_members(builder_config: object, changes: dict[str, object] | None = None) -> dict[str, object]:
    """trust-src's members; `_ABSENT` removes one."""
    members: dict[str, object] = {
        "components": b"trust-src\n",
        "install.sh": _KEEP_INSTALLER,
        "version": f"{_KEEP_VERSION}\n".encode(),
        "git-commit-hash": f"{_KEEP_COMMIT}\n".encode(),
        "builder-config": builder_config,
        "trust-src/manifest.in": f"file:{_KEEP_LIB.split('/', 1)[1]}\n".encode(),
        _KEEP_LIB: b"pub fn core() {}\n",
    }
    members.update(changes or {})
    return {name: value for name, value in members.items() if value is not _ABSENT}


def _keep_dev_members(host: str) -> dict[str, object]:
    library = f"lib/rustlib/{host}/lib/librustc_driver_fixture.rlib"
    return {
        "components": b"trustc-dev\n",
        "install.sh": _KEEP_INSTALLER,
        "version": f"{_KEEP_VERSION}\n".encode(),
        "git-commit-hash": f"{_KEEP_COMMIT}\n".encode(),
        "trustc-dev/manifest.in": f"file:{library}\n".encode(),
        f"trustc-dev/{library}": f"rustc_private for {host}\n".encode(),
    }


def _keep_manifest(built: dict[str, dict[str, tuple[str, str]]], host: str) -> dict:
    """A channel manifest: `built` maps component -> triple -> (url, sha256);
    every other seed component is unbuilt for `host`."""
    pkg: dict = {"trust": {"version": _KEEP_VERSION, "git_commit_hash": _KEEP_COMMIT}}
    for component in stage0_prepare.SOURCE_STAGE0_COMPONENTS:
        targets = {host: {"available": False}}
        for triple, (url, digest) in built.get(component, {}).items():
            targets[triple] = {"available": True, "xz_url": url, "xz_hash": digest}
        pkg[component] = {"version": _KEEP_VERSION, "git_commit_hash": _KEEP_COMMIT,
                          "target": targets}
    return {"date": _KEEP_DATE, "pkg": pkg}


def _keep_digest(path: Path) -> str:
    return stage0_prepare.sha256_file(path)


def _keep_tree(top: Path) -> dict[str, str]:
    return {
        path.relative_to(top).as_posix(): _keep_digest(path)
        for path in sorted(top.rglob("*")) if path.is_file()
    } if top.exists() else {}


class _KeepFixture:
    """The first host's output root (its pinned archives and manifest, as
    prepare.py wrote them) and the second host's dist, at `base`."""

    def __init__(self, base: Path, *, mac_src: dict | None = None, linux_src: dict | None = None):
        self.base = base
        self.output = base / "prepared" / "bootstrap" / "trust-stage0"
        self.stage0 = base / "prepared" / "src-stage0"
        self.input = base / "linux-dist"
        raw = base / "mac-raw"
        for directory in (self.input, raw, self.output / "dist" / _KEEP_DATE):
            directory.mkdir(parents=True)
        dated = self.output / "dist" / _KEEP_DATE
        # The first host's pin: prepare.py's own repacks, beside the manifest naming them.
        pinned: dict[str, dict[str, tuple[str, str]]] = {}
        for component, triple, name, members in (
            ("trust-src", "*", _KEEP_SRC,
             mac_src or _keep_src_members(b"[build]\nbuild-dir = 'build'\n")),
            ("trustc-dev", _KEEP_MAC, f"trustc-dev-{_KEEP_VERSION}-{_KEEP_MAC}.tar.xz",
             _keep_dev_members(_KEEP_MAC)),
        ):
            source = _keep_archive(raw / name, members)
            stage0_prepare.repack_owned_tarball(
                source, dated / name, old_filename=name, new_filename=name,
                source_channel="trust", owned_channel="trust",
            )
            pinned.setdefault(component, {})[triple] = (
                f"{_KEEP_SERVER}/dist/{_KEEP_DATE}/{name}", _keep_digest(dated / name)
            )
        self.pinned = {name: _keep_digest(dated / name) for name in (
            _KEEP_SRC, f"trustc-dev-{_KEEP_VERSION}-{_KEEP_MAC}.tar.xz")}
        text = stage0_prepare.dump_toml(_keep_manifest(pinned, _KEEP_MAC))
        for path in (self.output / "dist" / "channel-rust-trust.toml",
                     dated / "channel-rust-trust.toml"):
            path.write_text(text, encoding="utf-8")
        self.existing = stage0_prepare.tomllib.loads(text)
        # The second host's dist, as build-manifest wrote it, and its trustc-dev handoff.
        dev = f"trustc-dev-{_KEEP_VERSION}-{_KEEP_LINUX}.tar.xz"
        _keep_archive(self.input / dev, _keep_dev_members(_KEEP_LINUX))
        _keep_archive(self.input / _KEEP_SRC,
                      linux_src or _keep_src_members(b"[build]\nbuild-dir = 'build'\n"))
        built = {
            "trustc-dev": {_KEEP_LINUX: (f"https://trust.invalid/{_KEEP_DATE}/{dev}",
                                         _keep_digest(self.input / dev))},
            "trust-src": {"*": (f"https://trust.invalid/{_KEEP_DATE}/{_KEEP_SRC}",
                                _keep_digest(self.input / _KEEP_SRC))},
        }
        (self.input / "channel-rust-trust.toml").write_text(
            stage0_prepare.dump_toml(_keep_manifest(built, _KEEP_LINUX)), encoding="utf-8")
        for root in stage0_prepare.STAGE0_ARTIFACT_ROOTS:
            handoff = self.output / root / _KEEP_COMMIT / dev
            handoff.parent.mkdir(parents=True)
            shutil.copyfile(self.input / dev, handoff)

    def run(self, *flags: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        argv = ["--input-dist", str(self.input), "--output-root", str(self.output),
                "--stage0-output", str(self.stage0), "--stage0-seed-only", "--archive-format", "xz",
                "--git-commit-hash", _KEEP_COMMIT, "--date", _KEEP_DATE, "--dist-server", _KEEP_SERVER,
                *flags]
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = stage0_prepare.main(argv)
        return code, out.getvalue(), err.getvalue()

    def rows(self) -> dict[str, str]:
        return {key: value for key, value in stage0_prepare.stage0_key_values(self.stage0).items()
                if key.startswith("dist/")}


def test_stage0_keep_existing_shared_needs_merge_existing_and_xz() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        fixture = _KeepFixture(Path(tmp))
        before = _keep_tree(fixture.base)
        code, _out, err = fixture.run("--keep-existing-shared")
        assert code == 1, err
        assert "--keep-existing-shared needs --merge-existing" in err and "Nothing was written" in err, err
        code, _out, err = fixture.run("--merge-existing", "--keep-existing-shared", "--archive-format", "both")
        assert code == 1 and "compares .tar.xz archives" in err, err
        assert _keep_tree(fixture.base) == before


def test_stage0_keep_existing_shared_keeps_the_pinned_archive_and_every_darwin_row() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        fixture = _KeepFixture(Path(tmp))
        dated = fixture.output / "dist" / _KEEP_DATE
        code, out, err = fixture.run("--merge-existing", "--keep-existing-shared")
        assert code == 0, err
        # The shared archive in the output root is the pinned one, byte for byte.
        assert _keep_digest(dated / _KEEP_SRC) == fixture.pinned[_KEEP_SRC]
        rows = fixture.rows()
        linux = f"trustc-dev-{_KEEP_VERSION}-{_KEEP_LINUX}.tar.xz"
        assert rows == {
            f"dist/{_KEEP_DATE}/{_KEEP_SRC}": fixture.pinned[_KEEP_SRC],
            f"dist/{_KEEP_DATE}/trustc-dev-{_KEEP_VERSION}-{_KEEP_MAC}.tar.xz":
                fixture.pinned[f"trustc-dev-{_KEEP_VERSION}-{_KEEP_MAC}.tar.xz"],
            f"dist/{_KEEP_DATE}/{linux}": _keep_digest(dated / linux),
        }, rows
        # No Darwin or shared manifest table moved: every one is the existing entry.
        merged = stage0_prepare.tomllib.loads(
            (fixture.output / "dist" / "channel-rust-trust.toml").read_text(encoding="utf-8"))
        for component, package in fixture.existing["pkg"].items():
            for triple, entry in (package.get("target") or {}).items():
                if stage0_prepare.manifest_target_is_built(entry):
                    assert merged["pkg"][component]["target"][triple] == entry, (component, triple)
        # The record says what was kept and why; this run's repack is nowhere in the output root.
        record = json.loads((fixture.output / stage0_prepare.KEEP_SHARED_RECORD_FILENAME).read_text())
        assert record["schema"] == stage0_prepare.KEEP_SHARED_RECORD_SCHEMA
        [kept] = record["kept"]
        assert (kept["component"], kept["filename"], kept["pinned_sha256"], kept["this_run_discarded"]) == (
            "trust-src", _KEEP_SRC, fixture.pinned[_KEEP_SRC], True)
        assert kept["this_run_sha256"] != kept["pinned_sha256"]
        assert [row["path"] for row in kept["excluded"]] == ["builder-config"]
        assert "install.sh installs only the component directories" in kept["excluded"][0]["reason"]
        assert "builder-config excluded from the comparison: builder-config is the bootstrap config" in out, out
        files = _keep_tree(fixture.output)
        assert kept["this_run_sha256"] not in files.values()
        assert sorted(files) == sorted([
            "dist/channel-rust-trust.toml", "dist/channel-rust-trust.toml.sha256",
            f"dist/{_KEEP_DATE}/channel-rust-trust.toml", f"dist/{_KEEP_DATE}/channel-rust-trust.toml.sha256",
            f"dist/{_KEEP_DATE}/{_KEEP_SRC}", f"dist/{_KEEP_DATE}/{linux}",
            f"dist/{_KEEP_DATE}/trustc-dev-{_KEEP_VERSION}-{_KEEP_MAC}.tar.xz",
            *(f"{root}/{_KEEP_COMMIT}/{linux}" for root in stage0_prepare.STAGE0_ARTIFACT_ROOTS),
            stage0_prepare.STAGE0_ADMISSION_FILENAME, stage0_prepare.KEEP_SHARED_RECORD_FILENAME,
        ]), sorted(files)

    # Without the flag the same merge pins this host's trust-src over the first
    # host's: the shared row moves, which is what the flag is for.
    with tempfile.TemporaryDirectory() as tmp:
        fixture = _KeepFixture(Path(tmp))
        code, _out, err = fixture.run("--merge-existing")
        assert code == 0, err
        assert fixture.rows()[f"dist/{_KEEP_DATE}/{_KEEP_SRC}"] != fixture.pinned[_KEEP_SRC]
        assert not (fixture.output / stage0_prepare.KEEP_SHARED_RECORD_FILENAME).exists()


def test_stage0_keep_existing_shared_refuses_any_other_differing_member() -> None:
    linux_config = b"[build]\nbuild-dir = 'build'\n"
    prefix = f"trust-src-{_KEEP_VERSION}"
    for what, changes, pattern in (
        ("a source file", {_KEEP_LIB: b"pub fn other() {}\n"},
         rf"differ in 1 member\(s\) other than {prefix}/builder-config \({prefix}/{_KEEP_LIB}: this run "),
        ("an added file", {"trust-src/extra.rs": b"//\n"},
         rf"differ in 1 member\(s\) other than .*\({prefix}/trust-src/extra.rs: this run "),
        ("a mode", {"install.sh": ("file", 0o644, _KEEP_INSTALLER)},
         rf"\({prefix}/install.sh: this run .*'mode': 420.*pinned .*'mode': 493"),
    ):
        with tempfile.TemporaryDirectory() as tmp:
            fixture = _KeepFixture(Path(tmp), linux_src=_keep_src_members(linux_config, changes))
            before = _keep_tree(fixture.output)
            code, _out, err = fixture.run("--merge-existing", "--keep-existing-shared")
            assert code == 1 and re.search(pattern, err), (what, err)
            assert "Nothing was written to the output root" in err and "this run's copy was discarded" in err, err
            assert _keep_tree(fixture.output) == before, what
            assert not fixture.stage0.exists(), what
    # A link whose target alone differs is a differing member too (the table compares targets).
    with tempfile.TemporaryDirectory() as tmp:
        fixture = _KeepFixture(
            Path(tmp),
            mac_src=_keep_src_members(b"[build]\nbuild-dir = 'build'\n",
                                      {"trust-src/link": ("symlink", "a")}),
            linux_src=_keep_src_members(linux_config, {"trust-src/link": ("symlink", "b")}))
        before = _keep_tree(fixture.output)
        code, _out, err = fixture.run("--merge-existing", "--keep-existing-shared")
        assert code == 1 and re.search(
            rf"differ in 1 member\(s\) other than {prefix}/builder-config \({prefix}/trust-src/link: ", err), err
        assert _keep_tree(fixture.output) == before
        assert not fixture.stage0.exists()


def test_stage0_keep_existing_shared_refuses_a_link_member_even_where_builder_config_is_equal() -> None:
    # install.sh copies what a link points at, which no row of the table holds: a link
    # member refuses even when the two archives are member for member the same.
    config = b"[build]\nbuild-dir = '/same/for/both'\n"
    prefix = f"trust-src-{_KEEP_VERSION}"
    for what, changes, pattern in (
        ("a symlink", {"trust-src/lib/x.rs": ("symlink", "/etc/hostname")},
         rf"archive has 1 member\(s\) that are not a regular file or a directory: "
         rf"{prefix}/trust-src/lib/x.rs \(symlink -> /etc/hostname\)"),
        ("a hardlink", {"trust-src/lib/x.rs": ("hardlink", f"{prefix}/version")},
         rf"{prefix}/trust-src/lib/x.rs \(hardlink -> {prefix}/version\)"),
        # A name the table and the installer may read differently.
        ("a '.' component in a member name", {"trust-src/./extra.txt": b"x\n"},
         rf"archive has 1 member name\(s\) outside {prefix}/ or with an empty, '\.' or '\.\.' component or a "
         rf"backslash: \['{prefix}/trust-src/\./extra\.txt'\]"),
    ):
        with tempfile.TemporaryDirectory() as tmp:
            fixture = _KeepFixture(Path(tmp), mac_src=_keep_src_members(config, changes),
                                   linux_src=_keep_src_members(config, changes))
            before = _keep_tree(fixture.output)
            code, _out, err = fixture.run("--merge-existing", "--keep-existing-shared")
            assert code == 1 and re.search(pattern, err), (what, err)
            assert "stands for this run's" in err, (what, err)
            assert "only when install.sh can install nothing" in err, (what, err)
            assert "the pinned archive is untouched" in err and "Next: rebuild the archive" in err, (what, err)
            assert _keep_tree(fixture.output) == before, what
            assert not fixture.stage0.exists(), what


def test_stage0_keep_existing_shared_refuses_a_member_outside_the_package_root() -> None:
    # prepare.py's repack refuses such a name, so the two archives are written here directly,
    # member for member the same: only the name rule stands between them and a keep.
    prefix = f"trust-src-{_KEEP_VERSION}"
    with tempfile.TemporaryDirectory() as tmp:
        sides = []
        for side in ("this-run", "pinned"):
            path = Path(tmp) / side / _KEEP_SRC
            path.parent.mkdir()
            with tarfile.open(path, "w:xz") as archive:
                for name, data in ((f"{prefix}/components", b"trust-src\n"), ("elsewhere/x", b"x\n")):
                    info = tarfile.TarInfo(name)
                    info.size, info.mode = len(data), 0o644
                    archive.addfile(info, io.BytesIO(data))
            sides.append(path)
        try:
            stage0_prepare.compare_shared_archives(sides[0], sides[1], prefix)
        except ValueError as error:
            text = str(error)
        else:
            raise AssertionError("a member outside the package root was kept")
        for label in ("this run's", "the pinned"):
            assert re.search(rf"{label} archive has 1 member name\(s\) outside {prefix}/ or with an empty, '\.' or "
                             r"'\.\.' component or a backslash: \['elsewhere/x'\]", text), text
        assert "the pinned archive is untouched" in text, text


def test_stage0_keep_existing_shared_reads_install_sh_against_the_template_it_reviewed() -> None:
    # INSTALLER_TEMPLATE_SHA256 is the template in this tree: an edit of it moves the digest only
    # with a reading of what the edited install.sh reaches.
    data = _KEEP_TEMPLATE.read_bytes()
    assert stage0_prepare.hashlib.sha256(data).hexdigest() == stage0_prepare.INSTALLER_TEMPLATE_SHA256
    text = data.decode("utf-8")
    for slot, _value in stage0_prepare.INSTALLER_TEMPLATE_SLOTS:
        assert text.count(f"%%{slot}%%") == 1 and f"\n{slot}=%%{slot}%%\n" in text, slot
    assert b"builder-config" not in data
    assert stage0_prepare.installer_template_problem(_KEEP_INSTALLER) is None
    longer = stage0_prepare.hashlib.sha256(data + b"\n").hexdigest()
    assert stage0_prepare.installer_template_problem(_KEEP_INSTALLER + b"\n") == (
        f"with its five slot values put back it has sha256 {longer}")
    assert stage0_prepare.installer_template_problem(b"\xff") == "it is not UTF-8"


def test_stage0_keep_existing_shared_refuses_a_builder_config_outside_the_narrow_case() -> None:
    mac, linux = b"mac builder\n", b"linux builder\n"
    prefix = f"trust-src-{_KEEP_VERSION}"
    reached = b"file:../builder-config\n"
    named = _KEEP_INSTALLER + b'cp builder-config "$1"\n'
    library = f"file:{_KEEP_LIB.split('/', 1)[1]}\n".encode()
    # install.sh lines that reach builder-config without spelling it (the real install.sh
    # installed its bytes at <prefix>/lib/bc from each, measured 2026-11-13).
    call = b'install_components "$src_dir" "$abs_libdir" "$dest_prefix" "$components"\n'
    assert _KEEP_INSTALLER.count(call) == 1
    globbed = _KEEP_INSTALLER.replace(call, call + b'cp "$src_dir"/builder-conf?g "$dest_prefix/lib/bc"\n')
    split = _KEEP_INSTALLER.replace(call, call + b'cp "$src_dir/builder-""config" "$dest_prefix/lib/bc"\n')
    assert b"builder-config" not in globbed + split
    template = (rf"{prefix}/install.sh is not rust-installer's install-template.sh \(sha256 "
                rf"{stage0_prepare.INSTALLER_TEMPLATE_SHA256}\) with plain values in its five slots \(")

    def both(changes: dict[str, object]) -> tuple[dict[str, object], dict[str, object]]:
        return _keep_src_members(mac, changes), _keep_src_members(linux, changes)

    def line(text: str, why: str) -> str:
        return (rf"has the line {re.escape(repr(text))}, which is not a file: or dir: path inside its "
                rf"component directory \({re.escape(why)}")

    def odd_bytes(found: bytes) -> str:
        return (rf"{prefix}/components holds bytes other than letters, digits, '\.', '_', '-', space, tab and "
                rf"newline \({re.escape(repr(found))}\): install.sh splits it on space, tab and newline only")

    for what, mac_src, linux_src, pattern in (
        # components split where install.sh does not split it (IFS is space, tab and newline):
        # install.sh reads one component, 'trust-src\x1cfoo', whose manifest.in leaves it (the real
        # install.sh installed builder-config at <prefix>/.. from each, measured 2026-11-13).
        ("components split on \\x1c",
         *both({"components": b"trust-src\x1cfoo\n", "foo/manifest.in": b"file:x\n", "foo/x": b"x\n",
                "trust-src\x1cfoo/manifest.in": reached}),
         odd_bytes(b"\x1c")),
        ("components split on a no-break space",
         *both({"components": "trust-src foo\n".encode(), "foo/manifest.in": b"file:x\n", "foo/x": b"x\n",
                "trust-src foo/manifest.in": reached}),
         odd_bytes(b"\xa0\xc2")),
        ("a directory components does not name", *both({"extra/manifest.in": reached}),
         rf"archive has 1 director\(ies\) directly under {prefix}/ that {prefix}/components does not name "
         r"\(\['extra'\]\)"),
        # install.sh is a script: what it reaches is read from what it is, not from what it spells.
        ("install.sh reaching it by a glob", *both({"install.sh": globbed}),
         template + r"with its five slot values put back it has sha256 [0-9a-f]{64}\)"),
        ("install.sh reaching it by a quote split", *both({"install.sh": split}),
         template + r"with its five slot values put back it has sha256 [0-9a-f]{64}\)"),
        ("a slot value install.sh expands",
         *both({"install.sh": _keep_installer(TEMPLATE_PRODUCT_NAME='"$(cat builder-conf?g)"')}),
         template + r"it has 0 TEMPLATE_PRODUCT_NAME= line\(s\) with a plain value, and the template has one\)"),
        ("a slot assigned twice",
         *both({"install.sh": _KEEP_INSTALLER.replace(call, b"TEMPLATE_REL_MANIFEST_DIR=rustlib\n" + call)}),
         template + r"it has 2 TEMPLATE_REL_MANIFEST_DIR= line\(s\) with a plain value"),
        # A NUL `read` drops: '.\0.' is '..' to install.sh (the real install.sh installed
        # builder-config at <prefix>/.. without this rule, measured 2026-11-13).
        ("a NUL `read` drops", *both({"trust-src/manifest.in": library + b"file:.\x00./builder-config\n"}),
         line("file:.\x00./builder-config", "a control or line-separator character")),
        # The three shapes that reached builder-config through the text-only check
        # (the real install.sh installed its bytes from each, measured 2026-11-13).
        ("a symlink up to the package root",
         *both({"trust-src/up": ("symlink", ".."),
                "trust-src/manifest.in": library + b"file:up/builder-config\n"}),
         rf"archive has 1 member\(s\) that are not a regular file or a directory: {prefix}/trust-src/up "
         r"\(symlink -> \.\.\)"),
        ("a hardlink to builder-config",
         *both({"trust-src/lib/alias.rs": ("hardlink", f"{prefix}/builder-config"),
                "trust-src/manifest.in": library + b"file:lib/alias.rs\n"}),
         rf"{prefix}/trust-src/lib/alias.rs \(hardlink -> {prefix}/builder-config\)"),
        ("a line `read` rewrites to leave the component",
         *both({"trust-src/manifest.in": library + b"file:lib/.\\./.\\./builder-config\n"}),
         line("file:lib/.\\./.\\./builder-config", "a backslash")),
        ("trailing blanks `read` drops",
         *both({"trust-src/manifest.in": library.rstrip(b"\n") + b" \n"}),
         line(library.decode().rstrip("\n") + " ", "leading or trailing whitespace")),
        ("leading blanks `read` drops",
         *both({"trust-src/manifest.in": b" " + library}),
         line(" " + library.decode().rstrip("\n"), "leading or trailing whitespace")),
        ("a '.' component", *both({"trust-src/manifest.in": library + b"dir:.\n"}),
         line("dir:.", "an empty, '.' or '..' path component")),
        ("an empty component", *both({"trust-src/manifest.in": library + b"dir:lib//rustlib\n"}),
         line("dir:lib//rustlib", "an empty, '.' or '..' path component")),
        ("an absolute path", *both({"trust-src/manifest.in": b"file:/builder-config\n"}),
         line("file:/builder-config", "an absolute path")),
        ("an empty path", *both({"trust-src/manifest.in": b"file:\n"}), line("file:", "an empty path")),
        # builder-config must be a regular file in BOTH archives (SEED-SHARED-BUILDER-CONFIG-1).
        ("a symlink in the pinned archive", _keep_src_members(("symlink", "version")), _keep_src_members(linux),
         rf"the pinned archive has no regular file {prefix}/builder-config \(it is symlink\)"),
        ("absent from the pinned archive", _keep_src_members(_ABSENT), _keep_src_members(linux),
         rf"the pinned archive has no regular file {prefix}/builder-config \(it is absent\)"),
        ("a directory in the pinned archive", _keep_src_members(None), _keep_src_members(linux),
         rf"the pinned archive has no regular file {prefix}/builder-config \(it is dir\)"),
        # The installer's own files, which say what it installs.
        ("components naming '.'",
         *both({"components": b"trust-src .\n", "./manifest.in": b"file:builder-config\n"}),
         r"names '\.', which is not one component directory"),
        ("no components", *both({"components": _ABSENT}), rf"has no regular installer file {prefix}/components"),
        ("components naming nothing", *both({"components": b"\n"}), rf"{prefix}/components names no component"),
        ("a component without manifest.in", *both({"components": b"trust-src extra\n"}),
         rf"has no regular installer file {prefix}/extra/manifest.in"),
        ("no install.sh", *both({"install.sh": _ABSENT}), rf"has no regular installer file {prefix}/install.sh"),
        # The shapes shipped first.
        ("not at the package root",
         _keep_src_members(b"same\n", {"trust-src/builder-config": mac}),
         _keep_src_members(b"same\n", {"trust-src/builder-config": linux}),
         rf"other than {prefix}/builder-config \({prefix}/trust-src/builder-config: "),
        ("a symlink", _keep_src_members(mac), _keep_src_members(("symlink", "version")),
         rf"this run's archive has no regular file {prefix}/builder-config \(it is symlink\)"),
        ("absent", _keep_src_members(mac), _keep_src_members(_ABSENT),
         rf"this run's archive has no regular file {prefix}/builder-config \(it is absent\)"),
        ("a directory", _keep_src_members(mac), _keep_src_members(None),
         rf"this run's archive has no regular file {prefix}/builder-config \(it is dir\)"),
        ("named as a component",
         _keep_src_members(mac, {"components": b"trust-src builder-config\n"}),
         _keep_src_members(linux, {"components": b"trust-src builder-config\n"}),
         "names 'builder-config', which is not one component directory"),
        ("reached by a manifest.in line",
         _keep_src_members(mac, {"trust-src/manifest.in": reached}),
         _keep_src_members(linux, {"trust-src/manifest.in": reached}),
         "has the line 'file:../builder-config', which is not a file: or dir: path inside"),
        ("named by install.sh",
         _keep_src_members(mac, {"install.sh": named}),
         _keep_src_members(linux, {"install.sh": named}),
         rf"{prefix}/install.sh names builder-config"),
    ):
        with tempfile.TemporaryDirectory() as tmp:
            fixture = _KeepFixture(Path(tmp), mac_src=mac_src, linux_src=linux_src)
            before = _keep_tree(fixture.output)
            code, _out, err = fixture.run("--merge-existing", "--keep-existing-shared")
            assert code == 1 and re.search(pattern, err), (what, err)
            assert "the pinned archive is untouched" in err, (what, err)
            assert _keep_tree(fixture.output) == before, what
            assert not fixture.stage0.exists(), what


def test_stage0_keep_existing_shared_refuses_a_pinned_file_it_cannot_bind() -> None:
    """The guards of keep_existing_shared_archives and the merge, each by its own words:
    the pinned archive must be the file the existing manifest pins, by name and bytes,
    a regular file, unchanged while it is compared, and its '*' entry must survive the
    merge as the entry that was kept."""
    from unittest import mock

    def manifests(fixture: _KeepFixture) -> list[Path]:
        return [fixture.output / "dist" / "channel-rust-trust.toml",
                fixture.output / "dist" / _KEEP_DATE / "channel-rust-trust.toml"]

    def pinned(fixture: _KeepFixture) -> Path:
        return fixture.output / "dist" / _KEEP_DATE / _KEEP_SRC

    def another_valid_pin(fixture: _KeepFixture) -> None:
        # Another repack whose members are this run's but builder-config: only the digest tells.
        raw = fixture.base / "another-raw"
        raw.mkdir()
        source = _keep_archive(raw / _KEEP_SRC, _keep_src_members(b"[build]\nbuild-dir = '/elsewhere'\n"))
        pinned(fixture).unlink()
        stage0_prepare.repack_owned_tarball(source, pinned(fixture), old_filename=_KEEP_SRC,
                                            new_filename=_KEEP_SRC, source_channel="trust", owned_channel="trust")

    def renamed_in_the_manifest(fixture: _KeepFixture) -> None:
        for path in manifests(fixture):
            path.write_text(path.read_text().replace(f"/{_KEEP_SRC}", "/trust-src-other.tar.xz"))

    def symlinked(fixture: _KeepFixture) -> None:
        elsewhere = fixture.base / "elsewhere.tar.xz"
        shutil.copyfile(pinned(fixture), elsewhere)
        pinned(fixture).unlink()
        pinned(fixture).symlink_to(elsewhere)

    def no_manifest(fixture: _KeepFixture) -> None:
        for path in manifests(fixture):
            path.unlink()

    def after_the_compare(fixture: _KeepFixture, then) -> object:
        real = stage0_prepare.compare_shared_archives

        def compare(this_run: Path, pinned_path: Path, prefix: str) -> dict[str, object]:
            result = real(this_run, pinned_path, prefix)
            then(fixture, pinned_path)
            return result
        return mock.patch.object(stage0_prepare, "compare_shared_archives", compare)

    def appended(fixture: _KeepFixture, pinned_path: Path) -> None:
        with open(pinned_path, "ab") as handle:
            handle.write(b"\0")

    def entry_rewritten(fixture: _KeepFixture, _pinned: Path) -> None:
        old = fixture.existing["pkg"]["trust-src"]["target"]["*"]["xz_hash"]
        for path in manifests(fixture):
            path.write_text(path.read_text().replace(old, "0" * 64))

    def manifests_removed(fixture: _KeepFixture, _pinned: Path) -> None:
        no_manifest(fixture)

    for what, before_run, during, pattern, untouched in (
        ("(a) another valid archive at the pinned path", another_valid_pin, None,
         rf"{re.escape(str(Path('dist') / _KEEP_DATE / _KEEP_SRC))} has sha256 [0-9a-f]{{64}}, and .*pins "
         r"[0-9a-f]{64}\. Nothing was written\. Put the pinned archive at that path", True),
        ("(b) the manifest names another file", renamed_in_the_manifest, None,
         rf"trust-src '\*' is {re.escape(_KEEP_SRC)} in this run and trust-src-other.tar.xz in .*one archive "
         "cannot stand for another", True),
        ("(c) a symlink at the pinned path", symlinked, None,
         r"the pinned trust-src archive .* is not a regular file there .*Put the pinned archive at that path",
         True),
        ("(d) no existing manifest", no_manifest, None,
         r"there is no existing manifest at .* to keep a shared archive from\. Nothing was written", True),
        ("(e) the pinned archive changes while it is compared", None, appended,
         r"changed while it was compared\. Nothing was written", False),
        ("(f) the '*' entry changes after its archive was compared", None, entry_rewritten,
         r"the existing trust-src '\*' entry in .* changed after its archive was compared", False),
        ("(g) the manifest goes after the compare, so the merge keeps nothing", None, manifests_removed,
         r"after the merge, trust-src '\*' is not the pinned entry for " + re.escape(_KEEP_SRC), False),
    ):
        with tempfile.TemporaryDirectory() as tmp:
            fixture = _KeepFixture(Path(tmp))
            if before_run is not None:
                before_run(fixture)
            before = _keep_tree(fixture.output)
            with after_the_compare(fixture, during) if during else contextlib.nullcontext():
                code, _out, err = fixture.run("--merge-existing", "--keep-existing-shared")
            assert code == 1 and re.search(pattern, err), (what, err)
            assert not fixture.stage0.exists(), what
            assert not (fixture.output / stage0_prepare.KEEP_SHARED_RECORD_FILENAME).exists(), what
            if untouched:
                # Refused before anything was written: the output root is as it was.
                assert _keep_tree(fixture.output) == before, what


_PRODUCER_PREFLIGHT_INPUTS = (
    "x.py",
    "src/bootstrap/src/core/config/flags.rs",
    "src/bootstrap/src/core/builder/mod.rs",
    "src/bootstrap/src/core/build_steps/dist.rs",
    "bootstrap.example.toml",
    "src/bootstrap/defaults/bootstrap.dist.toml",
)


def _copy_producer_preflight_inputs(destination: Path) -> None:
    for relative in _PRODUCER_PREFLIGHT_INPUTS:
        source = REPO_ROOT / relative
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def test_producer_preflight_accepts_path_chained_aliases() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        _copy_producer_preflight_inputs(root)
        errors = stage0_prepare.producer_command_preflight_errors(root)
    assert errors == (), errors


def test_producer_preflight_cues_the_live_source_selector() -> None:
    # bootstrap.example.toml documents install.rs's `Src` selector, `rust-src`
    # since upstream 162423. The live example carries the cue; one that still
    # lists the retired `"src"` (as the port's conflict resolution left it)
    # is reported missing it.
    entry = '#    "rust-src",'
    cue_error = (
        "x.py config docs/defaults are missing producer cue "
        "'\"rust-src\"' in bootstrap.example.toml"
    )
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        _copy_producer_preflight_inputs(root)
        live = stage0_prepare.producer_command_preflight_errors(root)
        example = root / "bootstrap.example.toml"
        source = example.read_text(encoding="utf-8")
        assert source.count(entry) == 1
        example.write_text(source.replace(entry, '#    "src",'), encoding="utf-8")
        retired = stage0_prepare.producer_command_preflight_errors(root)
    assert not [error for error in live if "producer cue" in error], live
    assert cue_error in retired, retired


def test_producer_preflight_rejects_wrong_path_alias_chains() -> None:
    mutations = (
        (
            "trustc",
            'run.path("compiler/rustc").alias("trustc").alias("rustc")',
            'run.path("compiler/not-rustc").alias("trustc").alias("rustc")',
        ),
        (
            "trust-std",
            'run.path("library/std").alias("trust-std").alias("rust-std")',
            'run.path("library/not-std").alias("trust-std").alias("rust-std")',
        ),
    )
    for alias, accepted, rejected in mutations:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_producer_preflight_inputs(root)
            dist_steps = root / "src/bootstrap/src/core/build_steps/dist.rs"
            source = dist_steps.read_text(encoding="utf-8")
            assert source.count(accepted) == 1
            dist_steps.write_text(source.replace(accepted, rejected), encoding="utf-8")
            errors = stage0_prepare.producer_command_preflight_errors(root)
        expected = f"stage0 dist producer alias is not registered for x.py dist: {alias}"
        assert expected in errors, errors


def test_producer_preflight_rejects_non_executable_alias_decoys() -> None:
    registrations = (
        (
            "trustc",
            "Rustc",
            'run.path("compiler/rustc").alias("trustc").alias("rustc")',
        ),
        (
            "trust-std",
            "Std",
            'run.path("library/std").alias("trust-std").alias("rust-std")',
        ),
    )
    for alias, step_type, accepted in registrations:
        normal_string = accepted.replace('"', '\\"')
        decoys = "\n".join(
            (
                f"// {accepted}",
                f"/// {accepted}",
                f"/* outer /* {accepted} */ {accepted} */",
                f'const NORMAL_DECOY: &str = "{normal_string}";',
                f'const RAW_DECOY: &str = r#"{accepted}"#;',
                # A different command-line step carrying the accepted chain.
                "impl CommandLineStep for ProducerAuditDecoy {",
                "    type Output = ();",
                "    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {",
                f"        {accepted}",
                "    }",
                "}",
                # The retired spelling for the same step type: a plain
                # `Step` impl is a cached helper x.py dist never consults.
                f"impl Step for {step_type} {{",
                "    type Output = ();",
                "    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {",
                f"        {accepted}",
                "    }",
                "}",
            )
        )
        rejected_bodies = (
            f'run.alias("{alias}")',
            (
                f"let _discarded = {accepted};\n"
                '        run.path("wrong").alias("wrong")'
            ),
            # The accepted chain as the tail of a body that first rebinds
            # `run`: the returned ShouldRun is no longer exactly the chain.
            f'let run = run.alias("producer-audit-decoy");\n        {accepted}',
        )
        for rejected_body in rejected_bodies:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                _copy_producer_preflight_inputs(root)
                dist_steps = root / "src/bootstrap/src/core/build_steps/dist.rs"
                source = dist_steps.read_text(encoding="utf-8")
                assert source.count(accepted) == 1
                assert source.count(f"impl CommandLineStep for {step_type} {{") == 1
                source = source.replace(accepted, rejected_body, 1)
                dist_steps.write_text(f"{source}\n{decoys}\n", encoding="utf-8")
                errors = stage0_prepare.producer_command_preflight_errors(root)
            expected = (
                "stage0 dist producer alias is not registered for x.py dist: "
                f"{alias}"
            )
            assert expected in errors, (step_type, rejected_body, errors)


def test_producer_preflight_rejects_duplicate_target_step_impl() -> None:
    accepted = 'run.path("compiler/rustc").alias("trustc").alias("rustc")'
    duplicate = "\n".join(
        (
            "impl CommandLineStep for Rustc {",
            "    type Output = ();",
            "    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {",
            f"        {accepted}",
            "    }",
            "}",
        )
    )
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        _copy_producer_preflight_inputs(root)
        dist_steps = root / "src/bootstrap/src/core/build_steps/dist.rs"
        source = dist_steps.read_text(encoding="utf-8")
        assert source.count("impl CommandLineStep for Rustc {") == 1
        dist_steps.write_text(f"{source}\n{duplicate}\n", encoding="utf-8")
        errors = stage0_prepare.producer_command_preflight_errors(root)
    expected = "stage0 dist producer alias is not registered for x.py dist: trustc"
    assert expected in errors, errors


def test_producer_preflight_rejects_disabled_or_nested_target_definitions() -> None:
    accepted = 'run.path("compiler/rustc").alias("trustc").alias("rustc")'
    method = "\n".join(
        (
            "fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {",
            f"        {accepted}",
            "    }",
        )
    )
    nested_method = "\n".join(
        (
            "fn producer_audit_decoy() {",
            "        fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {",
            f"            {accepted}",
            "        }",
            "    }",
        )
    )
    nested_impl = "\n".join(
        (
            "producer_audit_decoy! {",
            "    impl CommandLineStep for Rustc {",
            "        type Output = ();",
            "        fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {",
            f"            {accepted}",
            "        }",
            "    }",
            "}",
        )
    )
    mutations = (
        lambda source: source.replace(method, f"#[cfg(any())]\n    {method}", 1),
        lambda source: source.replace(
            "impl CommandLineStep for Rustc {",
            "#[cfg(any())]\nimpl CommandLineStep for Rustc {",
            1,
        ),
        lambda source: source.replace(
            method,
            method.replace(
                "fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {",
                "fn should_run() -> ShouldRun<'_> {",
            ),
            1,
        ),
        lambda source: source.replace(method, nested_method, 1),
        lambda source: (
            source.replace(
                "impl CommandLineStep for Rustc {",
                "impl CommandLineStep for RemovedRustc {",
                1,
            )
            + f"\n{nested_impl}\n"
        ),
    )
    for mutate in mutations:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_producer_preflight_inputs(root)
            dist_steps = root / "src/bootstrap/src/core/build_steps/dist.rs"
            source = dist_steps.read_text(encoding="utf-8")
            assert source.count(method) == 1
            assert source.count("impl CommandLineStep for Rustc {") == 1
            mutated = mutate(source)
            assert mutated != source
            dist_steps.write_text(mutated, encoding="utf-8")
            errors = stage0_prepare.producer_command_preflight_errors(root)
        expected = "stage0 dist producer alias is not registered for x.py dist: trustc"
        assert expected in errors, errors


def test_producer_preflight_rejects_builder_prefix_and_wrong_kind_decoys() -> None:
    def replace_step(source: str, replacement: str) -> str:
        assert source.count("dist::Rustc,") == 1
        return source.replace("dist::Rustc,", replacement, 1)

    unrelated_match = "\n".join(
        (
            "fn producer_builder_decoy(kind: Kind) {",
            "    match kind {",
            "        Kind::Dist => describe!(dist::Rustc),",
            "        _ => unreachable!(),",
            "    }",
            "}",
        )
    )
    mutations = (
        (
            "prefix collision",
            lambda source: replace_step(source, "dist::RustcDocs,"),
        ),
        (
            "nested generic",
            lambda source: replace_step(
                source,
                "dist::Wrapper<Other, dist::Rustc, Other>,",
            ),
        ),
        (
            "wrong Kind",
            lambda source: replace_step(source, "dist::RemovedRustc,").replace(
                "Kind::Miri => describe!(test::Crate),",
                "Kind::Miri => describe!(test::Crate, dist::Rustc),",
                1,
            ),
        ),
        (
            "cfg-disabled arm",
            lambda source: replace_step(source, "dist::RemovedRustc,").replace(
                "            Kind::Dist => describe!(",
                "            #[cfg(any())]\n"
                "            Kind::Dist => describe!(dist::Rustc),\n"
                "            Kind::RemovedDist => describe!(",
                1,
            ),
        ),
        (
            "cfg-disabled match",
            lambda source: source.replace(
                "        match kind {",
                "        #[cfg(any())]\n        match kind {",
                1,
            ),
        ),
        (
            "unrelated match",
            lambda source: (
                replace_step(source, "dist::RemovedRustc,")
                + f"\n{unrelated_match}\n"
            ),
        ),
        (
            "wrong self type",
            lambda source: source.replace(
                "impl<'a> Builder<'a> {",
                "impl<'a> Wrapper<Builder<'a>> {",
                1,
            ),
        ),
        (
            "chained describe result",
            lambda source: source.replace(
                "                dist::ReproducibleArtifacts\n            ),",
                "                dist::ReproducibleArtifacts\n"
                "            ).into_iter().filter(producer_builder_decoy),",
                1,
            ),
        ),
    )
    for label, mutate in mutations:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_producer_preflight_inputs(root)
            builder = root / "src/bootstrap/src/core/builder/mod.rs"
            source = builder.read_text(encoding="utf-8")
            mutated = mutate(source)
            assert mutated != source, label
            builder.write_text(mutated, encoding="utf-8")
            errors = stage0_prepare.producer_command_preflight_errors(root)
        expected = "x.py dist does not describe the step for producer alias trustc"
        assert expected in errors, (label, errors)


_DIST_RS = "src/bootstrap/src/core/build_steps/dist.rs"
_BUILDER_RS = "src/bootstrap/src/core/builder/mod.rs"
_NOT_REGISTERED = "stage0 dist producer alias is not registered for x.py dist: "
_NOT_DESCRIBED = "x.py dist does not describe the step for producer alias "


def _producer_preflight_errors_after(relative: str, mutate) -> tuple[str, ...]:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        _copy_producer_preflight_inputs(root)
        path = root / relative
        source = path.read_text(encoding="utf-8")
        mutated = mutate(source)
        assert mutated != source, relative
        path.write_text(mutated, encoding="utf-8")
        return stage0_prepare.producer_command_preflight_errors(root)


def test_producer_preflight_pins_current_bootstrap_step_api() -> None:
    """The 2026-10-16 port renamed bootstrap's registration API to
    `CommandLineStep`/`CommandLineStepDescription`; the preflight must read
    exactly that spelling, and any other spelling (the retired one or the next
    rename) must be refused with an error that names the cause."""

    drift = stage0_prepare.BOOTSTRAP_STEP_API_DRIFT_ERROR
    aliases = stage0_prepare.STAGE0_DIST_PRODUCER_ALIASES
    all_not_described = {_NOT_DESCRIBED + alias for alias in aliases}
    dist_rs = REPO_ROOT / _DIST_RS
    builder_rs = REPO_ROOT / _BUILDER_RS

    # The real checkout is in the current spelling, and every parser accepts it.
    assert stage0_prepare.BOOTSTRAP_COMMAND_LINE_STEP_TRAIT == "CommandLineStep"
    assert (
        stage0_prepare.BOOTSTRAP_COMMAND_LINE_STEP_DESCRIPTION
        == "CommandLineStepDescription"
    )
    assert stage0_prepare.rust_declares_command_line_step_api(builder_rs)
    for alias, (step_type, body) in (
        stage0_prepare.STAGE0_DIST_PRODUCER_EXACT_SHOULD_RUN.items()
    ):
        assert stage0_prepare.rust_step_returns_exact_should_run(
            dist_rs, step_type, body
        ), alias
    for alias, (_, step_path) in stage0_prepare.STAGE0_DIST_PRODUCER_ALIAS_PATTERNS.items():
        assert stage0_prepare.rust_kind_describes_exact_step(
            builder_rs, "Dist", step_path
        ), alias

    # dist.rs: the retired `impl Step for` spelling, or any other trait name,
    # does not register the producer; the error names exactly that alias and
    # does not blame the (unchanged) builder API.
    for alias, step_type in (("trustc", "Rustc"), ("trust-std", "Std")):
        current = f"impl CommandLineStep for {step_type} {{"
        for replacement in (
            f"impl Step for {step_type} {{",
            f"impl CliStep for {step_type} {{",
        ):
            errors = _producer_preflight_errors_after(
                _DIST_RS,
                lambda source: source.replace(current, replacement, 1),
            )
            not_registered = {e for e in errors if e.startswith(_NOT_REGISTERED)}
            assert not_registered == {_NOT_REGISTERED + alias}, (replacement, errors)
            assert drift not in errors, (replacement, errors)

    # builder/mod.rs: `get_step_descriptions` returning the retired
    # `Vec<StepDescription>` describes no producer at all.
    errors = _producer_preflight_errors_after(
        _BUILDER_RS,
        lambda source: source.replace(
            "Vec<CommandLineStepDescription>", "Vec<StepDescription>", 1
        ),
    )
    assert all_not_described <= set(errors), errors

    # A wholesale rename of the API -- back to the retired spelling, or on to
    # the next one -- is reported as API drift, not only as eleven producers
    # that happen to be undescribed.
    for old, new in (("CommandLineStep", "Step"), ("CommandLineStep", "CliStep")):
        errors = _producer_preflight_errors_after(
            _BUILDER_RS,
            lambda source: source.replace(old, new),
        )
        assert drift in errors, (new, errors)
        assert all_not_described <= set(errors), (new, errors)

    # The anchor follows the registration chain, not the names alone.
    trait_should_run = "    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_>;\n"
    retired_trait_decoy = "\n".join(
        (
            "pub(crate) trait CommandLineStep: 'static + Clone {",
            "    fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_>;",
            "}",
        )
    )
    rename_real_trait = (
        lambda source: source.replace(
            "pub(crate) trait CommandLineStep:",
            "pub(crate) trait RemovedCommandLineStep:",
            1,
        )
    )
    anchor_mutations = (
        (
            "should_run moved off CommandLineStep",
            lambda source: source.replace(trait_should_run, "", 1),
        ),
        (
            "description built from a different bound",
            lambda source: source.replace(
                "fn from<S: CommandLineStep>(kind: Kind)",
                "fn from<S: Step>(kind: Kind)",
                1,
            ),
        ),
        (
            "description takes should_run from elsewhere",
            lambda source: source.replace(
                "should_run: S::should_run,", "should_run: Decoy::should_run,", 1
            ),
        ),
        (
            "duplicate root trait",
            lambda source: f"{source}\n{retired_trait_decoy}\n",
        ),
        (
            "trait only in a comment",
            lambda source: rename_real_trait(source)
            + "\n/*\n"
            + retired_trait_decoy
            + "\n*/\n",
        ),
        (
            "trait only nested in a module",
            lambda source: rename_real_trait(source)
            + f"\nmod producer_audit_decoy {{\n{retired_trait_decoy}\n}}\n",
        ),
        (
            "trait only behind a disabled cfg",
            lambda source: rename_real_trait(source)
            + f"\n#[cfg(any())]\n{retired_trait_decoy}\n",
        ),
    )
    for label, mutate in anchor_mutations:
        errors = _producer_preflight_errors_after(_BUILDER_RS, mutate)
        assert drift in errors, (label, errors)



def test_producer_preflight_requires_the_current_command_line_trait() -> None:
    accepted = "impl CommandLineStep for Rustc {"
    expected = "stage0 dist producer alias is not registered for x.py dist: trustc"
    for rejected in (
        "impl Step for Rustc {",  # The historical trait no longer registers CLI steps.
        "impl CommandLineStepDecoy for Rustc {",
        "impl decoy::CommandLineStep for Rustc {",
        "#[cfg(any())]\nimpl CommandLineStep for Rustc {",
    ):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_producer_preflight_inputs(root)
            path = root / "src/bootstrap/src/core/build_steps/dist.rs"
            source = path.read_text()
            assert source.count(accepted) == 1
            # Valid-looking names in comments and strings cannot repair an
            # implementation of the wrong, qualified or disabled trait.
            decoys = f'\n// {accepted}\nconst DECOY: &str = r#"{accepted}"#;\n'
            path.write_text(source.replace(accepted, rejected, 1) + decoys)
            errors = stage0_prepare.producer_command_preflight_errors(root)
        assert expected in errors, (rejected, errors)


def test_producer_preflight_requires_the_current_builder_result_type() -> None:
    accepted = "fn get_step_descriptions(kind: Kind) -> Vec<CommandLineStepDescription> {"
    expected = "x.py dist does not describe the step for producer alias trustc"
    for rejected in (
        "fn get_step_descriptions(kind: Kind) -> Vec<StepDescription> {",
        "fn get_step_descriptions(kind: Kind) -> Vec<CommandLineStepDescriptionDecoy> {",
        "fn get_step_descriptions(kind: Kind) -> Vec<decoy::CommandLineStepDescription> {",
        "fn get_step_descriptions(kind: Kind) -> Vec<Wrapper<CommandLineStepDescription>> {",
        "#[cfg(any())]\n    " + accepted,
    ):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_producer_preflight_inputs(root)
            path = root / "src/bootstrap/src/core/builder/mod.rs"
            source = path.read_text()
            assert source.count(accepted) == 1
            decoys = f'\n// {accepted}\nconst DECOY: &str = r#"{accepted}"#;\n'
            path.write_text(source.replace(accepted, rejected, 1) + decoys)
            errors = stage0_prepare.producer_command_preflight_errors(root)
        assert expected in errors, (rejected, errors)


def load_tests(loader, tests, pattern):
    """`land_gate.py validation-tests` loads this module with unittest (the
    landing gate's selector names it, LAND-SELECT-VALIDATION-REACH-1): each
    module-level test_* function is one case, as a direct run runs them."""
    tests.addTests(unittest.FunctionTestCase(value) for name, value in sorted(globals().items())
                   if name.startswith("test_") and callable(value))
    return tests


def main() -> int:
    tests = [
        test_checked_in_genesis_roots_meet_the_current_stage0_floor,
        test_genesis_root_accepts_only_the_full_pinned_rustc_tuple,
        test_documented_july_8_channel_mismatch_is_rejected,
        test_genesis_linter_versions_use_canonical_identity,
        test_genesis_tippy_preserves_direct_options_and_exact_z_namespace,
        test_genesis_wrapper_quotes_backend_paths_as_data,
        test_compiled_genesis_tippy_preserves_direct_options,
        test_stage0_contract_has_only_rustc_and_cargo_compatibility_aliases,
        test_genesis_emitters_have_exact_canonical_public_bin_surface,
        test_archive_contract_accepts_windows_suffixes_and_rejects_retired_aliases,
        test_stage0_repack_rejects_conflicting_tippy_aliases,
        test_stage0_repack_admits_dist_stock_names_and_refuses_link_entries,
        test_stage0_repack_keeps_installer_components_aligned,
        test_required_host_archives_prefer_canonical_then_pinned_legacy,
        test_sysroot_contract_rejects_forbidden_superset,
        test_stage0_merge_unions_dual_host_manifest_targets,
        test_stage0_merge_keeps_fresh_target_on_shared_triple,
        test_stage0_merge_refuses_mismatched_release,
        test_stage0_keep_existing_shared_needs_merge_existing_and_xz,
        test_stage0_keep_existing_shared_keeps_the_pinned_archive_and_every_darwin_row,
        test_stage0_keep_existing_shared_refuses_any_other_differing_member,
        test_stage0_keep_existing_shared_refuses_a_link_member_even_where_builder_config_is_equal,
        test_stage0_keep_existing_shared_refuses_a_member_outside_the_package_root,
        test_stage0_keep_existing_shared_reads_install_sh_against_the_template_it_reviewed,
        test_stage0_keep_existing_shared_refuses_a_builder_config_outside_the_narrow_case,
        test_stage0_keep_existing_shared_refuses_a_pinned_file_it_cannot_bind,
        test_producer_preflight_accepts_path_chained_aliases,
        test_producer_preflight_cues_the_live_source_selector,
        test_producer_preflight_rejects_wrong_path_alias_chains,
        test_producer_preflight_rejects_non_executable_alias_decoys,
        test_producer_preflight_rejects_duplicate_target_step_impl,
        test_producer_preflight_rejects_disabled_or_nested_target_definitions,
        test_producer_preflight_rejects_builder_prefix_and_wrong_kind_decoys,
        test_producer_preflight_pins_current_bootstrap_step_api,
        test_producer_preflight_requires_the_current_command_line_trait,
        test_producer_preflight_requires_the_current_builder_result_type,
    ]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
