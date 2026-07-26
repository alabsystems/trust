#!/usr/bin/env python3
"""Focused regressions for the canonical targo/tippy stage0 surface."""

from __future__ import annotations

import ast
import importlib.util
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path


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
    rustc = shutil.which("rustc")
    assert rustc is not None, "rustc is required to test the compiled genesis wrapper"
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        real = root / "cargo-clippy"
        fake_cargo_clippy(real)
        wrapper = root / "tippy"
        subprocess.run(
            [
                rustc,
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
                archive.extractall(extracted, filter="data")
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
                "impl Step for ProducerAuditDecoy {",
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
        )
        for rejected_body in rejected_bodies:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                _copy_producer_preflight_inputs(root)
                dist_steps = root / "src/bootstrap/src/core/build_steps/dist.rs"
                source = dist_steps.read_text(encoding="utf-8")
                assert source.count(accepted) == 1
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
            "impl Step for Rustc {",
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
            "    impl Step for Rustc {",
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
            method,
            method.replace(
                "fn should_run(run: ShouldRun<'_>) -> ShouldRun<'_> {",
                "fn should_run() -> ShouldRun<'_> {",
            ),
            1,
        ),
        lambda source: source.replace(method, nested_method, 1),
        lambda source: (
            source.replace("impl Step for Rustc {", "impl Step for RemovedRustc {", 1)
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
            dist_steps.write_text(mutate(source), encoding="utf-8")
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
                "                dist::Gcc\n            ),",
                "                dist::Gcc\n"
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
            builder.write_text(mutate(source), encoding="utf-8")
            errors = stage0_prepare.producer_command_preflight_errors(root)
        expected = "x.py dist does not describe the step for producer alias trustc"
        assert expected in errors, (label, errors)


def main() -> int:
    tests = [
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
        test_stage0_repack_keeps_installer_components_aligned,
        test_required_host_archives_prefer_canonical_then_pinned_legacy,
        test_sysroot_contract_rejects_forbidden_superset,
        test_stage0_merge_unions_dual_host_manifest_targets,
        test_stage0_merge_keeps_fresh_target_on_shared_triple,
        test_stage0_merge_refuses_mismatched_release,
        test_producer_preflight_accepts_path_chained_aliases,
        test_producer_preflight_rejects_wrong_path_alias_chains,
        test_producer_preflight_rejects_non_executable_alias_decoys,
        test_producer_preflight_rejects_duplicate_target_step_impl,
        test_producer_preflight_rejects_disabled_or_nested_target_definitions,
        test_producer_preflight_rejects_builder_prefix_and_wrong_kind_decoys,
    ]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
