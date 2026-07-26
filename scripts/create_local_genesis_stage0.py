#!/usr/bin/env python3
"""Create an explicit local genesis stage0 adapter for bootstrapping Trust.

This is not release evidence and not an admitted Trust stage0 seed. It creates
Trust-named wrappers around an installed Rust toolchain so a local builder can
produce the first host Trust artifacts when no host Trust stage0 archive exists.
The generated root is stamped and documented under build/ only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
from pathlib import Path


SCHEMA = "trust.local-genesis-stage0-adapter.v1"
GENESIS_ROOT_SCHEMA = "trust.genesis-roots.v1"
GENESIS_ROOTS_RELATIVE = Path("bootstrap/trust-genesis-roots.json")
REQUIRED_BINS = (
    "trustc",
    "rustc",
    "trustdoc",
    "targo",
    "cargo",
    "targo-trust",
    "trustfmt",
    "targo-fmt",
    "tippy",
    "targo-tippy",
    "tippy-driver",
    "trust-analyzer",
)
REQUIRED_LIBEXEC_BINS = (
    "trust-analyzer-proc-macro-srv",
)
FORBIDDEN_BINS = (
    "rustdoc",
    "rustfmt",
    "rust-analyzer",
    "cargo-trust",
    "tcargo",
    "tcargo-trust",
    "tcargo-fmt",
    "cargo-fmt",
    "cargo-clippy",
    "clippy-driver",
    "targo-clippy",
    "trust-clippy",
    "trust-clippy-driver",
    "trust-miri",
    "miri",
    "targo-miri",
    "cargo-miri",
    "rust-gdb",
    "rust-gdbgui",
    "rust-lldb",
    "rust-windbg.cmd",
)
FORBIDDEN_LIBEXEC_BINS = ("rust-analyzer-proc-macro-srv",)
WRAPPER_SOURCES = {
    "trustc": ("rustc", "rustc"),
    "rustc": ("rustc", "rustc"),
    "trustdoc": ("rustdoc", "rustdoc"),
    "targo": ("cargo", "cargo"),
    "cargo": ("cargo", "cargo"),
    "trustfmt": ("rustfmt", "rustfmt"),
    # cargo-fmt and cargo-clippy report their underlying tool identities in
    # --version output (`rustfmt` / `clippy`), not their executable filenames.
    "targo-fmt": ("cargo-fmt", "rustfmt"),
    "tippy": ("cargo-clippy", "clippy"),
    "targo-tippy": ("cargo-clippy", "clippy"),
    "tippy-driver": ("clippy-driver", "clippy"),
    "trust-analyzer": ("rust-analyzer", "rust-analyzer"),
}
# cargo-clippy expects argv[1] to be the external-subcommand marker and drops
# it before parsing options. Canonical `tippy` supplies that marker itself.
# `targo-tippy` strips Targo's `tippy` marker and replaces it with the private
# backend's `clippy` marker, preserving direct and dispatched invocations.
WRAPPER_ARG_PREFIXES = {
    "tippy": "clippy",
    "targo-tippy": "clippy",
}
WRAPPER_ARG_MARKERS = {
    "targo-tippy": "tippy",
}
# Public Tippy renamed the inherited driver's compiler pass-through switch.
# The genesis adapter still executes a stock clippy-driver, so translate the
# exact protocol token instead of leaking the retired spelling to users.
WRAPPER_ARG_RENAMES = {
    "tippy-driver": ("--trustc", "--rustc"),
}
TIPPY_VERSION_NAMES = {
    "tippy": "tippy",
    "targo-tippy": "tippy",
    "tippy-driver": "tippy",
}
TIPPY_VERSION_ARG_PREFIXES = {
    "tippy": "clippy",
    "targo-tippy": "clippy",
}
STUB_BINS = {
    "targo-trust": "targo-trust is not part of the inherited Rust genesis toolchain",
}
STUB_LIBEXEC_BINS = {
    "trust-analyzer-proc-macro-srv": (
        "trust-analyzer-proc-macro-srv is not part of the inherited Rust "
        "genesis toolchain"
    ),
}


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def run_stdout(args: list[str]) -> str:
    return subprocess.run(args, text=True, check=True, stdout=subprocess.PIPE).stdout


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rustc_verbose_fields(rustc: str) -> dict[str, str]:
    output = run_stdout([rustc, "--version", "--verbose"])
    fields: dict[str, str] = {}
    for line in output.splitlines():
        key, separator, value = line.partition(": ")
        if not separator:
            continue
        if key in fields:
            raise SystemExit(f"rustc verbose output repeats {key!r}")
        fields[key] = value
    required = ("binary", "commit-hash", "commit-date", "host", "release")
    missing = [field for field in required if not fields.get(field)]
    if missing:
        raise SystemExit(
            "rustc verbose output is missing required genesis identity fields: "
            + ", ".join(missing)
        )
    return fields


def validate_pinned_genesis_toolchain(
    root: Path, rustc: str, host: str
) -> dict[str, object]:
    """Refuse to wrap a compiler other than the checked-in genesis root.

    A local-genesis adapter remains explicitly non-evidentiary, but even that
    one external compiler event must be reproducible.  In particular, a dated
    rustup channel name is not sufficient: adjacent nightly names and compiler
    commit dates differ by one day.  Bind all fields emitted by `rustc -Vv`.
    """
    roots_path = root / GENESIS_ROOTS_RELATIVE
    if roots_path.is_symlink() or not roots_path.is_file():
        raise SystemExit(f"missing regular genesis-root manifest: {roots_path}")
    try:
        document = json.loads(roots_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise SystemExit(f"cannot parse genesis-root manifest {roots_path}: {error}") from error
    if not isinstance(document, dict) or document.get("schema") != GENESIS_ROOT_SCHEMA:
        raise SystemExit(f"unsupported genesis-root manifest schema in {roots_path}")
    if (
        document.get("admission") != "external-bootstrap-root-only"
        or document.get("counts_as_trust_stage0_evidence") is not False
    ):
        raise SystemExit(
            f"genesis-root manifest must preserve its non-evidentiary admission in {roots_path}"
        )
    channel = document.get("channel_manifest")
    if not isinstance(channel, dict):
        raise SystemExit(f"genesis-root manifest has no channel identity in {roots_path}")
    channel_date = channel.get("date")
    channel_digest = channel.get("sha256")
    if (
        not isinstance(channel_date, str)
        or re.fullmatch(r"\d{4}-\d{2}-\d{2}", channel_date) is None
        or not isinstance(channel_digest, str)
        or re.fullmatch(r"[0-9a-f]{64}", channel_digest) is None
    ):
        raise SystemExit(f"genesis-root channel identity is malformed in {roots_path}")
    roots = document.get("roots")
    expected = roots.get(host) if isinstance(roots, dict) else None
    if not isinstance(expected, dict):
        raise SystemExit(
            f"no pinned external genesis root for host {host!r} in {roots_path}"
        )
    if (
        expected.get("rustup_toolchain") != f"nightly-{channel_date}"
        or not isinstance(expected.get("rustc_archive_sha256"), str)
        or re.fullmatch(r"[0-9a-f]{64}", expected["rustc_archive_sha256"]) is None
    ):
        raise SystemExit(f"genesis-root host pin is malformed for {host!r} in {roots_path}")
    observed = rustc_verbose_fields(rustc)
    comparisons = {
        "binary": "rustc",
        "release": expected.get("release"),
        "commit-hash": expected.get("commit_hash"),
        "commit-date": expected.get("commit_date"),
        "host": expected.get("host"),
    }
    mismatches = [
        f"{field}: expected {value!r}, observed {observed.get(field)!r}"
        for field, value in comparisons.items()
        if not isinstance(value, str) or not value or observed.get(field) != value
    ]
    if mismatches:
        raise SystemExit(
            "refusing unpinned genesis rustc; the adapter is an auditable external "
            "bootstrap root, not a bring-whatever compiler wrapper:\n  "
            + "\n  ".join(mismatches)
        )
    rustc_path = Path(rustc).resolve(strict=True)
    return {
        "manifest": str(GENESIS_ROOTS_RELATIVE),
        "channel_manifest": channel,
        "pin": expected,
        "observed": observed,
        "rustc_path": str(rustc_path),
        "rustc_sha256": sha256_file(rustc_path),
    }


def stage0_values(stage0_path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for raw_line in stage0_path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        values[key.strip()] = value.strip()
    return values


def host_triple_from_rustc(rustc: str) -> str:
    output = run_stdout([rustc, "--version", "--verbose"])
    for line in output.splitlines():
        if line.startswith("host: "):
            return line.split(":", 1)[1].strip()
    raise RuntimeError(f"could not determine host triple from {rustc}")


def tool_version(tool: str) -> str:
    try:
        return run_stdout([tool, "--version"]).splitlines()[0]
    except (FileNotFoundError, subprocess.CalledProcessError, IndexError):
        return "<unavailable>"


def tool_sysroot(rustc: str) -> Path:
    return Path(run_stdout([rustc, "--print", "sysroot"]).strip())


def find_tool(name: str, sysroot_bin: Path | None = None) -> str | None:
    if sysroot_bin is not None:
        suffix = ".exe" if os.name == "nt" else ""
        candidate = sysroot_bin / f"{name}{suffix}"
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate.resolve())
        return None
    return shutil.which(name)


def write_executable(path: Path, text: str) -> None:
    path.write_text(text, encoding="utf-8")
    path.chmod(0o755)


def wrapper_script(
    *,
    real: str,
    source_name: str,
    trust_name: str,
    argument_prefix: str | None = None,
    argument_marker: str | None = None,
    version_name: str | None = None,
    version_argument_prefix: str | None = None,
    argument_rename: tuple[str, str] | None = None,
) -> str:
    # The version rewrite lets bootstrap's normal stage0 version check see the
    # Trust public name while all non-version invocations go to the real tool.
    normalize_version_probe = version_name is not None
    version_name = version_name or trust_name
    # tippy-driver is also a rustc-compatible compiler program. Combined
    # verbose-version probes are a compiler metadata protocol used by Cargo
    # and ui_test, so only the two product-version flags are branded there.
    single_version_flags = (
        "--version|-V" if trust_name == "tippy-driver" else "--version|-V|-vV|-Vv"
    )
    version_args = "--version" if normalize_version_probe else '"$@"'
    version_command = (
        f'"$real" {shlex.quote(version_argument_prefix)} {version_args}'
        if version_argument_prefix
        else f'"$real" {version_args}'
    )
    rename_case = ""
    if argument_rename is not None:
        old_arg, new_arg = argument_rename
        rename_case = (
            f"        {shlex.quote(old_arg)}) "
            f'set -- "$@" {shlex.quote(new_arg)}; continue ;;\n'
        )
    return f"""#!/bin/sh
real={shlex.quote(real)}
{f'if [ "${{1-}}" = {shlex.quote(argument_marker)} ]; then shift; fi' if argument_marker else ''}
rewrite_version() {{
    trust_output=$({version_command})
    trust_status=$?
    printf '%s\n' "$trust_output" | command -p sed -e '1s/^{source_name} /{version_name} /' -e 's/^binary: .*/binary: {trust_name}/'
    return "$trust_status"
}}
if [ "$#" -eq 1 ]; then
    case "$1" in
        {single_version_flags})
            rewrite_version "$@"
            exit $?
            ;;
    esac
fi
if [ "$#" -eq 2 ] && {{ [ "$1" = "--version" ] && [ "$2" = "--verbose" ]; }}; then
    rewrite_version "$@"
    exit $?
fi
if [ "$#" -eq 2 ] && {{ [ "$1" = "--verbose" ] && [ "$2" = "--version" ]; }}; then
    rewrite_version "$@"
    exit $?
fi
# Genesis stage0 wraps a stock rustc that cannot parse Trust-only -Z options
# (the `trust-*` family). Strip exactly that namespace so
# unrelated flags whose values merely contain the word "trust" survive.
pending_z=0
for arg do
    shift
    if [ "$pending_z" -eq 1 ]; then
        pending_z=0
        case "$arg" in
            trust-*) continue ;;
            *) set -- "$@" "-Z" "$arg"; continue ;;
        esac
    fi
    case "$arg" in
{rename_case.rstrip()}
        -Z) pending_z=1 ;;
        -Ztrust-verify=off|-Ztrust-*) ;;
        *) set -- "$@" "$arg" ;;
    esac
done
[ "$pending_z" -eq 1 ] && set -- "$@" "-Z"
{f'exec "$real" {shlex.quote(argument_prefix)} "$@"' if argument_prefix else 'exec "$real" "$@"'}
"""


def stub_script(*, name: str, message: str) -> str:
    return f"""#!/bin/sh
if [ "$#" -eq 1 ] && {{ [ "$1" = "--version" ] || [ "$1" = "-V" ]; }}; then
    printf '%s\\n' '{name} local-genesis-adapter'
    exit 0
fi
printf '%s\\n' '{message}; build a real Trust stage0 artifact before invoking {name}' >&2
exit 127
"""


def host_from_platform() -> str:
    machine = platform.machine().lower()
    system = platform.system().lower()
    arch = "aarch64" if machine in {"arm64", "aarch64"} else machine
    if system == "darwin":
        return f"{arch}-apple-darwin"
    if system == "linux":
        return f"{arch}-unknown-linux-gnu"
    if system == "windows":
        # This POSIX adapter emits #!/bin/sh wrappers + os.symlink, neither of
        # which works natively on Windows. Windows has a dedicated native genesis.
        raise RuntimeError(
            "this POSIX genesis adapter does not run on Windows; use the native "
            "Windows genesis instead: `py -3 scripts/win-genesis/win_genesis.py` "
            "(see scripts/win-genesis/README.md)"
        )
    raise RuntimeError(f"unsupported host platform for default triple: {system}/{machine}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=repo_root())
    parser.add_argument("--out", type=Path)
    parser.add_argument("--host", default=None)
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo_root.resolve()
    values = stage0_values(root / "src" / "stage0")
    rustc_frontend = find_tool("rustc")
    if rustc_frontend is None:
        raise SystemExit("rustc must be on PATH to create a genesis adapter")
    inherited_sysroot = tool_sysroot(rustc_frontend).resolve()
    sysroot_bin = inherited_sysroot / "bin"
    # A rustup proxy is mutable: changing the default after adapter creation
    # would silently change the compiler it executes.  Resolve every available
    # source tool inside the selected sysroot and write those exact paths into
    # the wrappers instead.
    rustc = find_tool("rustc", sysroot_bin)
    cargo = find_tool("cargo", sysroot_bin)
    if rustc is None or cargo is None:
        raise SystemExit(
            f"selected rustc sysroot must contain executable rustc and cargo: {sysroot_bin}"
        )

    host = args.host or host_triple_from_rustc(rustc) or host_from_platform()
    genesis_root = validate_pinned_genesis_toolchain(root, rustc, host)
    # Default OUTSIDE bootstrap.py's managed bin_root (build/<host>/stage0):
    # download_toolchain() wipes that root on any stage0 pin-date advance,
    # which would delete this adapter mid-flow.
    out = args.out.resolve() if args.out else root / "build" / host / "genesis-stage0"
    bin_dir = out / "bin"
    libexec_dir = out / "libexec"
    if out.exists() and not args.force:
        raise SystemExit(f"{out} already exists; pass --force to replace it")
    if out.exists():
        shutil.rmtree(out)
    bin_dir.mkdir(parents=True)
    libexec_dir.mkdir(parents=True)
    inherited_lib = inherited_sysroot / "lib"
    if not inherited_lib.is_dir():
        raise SystemExit(f"inherited rustc sysroot has no lib directory: {inherited_lib}")
    # Link the inherited rustc sysroot lib/ into the genesis stage0. A plain
    # os.symlink needs SeCreateSymbolicLink privilege on Windows (WinError 1314
    # without admin / Developer Mode), so use a directory JUNCTION there —
    # privilege-free and transparent to the toolchain's file access. Unix keeps
    # the symlink.
    if os.name == "nt":
        subprocess.run(
            ["cmd", "/c", "mklink", "/J", str(out / "lib"), str(inherited_lib)],
            check=True,
            stdout=subprocess.DEVNULL,
        )
    else:
        os.symlink(inherited_lib, out / "lib", target_is_directory=True)

    sources: dict[str, str | None] = {}
    for trust_name, (source_program, source_name) in WRAPPER_SOURCES.items():
        real = find_tool(source_program, sysroot_bin)
        sources[trust_name] = real
        if real is None:
            write_executable(
                bin_dir / trust_name,
                stub_script(
                    name=trust_name,
                    message=f"{source_program} was not found in PATH",
                ),
            )
        else:
            write_executable(
                bin_dir / trust_name,
                wrapper_script(
                    real=real,
                    source_name=source_name,
                    trust_name=trust_name,
                    argument_prefix=WRAPPER_ARG_PREFIXES.get(trust_name),
                    argument_marker=WRAPPER_ARG_MARKERS.get(trust_name),
                    version_name=TIPPY_VERSION_NAMES.get(trust_name),
                    version_argument_prefix=TIPPY_VERSION_ARG_PREFIXES.get(trust_name),
                    argument_rename=WRAPPER_ARG_RENAMES.get(trust_name),
                ),
            )

    for name, message in STUB_BINS.items():
        sources[name] = None
        write_executable(bin_dir / name, stub_script(name=name, message=message))
    for name, message in STUB_LIBEXEC_BINS.items():
        sources[name] = None
        write_executable(libexec_dir / name, stub_script(name=name, message=message))

    for forbidden in FORBIDDEN_BINS:
        forbidden_path = bin_dir / forbidden
        if os.path.lexists(forbidden_path):
            forbidden_path.unlink()
    for forbidden in FORBIDDEN_LIBEXEC_BINS:
        forbidden_path = libexec_dir / forbidden
        if os.path.lexists(forbidden_path):
            forbidden_path.unlink()

    stamp = values.get("compiler_date")
    if not stamp:
        raise SystemExit("src/stage0 does not contain compiler_date")
    # Bootstrap's BuildStamp::with_prefix("trustc") looks for `.trustc-stamp`
    # in the stage0 root for the "is the downloaded stage0 still current?"
    # check. Writing `.rustc-stamp` (the upstream-Rust name) leaves the stamp
    # invisible to bootstrap, which then wipes the genesis adapter and tries to
    # download. Write both names so the adapter satisfies Trust's check while
    # keeping the inherited filename for tooling that reads it.
    (out / ".trustc-stamp").write_text(stamp, encoding="utf-8")
    (out / ".rustc-stamp").write_text(stamp, encoding="utf-8")

    missing_surface = [
        str(path)
        for path in [*(bin_dir / name for name in REQUIRED_BINS), *(libexec_dir / name for name in REQUIRED_LIBEXEC_BINS)]
        if not path.exists()
    ]
    if missing_surface:
        raise SystemExit("failed to create required stage0 surface: " + ", ".join(missing_surface))

    manifest = {
        "schema": SCHEMA,
        "admission": "local-genesis-only",
        "public_upload": False,
        "counts_as_trust_stage0_evidence": False,
        "repo_root": str(root),
        "stage0_root": str(out),
        "host": host,
        "stamp": stamp,
        "compiler_version_target": values.get("compiler_version"),
        "genesis_root": genesis_root,
        "source_tools": {
            "rustc": rustc,
            "rustc_version": tool_version(rustc),
            "rustc_sysroot": str(inherited_sysroot),
            "cargo": cargo,
            "cargo_version": tool_version(cargo),
        },
        "generated_bins": {name: str(bin_dir / name) for name in REQUIRED_BINS},
        "generated_libexec_bins": {
            name: str(libexec_dir / name) for name in REQUIRED_LIBEXEC_BINS
        },
        "wrapper_sources": sources,
        "warnings": [
            "This adapter exists only to bootstrap a first local Trust build.",
            "Do not use this directory as release evidence or admitted stage0 lineage.",
            "Materialize real Trust archives from the resulting x dist output and admit those separately.",
        ],
    }
    manifest_path = out / "trust-local-genesis-stage0.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if args.json:
        print(json.dumps(manifest, indent=2, sort_keys=True))
    else:
        print(f"local genesis stage0 adapter: {out}")
        print(f"manifest: {manifest_path}")
        print("next: ./x.py build --stage 1 compiler/rustc library/std")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
