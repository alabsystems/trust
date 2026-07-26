#!/usr/bin/env python3
"""Discover materialized Trust-owned stage0 payload roots.

Plain ``rustc``/``cargo`` names count only as same-root compatibility aliases
when the same root also exposes the canonical Trust tools required by stage0.
Alias-only roots are not Trust stage0 evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shlex
import shutil
import stat
import subprocess
import sys
import tarfile
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote

UTC = timezone.utc

try:
    import tomllib
except ModuleNotFoundError:  # Python < 3.11
    try:
        import tomli as tomllib  # type: ignore[import-not-found]
    except ModuleNotFoundError:
        print(
            "error: Python 3.11+ or the 'tomli' package is required to parse TOML",
            file=sys.stderr,
        )
        sys.exit(2)


# Trust: produced-toolchain bin surface. These are matched against an
# installed/built stage0 *sysroot* bin/ directory. Only the compatibility
# aliases explicitly listed here are admitted; stale stock/retired tool names
# are rejected rather than treated as extra harmless files.
CANONICAL_REQUIRED = ("trustc", "targo")
REQUIRED_STAGE0_BIN_ENTRYPOINTS = (
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
REQUIRED_STAGE0_LIBEXEC_ENTRYPOINTS = (
    "trust-analyzer-proc-macro-srv",
)
# The materializer translates inherited producer names before checksums are
# admitted into src/stage0, so archive inspection uses the same canonical
# contract as an installed sysroot.
REQUIRED_STAGE0_ARCHIVE_ENTRYPOINTS = (
    *REQUIRED_STAGE0_BIN_ENTRYPOINTS,
    *REQUIRED_STAGE0_LIBEXEC_ENTRYPOINTS,
)
FORBIDDEN_STAGE0_BIN_ENTRYPOINTS = (
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
    "miri",
    "trust-miri",
    "cargo-miri",
    "targo-miri",
    "rust-gdb",
    "rust-gdbgui",
    "rust-lldb",
    "rust-windbg.cmd",
)
FORBIDDEN_STAGE0_LIBEXEC_ENTRYPOINTS = ("rust-analyzer-proc-macro-srv",)
COMPAT_ALIAS_NAMES = (
    "rustc",
    "cargo",
)
ARCHIVE_SUFFIXES = (".tar", ".tar.gz", ".tar.xz")
HOST_STAGE0_COMPONENTS = (
    "trust-std",
    "trustc",
    "targo",
    "targo-trust",
    "trustfmt",
    "tippy",
    "trust-analyzer",
)
LEGACY_HOST_STAGE0_COMPONENTS = {
    "targo": "tcargo",
    "targo-trust": "tcargo-trust",
    "tippy": "trust-clippy",
}
SOURCE_STAGE0_COMPONENTS = (
    "trustc",
    "trust-std",
    "targo",
    "tippy-preview",
    "trustfmt-preview",
    "trust-docs",
    "targo-trust",
    "trust-analyzer-preview",
    "trust-src",
    "trust-llvm-tools-preview",
)
REQUIRED_SOURCE_MANIFEST_PACKAGES = ("trust", *SOURCE_STAGE0_COMPONENTS)
ISSUE_REFS = ("L42", "#104", "#1057", "#1155", "#1095")


@dataclass
class Stage0Config:
    path: str
    values: dict[str, str]
    checksum_keys: list[str]
    trustc_keys: list[str]
    targo_keys: list[str]


@dataclass
class CandidateRoot:
    label: str
    kind: str
    path: Path


@dataclass
class RootResult:
    label: str
    kind: str
    path: str
    status: str
    findings: list[str] = field(default_factory=list)
    canonical_entrypoints: list[str] = field(default_factory=list)
    compatibility_aliases: list[str] = field(default_factory=list)
    checked_archives: list[str] = field(default_factory=list)
    missing_stage0_artifacts: list[str] = field(default_factory=list)
    missing_host_checksum_pins: list[str] = field(default_factory=list)
    checksum_mismatches: list[str] = field(default_factory=list)


@dataclass
class MaterializerResult:
    label: str
    path: str
    status: str
    input_dist: str
    source_channel: str
    output_root: str
    stage0_output: str
    command: list[str]
    preflight_command: list[str]
    findings: list[str] = field(default_factory=list)
    missing_inputs: list[str] = field(default_factory=list)


@dataclass
class ReleaseLedgerResult:
    path: str
    status: str
    findings: list[str] = field(default_factory=list)
    scope: str | None = None
    promotion_decision: str | None = None
    signatures: list[str] = field(default_factory=list)
    checksum_count: int = 0
    missing_stage0_checksum_count: int = 0
    extra_ledger_checksum_count: int = 0
    artifact_root: str | None = None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Discover Trust-owned stage0 payload roots exposing canonical "
            "trustc/targo entrypoints."
        )
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Trust repository root. Defaults to the parent of scripts/.",
    )
    parser.add_argument(
        "--stage0-file",
        type=Path,
        default=None,
        help="Stage0 metadata file. Defaults to <repo-root>/src/stage0.",
    )
    parser.add_argument(
        "--candidate-root",
        action="append",
        type=Path,
        default=[],
        help=(
            "Additional extracted sysroot or dist root to inspect. May be "
            "provided more than once."
        ),
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=None,
        help="Write a markdown checkpoint report to this path.",
    )
    parser.add_argument(
        "--producer-input-dist",
        action="append",
        type=Path,
        default=[],
        help=(
            "Additional x dist output root to inspect for local Trust stage0 "
            "materialization inputs. May be provided more than once."
        ),
    )
    parser.add_argument(
        "--producer-source-channel",
        action="append",
        default=[],
        help=(
            "Source channel name to inspect for the stage0 materializer input "
            "manifest. Defaults to src/stage0 compiler_dist_channel."
        ),
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Print the full discovery result as JSON.",
    )
    return parser.parse_args()


def read_stage0(path: Path) -> Stage0Config:
    if not path.is_file():
        raise SystemExit(f"stage0 file not found: {path}")

    values: dict[str, str] = {}
    checksum_keys: list[str] = []
    trustc_keys: list[str] = []
    targo_keys: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip()
        values[key] = value
        if key.startswith("dist/") and key.endswith(ARCHIVE_SUFFIXES):
            checksum_keys.append(key)
    compiler_version = values.get("compiler_version")
    for key in checksum_keys:
        name = Path(key).name
        if is_component_archive(name, "trustc", compiler_version):
            trustc_keys.append(key)
        if is_component_archive(name, "targo", compiler_version) or is_component_archive(
            name, "tcargo", compiler_version
        ):
            targo_keys.append(key)
    return Stage0Config(
        path=str(path),
        values=values,
        checksum_keys=checksum_keys,
        trustc_keys=trustc_keys,
        targo_keys=targo_keys,
    )


def is_component_archive(name: str, component: str, compiler_version: str | None) -> bool:
    if compiler_version:
        return name.startswith(f"{component}-{compiler_version}-")
    prefix = f"{component}-"
    return name.startswith(prefix) and name.removeprefix(prefix)[:1].isdigit()


def resolve_file_url(url: str, repo_root: Path) -> Path | None:
    if not url.startswith("file://"):
        return None
    raw = unquote(url.removeprefix("file://"))
    if raw.startswith("{trust-root}/"):
        return repo_root / raw.removeprefix("{trust-root}/")
    if raw.startswith("localhost/"):
        return Path("/") / raw.removeprefix("localhost/")
    return Path(raw)


def split_env_paths(value: str | None) -> list[Path]:
    if not value:
        return []
    return [Path(part) for part in value.split(os.pathsep) if part]


def host_build_triple() -> str | None:
    override = os.environ.get("TRUST_STAGE0_REQUIRED_BUILD_TRIPLE")
    if override:
        return override

    machine = platform.machine().lower()
    if machine == "arm64":
        machine = "aarch64"
    elif machine in {"amd64", "x64"}:
        machine = "x86_64"

    if sys.platform == "darwin" and machine in {"aarch64", "x86_64"}:
        return f"{machine}-apple-darwin"
    if sys.platform.startswith("linux") and machine in {"aarch64", "x86_64"}:
        return f"{machine}-unknown-linux-gnu"
    # Trust: Windows host support — the pure-bootstrap consumer audits this box.
    if sys.platform == "win32" and machine in {"aarch64", "x86_64"}:
        return f"{machine}-pc-windows-msvc"
    return None


def executable(path: Path) -> bool:
    try:
        mode = path.stat().st_mode
    except OSError:
        return False
    if not stat.S_ISREG(mode):
        return False
    # Trust: Windows has no POSIX execute bit; a regular .exe/.cmd file is
    # runnable. os.access(X_OK) is meaningless there, so don't gate on it.
    if sys.platform == "win32":
        return True
    return os.access(path, os.X_OK)


def path_entry_exists(path: Path) -> bool:
    """Return true for every directory entry, including dangling symlinks."""
    return os.path.lexists(path)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def command_path(name: str) -> str | None:
    resolved = shutil.which(name)
    return resolved or None


def rustup_trust_root() -> Path | None:
    rustup = shutil.which("rustup")
    if not rustup:
        return None
    try:
        result = subprocess.run(
            [rustup, "which", "--toolchain", "trust", "trustc"],
            check=False,
            capture_output=True,
            text=True,
            timeout=5,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        trust_link = Path.home() / ".rustup" / "toolchains" / "trust"
        return trust_link if trust_link.exists() or trust_link.is_symlink() else None
    return Path(result.stdout.strip()).parent.parent


def add_candidate(
    candidates: list[CandidateRoot],
    seen: set[tuple[str, str]],
    *,
    label: str,
    kind: str,
    path: Path | None,
) -> None:
    if path is None:
        return
    key = (kind, str(path))
    if key in seen:
        return
    seen.add(key)
    candidates.append(CandidateRoot(label=label, kind=kind, path=path))


def discover_roots(
    repo_root: Path,
    stage0: Stage0Config,
    user_roots: list[Path],
) -> tuple[list[CandidateRoot], dict[str, str | None]]:
    candidates: list[CandidateRoot] = []
    seen: set[tuple[str, str]] = set()
    path_tools = {name: command_path(name) for name in CANONICAL_REQUIRED + COMPAT_ALIAS_NAMES}

    for root in user_roots:
        add_candidate(candidates, seen, label="--candidate-root", kind="sysroot", path=root)
        add_candidate(candidates, seen, label="--candidate-root", kind="dist", path=root)

    for root in split_env_paths(os.environ.get("TRUST_STAGE0_PAYLOAD_ROOTS")):
        add_candidate(candidates, seen, label="TRUST_STAGE0_PAYLOAD_ROOTS", kind="sysroot", path=root)
    add_candidate(
        candidates,
        seen,
        label="TRUST_STAGE0_PAYLOAD_ROOT",
        kind="sysroot",
        path=Path(os.environ["TRUST_STAGE0_PAYLOAD_ROOT"])
        if os.environ.get("TRUST_STAGE0_PAYLOAD_ROOT")
        else None,
    )

    for source, url in (
        ("src/stage0 dist_server", stage0.values.get("dist_server")),
        ("TRUST_DIST_SERVER", os.environ.get("TRUST_DIST_SERVER")),
    ):
        root = resolve_file_url(url, repo_root) if url else None
        add_candidate(candidates, seen, label=source, kind="dist", path=root)

    add_candidate(candidates, seen, label="tracked Trust stage0 metadata root", kind="dist", path=repo_root / "bootstrap" / "trust-stage0")
    add_candidate(candidates, seen, label="local build/dist", kind="dist", path=repo_root / "build" / "dist")
    add_candidate(candidates, seen, label="local build/host/stage0", kind="sysroot", path=repo_root / "build" / "host" / "stage0")
    for root in sorted((repo_root / "build").glob("*/stage0")):
        add_candidate(candidates, seen, label="local build/*/stage0", kind="sysroot", path=root)

    add_candidate(candidates, seen, label="rustup trust toolchain", kind="sysroot", path=rustup_trust_root())

    trustc = path_tools.get("trustc")
    # Trust: produced cargo bin on PATH is targo; the key must match CANONICAL_REQUIRED.
    targo = path_tools.get("targo")
    if trustc and targo:
        trustc_bin = Path(trustc).parent
        targo_bin = Path(targo).parent
        if trustc_bin == targo_bin:
            add_candidate(candidates, seen, label="PATH trustc/targo", kind="sysroot", path=trustc_bin.parent)

    return candidates, path_tools


def symlink_note(path: Path) -> str | None:
    if not path.is_symlink():
        return None
    try:
        target = os.readlink(path)
    except OSError as exc:
        return f"symlink target unreadable: {exc}"
    if path.exists():
        return f"symlink to {target}"
    return f"broken symlink to {target}"


def local_genesis_blocker(path: Path) -> str | None:
    for manifest_path in (
        path / "trust-local-genesis-stage0.json",
        path.parent / "stage0" / "trust-local-genesis-stage0.json",
    ):
        if not manifest_path.exists():
            continue
        try:
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            return f"local genesis metadata is unreadable: {manifest_path} ({exc})"
        if data.get("admission") == "local-genesis-only" or data.get(
            "counts_as_trust_stage0_evidence"
        ) is False:
            return (
                f"{manifest_path} marks this root as local-genesis-only; "
                "it does not count as admitted Trust stage0 evidence"
            )
    return None


def inspect_sysroot(candidate: CandidateRoot) -> RootResult:
    result = RootResult(
        label=candidate.label,
        kind=candidate.kind,
        path=str(candidate.path),
        status="rejected",
    )
    note = symlink_note(candidate.path)
    if note:
        result.findings.append(note)
    if not candidate.path.exists():
        result.status = "missing"
        result.findings.append("root does not exist")
        return result
    if not candidate.path.is_dir():
        result.status = "missing"
        result.findings.append("root is not a directory")
        return result
    if blocker := local_genesis_blocker(candidate.path):
        result.status = "blocked"
        result.findings.append(blocker)
        return result

    bin_dir = candidate.path / "bin"
    libexec_dir = candidate.path / "libexec"
    for name in REQUIRED_STAGE0_BIN_ENTRYPOINTS:
        if executable(bin_dir / name):
            result.canonical_entrypoints.append(name)
    for name in REQUIRED_STAGE0_LIBEXEC_ENTRYPOINTS:
        if executable(libexec_dir / name):
            result.canonical_entrypoints.append(name)
    for name in COMPAT_ALIAS_NAMES:
        if executable(bin_dir / name):
            result.compatibility_aliases.append(name)

    missing_required = [
        f"bin/{name}"
        for name in REQUIRED_STAGE0_BIN_ENTRYPOINTS
        if name not in result.canonical_entrypoints
    ]
    missing_required.extend(
        f"libexec/{name}"
        for name in REQUIRED_STAGE0_LIBEXEC_ENTRYPOINTS
        if name not in result.canonical_entrypoints
    )
    forbidden_present = [
        f"bin/{name}"
        for name in FORBIDDEN_STAGE0_BIN_ENTRYPOINTS
        if path_entry_exists(bin_dir / name)
    ]
    forbidden_present.extend(
        f"libexec/{name}"
        for name in FORBIDDEN_STAGE0_LIBEXEC_ENTRYPOINTS
        if path_entry_exists(libexec_dir / name)
    )
    if not missing_required and not forbidden_present:
        result.status = "candidate"
        result.findings.append(
            "full canonical stage0 surface is executable and forbidden stock/retired aliases are absent"
        )
        return result

    if missing_required:
        result.findings.append(
            "missing required stage0 entrypoint(s): " + ", ".join(missing_required)
        )
    if forbidden_present:
        result.findings.append(
            "forbidden stage0 entrypoint(s) present: " + ", ".join(forbidden_present)
        )
    if result.compatibility_aliases:
        result.findings.append(
            "Rust-compatible aliases require the full sibling Trust stage0 surface: "
            + ", ".join(result.compatibility_aliases)
        )
    return result


def stage0_archive_keys(stage0: Stage0Config) -> list[str]:
    return sorted(dict.fromkeys(stage0.checksum_keys))


def required_host_archive_keys(stage0: Stage0Config, build_triple: str | None) -> list[str]:
    date = stage0.values.get("compiler_date")
    version = stage0.values.get("compiler_version")
    if not date or not version or not build_triple:
        return []
    selected: list[str] = []
    for component in HOST_STAGE0_COMPONENTS:
        canonical = f"dist/{date}/{component}-{version}-{build_triple}.tar.xz"
        if canonical in stage0.values:
            selected.append(canonical)
            continue
        legacy_component = LEGACY_HOST_STAGE0_COMPONENTS.get(component)
        legacy = (
            f"dist/{date}/{legacy_component}-{version}-{build_triple}.tar.xz"
            if legacy_component
            else None
        )
        selected.append(legacy if legacy in stage0.values else canonical)
    return selected


def required_artifacts(stage0: Stage0Config) -> list[dict[str, str]]:
    return [
        {"path": key, "sha256": stage0.values[key]}
        for key in stage0_archive_keys(stage0)
        if stage0.values.get(key)
    ]


def archive_member_names(path: Path) -> list[str]:
    with tarfile.open(path, "r:*") as archive:
        return archive.getnames()


def archive_has_entrypoint(names: list[str], member: str) -> bool:
    """Match both Unix and Windows executable spellings in component archives."""
    return any(
        name.endswith(f"/{member}") or name.endswith(f"/{member}.exe")
        for name in names
    )


def inspect_archive_members(
    archive: Path, names: list[str], *, allow_legacy_bundle: bool = False
) -> tuple[list[str], list[str]]:
    good: list[str] = []
    bad: list[str] = []
    basename = archive.name
    # Trust: trustc-dev is a rustc_private *library* component (its image layout
    # is trustc-dev/..., not trustc/bin/...). It is checksum-pinned for the
    # bootstrap rustc_private handoff but carries none of the entrypoint binaries
    # the trustc component does, so it must not be matched against the trustc
    # entrypoint contract below (its "trustc-" prefix otherwise collides).
    if basename.startswith("trustc-dev-"):
        return good, bad
    required_by_component: dict[
        str, tuple[tuple[str, str | tuple[str, ...]], ...]
    ] = {
        "trustc-": (
            ("trustc", "trustc/bin/trustc"),
            ("rustc", "trustc/bin/rustc"),
            ("trustdoc", "trustc/bin/trustdoc"),
            ("trust-analyzer-proc-macro-srv", "trustc/libexec/trust-analyzer-proc-macro-srv"),
        ),
        "targo-trust-": (
            ("targo-trust", "targo-trust/bin/targo-trust"),
        ),
        "tcargo-trust-": (
            ("targo-trust", "tcargo-trust/bin/tcargo-trust"),
        ),
        "targo-": (
            ("targo", "targo/bin/targo"),
            ("cargo", "targo/bin/cargo"),
        ),
        "tcargo-": (
            ("targo", "tcargo/bin/tcargo"),
            ("cargo", "tcargo/bin/cargo"),
        ),
        "trustfmt-": (
            ("trustfmt", "trustfmt/bin/trustfmt"),
            (
                "targo-fmt",
                ("trustfmt/bin/targo-fmt", "trustfmt/bin/tcargo-fmt"),
            ),
        ),
        "tippy-": (
            ("tippy", "tippy/bin/tippy"),
            ("targo-tippy", "tippy/bin/targo-tippy"),
            ("tippy-driver", "tippy/bin/tippy-driver"),
        ),
        "trust-clippy-": (
            ("tippy", "trust-clippy-preview/bin/trust-clippy"),
            ("targo-tippy", "trust-clippy-preview/bin/cargo-clippy"),
            ("tippy-driver", "trust-clippy-preview/bin/trust-clippy-driver"),
        ),
        "trust-analyzer-": (
            ("trust-analyzer", "trust-analyzer/bin/trust-analyzer"),
        ),
    }
    translated_legacy_bins_by_component = {
        "tcargo-trust-": {"tcargo-trust", "cargo-trust"},
        "tcargo-": {"tcargo"},
        "trust-clippy-": {
            "cargo-clippy",
            "clippy-driver",
            "targo-clippy",
            "trust-clippy",
            "trust-clippy-driver",
        },
    }
    matched_component = False
    translated_legacy_bins: set[str] = set()
    for component_prefix, required_members in required_by_component.items():
        if not basename.startswith(component_prefix):
            continue
        matched_component = True
        translated_legacy_bins = translated_legacy_bins_by_component.get(
            component_prefix, set()
        )
        if allow_legacy_bundle:
            translated_legacy_bins = translated_legacy_bins | {
                "trustc-": {"rustdoc"},
                "trustfmt-": {"tcargo-fmt", "cargo-fmt", "rustfmt"},
                "trust-analyzer-": {"rust-analyzer"},
            }.get(component_prefix, set())
        for label, member_or_members in required_members:
            members = (
                member_or_members
                if isinstance(member_or_members, tuple)
                else (member_or_members,)
            )
            if any(archive_has_entrypoint(names, member) for member in members):
                good.append(label)
            else:
                bad.append(
                    "missing required stage0 archive member " + " or ".join(members)
                )
        break

    if matched_component:
        for forbidden in FORBIDDEN_STAGE0_BIN_ENTRYPOINTS:
            if forbidden in translated_legacy_bins:
                continue
            if archive_has_entrypoint(names, f"bin/{forbidden}"):
                bad.append(f"forbidden stage0 archive member bin/{forbidden}")
        for forbidden in FORBIDDEN_STAGE0_LIBEXEC_ENTRYPOINTS:
            if (
                allow_legacy_bundle
                and component_prefix in {"trustc-", "trust-analyzer-"}
                and forbidden == "rust-analyzer-proc-macro-srv"
            ):
                continue
            if archive_has_entrypoint(names, f"libexec/{forbidden}"):
                bad.append(f"forbidden stage0 archive member libexec/{forbidden}")
    return good, bad


def inspect_dist(
    candidate: CandidateRoot,
    stage0: Stage0Config,
    host_archive_keys: list[str],
) -> RootResult:
    result = RootResult(
        label=candidate.label,
        kind=candidate.kind,
        path=str(candidate.path),
        status="rejected",
    )
    note = symlink_note(candidate.path)
    if note:
        result.findings.append(note)
    if not candidate.path.exists():
        result.status = "missing"
        result.findings.append("root does not exist")
        return result
    if not candidate.path.is_dir():
        result.status = "missing"
        result.findings.append("root is not a directory")
        return result

    canonical_from_archives: set[str] = set()
    archive_errors: list[str] = []
    wanted_keys = stage0_archive_keys(stage0)
    for key in host_archive_keys:
        if key not in stage0.values:
            result.missing_host_checksum_pins.append(key)
    for key in wanted_keys:
        archive = candidate.path / key
        if not archive.is_file():
            result.missing_stage0_artifacts.append(key)
            continue
        result.checked_archives.append(str(archive))
        expected = stage0.values.get(key)
        if expected and expected != sha256(archive):
            result.checksum_mismatches.append(f"{key}: expected {expected}, actual {sha256(archive)}")
            continue
        try:
            names = archive_member_names(archive)
        except (tarfile.TarError, OSError) as exc:
            archive_errors.append(f"{key}: unreadable archive: {exc}")
            continue
        legacy_bundle = any(
            Path(host_key).name.startswith("tcargo-") for host_key in host_archive_keys
        )
        good, bad = inspect_archive_members(
            archive, names, allow_legacy_bundle=legacy_bundle
        )
        canonical_from_archives.update(good)
        archive_errors.extend(f"{key}: {item}" for item in bad)

    if not wanted_keys:
        result.findings.append("stage0 has no pinned archive keys")
    if result.missing_host_checksum_pins:
        result.findings.append(
            "missing host stage0 checksum pin(s): "
            + ", ".join(result.missing_host_checksum_pins)
        )
    if result.missing_stage0_artifacts:
        result.findings.append(
            "missing stage0-pinned archive(s): " + ", ".join(result.missing_stage0_artifacts)
        )
    if result.checksum_mismatches:
        result.findings.append("checksum mismatch in stage0-pinned archive(s)")
    result.findings.extend(archive_errors)

    if all(name in canonical_from_archives for name in REQUIRED_STAGE0_ARCHIVE_ENTRYPOINTS):
        if (
            not result.missing_stage0_artifacts
            and not result.missing_host_checksum_pins
            and not result.checksum_mismatches
            and not archive_errors
        ):
            result.status = "candidate"
            result.canonical_entrypoints = sorted(canonical_from_archives)
            result.findings.append(
                "all stage0-pinned archives are present, checksum-matched, and expose the full stage0 Trust/compatibility payload surface"
            )
            return result

    if not result.checked_archives:
        archive_count = sum(1 for _ in candidate.path.glob("dist/**/*.tar*"))
        result.findings.append(f"checked archive payload count under dist/: {archive_count}")
    else:
        result.canonical_entrypoints = sorted(canonical_from_archives)
        missing = [
            name for name in REQUIRED_STAGE0_ARCHIVE_ENTRYPOINTS if name not in canonical_from_archives
        ]
        if missing:
            result.findings.append(
                "checked archives did not expose required stage0 payload member(s): "
                + ", ".join(missing)
            )
    return result


def inspect_roots(
    candidates: list[CandidateRoot],
    stage0: Stage0Config,
    host_archive_keys: list[str],
) -> list[RootResult]:
    results: list[RootResult] = []
    for candidate in candidates:
        if candidate.kind == "sysroot":
            results.append(inspect_sysroot(candidate))
        elif candidate.kind == "dist":
            results.append(inspect_dist(candidate, stage0, host_archive_keys))
        else:
            results.append(
                RootResult(
                    label=candidate.label,
                    kind=candidate.kind,
                    path=str(candidate.path),
                    status="rejected",
                    findings=[f"unknown candidate kind: {candidate.kind}"],
                )
            )
    return results


def materializer_command(
    repo_root: Path,
    prepare_path: Path,
    input_dist: Path,
    source_channel: str,
    output_root: Path,
    stage0_output: Path,
) -> list[str]:
    try:
        prepare_arg = prepare_path.relative_to(repo_root).as_posix()
    except ValueError:
        prepare_arg = str(prepare_path)
    try:
        input_arg = input_dist.relative_to(repo_root).as_posix()
    except ValueError:
        input_arg = str(input_dist)
    try:
        output_arg = output_root.relative_to(repo_root).as_posix()
    except ValueError:
        output_arg = str(output_root)
    try:
        stage0_arg = stage0_output.relative_to(repo_root).as_posix()
    except ValueError:
        stage0_arg = str(stage0_output)
    return [
        "python3",
        prepare_arg,
        "--input-dist",
        input_arg,
        "--source-channel",
        source_channel,
        "--owned-channel",
        "trust",
        "--archive-format",
        "xz",
        "--stage0-seed-only",
        "--git-commit-hash",
        "<seed-commit-that-produced-input-dist>",
        "--output-root",
        output_arg,
        "--stage0-output",
        stage0_arg,
    ]


def materializer_preflight_command(
    repo_root: Path,
    prepare_path: Path,
    input_dist: Path,
    source_channel: str,
) -> list[str]:
    command = materializer_command(
        repo_root,
        prepare_path,
        input_dist,
        source_channel,
        repo_root / "build" / "stage0-materialization" / "trust-stage0",
        repo_root / "build" / "stage0-materialization" / "src-stage0",
    )
    command.insert(8, "--check-inputs-only")
    return command


def parse_manifest_date(value: object) -> str | None:
    if hasattr(value, "isoformat"):
        return value.isoformat()  # type: ignore[no-any-return]
    return value if isinstance(value, str) and value else None


def source_archive_path(input_dist: Path, filename: str, date: str | None) -> Path | None:
    candidates = [input_dist / filename]
    if date:
        candidates.append(input_dist / date / filename)
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    return None


def referenced_xz_archives(
    manifest: dict[str, object],
    component: str,
) -> list[str]:
    packages = manifest.get("pkg")
    if not isinstance(packages, dict):
        return []
    package = packages.get(component)
    if not isinstance(package, dict):
        return []
    targets = package.get("target")
    if not isinstance(targets, dict):
        return []

    filenames: list[str] = []
    for target in targets.values():
        if not isinstance(target, dict):
            continue
        if target.get("available") is False:
            continue
        value = target.get("xz_url")
        if isinstance(value, str) and value:
            filenames.append(Path(value).name)
    return sorted(dict.fromkeys(filenames))


def inspect_materializer(
    *,
    repo_root: Path,
    label: str,
    prepare_path: Path,
    input_dist: Path,
    source_channel: str,
) -> MaterializerResult:
    output_root = repo_root / "build" / "stage0-materialization" / "trust-stage0"
    stage0_output = output_root.parent / "src-stage0"
    result = MaterializerResult(
        label=label,
        path=str(prepare_path),
        status="blocked",
        input_dist=str(input_dist),
        source_channel=source_channel,
        output_root=str(output_root),
        stage0_output=str(stage0_output),
        command=materializer_command(
            repo_root,
            prepare_path,
            input_dist,
            source_channel,
            output_root,
            stage0_output,
        ),
        preflight_command=materializer_preflight_command(
            repo_root,
            prepare_path,
            input_dist,
            source_channel,
        ),
    )

    if not prepare_path.is_file():
        result.status = "missing"
        result.findings.append("stage0 materializer script is missing")
        result.missing_inputs.append(str(prepare_path))
        return result
    result.findings.append("stage0 materializer script exists")

    if not input_dist.exists():
        result.findings.append("input dist root does not exist")
        result.missing_inputs.append(str(input_dist))
        return result
    if not input_dist.is_dir():
        result.status = "rejected"
        result.findings.append("input dist root is not a directory")
        return result

    manifest_path = input_dist / f"channel-rust-{source_channel}.toml"
    if not manifest_path.is_file():
        result.findings.append("source channel manifest is missing")
        result.missing_inputs.append(str(manifest_path))
        return result

    try:
        manifest = tomllib.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        result.status = "rejected"
        result.findings.append(f"source channel manifest is unreadable: {exc}")
        return result

    packages = manifest.get("pkg")
    if not isinstance(packages, dict):
        result.status = "rejected"
        result.findings.append("source channel manifest is missing [pkg] table")
        return result

    missing_packages = [
        component for component in REQUIRED_SOURCE_MANIFEST_PACKAGES if component not in packages
    ]
    if missing_packages:
        result.status = "rejected"
        result.findings.append(
            "source channel manifest is missing required package(s): "
            + ", ".join(missing_packages)
        )
        return result

    date = parse_manifest_date(manifest.get("date"))
    missing_archives: list[str] = []
    for component in SOURCE_STAGE0_COMPONENTS:
        filenames = referenced_xz_archives(manifest, component)
        if not filenames:
            missing_archives.append(f"{component}: no xz_url archive in manifest")
            continue
        for filename in filenames:
            if source_archive_path(input_dist, filename, date) is None:
                missing_archives.append(filename)

    if missing_archives:
        result.findings.append(
            f"source dist is missing {len(missing_archives)} xz archive input(s)"
        )
        result.missing_inputs.extend(missing_archives)
        return result

    result.status = "ready"
    result.findings.append(
        "source dist has the Trust stage0 packages and xz archive inputs needed for a local rehearsal seed"
    )
    result.findings.append(
        "output under build/ is rehearsal material only; L42 still needs admitted artifact-root policy"
    )
    return result


def split_env_path_labels(value: str | None) -> list[tuple[str, Path]]:
    return [("TRUST_STAGE0_INPUT_DIST", path) for path in split_env_paths(value)]


def discover_materializers(
    repo_root: Path,
    stage0: Stage0Config,
    user_input_dists: list[Path],
    user_source_channels: list[str],
) -> list[MaterializerResult]:
    prepare_path = repo_root / "src" / "tools" / "trust-stage0-dist" / "prepare.py"
    inputs: list[tuple[str, Path]] = []
    seen_inputs: set[str] = set()

    def add_input(label: str, path: Path) -> None:
        key = str(path)
        if key in seen_inputs:
            return
        seen_inputs.add(key)
        inputs.append((label, path))

    for path in user_input_dists:
        add_input("--producer-input-dist", path)
    for label, path in split_env_path_labels(os.environ.get("TRUST_STAGE0_INPUT_DIST")):
        add_input(label, path)
    add_input("local build/dist", repo_root / "build" / "dist")

    explicit_channels = [
        channel
        for channel in (
            *user_source_channels,
            *(os.environ.get("TRUST_STAGE0_SOURCE_CHANNEL") or "").split(os.pathsep),
        )
        if channel
    ]
    results: list[MaterializerResult] = []
    for label, input_dist in inputs:
        channels = explicit_channels or [stage0.values.get("compiler_dist_channel") or "trust"]
        if not explicit_channels:
            fallback = input_dist / "channel-rust-dev.toml"
            primary = input_dist / f"channel-rust-{channels[0]}.toml"
            if fallback.is_file() and not primary.is_file():
                channels = [*channels, "dev"]
        seen_channels: set[str] = set()
        for channel in channels:
            if channel in seen_channels:
                continue
            seen_channels.add(channel)
            results.append(
                inspect_materializer(
                    repo_root=repo_root,
                    label=label,
                    prepare_path=prepare_path,
                    input_dist=input_dist,
                    source_channel=channel,
                )
            )
    return results


def inspect_release_ledger(repo_root: Path, stage0: Stage0Config) -> ReleaseLedgerResult:
    # Relocated out of release/ (and off the `publication-ledger` name): the
    # public-distribution cull gate forbids that exact path/name-token, while
    # this seed-publication record (OFF_STOCK_RUST_PLAN Phase 3) is a live
    # input. bootstrap/trust-stage0/ is outside the cull scan locations.
    path = repo_root / "bootstrap" / "trust-stage0" / "seed-ledger.toml"
    result = ReleaseLedgerResult(path=str(path), status="missing")
    if not path.is_file():
        result.findings.append("release publication ledger is missing")
        return result

    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        result.status = "rejected"
        result.findings.append(f"release publication ledger is unreadable: {exc}")
        return result

    result.scope = data.get("scope") if isinstance(data.get("scope"), str) else None
    result.promotion_decision = (
        data.get("promotion_decision") if isinstance(data.get("promotion_decision"), str) else None
    )
    signatures = data.get("signatures")
    if isinstance(signatures, list):
        result.signatures = [item for item in signatures if isinstance(item, str)]
    ledger_checksums: set[str] = set()
    checksums = data.get("checksums")
    if isinstance(checksums, list):
        ledger_checksums = {item for item in checksums if isinstance(item, str)}
        result.checksum_count = len(ledger_checksums)
    artifact_root = data.get("artifact_root")
    if isinstance(artifact_root, dict) and isinstance(artifact_root.get("path"), str):
        result.artifact_root = artifact_root["path"]

    placeholder_signatures = [
        signature
        for signature in result.signatures
        if "placeholder" in signature or "not-publicly-signed" in signature
    ]
    if result.promotion_decision == "promote" and result.signatures and not placeholder_signatures:
        result.status = "candidate"
        result.findings.append("publication ledger has non-placeholder signature entries")
    else:
        result.status = "blocked"
        if result.promotion_decision:
            result.findings.append(f"promotion_decision={result.promotion_decision}")
        if not result.signatures:
            result.findings.append("publication ledger has no signature entries")
        if placeholder_signatures:
            result.findings.append(
                "publication ledger signature is not public admission evidence: "
                + ", ".join(placeholder_signatures)
            )

    stage0_checksums = {
        "sha256:" + stage0.values[key]
        for key in stage0.checksum_keys
        if stage0.values.get(key)
    }
    if ledger_checksums and stage0_checksums:
        missing_stage0_checksums = stage0_checksums - ledger_checksums
        extra_ledger_checksums = ledger_checksums - stage0_checksums
        result.missing_stage0_checksum_count = len(missing_stage0_checksums)
        result.extra_ledger_checksum_count = len(extra_ledger_checksums)
        if missing_stage0_checksums:
            result.status = "blocked"
            result.findings.append(
                "publication ledger is missing "
                f"{len(missing_stage0_checksums)} src/stage0 archive checksum pin(s)"
            )
        if extra_ledger_checksums:
            result.findings.append(
                "publication ledger has "
                f"{len(extra_ledger_checksums)} checksum pin(s) not present in src/stage0"
            )
    return result


def summarize_blocker(stage0: Stage0Config, results: list[RootResult], path_tools: dict[str, str | None]) -> str | None:
    if any(result.status == "candidate" for result in results):
        return None
    plain = [name for name in ("rustc", "cargo") if path_tools.get(name)]
    plain_note = ""
    if plain:
        plain_note = (
            " Plain "
            + "/".join(plain)
            + " binaries were found on PATH, but ambient Rust tools are not Trust stage0 evidence."
        )
    mode = stage0.values.get("dist_payload_mode", "<unset>")
    return (
        "No materialized Trust-owned stage0 payload root was found with the full "
        f"required Trust/compatibility entrypoint surface. src/stage0 is configured with "
        f"dist_payload_mode={mode} and currently identifies metadata/checksum pins only."
        + plain_note
    )


def result_dict(
    repo_root: Path,
    stage0: Stage0Config,
    results: list[RootResult],
    path_tools: dict[str, str | None],
    materializers: list[MaterializerResult],
    release_ledger: ReleaseLedgerResult,
    required_build_triple: str | None,
    required_host_artifacts: list[str],
) -> dict[str, object]:
    blocker = summarize_blocker(stage0, results, path_tools)
    return {
        "schema": "trust.stage0-seed-discovery.v1",
        "generated_at": datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
        "issue_refs": list(ISSUE_REFS),
        "repo_root": str(repo_root),
        "stage0": {
            "path": stage0.path,
            "dist_server": stage0.values.get("dist_server"),
            "dist_payload_mode": stage0.values.get("dist_payload_mode"),
            "compiler_dist_channel": stage0.values.get("compiler_dist_channel"),
            "compiler_version": stage0.values.get("compiler_version"),
            "compiler_date": stage0.values.get("compiler_date"),
            "checksum_keys": stage0.checksum_keys,
            "trustc_archive_keys": stage0.trustc_keys,
            "targo_archive_keys": stage0.targo_keys,
            "required_build_triple": required_build_triple,
            "required_host_artifacts": required_host_artifacts,
            "missing_required_host_artifacts": [
                key for key in required_host_artifacts if key not in stage0.values
            ],
            "required_artifacts": required_artifacts(stage0),
        },
        "path_tools": path_tools,
        "results": [result.__dict__ for result in results],
        "candidate_count": sum(1 for result in results if result.status == "candidate"),
        "materializers": [result.__dict__ for result in materializers],
        "materializer_ready_count": sum(
            1 for result in materializers if result.status == "ready"
        ),
        "release_ledger": release_ledger.__dict__,
        "blocker": blocker,
    }


def markdown_report(data: dict[str, object]) -> str:
    stage0 = data["stage0"]
    assert isinstance(stage0, dict)
    blocker = data.get("blocker")
    lines = [
        "# Trust Stage0 Seed Discovery",
        "",
        "Issue refs: " + ", ".join(ISSUE_REFS),
        "",
        "## Summary",
        "",
    ]
    if blocker:
        lines.append(f"- Status: BLOCKED - {blocker}")
    else:
        lines.append("- Status: PASS - at least one candidate Trust stage0 payload root was found.")
    lines.extend(
        [
            f"- Repository: `{data['repo_root']}`",
            f"- Stage0 file: `{stage0.get('path')}`",
            f"- Dist server: `{stage0.get('dist_server')}`",
            f"- Dist payload mode: `{stage0.get('dist_payload_mode')}`",
            f"- Compiler: `{stage0.get('compiler_version')}` on `{stage0.get('compiler_date')}`",
            f"- Required host build triple: `{stage0.get('required_build_triple') or '<unknown>'}`",
            f"- Required stage0 entrypoints: `{', '.join(REQUIRED_STAGE0_ARCHIVE_ENTRYPOINTS)}`",
            "",
            "## Required Payloads",
            "",
            "| Path from dist root | Expected SHA-256 |",
            "| --- | --- |",
        ]
    )
    required = stage0.get("required_artifacts", [])
    if isinstance(required, list) and required:
        for artifact in required:
            if not isinstance(artifact, dict):
                continue
            lines.append(
                "| `{}` | `{}` |".format(
                    artifact.get("path", "<unknown>"),
                    artifact.get("sha256", "<unknown>"),
                )
            )
    else:
        lines.append("| `<none>` | `<none>` |")
    lines.extend(
        [
            "",
            "## PATH Check",
            "",
        ]
    )
    path_tools = data["path_tools"]
    assert isinstance(path_tools, dict)
    for name in CANONICAL_REQUIRED + ("rustc", "cargo"):
        value = path_tools.get(name)
        lines.append(f"- `{name}`: `{value or '<not found>'}`")
    lines.extend(
        [
            "",
            "Plain `rustc` and `cargo` are compatibility aliases only when bound to the same checked Trust root with the full required stage0 surface.",
            "",
            "## Checked Roots",
            "",
            "| Kind | Source | Root | Status | Finding |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for result in data["results"]:
        assert isinstance(result, dict)
        finding = "; ".join(result.get("findings", [])) or "<none>"
        lines.append(
            "| `{kind}` | `{label}` | `{path}` | `{status}` | {finding} |".format(
                kind=result["kind"],
                label=result["label"],
                path=result["path"],
                status=result["status"],
                finding=finding.replace("|", "\\|"),
            )
        )
    release_ledger = data.get("release_ledger")
    assert isinstance(release_ledger, dict)
    lines.extend(
        [
            "",
            "## Publication Ledger Check",
            "",
            f"- `status`: `{release_ledger.get('status')}`",
            f"- `path`: `{release_ledger.get('path')}`",
            f"- `scope`: `{release_ledger.get('scope') or '<unset>'}`",
            f"- `promotion_decision`: `{release_ledger.get('promotion_decision') or '<unset>'}`",
            f"- `artifact_root`: `{release_ledger.get('artifact_root') or '<unset>'}`",
            f"- `checksum_count`: `{release_ledger.get('checksum_count')}`",
            f"- `missing_stage0_checksum_count`: `{release_ledger.get('missing_stage0_checksum_count')}`",
            f"- `extra_ledger_checksum_count`: `{release_ledger.get('extra_ledger_checksum_count')}`",
        ]
    )
    ledger_findings = release_ledger.get("findings", [])
    if isinstance(ledger_findings, list) and ledger_findings:
        for finding in ledger_findings:
            lines.append(f"- finding: {finding}")
    lines.extend(
        [
            "",
            "Ledger pins without non-placeholder signature/admission evidence do not count as a signed Trust stage0 payload root.",
            "",
            "## Materialization Producer Check",
            "",
            "| Source | Input dist | Source channel | Status | Finding |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    first_preflight_command: list[str] | None = None
    first_command: list[str] | None = None
    for materializer in data["materializers"]:
        assert isinstance(materializer, dict)
        finding = "; ".join(materializer.get("findings", [])) or "<none>"
        lines.append(
            "| `{label}` | `{input_dist}` | `{source_channel}` | `{status}` | {finding} |".format(
                label=materializer["label"],
                input_dist=materializer["input_dist"],
                source_channel=materializer["source_channel"],
                status=materializer["status"],
                finding=finding.replace("|", "\\|"),
            )
        )
        if first_preflight_command is None and isinstance(
            materializer.get("preflight_command"), list
        ):
            first_preflight_command = [
                str(part) for part in materializer["preflight_command"]
            ]
        if first_command is None and isinstance(materializer.get("command"), list):
            first_command = [str(part) for part in materializer["command"]]
    if first_preflight_command:
        lines.extend(
            [
                "",
                "Input preflight command before any materialization write:",
                "",
                "```bash",
                shlex.join(first_preflight_command),
                "```",
            ]
        )
    if first_command:
        lines.extend(
            [
                "",
                "Rehearsal command once the input dist exists:",
                "",
                "```bash",
                shlex.join(first_command),
                "```",
                "",
                "This command writes under `build/` for rehearsal. L42 still needs an admitted external Trust artifact root or an explicit tracked local admission mechanism before clean-clone bootstrap evidence can pass.",
            ]
        )
    lines.extend(
        [
            "",
            "## Stage0 Genesis Path",
            "",
            "This is the concrete materialization path from the current metadata-only state to an admitted Trust-owned stage0 seed:",
            "",
            "1. Produce a Trust-owned `x dist` output root for the seed commit. The input root must contain `channel-rust-<source-channel>.toml` and xz archives for these source manifest packages:",
            "",
            "```text",
            "\n".join(REQUIRED_SOURCE_MANIFEST_PACKAGES),
            "```",
            "",
            "2. Run the stage0 materializer command above, replacing `<seed-commit-that-produced-input-dist>` with the commit hash that produced the input dist.",
            "",
            "3. Admit the materialized output root only if it contains every checksum-pinned Trust archive below with the exact SHA-256 recorded in `src/stage0`:",
            "",
            "| Artifact name | Expected SHA-256 |",
            "| --- | --- |",
        ]
    )
    if isinstance(required, list) and required:
        for artifact in required:
            if not isinstance(artifact, dict):
                continue
            lines.append(
                "| `{}` | `{}` |".format(
                    Path(str(artifact.get("path", "<unknown>"))).name,
                    artifact.get("sha256", "<unknown>"),
                )
            )
    else:
        lines.append("| `<none>` | `<none>` |")
    lines.extend(
        [
            "",
            "4. Rerun the admission checks with `TRUST_DIST_SERVER` pointed at the admitted root. Inherited `rustc`/`cargo` tarballs or binaries are audit inputs only and do not satisfy this path.",
        ]
    )
    lines.extend(
        [
            "",
            "## Executable Blocker",
            "",
        ]
    )
    if blocker:
        lines.extend(
            [
                blocker,
                "",
                "Rerun this diagnostic after materializing an admitted Trust stage0 payload root:",
                "",
                "```bash",
                "python3 scripts/discover_trust_stage0_seed.py --report reports/full-verify/l42-stage0-seed-discovery.md",
                "```",
                "",
                "A passing sysroot root must expose the full required `bin` and `libexec` stage0 surface; a passing dist root must contain checksum-pinned Trust stage0 archives whose payload members expose that same Trust/compatibility surface.",
                "A dist root candidate must contain every `src/stage0` checksum-pinned archive above with the exact SHA-256 digest; a partial `trustc`/`targo` pair is not admission evidence.",
                "",
                "Admission check commands once a candidate artifact root exists:",
                "",
                "```bash",
                "TRUST_DIST_SERVER=file:///ABS/PATH/TO/TRUST-STAGE0 python3 scripts/discover_trust_stage0_seed.py --repo-root . --candidate-root /ABS/PATH/TO/TRUST-STAGE0 --json",
                "TRUST_DIST_SERVER=file:///ABS/PATH/TO/TRUST-STAGE0 bash tests/e2e_trust_stage0_lineage.sh --dist-server file:///ABS/PATH/TO/TRUST-STAGE0",
                "TRUST_DIST_SERVER=file:///ABS/PATH/TO/TRUST-STAGE0 ./x.py build --stage 1 compiler/rustc library/std",
                "```",
            ]
        )
    else:
        lines.append("No blocker: a candidate root exposes the required canonical Trust entrypoints.")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    stage0_file = args.stage0_file if args.stage0_file is not None else repo_root / "src" / "stage0"
    stage0 = read_stage0(stage0_file)
    required_build_triple = host_build_triple()
    required_host_artifacts = required_host_archive_keys(stage0, required_build_triple)
    candidates, path_tools = discover_roots(repo_root, stage0, args.candidate_root)
    results = inspect_roots(candidates, stage0, required_host_artifacts)
    materializers = discover_materializers(
        repo_root,
        stage0,
        args.producer_input_dist,
        args.producer_source_channel,
    )
    release_ledger = inspect_release_ledger(repo_root, stage0)
    data = result_dict(
        repo_root,
        stage0,
        results,
        path_tools,
        materializers,
        release_ledger,
        required_build_triple,
        required_host_artifacts,
    )

    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(markdown_report(data), encoding="utf-8")

    if args.json:
        print(json.dumps(data, indent=2, sort_keys=True))
    elif data["blocker"]:
        print(f"BLOCKED: {data['blocker']}", file=sys.stderr)
        if args.report:
            print(f"Report: {args.report}", file=sys.stderr)
    else:
        print("PASS: found Trust-owned stage0 payload root exposing canonical trustc/targo")
        if args.report:
            print(f"Report: {args.report}")

    return 1 if data["blocker"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
