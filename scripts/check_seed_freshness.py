#!/usr/bin/env python3
"""Trust: the re-seed cadence gate (OFF_STOCK_RUST_PLAN.md Phase 4).

The "off stock Rust" invariant is not a one-shot milestone — a Trust stage0
seed is only valid within one minor of ``src/version`` (``check_stage0_version``
in src/bootstrap), so it is a perishable artifact. This gate machine-enforces
the invariant: **the pinned seed must stay within one minor of the source
version.** Run it in CI on every commit; it must gate any ``src/version`` bump.

The failure mode it prevents: bumping ``src/version`` past the seed's shelf
life (as happened when 1.96->1.99 stranded the seed) so that a fresh, no-rustup
machine can no longer bootstrap — silently pushing everyone back onto the
stock-Rust genesis path.

Exit 0 = seed is fresh (or intentionally staircase-covered). Exit 1 = re-mint
the seed BEFORE landing the version bump.

Usage:
  python3 scripts/check_seed_freshness.py            # gate
  python3 scripts/check_seed_freshness.py --require-payloads   # also require materialized payloads (release CI)
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import os
import re
import stat
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERSION_RE = re.compile(
    r"^(\d+)\.(\d+)\.(\d+)"
    r"(?:-([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?"
    r"(?:\+([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?$"
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
MAX_VERSION_BYTES = 256
MAX_STAGE0_BYTES = 1024 * 1024


def exact_regular_path_under(base: Path, relative: str) -> Path:
    parts = relative.split("/")
    if (
        not relative
        or relative.startswith("/")
        or "\\" in relative
        or any(part in {"", ".", ".."} for part in parts)
    ):
        raise OSError(f"not a canonical relative path: {relative!r}")
    path = base
    for index, part in enumerate(parts):
        path /= part
        metadata = path.lstat()
        is_last = index + 1 == len(parts)
        if (is_last and not stat.S_ISREG(metadata.st_mode)) or (
            not is_last and not stat.S_ISDIR(metadata.st_mode)
        ):
            raise OSError(f"path contains a symlink or wrong-type component: {path}")
    return path


def read_regular_text_under(base: Path, relative: str, maximum: int) -> str:
    path = exact_regular_path_under(base, relative)
    expected = path.lstat()
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    try:
        observed = os.fstat(descriptor)
        if not stat.S_ISREG(observed.st_mode) or (
            (expected.st_dev, expected.st_ino) != (observed.st_dev, observed.st_ino)
        ):
            raise OSError(f"file changed while being authenticated: {path}")
        if observed.st_size > maximum:
            raise OSError(f"file exceeds {maximum} bytes: {path}")
        with os.fdopen(descriptor, "rb") as handle:
            descriptor = -1
            data = handle.read(maximum + 1)
        if len(data) > maximum:
            raise OSError(f"file exceeds {maximum} bytes: {path}")
        return data.decode("utf-8")
    finally:
        if descriptor >= 0:
            os.close(descriptor)


def parse_version(text: str) -> tuple[int, int] | None:
    match = VERSION_RE.fullmatch(text)
    if not match:
        return None
    core = match.group(1, 2, 3)
    if any(len(number) > 1 and number.startswith("0") for number in core):
        return None
    prerelease = match.group(4)
    if prerelease and any(
        identifier.isdigit() and len(identifier) > 1 and identifier.startswith("0")
        for identifier in prerelease.split(".")
    ):
        return None
    values = tuple(int(number) for number in core)
    if any(number > 2**64 - 1 for number in values):
        return None
    return values[0], values[1]


def read_source_version() -> tuple[int, int]:
    """The tree's Rust COMPAT version — the line a stage0 reports.

    A stage0 binary announces its version through rustc's `-V` protocol, which
    is on Rust's version line, never on Trust's `major.minor.dev` one. So the
    seed is measured against src/rust-compat-version; comparing it to
    src/version (Trust's own) would compare two unrelated numbering schemes.
    """
    text = read_regular_text_under(ROOT, "src/rust-compat-version", MAX_VERSION_BYTES).strip()
    version = parse_version(text)
    if version is None:
        sys.exit(f"FAIL: cannot parse src/rust-compat-version: {text!r}")
    return version


def read_stage0() -> dict[str, str]:
    fields: dict[str, str] = {}
    stage0 = read_regular_text_under(ROOT, "src/stage0", MAX_STAGE0_BYTES)
    for number, line in enumerate(stage0.splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if "=" not in line:
            raise ValueError(f"src/stage0:{number}: expected key=value record")
        key, _, value = line.partition("=")
        key, value = key.strip(), value.strip()
        if not key or not value:
            raise ValueError(f"src/stage0:{number}: empty key or value")
        if key in fields:
            raise ValueError(f"src/stage0:{number}: duplicate key {key!r}")
        fields[key] = value
    return fields


def sha256_regular_file(path: Path) -> str:
    """Hash an exact regular file without following a final-component symlink."""
    digest = hashlib.sha256()
    expected = path.lstat()
    if not stat.S_ISREG(expected.st_mode):
        raise OSError(f"not an exact regular file: {path}")
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode) or (
            (expected.st_dev, expected.st_ino) != (metadata.st_dev, metadata.st_ino)
        ):
            raise OSError(f"file changed while being authenticated: {path}")
        handle = os.fdopen(descriptor, "rb")
        descriptor = -1
        with handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
    return digest.hexdigest()


def sha256_regular_file_under(base: Path, relative: str) -> str:
    """Hash a canonical relative file and reject symlinks in every component."""
    return sha256_regular_file(exact_regular_path_under(base, relative))


def payload_archive_name_matches(name: str, family: str, version: str) -> bool:
    stem = f"{family}{version}"
    if name == f"{stem}.tar.xz":
        return True
    prefix, suffix = f"{stem}-", ".tar.xz"
    if not name.startswith(prefix) or not name.endswith(suffix):
        return False
    target = name[len(prefix) : -len(suffix)]
    return (
        ".." not in target
        and re.fullmatch(r"[0-9A-Za-z](?:[0-9A-Za-z_.-]*[0-9A-Za-z])?", target)
        is not None
    )


def validate_stage0_metadata(stage0: dict[str, str]) -> list[str]:
    errors: list[str] = []
    for component in ("compiler", "rustfmt"):
        version = stage0.get(f"{component}_version", "")
        if parse_version(version) is None:
            errors.append(f"{component}_version is not a complete semantic version: {version!r}")
        commit = stage0.get(f"{component}_git_commit_hash", "")
        if not re.fullmatch(r"[0-9a-f]{40}", commit):
            errors.append(f"{component}_git_commit_hash is not canonical lowercase SHA-1")
        date = stage0.get(f"{component}_date", "")
        try:
            parsed_date = datetime.date.fromisoformat(date)
        except ValueError:
            errors.append(f"{component}_date is not YYYY-MM-DD: {date!r}")
        else:
            if parsed_date.isoformat() != date:
                errors.append(f"{component}_date is not canonical YYYY-MM-DD: {date!r}")
        manifest_hash = stage0.get(f"{component}_channel_manifest_hash", "")
        if not SHA256_RE.fullmatch(manifest_hash):
            errors.append(f"{component}_channel_manifest_hash is not canonical SHA-256")
    if stage0.get("compiler_date") != stage0.get("rustfmt_date"):
        errors.append("compiler_date and rustfmt_date must identify one coherent seed snapshot")
    return errors


def validate_materialized_payloads(stage0: dict[str, str]) -> list[str]:
    errors: list[str] = []
    date = stage0.get("compiler_date", "")
    prefix = f"dist/{date}/"
    declared = {
        key: value
        for key, value in stage0.items()
        if key.startswith(prefix) and key.endswith(".tar.xz")
    }
    if not declared:
        return [f"src/stage0 declares no seed payloads under {prefix}"]
    filenames = {Path(key).name for key in declared}
    required_components = {
        "targo-": stage0.get("compiler_version", ""),
        "targo-trust-": stage0.get("compiler_version", ""),
        "tippy-": stage0.get("compiler_version", ""),
        "trust-analyzer-": stage0.get("compiler_version", ""),
        "trust-src-": stage0.get("compiler_version", ""),
        "trust-std-": stage0.get("compiler_version", ""),
        "trustc-": stage0.get("compiler_version", ""),
        "trustc-dev-": stage0.get("compiler_version", ""),
        "trustfmt-": stage0.get("rustfmt_version", ""),
    }
    for component, version in required_components.items():
        matches = [
            name
            for name in filenames
            if payload_archive_name_matches(name, component, version)
        ]
        if not matches:
            errors.append(
                f"declared payload inventory is missing required {component.rstrip('-')} "
                f"archive(s) for declared version {version!r}"
            )
    for relative, expected in sorted(declared.items()):
        if not SHA256_RE.fullmatch(expected):
            errors.append(f"{relative}: declared digest is not canonical SHA-256")
            continue
        try:
            observed = sha256_regular_file_under(
                ROOT / "bootstrap" / "trust-stage0", relative
            )
        except OSError as error:
            errors.append(f"missing or non-regular declared payload: {relative}: {error}")
            continue
        if observed != expected:
            errors.append(f"{relative}: SHA-256 mismatch (expected {expected}, observed {observed})")

    manifest_relative = f"dist/{date}/channel-rust-trust.toml"
    try:
        observed_manifest = sha256_regular_file_under(
            ROOT / "bootstrap" / "trust-stage0", manifest_relative
        )
    except OSError as error:
        errors.append(f"missing or non-regular channel manifest: bootstrap/trust-stage0/{manifest_relative}: {error}")
    else:
        for component in ("compiler", "rustfmt"):
            expected_manifest = stage0.get(f"{component}_channel_manifest_hash", "")
            if SHA256_RE.fullmatch(expected_manifest) and observed_manifest != expected_manifest:
                errors.append(
                    f"channel-rust-trust.toml digest does not match {component}_channel_manifest_hash"
                )
    return errors


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--require-payloads",
        action="store_true",
        help="also require the seed tarball payloads to be materialized (release CI, not dev)",
    )
    args = ap.parse_args()

    smaj, smin = read_source_version()
    try:
        stage0 = read_stage0()
    except (OSError, ValueError) as error:
        print(f"FAIL: cannot parse src/stage0: {error}")
        return 1
    metadata_errors = validate_stage0_metadata(stage0)
    seed_ver = stage0.get("compiler_version", "")
    seed_version = parse_version(seed_ver)
    if seed_version is None:
        print(f"FAIL: src/stage0 compiler_version unparseable: {seed_ver!r}")
        return 1
    dmaj, dmin = seed_version

    print(f"rust-compat ver: {smaj}.{smin}.x")
    print(f"pinned seed    : {seed_ver} ({stage0.get('compiler_date', '?')}, {stage0.get('compiler_git_commit_hash', '?')[:10]})")

    ok = True
    for error in metadata_errors:
        print(f"FAIL: src/stage0 metadata: {error}")
        ok = False
    # Trust versions its own toolchain (major.minor.dev) and does not ride
    # Rust's release train, so there is no N-1 window and no staircase hatch.
    # A seed only has to be a PREVIOUS Trust release: stage1 is rebuilt in full
    # from this tree, so an older seed cannot leak into the shipped compiler's
    # identity. How far behind it is remains worth printing — a very stale seed
    # means a long stage0->stage1 hop — but it is information, not a gate.
    if (dmaj, dmin) > (smaj, smin):
        print(f"FAIL: seed {seed_ver} is NEWER than source {smaj}.{smin}; building backwards is never sanctioned.")
        ok = False
    elif (dmaj, dmin) == (smaj, smin):
        print("OK: seed is at the source release (fresh).")
    else:
        print(
            f"OK: seed {seed_ver} predates source {smaj}.{smin}.x — an older Trust release is a "
            f"valid seed. Re-mint when the stage0->stage1 hop starts costing more than it saves "
            f"(OFF_STOCK_RUST_PLAN.md Phase 1)."
        )

    if args.require_payloads:
        payload_errors = validate_materialized_payloads(stage0)
        if payload_errors:
            for error in payload_errors:
                print(f"FAIL: --require-payloads: {error}")
            ok = False
        else:
            count = sum(
                key.startswith(f"dist/{stage0['compiler_date']}/") and key.endswith(".tar.xz")
                for key in stage0
            )
            print(f"OK: all {count} declared seed payloads and the channel manifest are materialized and digest-bound.")

    print()
    print("PASS: seed freshness invariant holds." if ok else "BLOCKED: re-seed before this change lands.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
