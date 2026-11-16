#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
exec python3 "$0" "$@"
":"""
from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 check_seed_freshness.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
#
# This script became a floor script in `3bafe6c1f14`, when the freshness gate started reading
# `bootstrap.toml`'s configured seed with stdlib `tomllib`. That commit did not apply the
# discipline `f17d1becf3b` set for exactly this case — polyglot block, re-exec guard, and no
# harness row starting it via bare `python3` — so on a machine whose `python3` is 3.9 the
# `fast.seed-freshness` push lane failed closed with "cannot read the configured seed", for
# every push, regardless of what the push changed.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    # NO 3.11+ found: fall through on this interpreter rather than exit. Unlike the four
    # `f17d1becf3b` floor scripts this one HAS a `tomli` fallback, so a 3.9 + `tomli` machine
    # works today, and exiting here would regress it. With neither, the reader below still
    # fails closed with its own "cannot read the configured seed" message.
__doc__ = """Trust: the re-seed cadence gate (docs/SEED_STAIRCASE.md).

The "off stock Rust" invariant is not a one-shot milestone — a Trust stage0
seed is only valid within one minor of ``src/version`` (``check_stage0_version``
in src/bootstrap), so it is a perishable artifact. This gate machine-enforces
the invariant: **the pinned seed must stay within one minor of the source
version.** Run it in CI on every commit; it must gate any ``src/version`` bump.

The failure mode it prevents: bumping ``src/version`` past the seed's shelf
life (as happened when 1.96->1.99 stranded the seed) so that a fresh, no-rustup
machine can no longer bootstrap — silently pushing everyone back onto the
stock-Rust genesis path.

Exit 0 = seed is fresh (or intentionally staircase-covered). Exit 1 = a seed/configuration/payload failure. Exit 2 = contract execution
unavailable, with no conclusion that the seed needs re-minting.

Beyond the version window, the gate now runs a REAL CONTRACT PROBE whenever a
materialized stage0 binary exists under ``build/<host>/stage0/bin/rustc``:

* identity — ``rustc -vV``'s commit-hash / commit-date / release line must
  match the ``src/stage0`` pin (previously the binary was never executed, so
  the gate passed on any binary whose *pinned metadata* looked fresh);
* flag contract — the seed must accept a real compile under exactly what
  bootstrap hands a stage0 snapshot: ``--cfg bootstrap`` on argv and the
  verification off-switch through the ``TRUST_NO_VERIFY=1`` environment
  transport. Bootstrap puts no verifier flag on a snapshot's argv at all
  (``bootstrap_disables_default_trust_verification`` is false for
  ``build_compiler_stage == 0`` in src/bootstrap/src/core/builder/cargo.rs, and
  src/bootstrap/src/bin/rustc.rs routes a snapshot through the env transport
  because a seed may predate the ``-Ztrust-verify=off`` rename). Until
  2026-09-23 this probe passed ``-Zno-trust-verify`` on argv instead — a
  spelling bootstrap no longer sends, which the atpkg 321aaeda7 seed rejects
  (``unknown unstable option``) while building this tree fine.

  Only an extraction whose ``.rustc-stamp`` is the pin's extraction identity is probed:
  bootstrap re-extracts any other, so a checkout that has not rebuilt since a
  re-pin landed is not red for it.

* configured seed — ``bootstrap.toml``'s ``[build] rustc`` or ``cargo`` FAILS,
  whatever it reports: the committed pin is the only seed (DECISION_QUEUE D12,
  resolved 2026-09-29). When either key is set, bootstrap never downloads the
  ``src/stage0`` pin: the configured binary IS the seed. Until 2026-09-23 this
  gate never read the file, so on the owner's machine it passed while every
  build seeded from atpkg's ``store/trust/current`` (TRUST-19); until
  2026-09-29 it passed a configured seed whose ``-vV`` matched the pin.

KNOWN RESIDUAL, filed precisely rather than papered over: when no stage0 is
materialized and none is configured (fresh CI checkout), the contract probe
SKIPS — there is no binary to execute, and the version window is all this gate
can check. A configured seed is read as bootstrap merges it (the file, its
``include``s and its ``profile``); a value supplied through ``--set`` on an
x.py command line is not seen. And the probe checks that the contract COMPILES, not the off-switch's
POLARITY: a seed that ignores or inverts ``TRUST_NO_VERIFY`` (the f24fdb2fdb
BUG-C alias class) still passes; detecting inversion needs a compile whose verdict
differs under verify-on vs verify-off, which is a compiler-fixture concern,
not a freshness-gate concern.

Usage:
  python3 scripts/check_seed_freshness.py            # gate
  python3 scripts/check_seed_freshness.py --require-payloads   # also require materialized payloads (release CI)
"""

import argparse
import datetime
import hashlib
import importlib.util
import os
import re
import stat
import subprocess
import sys
import time
from pathlib import Path


# Trust: load the extraction-key owner by path, including under isolated -I -S.
_IDENTITY_SPEC = importlib.util.spec_from_file_location(
    "trust_stage0_identity", Path(__file__).resolve().parents[1] / "src/bootstrap/stage0_identity.py",
)
_IDENTITY_OWNER = importlib.util.module_from_spec(_IDENTITY_SPEC)
_IDENTITY_SPEC.loader.exec_module(_IDENTITY_OWNER)
stage0_extraction_stamp = _IDENTITY_OWNER.extraction_stamp

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts/lib"))
import landing_targo
import native_serial
seed_identity = importlib.import_module("seed_compiler_identity")
SeedIdentityError = seed_identity.SeedIdentityError
authenticate_compiler = seed_identity.authenticate_compiler
check_compiler_snapshot = seed_identity.check_compiler_snapshot


class ProbeUnavailable(str):
    """An unexecuted/infrastructure result, never evidence that the seed is bad."""


# One lifetime implementation also protects the two recreator launch sites.
run_seed_command = native_serial.run_custodied_command


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
    is on Rust's version line, never on Trust's `MAJOR.MINOR.0` one. So the
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


def validate_payload_inventory(stage0: dict[str, str], host: str | None = None) -> list[str]:
    """Check declared component coverage; another host cannot fill a requested cohort."""
    errors: list[str] = []
    if host is not None and (
        ".." in host or re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]{2,127}", host) is None
    ):
        return [f"requested host is not a canonical target triple: {host!r}"]
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
            and (
                host is None
                or name == f"{component}{version}{'' if component == 'trust-src-' else '-' + host}.tar.xz"
            )
        ]
        if not matches:
            errors.append(
                f"declared payload inventory is missing required {component.rstrip('-')} "
                f"archive(s) for declared version {version!r}"
                + (f" and host {host!r}" if host is not None else "")
            )
    return errors


def native_payload_host() -> str:
    """Use the mint's native GNU/musl/macOS detection, never an ambient tool probe."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from mint_seed_support import detected_host

    return detected_host()


def validate_materialized_payloads(stage0: dict[str, str], host: str | None = None) -> list[str]:
    if host is None:
        try:
            host = native_payload_host()
        except (ImportError, OSError, RuntimeError) as error:
            return [f"cannot determine the native seed host: {error}"]
    errors = validate_payload_inventory(stage0, host)
    date = stage0.get("compiler_date", "")
    prefix = f"dist/{date}/"
    declared = {
        key: value
        for key, value in stage0.items()
        if key.startswith(prefix) and key.endswith(".tar.xz")
    }
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


def probe_seed_binary(
    binary: Path, label: str, stage0: dict[str, str]
) -> tuple[list[str], list[str]]:
    """Run one seed binary against the pin: identity (-vV) and flag contract."""
    import subprocess
    import tempfile

    errors: list[str] = []
    notes: list[str] = []
    pinned_hash = stage0.get("compiler_git_commit_hash", "")
    pinned_date = stage0.get("compiler_date", "")
    pinned_version = parse_version(stage0.get("compiler_version", ""))

    identity_matches = True
    try:
        compiler_binding = authenticate_compiler(
            ROOT, binary, stage0, deadline=time.monotonic() + 120
        )
    except SeedIdentityError as error:
        errors.append(f"{label}: selected compiler identity failed: {error}")
        return errors, notes
    except (OSError, subprocess.TimeoutExpired) as error:
        errors.append(ProbeUnavailable(f"{label}: selected compiler identity unavailable: {error}"))
        return errors, notes
    # --- identity: the binary must BE the pinned seed ------------------------
    try:
        result = run_seed_command([str(binary), "-vV"], env=dict(os.environ), timeout=60)
        check_compiler_snapshot(binary, compiler_binding)
    except SeedIdentityError as error:
        errors.append(f"{label}: selected compiler changed: {error}")
        return errors, notes
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        errors.append(ProbeUnavailable(f"{label}: cannot execute for -vV: {error}"))
        return errors, notes
    if result.returncode != 0:
        errors.append((ProbeUnavailable if result.returncode == 75 else str)(
            f"{label}: -vV exited {result.returncode}"))
        return errors, notes
    fields = {}
    for line in result.stdout.splitlines():
        key, sep, value = line.partition(": ")
        if sep:
            fields[key.strip()] = value.strip()
    observed_hash = fields.get("commit-hash", "")
    if observed_hash != pinned_hash:
        identity_matches = False
        errors.append(
            f"{label}: commit-hash {observed_hash!r} does not match pinned "
            f"compiler_git_commit_hash {pinned_hash!r}"
        )
    observed_date = fields.get("commit-date", "")
    if observed_date != pinned_date:
        identity_matches = False
        errors.append(
            f"{label}: commit-date {observed_date!r} does not match pinned "
            f"compiler_date {pinned_date!r}"
        )
    # compiler_version is the dist package version, `<src/version>-trust` at
    # the seed's commit. Since Trust's own version line split from Rust's
    # (c9a8f1f481, 2026-09-23) that is the `trust:` line of -vV; a seed minted
    # before the split reports no `trust:` line and carried its Rust-line
    # `release:` in the archive name (the 2026-07-13 pin: 1.99.0-trust).
    version_field = "trust" if "trust" in fields else "release"
    observed_version = parse_version(fields.get(version_field, ""))
    if pinned_version is not None and observed_version != pinned_version:
        identity_matches = False
        errors.append(
            f"{label}: {version_field} {fields.get(version_field, '')!r} is not at the "
            f"pinned seed's major.minor {pinned_version[0]}.{pinned_version[1]}"
        )
    # A known identity mismatch cannot start the producing query or its owner.
    if not identity_matches:
        return errors, notes
    # --- flag contract: exactly what bootstrap hands a stage0 snapshot -------
    # `--cfg bootstrap` on argv; the off-switch as TRUST_NO_VERIFY=1 in the
    # environment (src/bootstrap/src/bin/rustc.rs: a snapshot never gets a
    # verifier flag on argv). A seed that cannot compile under that strands
    # stage1 at its first crate.
    with tempfile.TemporaryDirectory() as scratch:
        probe = Path(scratch) / "probe.rs"
        probe.write_text("pub fn probe() {}\n", encoding="utf-8")
        out = Path(scratch) / "probe.rmeta"
        try:
            environment = {**os.environ, "TRUST_NO_VERIFY": "1"}
            executor = native_serial.managed_serial_executor(environment)
            result = run_seed_command(
                [
                    str(executor), "--", str(binary),
                    "--edition",
                    "2021",
                    "--crate-type",
                    "lib",
                    "--emit=metadata",
                    "--cfg",
                    "bootstrap",
                    "-o",
                    str(out),
                    str(probe),
                ],
                timeout=120,
                cwd=scratch,
                env=environment,
            )
            check_compiler_snapshot(binary, compiler_binding)
        except SeedIdentityError as error:
            errors.append(f"{label}: selected compiler changed: {error}")
            return errors, notes
        except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
            errors.append(ProbeUnavailable(f"{label}: flag-contract probe did not run: {error}"))
            return errors, notes
        try:
            output = out.lstat()
            fresh_output = stat.S_ISREG(output.st_mode) and output.st_size > 0
        except OSError:
            fresh_output = False
        if result.returncode != 0 or not fresh_output:
            first = (result.stderr or result.stdout).strip().splitlines()
            errors.append(
                (ProbeUnavailable if result.returncode == 75 else str)(
                f"{label}: rejected the bootstrap stage0 contract "
                f"(--cfg bootstrap, TRUST_NO_VERIFY=1): rc={result.returncode}"
                + (f"; first error: {first[0][:160]}" if first else ""))
            )
            return errors, notes
    if identity_matches:
        notes.append(
            f"{label}: identity matches the pin ({observed_hash[:10]}, {observed_date}) "
            "and the bootstrap stage0 contract compiles"
        )
    return errors, notes


def probe_materialized_stage0(stage0: dict[str, str]) -> tuple[list[str], list[str]]:
    """Execute every materialized stage0 seed that bootstrap would REUSE.

    Returns ``(errors, notes)``. Bootstrap reuses ``build/<host>/stage0`` only
    while its ``.rustc-stamp`` holds the pin's compiler/archive identity, and
    re-extracts the pin otherwise, including old date-only stamps.
    So an extraction stamped for another pin is what every checkout holds the
    day a re-pin lands: a note, not a failure. A stamp-current binary that
    misreports its identity or rejects the bootstrap flag contract is an error,
    because that binary IS the seed of the next build. No materialized seed at
    all (a fresh checkout) is a note too.
    """
    errors: list[str] = []
    notes: list[str] = []
    binaries = []
    for target in sorted(ROOT.glob("build/*")):
        # Session recreates this convenience sysroot link from host_target;
        # it is not an extraction target (core/session.rs). Do not traverse it
        # or invent a second archive host named "host". Every concrete target
        # still passes the unchanged stamp, archive and execution checks below.
        # In particular, this is no permission to invoke a seed through a link.
        if target.name == "host" and target.is_symlink():
            notes.append("build/host: mutable sysroot alias is not a stage0 target; "
                         "concrete materialized seeds are checked independently")
            continue
        binaries.extend(target.glob("stage0/bin/rustc"))
    if not binaries:
        notes.append(
            "stage0 not materialized under build/<host>/stage0/bin/rustc — "
            "contract probe skipped (version-window check only)"
        )
        return errors, notes
    expected_stamp = stage0_extraction_stamp(stage0)
    for binary in binaries:
        label = str(binary.relative_to(ROOT))
        stamp_path = binary.parent.parent / ".rustc-stamp"
        try:
            stamp = stamp_path.read_text(encoding="utf-8")
        except OSError:
            stamp = None
        if stamp != expected_stamp:
            notes.append(
                f"{label}: extraction stamp {stamp!r} is not the pin's {expected_stamp!r}; "
                "the next x.py run re-extracts the pinned seed, so this binary is not probed"
            )
            continue
        if sys.platform == "win32":
            errors.append(ProbeUnavailable(
                f"{label}: actual Stage0 compiler execution is unavailable on Windows; "
                "metadata and payload checks do not establish its compiler contract"))
            continue
        if __name__ == "__main__" and os.environ.get("BUILD_SLOT_HELD") != "1":
            # No admission is needed for metadata/payload-only checks. Re-enter
            # through the maintained gate only before executing a real seed.
            # This marker routes; the native owner authenticates actual custody.
            os.execv(str(ROOT / "scripts/build-slot"),
                     [str(ROOT / "scripts/build-slot"), "--", sys.executable,
                      str(Path(__file__).resolve()), *sys.argv[1:]])
        binary_errors, binary_notes = probe_seed_binary(binary, label, stage0)
        errors.extend(binary_errors)
        notes.extend(binary_notes)
    return errors, notes


def bootstrap_config_path() -> Path | None:
    """The config file bootstrap reads, in bootstrap's own order.

    `RUST_BOOTSTRAP_CONFIG`, then `<root>/bootstrap.toml`, then the legacy
    `<root>/config.toml` (src/bootstrap/bootstrap.py and config.rs; the `./`
    variants are the same files because this gate runs from the root).
    """
    explicit = os.environ.get("RUST_BOOTSTRAP_CONFIG")
    if explicit:
        return Path(explicit)
    for name in ("bootstrap.toml", "config.toml"):
        candidate = ROOT / name
        if candidate.exists():
            return candidate
    return None


# The two stage0 selectors that make a configured binary the seed: bootstrap
# compiles stage1 with `[build] rustc` and drives it with `[build] cargo`.
SEED_OVERRIDE_KEYS = ("rustc", "cargo")


def configured_seed_overrides(config: Path) -> tuple[dict[str, object], list[str]]:
    """The seed selectors bootstrap would see, as ``{key: value}``: the file,
    its includes and its profile, read by the same reader the pack cut uses
    (``mint_seed_support.effective_build_table``)."""
    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        import mint_seed_support
    finally:
        sys.path.pop(0)
    if mint_seed_support.tomllib is None:
        return {}, [
            f"{config}: cannot read the configured seed — needs Python 3.11+ "
            "(tomllib) or tomli; a seed this gate cannot read is not a seed it passed"
        ]
    try:
        build = mint_seed_support.effective_build_table(ROOT, config.resolve(), confine=False)
    except (OSError, mint_seed_support.WorkflowError) as error:
        return {}, [f"{config}: unreadable bootstrap config: {error}"]
    return {key: build[key] for key in SEED_OVERRIDE_KEYS if key in build}, []


def probe_configured_seed(stage0: dict[str, str]) -> tuple[list[str], list[str]]:
    """Refuse a local seed override: the committed pin is the only seed (D12).

    `[build] rustc`/`cargo` replace the `src/stage0` download entirely, so a
    configured one is a seed that moves without the pin moving (TRUST-19). Until
    2026-09-29 this gate probed its identity and passed it when it matched the
    pin; now every configured seed fails, whatever it reports, because an
    identity line is a claim, while the pin is checksum-bound archives. The
    stock-rust genesis adapter (`recreate_bootstrap.py --genesis`) is such an
    override too, and is reported the same way: it is not a seed.
    """
    config = bootstrap_config_path()
    if config is None:
        return [], ["no bootstrap config; the seed is the src/stage0 download"]
    if not config.exists():
        return [f"RUST_BOOTSTRAP_CONFIG names a missing file: {config}"], []
    overrides, errors = configured_seed_overrides(config)
    if errors:
        return errors, []
    label_config = config.name if config.parent == ROOT else str(config)
    if not overrides:
        return [], [
            f"{label_config} sets no [build] rustc or cargo; the seed is the src/stage0 download"
        ]
    return [
        f"{label_config} [build] {key} = {value!r} overrides the src/stage0 pin "
        f"({stage0.get('compiler_git_commit_hash', '?')[:10]}, {stage0.get('compiler_date', '?')})"
        for key, value in overrides.items()
    ], []


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--require-payloads",
        action="store_true",
        help="also require the seed tarball payloads to be materialized (release CI, not dev)",
    )
    ap.add_argument("--host", help="inspect this host's complete payload cohort (default: native host)")
    args = ap.parse_args()
    if args.host is not None and not args.require_payloads:
        ap.error("--host requires --require-payloads")

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
    # Trust versions its own toolchain (MAJOR.MINOR.0) and does not ride
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
            f"(docs/SEED_STAIRCASE.md)."
        )

    probe_errors, probe_notes = probe_materialized_stage0(stage0)
    for note in probe_notes:
        print(f"note: {note}")
    unavailable = [error for error in probe_errors if isinstance(error, ProbeUnavailable)]
    for error in probe_errors:
        if isinstance(error, ProbeUnavailable):
            print(f"COULD NOT RUN: stage0 contract probe: {error}")
        else:
            print(f"FAIL: stage0 contract probe: {error}")
            ok = False

    # Everything above judges the COMMITTED seed, which a push carries. What
    # follows judges this checkout: its own bootstrap.toml and its dist/ folder,
    # which no commit carries. Each red needs a different fix, so the verdict
    # line names which one it is (verdict_line).
    committed_seed_ok = ok
    configured_errors, configured_notes = probe_configured_seed(stage0)
    for note in configured_notes:
        print(f"note: {note}")
    for error in configured_errors:
        print(f"FAIL: configured seed: {error}")
        ok = False
    if configured_errors:
        print(
            "      The committed src/stage0 pin is the only seed. Delete the override "
            "line(s); x.py then extracts the pin. A new seed arrives as a re-pin "
            "commit minted at a pack cut (scripts/mint_and_prove_seed.sh; D12)."
        )
        print(
            "      If the pin's payloads are not under bootstrap/trust-stage0/dist/"
            f"{stage0.get('compiler_date', '<date>')}/ yet, fetch them first with the "
            "`authenticated_fetch` command in bootstrap/trust-stage0/seed-ledger.toml."
        )

    payload_errors: list[str] = []
    if args.require_payloads:
        payload_errors = validate_materialized_payloads(stage0, args.host)
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
    if ok and unavailable:
        print("COULD NOT RUN: seed contract admission/execution unavailable; no re-seed conclusion.")
        return 2
    print(verdict_line(ok, committed_seed_ok, bool(configured_errors), bool(payload_errors)))
    return 0 if ok else 1


def verdict_line(ok: bool, committed_seed_ok: bool, configured_red: bool, payloads_red: bool) -> str:
    """The last line, which says which seed is red.

    Until 2026-10-28 every red ended "re-seed before this change lands", the
    verdict for a stale COMMITTED seed, even when the committed pin had passed
    every check and the only red was this checkout's own bootstrap.toml override
    (D12 refuses it) or its unfetched payloads. Agents read that as main's red
    and pushed past the hook. The exit status is unchanged: every red still
    refuses.
    """
    if ok:
        return "PASS: seed freshness invariant holds."
    if not committed_seed_ok:
        return "BLOCKED: re-seed before this change lands."
    if configured_red:
        return (
            "BLOCKED: this checkout's bootstrap.toml configures its own seed; the committed "
            "seed passed every check above. Delete the override line(s), not the pin (D12)."
        )
    assert payloads_red, "a red verdict with no red check"
    return (
        "BLOCKED: this checkout has not materialized the pinned seed's payloads; the committed "
        "seed passed every check above. Fetch them (seed-ledger.toml authenticated_fetch)."
    )


def prefer_real_toml_parser() -> None:
    """Re-exec under Python >= 3.11 when no TOML parser is importable.

    The configured-seed check needs `tomllib` (3.11+) or `tomli`. Without either
    it correctly refuses to call an unreadable seed fresh, but it then prints the
    verdict for a STALE SEED — "BLOCKED: re-seed before this change lands" — and
    exits 1, so a machine whose default `python3` is 3.9 was told to re-seed when
    the only problem was the interpreter (measured 2026-09-27). Same shim and
    search order as scripts/validate_upstream_rust_compat_summary.py; the
    in-function refusal stays as the last resort.
    """
    if sys.version_info >= (3, 11):
        return
    try:
        import tomli  # noqa: F401
    except ModuleNotFoundError:
        pass
    else:
        return
    for prefix in ("/opt/homebrew/bin", "/usr/local/bin", "/usr/bin"):
        for minor in (14, 13, 12, 11):
            candidate = f"{prefix}/python3.{minor}"
            if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
                os.execv(candidate, [candidate, *sys.argv])


if __name__ == "__main__":
    prefer_real_toml_parser()
    raise SystemExit(main())
