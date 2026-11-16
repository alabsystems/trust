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
echo "trust_version_sync.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
from __future__ import annotations

import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 trust_version_sync.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("trust_version_sync.py requires Python 3.11+ (tomllib); none found on PATH")

__doc__ = """Keep every mirror of Trust's version in step with its ONE authority.

THE AUTHORITY is the root `Cargo.toml` `[workspace.package] version` -- the key
`pub bump` edits and `pub version` / `pub promote` read
(`publication/VERSIONING.md`: "read it, do not recall it"). It must be
`MAJOR.MINOR.0`: the patch slot is always 0, and a dev build is identified by
SemVer build metadata (`-dev.<count>+g<sha>` / `+g<sha>`), never by a counter in
the patch slot. This script refuses any other authority.

THE MIRRORS state the same number for a reader that cannot read the authority.
Nothing but `--write` may change them:

  src/version                  bootstrap -> CFG_TRUST_VERSION (the `trust:` line
                               of `trustc -Vv`) and the dist archive names
  release/trust-version.toml   `trust_product_version`, what `targo trust
                               version` reports
  targo-trust/Cargo.toml       `[package] version`, what `targo-trust --version`
                               prints
  every tracked Cargo.lock     the entries of the path packages whose version the
                               manifests above set

NOT a mirror: `src/rust-compat-version` is the Rust `-V` protocol line (what
build scripts parse out of `rustc -V`). It is a different number on purpose and
this script never reads or writes it.

Usage:
  python3 scripts/trust_version_sync.py --check   # exit 0 in sync, 1 listing every
                                                  # disagreeing file and the fix
  python3 scripts/trust_version_sync.py --write   # rewrite every mirror from the
                                                  # authority, then prove the locks

Bumping the version is two commands:
  pub bump trust --write                          # edits the authority only
  python3 scripts/trust_version_sync.py --write   # moves every mirror with it

`--write` edits lockfiles surgically -- only the `version` of the governed path
packages changes -- and then asks cargo to CONFIRM the build's lockfiles with
`targo metadata --format-version 1 --offline --locked`. It never lets cargo
re-resolve anything, so no third-party dependency can move (never run
`targo update` / `cargo update` for a version bump). Set `TARGO` to choose the
binary.

Enforcement, so drift cannot ship:
  * bootstrap refuses to build when a mirror it reads disagrees with the
    authority (src/bootstrap/src/utils/trust_version_authority.rs);
  * `crates/trust-version`'s `every_version_mirror_agrees_with_the_authority`
    test fails on any disagreeing manifest mirror;
  * this script's `--check` covers the lockfiles as well.
Keep the mirror list here, in that test and in the bootstrap gate in step.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

import argparse
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python < 3.11
    sys.exit("trust_version_sync: needs Python 3.11+ (tomllib)")


REPO_ROOT = Path(__file__).resolve().parents[1]
AUTHORITY = "Cargo.toml"
FIX = "python3 scripts/trust_version_sync.py --write"

# Lockfiles of the workspaces the build itself resolves. `--write` proves each
# with `targo metadata --offline --locked` after rewriting it.
CARGO_CONFIRMED_WORKSPACES = (".", "library")

# Tracked lockfiles under these prefixes are never mirrors: first-party
# submodules carry their own version lines, vendor/ is foreign, and reports/
# holds historical evidence copies that must stay as they were measured.
LOCK_EXCLUDED_PREFIXES = ("first-party/", "vendor/", "reports/")

# Directory names never walked when git cannot list the tracked files.
# `build.noindex` is the Spotlight-excluded home `build` may link to
# (docs/BUILD_AND_INSTALL.md): os.walk skips the link but not the real directory.
WALK_PRUNE = {".git", "build", "build.noindex", "first-party", "vendor", "reports", "node_modules"}

VERSION_RE = re.compile(r"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$")


class SyncError(Exception):
    """A condition the script refuses to paper over."""


# ---------------------------------------------------------------------------
# The authority
# ---------------------------------------------------------------------------


def validate_release_line(version: str, where: str) -> str:
    match = VERSION_RE.match(version)
    if match is None:
        raise SyncError(
            f"{where} version {version!r} is not MAJOR.MINOR.0 -- three numbers, "
            "no leading zeros, no suffix (publication/VERSIONING.md)"
        )
    if match.group(3) != "0":
        raise SyncError(
            f"{where} version {version!r} has a nonzero patch slot: Trust releases "
            "are MAJOR.MINOR.0 and the patch slot is always 0 (publication/"
            "VERSIONING.md); dev builds are identified by build metadata "
            "(+g<sha>), never by a patch counter. Bump MINOR with `pub bump`."
        )
    return version


def read_authority(root: Path) -> str:
    path = root / AUTHORITY
    try:
        manifest = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as err:
        raise SyncError(f"cannot read the authority {AUTHORITY}: {err}") from err
    version = manifest.get("workspace", {}).get("package", {}).get("version")
    if not isinstance(version, str):
        raise SyncError(f"{AUTHORITY} has no `[workspace.package] version` string")
    return validate_release_line(version, f"{AUTHORITY} [workspace.package]")


# ---------------------------------------------------------------------------
# Manifest mirrors
# ---------------------------------------------------------------------------


def _table_header(line: str) -> str | None:
    """The table a header line opens (`[a.b]` -> `a.b`, `[[p]]` -> `[[p]]`)."""
    stripped = line.strip()
    if stripped.startswith("[["):
        end = stripped.find("]]")
        return None if end < 0 else f"[[{stripped[2:end].strip()}]]"
    if stripped.startswith("["):
        end = stripped.find("]")
        return None if end < 0 else stripped[1:end].strip()
    return None


def set_toml_string(text: str, table: str | None, key: str, value: str) -> str:
    """Rewrite `key = "..."` in `table` (None = top level), touching nothing else."""
    key_re = re.compile(r'^(\s*' + re.escape(key) + r'\s*=\s*")([^"]*)(".*)$')
    lines = text.splitlines(keepends=True)
    current: str | None = None
    hits: list[int] = []
    for index, line in enumerate(lines):
        header = _table_header(line)
        if header is not None:
            current = header
            continue
        if current == table and key_re.match(line.rstrip("\r\n")):
            hits.append(index)
    where = f"[{table}] {key}" if table else key
    if len(hits) != 1:
        raise SyncError(f"expected exactly one `{where} = \"...\"` line, found {len(hits)}")
    line = lines[hits[0]]
    ending = line[len(line.rstrip("\r\n")) :]
    lines[hits[0]] = key_re.sub(
        lambda m: m.group(1) + value + m.group(3), line.rstrip("\r\n"), count=1
    ) + ending
    return "".join(lines)


def _toml_lookup(document: dict, table: str | None, key: str) -> object:
    node: object = document
    for part in table.split(".") if table else []:
        node = node.get(part, {}) if isinstance(node, dict) else {}
    return node.get(key) if isinstance(node, dict) else None


@dataclass(frozen=True)
class Mirror:
    path: str
    label: str
    read: Callable[[str], object]
    write: Callable[[str, str], str]


def _toml_mirror(path: str, table: str | None, key: str) -> Mirror:
    label = f"[{table}] {key}" if table else key

    def read(text: str) -> object:
        return _toml_lookup(tomllib.loads(text), table, key)

    def write(text: str, version: str) -> str:
        updated = set_toml_string(text, table, key, version)
        # Postcondition: the ONLY semantic change is this one value.
        before, after = tomllib.loads(text), tomllib.loads(updated)
        node = before
        for part in table.split(".") if table else []:
            node = node[part]
        node[key] = version
        if before != after:
            raise SyncError(f"{path}: rewriting {label} changed more than that value")
        return updated

    return Mirror(path, label, read, write)


MIRRORS = (
    Mirror(
        "src/version",
        "contents",
        lambda text: text.strip(),
        lambda _text, version: f"{version}\n",
    ),
    _toml_mirror("release/trust-version.toml", None, "trust_product_version"),
    _toml_mirror("targo-trust/Cargo.toml", "package", "version"),
)


# ---------------------------------------------------------------------------
# Lockfile mirrors
# ---------------------------------------------------------------------------


def _inherits_workspace_version(manifest: Path) -> str | None:
    """The package name, when its version is `version.workspace = true`."""
    try:
        package = tomllib.loads(manifest.read_text(encoding="utf-8")).get("package", {})
    except (OSError, tomllib.TOMLDecodeError):
        return None
    version = package.get("version")
    if isinstance(version, dict) and version.get("workspace") is True:
        name = package.get("name")
        return name if isinstance(name, str) else None
    return None


def governed_packages(root: Path) -> set[str]:
    """Packages whose version IS the authority's number once the mirrors agree.

    The members of the canonical workspace that inherit
    `[workspace.package] version`, plus `targo-trust`, whose own `[package]
    version` is a mirror. A `crates/*` member that spells a literal version
    (`memchr` 2.8.3, the `sha2` shim, ...) is on its own line and not governed.
    """
    manifests: set[Path] = set()
    for workspace in (root,):
        try:
            document = tomllib.loads((workspace / "Cargo.toml").read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError):
            continue
        for member in document.get("workspace", {}).get("members", []):
            for directory in workspace.glob(member):
                manifests.add(directory / "Cargo.toml")
    # Path dependencies under a workspace root are implicit members, so every
    # crates/* manifest counts even when neither list names it.
    manifests.update((root / "crates").glob("*/Cargo.toml"))
    names = {name for m in sorted(manifests) if (name := _inherits_workspace_version(m))}
    try:
        targo_trust = tomllib.loads((root / "targo-trust/Cargo.toml").read_text(encoding="utf-8"))
        names.add(targo_trust["package"]["name"])
    except (OSError, KeyError, tomllib.TOMLDecodeError):
        pass
    return names


def tracked_lockfiles(root: Path) -> list[str]:
    try:
        listed = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*Cargo.lock"],
            check=True,
            capture_output=True,
        ).stdout.decode("utf-8")
        paths = [p for p in listed.split("\0") if p]
    except (OSError, subprocess.CalledProcessError):
        paths = []
        for directory, subdirs, files in os.walk(root):
            subdirs[:] = [d for d in subdirs if d not in WALK_PRUNE and not d.startswith("target")]
            if "Cargo.lock" in files:
                paths.append(Path(directory, "Cargo.lock").relative_to(root).as_posix())
    return sorted(
        p
        for p in paths
        if Path(p).name == "Cargo.lock" and not p.startswith(LOCK_EXCLUDED_PREFIXES)
    )


def lock_drift(text: str, governed: set[str], version: str) -> list[tuple[str, str]]:
    """(name, found) for every governed path package not at `version`."""
    document = tomllib.loads(text)
    return sorted(
        (package["name"], package["version"])
        for package in document.get("package", [])
        if "source" not in package
        and package.get("name") in governed
        and package.get("version") != version
    )


def rewrite_lock(text: str, governed: set[str], version: str) -> str:
    """Set every governed path package's `version` line, and nothing else."""
    lines = text.splitlines(keepends=True)
    renamed: set[tuple[str, str]] = set()
    block: dict[str, object] | None = None

    def close(current: dict[str, object] | None) -> None:
        if not current or current.get("source") or current.get("name") not in governed:
            return
        index = current.get("version_line")
        old = current.get("version")
        if not isinstance(index, int) or old == version:
            return
        line = lines[index]
        ending = line[len(line.rstrip("\r\n")) :]
        lines[index] = f'version = "{version}"{ending}'
        renamed.add((str(current["name"]), str(old)))

    for index, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("["):
            close(block)
            block = {} if stripped == "[[package]]" else None
            continue
        if block is None:
            continue
        if match := re.match(r'^name = "([^"]*)"$', stripped):
            block["name"] = match.group(1)
        elif match := re.match(r'^version = "([^"]*)"$', stripped):
            block["version"] = match.group(1)
            block["version_line"] = index
        elif stripped.startswith("source = "):
            block["source"] = True
    close(block)

    updated = "".join(lines)
    # A dependency edge names the version only when the name is ambiguous in
    # the lock (`"name 0.1.0"`; a path package carries no source suffix), so
    # move exactly those edges with their package.
    edges = {f"{name} {old}": f"{name} {version}" for name, old in renamed}
    for old_edge, new_edge in sorted(edges.items()):
        updated = updated.replace(f'"{old_edge}"', f'"{new_edge}"')

    # Postcondition: the only semantic change is the governed versions.
    expected = tomllib.loads(text)
    for package in expected.get("package", []):
        if "source" not in package and (package.get("name"), package.get("version")) in renamed:
            package["version"] = version
        if "dependencies" in package:
            package["dependencies"] = [edges.get(dep, dep) for dep in package["dependencies"]]
    if tomllib.loads(updated) != expected:
        raise SyncError("rewriting a lockfile changed more than the governed versions")
    return updated


# ---------------------------------------------------------------------------
# check / write
# ---------------------------------------------------------------------------


@dataclass
class Finding:
    path: str
    detail: str


def check(root: Path) -> tuple[str, list[Finding], int]:
    """(authority, findings, lockfiles inspected). Raises SyncError on a bad authority."""
    authority = read_authority(root)
    findings: list[Finding] = []
    for mirror in MIRRORS:
        path = root / mirror.path
        try:
            found = mirror.read(path.read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError) as err:
            findings.append(Finding(mirror.path, f"unreadable ({err})"))
            continue
        if found != authority:
            detail = f"{mirror.label} = {found!r}, expected {authority!r}"
            findings.append(Finding(mirror.path, detail))
    governed = governed_packages(root)
    locks = tracked_lockfiles(root)
    for lock in locks:
        try:
            drift = lock_drift((root / lock).read_text(encoding="utf-8"), governed, authority)
        except (OSError, tomllib.TOMLDecodeError) as err:
            findings.append(Finding(lock, f"unreadable ({err})"))
            continue
        if drift:
            found = sorted({v for _, v in drift})
            names = ", ".join(name for name, _ in drift[:4]) + (", ..." if len(drift) > 4 else "")
            findings.append(
                Finding(
                    lock,
                    f"{len(drift)} path package(s) at {', '.join(found)}, expected "
                    f"{authority!r} ({names})",
                )
            )
    return authority, findings, len(locks)


def confirm_with_cargo(root: Path) -> list[str]:
    """Ask cargo whether each build lockfile is consistent, without letting it write."""
    targo = os.environ.get("TARGO", "targo")
    failures = []
    for workspace in CARGO_CONFIRMED_WORKSPACES:
        directory = root / workspace
        if not (directory / "Cargo.lock").is_file():
            continue
        command = [targo, "metadata", "--format-version", "1", "--offline", "--locked"]
        try:
            result = subprocess.run(
                command, cwd=directory, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True
            )
        except OSError as err:
            failures.append(f"{workspace}: cannot run {targo!r}: {err}")
            continue
        if result.returncode != 0:
            tail = "\n    ".join(result.stderr.strip().splitlines()[-6:])
            failures.append(
                f"{workspace}: `{' '.join(command)}` exited {result.returncode}\n    {tail}"
            )
    return failures


def write(root: Path, run_cargo: bool) -> int:
    authority = read_authority(root)
    changed: list[str] = []
    for mirror in MIRRORS:
        path = root / mirror.path
        text = path.read_text(encoding="utf-8")
        if mirror.read(text) == authority:
            continue
        path.write_text(mirror.write(text, authority), encoding="utf-8")
        changed.append(mirror.path)
    governed = governed_packages(root)
    for lock in tracked_lockfiles(root):
        path = root / lock
        text = path.read_text(encoding="utf-8")
        if not lock_drift(text, governed, authority):
            continue
        path.write_text(rewrite_lock(text, governed, authority), encoding="utf-8")
        changed.append(lock)
    for path in changed:
        print(f"wrote {path}")
    if not changed:
        print("nothing to write: every mirror already agrees")

    status = 0
    if run_cargo:
        failures = confirm_with_cargo(root)
        for failure in failures:
            print(f"CARGO {failure}", file=sys.stderr)
        if failures:
            print(
                "trust_version_sync: cargo does not accept a build lockfile as written. "
                "Nothing was re-resolved; inspect the lock above rather than running "
                "`targo update`, which can move third-party dependencies.",
                file=sys.stderr,
            )
            status = 1
        else:
            print(
                "cargo confirms the build lockfiles (--offline --locked): "
                + ", ".join(CARGO_CONFIRMED_WORKSPACES)
            )
    unconfirmed = [
        lock
        for lock in changed
        if lock.endswith("Cargo.lock")
        and Path(lock).parent.as_posix() not in CARGO_CONFIRMED_WORKSPACES
    ]
    for lock in unconfirmed:
        print(
            f"note: {lock} is not a build lockfile; only its governed versions were "
            "rewritten. Whether it is otherwise current is its own harness's question."
        )

    _, findings, _ = check(root)
    for finding in findings:
        print(f"DRIFT {finding.path}: {finding.detail}", file=sys.stderr)
    return 1 if findings else status


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="report drift; exit 1 on any")
    mode.add_argument("--write", action="store_true", help="rewrite every mirror")
    parser.add_argument("--root", type=Path, default=REPO_ROOT, help=argparse.SUPPRESS)
    parser.add_argument(
        "--no-cargo",
        action="store_true",
        help="with --write: skip the `targo metadata --locked` confirmation",
    )
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        if args.write:
            return write(root, run_cargo=not args.no_cargo)
        authority, findings, locks = check(root)
    except (SyncError, OSError, tomllib.TOMLDecodeError) as err:
        print(f"trust_version_sync: REFUSED: {err}", file=sys.stderr)
        return 1
    if findings:
        print(
            f"trust_version_sync: {len(findings)} mirror(s) disagree with the authority "
            f"({AUTHORITY} [workspace.package] version = {authority}):",
            file=sys.stderr,
        )
        for finding in findings:
            print(f"  {finding.path}: {finding.detail}", file=sys.stderr)
        print(f"fix: {FIX}", file=sys.stderr)
        return 1
    print(
        f"OK: {len(MIRRORS)} manifest mirrors and {locks} tracked lockfiles agree with "
        f"{AUTHORITY} [workspace.package] version = {authority}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
