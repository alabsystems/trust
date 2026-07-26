#!/usr/bin/env python3
"""Fail-closed helpers for prove_rust_free_build.sh.

The helper intentionally uses only the Python standard library and is invoked
with ``python -I -S``.  Records consumed by the shell use a tiny tab-delimited
protocol; user-controlled paths are normalized to single-line diagnostics.
"""

from __future__ import annotations

import ast
import hashlib
import os
import re
import shutil
import stat
import sys
import tempfile
import time
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:
    tomllib = None  # type: ignore[assignment]


STOCK_NAMES = {
    "rustc",
    "cargo",
    "rustdoc",
    "rustfmt",
    "cargo-clippy",
    "clippy-driver",
    "rustup",
}
TRUST_NAMES = {
    "trustc",
    "targo",
    "tcargo",
    "trustdoc",
    "trustfmt",
    "tippy",
    "tippy-driver",
    "targo-clippy",
    "trust-clippy",
    "trust-clippy-driver",
}
RUST_FAMILY_NAMES = STOCK_NAMES | TRUST_NAMES

# A stock-compatible spelling is legitimate only when it is an alias of the
# corresponding Trust frontend in the same toolchain directory.  Trust ships
# these aliases for ecosystem compatibility; merely placing an unrelated
# executable named ``rustc`` under build/ is not authentication.
STOCK_ALIAS_TARGETS = {
    "rustc": ("trustc",),
    "cargo": ("targo", "tcargo"),
    "rustdoc": ("trustdoc",),
    "rustfmt": ("trustfmt",),
    "cargo-clippy": ("tippy", "targo-clippy", "trust-clippy"),
    "clippy-driver": ("tippy-driver", "trust-clippy-driver"),
}

MAX_REPORTED_FINDINGS = 256
MAX_CONFIG_BYTES = 16 * 1024 * 1024
MAX_TRACE_BYTES = 512 * 1024 * 1024
# Linux's aggregate exec argument/environment limit is far below this.  The
# margin also covers strace's escaped rendering without allowing one corrupt
# no-newline record to allocate the entire trace ceiling in the parser.
MAX_TRACE_LINE_BYTES = 16 * 1024 * 1024

PRIMARY_TOOLS = {
    "rustc": {"trustc"},
    "cargo": {"targo", "tcargo"},
    "rustdoc": {"trustdoc"},
    "rustfmt": {"trustfmt"},
    "cargo-clippy": {"tippy", "targo-clippy", "trust-clippy"},
}

TAINTED_ENV_EXACT = {
    "BASH_ENV",
    "ENV",
    "PYTHONHOME",
    "PYTHONPATH",
    "LD_PRELOAD",
    "LD_LIBRARY_PATH",
    "DYLD_INSERT_LIBRARIES",
    "DYLD_LIBRARY_PATH",
    "DYLD_FRAMEWORK_PATH",
    "RUST_BOOTSTRAP_CONFIG",
    "BOOTSTRAP_RUSTC",
    "BOOTSTRAP_CARGO",
    "RUSTC",
    "RUSTDOC",
    "CARGO",
    "RUSTC_REAL",
    "RUSTDOC_REAL",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "RUSTC_WRAPPER_REAL",
    "RUSTC_SYSROOT",
    "RUSTC_ON_FAIL",
    "RUSTUP_TOOLCHAIN",
    "RUSTFLAGS",
    "RUSTDOCFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_ENCODED_RUSTDOCFLAGS",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTDOC",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
}


class Findings:
    def __init__(self) -> None:
        self.errors: list[str] = []
        self.notes: list[str] = []
        self.omitted_errors = 0
        self.omitted_notes = 0

    @staticmethod
    def clean(message: object) -> str:
        return str(message).replace("\t", " ").replace("\r", " ").replace("\n", " ")

    def error(self, message: object) -> None:
        if len(self.errors) < MAX_REPORTED_FINDINGS:
            self.errors.append(self.clean(message))
        else:
            self.omitted_errors += 1

    def note(self, message: object) -> None:
        if len(self.notes) < MAX_REPORTED_FINDINGS:
            self.notes.append(self.clean(message))
        else:
            self.omitted_notes += 1

    def emit(self, fingerprint: str | None = None) -> int:
        for message in self.notes:
            print(f"NOTE\t{message}")
        if self.omitted_notes:
            print(f"NOTE\t{self.omitted_notes} additional notes omitted by the output bound")
        for message in self.errors:
            print(f"ERROR\t{message}")
        if self.omitted_errors:
            print(f"ERROR\t{self.omitted_errors} additional errors omitted by the output bound")
        if fingerprint is not None:
            print(f"FINGERPRINT\t{fingerprint}")
        return 1 if self.errors or self.omitted_errors else 0


def inside(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def forbidden_tree(path: Path) -> bool:
    parts = [part.lower() for part in path.parts]
    if ".rustup" in parts:
        return True
    if any(part == "genesis-stage0" or part.startswith("genesis-stage0-") for part in parts):
        return True
    return any(part == "rustup" and "toolchains" in parts[i + 1 :] for i, part in enumerate(parts))


def executable_basename(path: Path) -> str:
    name = path.name.lower()
    return name[:-4] if name.endswith(".exe") else name


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_stage0(path: Path, findings: Findings) -> tuple[dict[str, str], list[tuple[str, str]]]:
    values: dict[str, str] = {}
    artifacts: list[tuple[str, str]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        findings.error(f"cannot read {path}: {error}")
        return values, artifacts

    for number, raw in enumerate(lines, 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if "=" not in line:
            findings.error(f"{path}:{number}: malformed stage0 record")
            continue
        key, value = line.split("=", 1)
        key = key.strip()
        value = value.strip()
        if key in values:
            findings.error(f"{path}:{number}: duplicate stage0 key {key!r}")
            continue
        values[key] = value
        if key.startswith("dist/") and key.endswith(".tar.xz"):
            artifacts.append((key, value))
    return values, artifacts


def validate_seed(root: Path, findings: Findings, fingerprint: hashlib._Hash) -> None:
    stage0_path = root / "src/stage0"
    version_path = root / "src/version"
    unsafe_metadata = False
    for path in (stage0_path, version_path):
        try:
            resolved_path = path.resolve(strict=True)
        except OSError:
            resolved_path = path
        if path.is_symlink() or not path.is_file() or not inside(resolved_path, root):
            findings.error(
                f"seed metadata is not a regular repository-owned file: {path.relative_to(root)}"
            )
            unsafe_metadata = True
    if unsafe_metadata:
        return
    values, artifacts = parse_stage0(stage0_path, findings)
    expected_server = "file://{trust-root}/bootstrap/trust-stage0"
    if values.get("dist_server") != expected_server:
        findings.error(
            "src/stage0 dist_server is not the authenticated repository-local Trust seed server"
        )
    for path in (stage0_path, version_path):
        fingerprint.update(str(path.relative_to(root)).encode())
        fingerprint.update(sha256_file(path).encode())

    try:
        source_text = version_path.read_text(encoding="utf-8").strip()
    except OSError as error:
        findings.error(f"cannot read {version_path}: {error}")
        return
    source_match = re.fullmatch(r"(\d+)\.(\d+)(?:\.\d+)?(?:[-+].*)?", source_text)
    seed_match = re.fullmatch(r"(\d+)\.(\d+)(?:\.\d+)?(?:[-+].*)?", values.get("compiler_version", ""))
    date = values.get("compiler_date", "")
    if source_match is None:
        findings.error("src/version is not a recognized semantic version")
    if seed_match is None:
        findings.error("src/stage0 has no valid compiler_version pin")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date):
        findings.error("src/stage0 has no valid compiler_date pin")

    if source_match and seed_match:
        source_major, source_minor = map(int, source_match.groups())
        seed_major, seed_minor = map(int, seed_match.groups())
        if seed_major != source_major or source_minor not in {seed_minor, seed_minor + 1}:
            findings.error(
                f"seed {values['compiler_version']} is not source-major/current-or-one-minor for {source_text}"
            )
        else:
            findings.note(f"seed {values['compiler_version']} is version-current for source {source_text}")

    date_prefix = f"dist/{date}/"
    dated_artifacts = [(key, digest) for key, digest in artifacts if key.startswith(date_prefix)]
    required_patterns = {
        "trustc": re.compile(rf"^{re.escape(date_prefix)}trustc-\d"),
        "targo": re.compile(rf"^{re.escape(date_prefix)}targo-\d"),
        "trust-std": re.compile(rf"^{re.escape(date_prefix)}trust-std-\d"),
    }
    for component, pattern in required_patterns.items():
        if not any(pattern.search(key) for key, _ in dated_artifacts):
            findings.error(f"src/stage0 does not pin a dated {component} seed payload")

    if not dated_artifacts:
        findings.error(f"src/stage0 has no seed payload pins under {date_prefix}")
    for relative, expected in dated_artifacts:
        if not re.fullmatch(r"[0-9a-f]{64}", expected):
            findings.error(f"{relative} has an invalid SHA-256 pin")
            continue
        # Artifact keys in src/stage0 are relative to dist_server, whose
        # checked-in value is bootstrap/trust-stage0 (not the repository root).
        lexical = root / "bootstrap/trust-stage0" / relative
        try:
            resolved = lexical.resolve(strict=True)
        except OSError as error:
            findings.error(f"missing pinned seed payload {relative}: {error}")
            continue
        if (
            lexical.is_symlink()
            or not lexical.is_file()
            or not inside(resolved, root / "bootstrap/trust-stage0")
        ):
            findings.error(f"pinned seed payload is not a regular repository-owned file: {relative}")
            continue
        actual = sha256_file(lexical)
        fingerprint.update(relative.encode())
        fingerprint.update(actual.encode())
        if actual != expected:
            findings.error(f"SHA-256 mismatch for pinned seed payload {relative}")

    manifest_hash = values.get("compiler_channel_manifest_hash", "")
    if date:
        manifest = root / f"bootstrap/trust-stage0/dist/{date}/channel-rust-trust.toml"
        if not re.fullmatch(r"[0-9a-f]{64}", manifest_hash):
            findings.error("src/stage0 has no valid compiler_channel_manifest_hash")
        elif not manifest.is_file() or manifest.is_symlink():
            findings.error(f"missing regular pinned channel manifest {manifest.relative_to(root)}")
        else:
            try:
                resolved_manifest = manifest.resolve(strict=True)
            except OSError as error:
                findings.error(f"cannot resolve pinned channel manifest: {error}")
                return
            if not inside(resolved_manifest, root / "bootstrap/trust-stage0"):
                findings.error("pinned channel manifest escapes the repository-local seed tree")
                return
            actual = sha256_file(manifest)
            fingerprint.update(str(manifest.relative_to(root)).encode())
            fingerprint.update(actual.encode())
            if actual != manifest_hash:
                findings.error("pinned channel manifest SHA-256 does not match src/stage0")


def walk_strings(value: object):
    if isinstance(value, dict):
        for child in value.values():
            yield from walk_strings(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk_strings(child)
    elif isinstance(value, str):
        yield value


def tool_value(document: dict[str, object], key: str) -> object | None:
    build = document.get("build")
    return build.get(key) if isinstance(build, dict) else None


def validate_tool_path(
    root: Path,
    config_path: Path,
    key: str,
    value: object,
    allowed_names: set[str] | None,
    findings: Findings,
    fingerprint: hashlib._Hash,
    cargo_config: bool,
) -> None:
    if not isinstance(value, str) or not value:
        findings.error(f"{config_path.name}: build.{key} must be one executable path string")
        return
    if "/" not in value and "\\" not in value:
        discovered = shutil.which(value, path=os.environ.get("PATH", ""))
        if discovered is None:
            findings.error(
                f"{config_path.name}: build.{key} command is not reachable on PATH: {value!r}"
            )
            return
        lexical = Path(discovered)
    else:
        lexical = Path(value).expanduser()
        if not lexical.is_absolute():
            # Cargo's ConfigRelativePath is relative to the config file that
            # defined the value, including recursively included files.
            # Bootstrap's raw PathBuf values execute from the checkout root.
            lexical = (config_path.parent if cargo_config else root) / lexical
    try:
        resolved = lexical.resolve(strict=True)
    except OSError as error:
        findings.error(f"{config_path.name}: build.{key} path is missing: {error}")
        return
    name = executable_basename(resolved)
    if forbidden_tree(lexical) or forbidden_tree(resolved):
        findings.error(f"{config_path.name}: build.{key} resolves through rustup/genesis-stage0")
    if not inside(resolved, root):
        findings.error(f"{config_path.name}: build.{key} is outside the authenticated checkout")
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        findings.error(f"{config_path.name}: build.{key} is not a regular executable")
    else:
        # Config content alone does not detect replacement of the executable
        # named by that content.  Bind the pre/post fingerprint to the bytes.
        fingerprint.update(f"configured-tool:{key}:{resolved}".encode())
        try:
            fingerprint.update(sha256_file(resolved).encode())
        except OSError as error:
            findings.error(f"{config_path.name}: cannot hash build.{key}: {error}")
    if allowed_names is not None and name not in allowed_names:
        findings.error(
            f"{config_path.name}: build.{key} resolves to {name!r}, not an expected Trust frontend"
        )


def validate_config_file(
    root: Path,
    path: Path,
    findings: Findings,
    fingerprint: hashlib._Hash,
    cargo_config: bool = False,
    stack: tuple[Path, ...] = (),
) -> None:
    if not os.path.lexists(path):
        return
    if path.is_symlink() or not path.is_file():
        findings.error(f"configuration is not a regular repository-owned file: {path}")
        return
    resolved_path = path.resolve()
    if not inside(resolved_path, root):
        findings.error(f"configuration include escapes the authenticated checkout: {path}")
        return
    if resolved_path in stack:
        findings.error(f"cyclic configuration include: {path.relative_to(root)}")
        return
    if tomllib is None:
        findings.error("Python 3.11+ tomllib is required to parse configuration without grep ambiguity")
        return
    try:
        size = path.stat().st_size
    except OSError as error:
        findings.error(f"cannot stat {path.relative_to(root)}: {error}")
        return
    if size > MAX_CONFIG_BYTES:
        findings.error(
            f"configuration exceeds the {MAX_CONFIG_BYTES}-byte parser bound: "
            f"{path.relative_to(root)}"
        )
        return
    raw = path.read_bytes()
    fingerprint.update(str(path.relative_to(root)).encode())
    fingerprint.update(hashlib.sha256(raw).digest())
    try:
        document = tomllib.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        findings.error(f"cannot parse {path.relative_to(root)}: {error}")
        return

    for value in walk_strings(document):
        candidate = Path(value).expanduser()
        if forbidden_tree(candidate):
            findings.error(f"{path.relative_to(root)} contains a rustup/genesis-stage0 reference")
            break

    download = document.get("rust")
    if isinstance(download, dict):
        setting = download.get("download-rustc", False)
        if setting is not False and setting is not None:
            findings.error(f"{path.relative_to(root)} enables an upstream rustc download")

    if cargo_config:
        selectors = {
            "rustc": PRIMARY_TOOLS["rustc"],
            "rustdoc": PRIMARY_TOOLS["rustdoc"],
            "rustc-wrapper": None,
            "rustc-workspace-wrapper": None,
        }
    else:
        selectors = PRIMARY_TOOLS
    for key, allowed in selectors.items():
        value = tool_value(document, key)
        if value is not None:
            validate_tool_path(
                root,
                path,
                key,
                value,
                allowed,
                findings,
                fingerprint,
                cargo_config,
            )

    if "include" in document:
        includes = document["include"]
        parsed_includes: list[tuple[str, bool]] = []
        if not isinstance(includes, list):
            findings.error(f"{path.relative_to(root)}: include must be a list")
        else:
            for index, item in enumerate(includes):
                if isinstance(item, str):
                    parsed_includes.append((item, False))
                elif cargo_config and isinstance(item, dict):
                    include = item.get("path")
                    optional = item.get("optional", False)
                    if not isinstance(include, str) or not isinstance(optional, bool):
                        findings.error(
                            f"{path.relative_to(root)}: include[{index}] requires a string "
                            "path and optional boolean"
                        )
                    else:
                        parsed_includes.append((include, optional))
                else:
                    qualifier = "strings or path tables" if cargo_config else "path strings"
                    findings.error(
                        f"{path.relative_to(root)}: include[{index}] must contain {qualifier}"
                    )
            for include, optional in parsed_includes:
                include_path = Path(include).expanduser()
                if not include_path.is_absolute():
                    include_path = path.parent / include_path
                if not os.path.lexists(include_path):
                    fingerprint.update(f"missing-include:{include_path}".encode())
                    if not (cargo_config and optional):
                        findings.error(
                            f"{path.relative_to(root)} includes missing configuration {include!r}"
                        )
                else:
                    validate_config_file(
                        root,
                        include_path,
                        findings,
                        fingerprint,
                        cargo_config=cargo_config,
                        stack=stack + (resolved_path,),
                    )

    profile = document.get("profile")
    if not cargo_config and isinstance(profile, str):
        profile_name = "dist" if profile == "user" else profile
        profile_path = root / f"src/bootstrap/defaults/bootstrap.{profile_name}.toml"
        if not profile_path.is_file() or profile_path.is_symlink():
            findings.error(f"{path.relative_to(root)} selects missing/unsafe profile {profile!r}")
        else:
            validate_config_file(
                root,
                profile_path,
                findings,
                fingerprint,
                stack=stack + (resolved_path,),
            )


def validate_configs(root: Path, findings: Findings, fingerprint: hashlib._Hash) -> None:
    for relative in ("bootstrap.toml", "config.toml"):
        validate_config_file(root, root / relative, findings, fingerprint)
    for relative in (".cargo/config.toml", ".cargo/config", "library/.cargo/config.toml", "library/.cargo/config"):
        validate_config_file(root, root / relative, findings, fingerprint, cargo_config=True)

    # Cargo discovers .cargo/config{,.toml} while walking every ancestor of its
    # current directory.  The audited build runs from `root`, so an unchecked
    # config in root.parent could otherwise select a compiler or wrapper after
    # the repository preflight had passed.  The private CARGO_HOME supplied to
    # the build covers Cargo's separate home-directory lookup.
    for ancestor in root.parents:
        for relative in (".cargo/config.toml", ".cargo/config"):
            candidate = ancestor / relative
            fingerprint.update(f"cargo-ancestor:{candidate}:".encode())
            if os.path.lexists(candidate):
                fingerprint.update(b"present")
                findings.error(
                    "Cargo would discover configuration outside the authenticated checkout: "
                    f"{candidate}"
                )
            else:
                fingerprint.update(b"missing")


def validate_environment(findings: Findings) -> None:
    tainted = []
    for name, value in os.environ.items():
        if not value:
            continue
        dynamic = bool(
            re.fullmatch(r"CARGO_TARGET_.+_(?:RUNNER|RUSTFLAGS|RUSTDOCFLAGS|RUSTC|RUSTDOC)", name)
        )
        if name in TAINTED_ENV_EXACT or dynamic:
            tainted.append(name)
    if tainted:
        findings.error(
            "inherited compiler/wrapper/startup environment is set: " + ", ".join(sorted(tainted))
        )
    if os.environ.get("CARGO_HOME") or os.environ.get("RUSTUP_HOME"):
        findings.note("CARGO_HOME/RUSTUP_HOME will be replaced with owner-private empty directories")


def validate_path(root: Path, findings: Findings, fingerprint: hashlib._Hash) -> None:
    raw_path = os.environ.get("PATH", "")
    if not raw_path:
        findings.error("PATH is empty")
        return
    seen: set[Path] = set()
    for item in raw_path.split(os.pathsep):
        if not item:
            findings.error("PATH contains an empty component (the current directory)")
            continue
        lexical_dir = Path(item).expanduser()
        try:
            directory = lexical_dir.resolve(strict=True)
        except OSError as error:
            findings.error(f"PATH component cannot be resolved: {item!r}: {error}")
            continue
        if directory in seen:
            continue
        seen.add(directory)
        if not directory.is_dir():
            findings.error(f"PATH component is not a directory: {item!r}")
            continue
        if forbidden_tree(lexical_dir) or forbidden_tree(directory):
            findings.error(f"PATH component resolves through rustup/genesis-stage0: {item!r}")
        fingerprint.update(str(directory).encode())
        try:
            directory_stat = directory.stat()
            fingerprint.update(
                f"{directory_stat.st_dev}:{directory_stat.st_ino}:"
                f"{directory_stat.st_mode}:{directory_stat.st_mtime_ns}".encode()
            )
        except OSError as error:
            findings.error(f"cannot stat PATH component {item!r}: {error}")
            continue
        for name in sorted(RUST_FAMILY_NAMES):
            for suffix in ("", ".exe"):
                candidate = directory / f"{name}{suffix}"
                if not os.path.lexists(candidate):
                    continue
                try:
                    resolved = candidate.resolve(strict=True)
                    candidate_stat = resolved.stat()
                except OSError as error:
                    findings.error(f"Rust-family PATH entry cannot be canonicalized: {candidate}: {error}")
                    continue
                if not stat.S_ISREG(candidate_stat.st_mode) or not os.access(resolved, os.X_OK):
                    continue
                fingerprint.update(str(candidate).encode())
                fingerprint.update(
                    f"{resolved}:{candidate_stat.st_dev}:{candidate_stat.st_ino}:{candidate_stat.st_size}:{candidate_stat.st_mtime_ns}".encode()
                )
                try:
                    fingerprint.update(sha256_file(resolved).encode())
                except OSError as error:
                    findings.error(f"cannot hash Rust-family PATH entry {candidate}: {error}")
                if name in STOCK_NAMES:
                    findings.error(f"stock-Rust command name is reachable on PATH: {candidate}")
                elif forbidden_tree(candidate) or forbidden_tree(resolved):
                    findings.error(f"Trust-named PATH entry resolves into rustup/genesis-stage0: {candidate}")
                elif not inside(resolved, root):
                    findings.error(f"unauthenticated Trust-named executable is reachable on PATH: {candidate}")
                elif executable_basename(resolved) not in TRUST_NAMES:
                    findings.error(
                        f"Trust-named PATH entry resolves to a non-Trust executable name: {candidate}"
                    )


def preflight(root_arg: str) -> int:
    findings = Findings()
    root = Path(root_arg).resolve()
    fingerprint = hashlib.sha256()
    if not (root / "x.py").is_file():
        findings.error(f"not a Trust checkout: {root}")
    for relative in (
        "x.py",
        "scripts/prove_rust_free_build.sh",
        "scripts/off_stock_rust_audit.py",
    ):
        path = root / relative
        try:
            resolved_path = path.resolve(strict=True)
        except OSError:
            resolved_path = path
        if path.is_symlink() or not path.is_file() or not inside(resolved_path, root):
            findings.error(f"security-relevant gate input is missing or symlinked: {relative}")
        else:
            fingerprint.update(relative.encode())
            fingerprint.update(sha256_file(path).encode())
    validate_environment(findings)
    validate_seed(root, findings, fingerprint)
    validate_configs(root, findings, fingerprint)
    validate_path(root, findings, fingerprint)
    if not findings.errors:
        findings.note("seed payloads, configuration, environment, and PATH passed static validation")
    return findings.emit(fingerprint.hexdigest())


EXEC_RE = re.compile(r"\b(execve|execveat)\(")
EXEC_PREFIX_RE = re.compile(r"^\s*(?:(?:\[pid\s+\d+\]|\d+)\s+)?(execve|execveat)\(")
EXEC_RESULT_DELIMITER_RE = re.compile(r"\)\s+=\s+")
EXEC_RESULT_SUFFIX_RE = re.compile(
    r"(-?\d+)(?:\s+[A-Z][A-Z0-9_]*(?:\s+\([A-Za-z0-9 _.,:/+'-]*\))?)?\s*$"
)


def parse_exec_path(line: str) -> tuple[str | None, str | None]:
    if re.search(r"(?:execve|execveat).*<unfinished \.\.\.>", line) or re.search(
        r"<\.\.\. (?:execve|execveat) resumed>", line
    ):
        return None, "unfinished/resumed exec event cannot be authenticated"
    match = EXEC_PREFIX_RE.match(line)
    if match is None:
        if EXEC_RE.search(line):
            return None, "malformed/interleaved exec event cannot be authenticated"
        return None, None
    if len(EXEC_RE.findall(line)) != 1:
        return None, "multiple/interleaved exec events cannot be authenticated"
    # Failed PATH probes do not execute code.  Successful events must be fully
    # understood; ambiguous/resumed/relative/fd-only events fail closed.
    # Anchor to strace's terminal syscall result.  Searching the whole record
    # lets attacker-controlled argv text such as "= -1 ENOENT" disguise a
    # successful exec as a failed PATH probe.
    delimiters = list(EXEC_RESULT_DELIMITER_RE.finditer(line))
    result = (
        EXEC_RESULT_SUFFIX_RE.fullmatch(line[delimiters[-1].end() :]) if delimiters else None
    )
    if result is None:
        return None, f"successful/failed {match.group(1)} result is missing or truncated"
    if result.group(1) != "0":
        return None, None
    call = match.group(1)
    tail = line[match.end() :]
    strings = re.findall(r'"(?:[^"\\]|\\.)*"', tail)
    # execve's first argument and execveat's second argument are both the
    # first quoted string in strace output (dirfd is rendered unquoted).
    index = 0
    if len(strings) <= index:
        return None, f"cannot parse successful {call} event"
    try:
        path = ast.literal_eval(strings[index])
    except (SyntaxError, ValueError):
        return None, f"cannot decode successful {call} path"
    if not isinstance(path, str) or not path:
        return None, f"successful {call} used an empty/fd-only path"
    return path, None


def files_are_same_artifact(left: Path, right: Path, digest_cache: dict[tuple[int, int, int, int], str]) -> bool:
    try:
        left_stat = left.stat()
        right_stat = right.stat()
    except OSError:
        return False
    if not stat.S_ISREG(left_stat.st_mode) or not stat.S_ISREG(right_stat.st_mode):
        return False
    if (left_stat.st_dev, left_stat.st_ino) == (right_stat.st_dev, right_stat.st_ino):
        return True
    if left_stat.st_size != right_stat.st_size:
        return False

    def digest(path: Path, metadata: os.stat_result) -> str:
        key = (metadata.st_dev, metadata.st_ino, metadata.st_size, metadata.st_mtime_ns)
        if key not in digest_cache:
            digest_cache[key] = sha256_file(path)
        return digest_cache[key]

    try:
        return digest(left, left_stat) == digest(right, right_stat)
    except OSError:
        return False


def stock_alias_is_authenticated(
    lexical: Path,
    resolved: Path,
    stock_name: str,
    approved_roots: tuple[Path, ...],
    digest_cache: dict[tuple[int, int, int, int], str],
) -> bool:
    aliases = STOCK_ALIAS_TARGETS.get(stock_name)
    if aliases is None:
        return False
    # A stock spelling may be a symlink (lexical directory) or the canonical
    # file itself (resolved directory).  In either case its sibling Trust name
    # must resolve within the same approved policy root and have identical
    # bytes/inode identity.
    directories = []
    if executable_basename(lexical) == stock_name:
        directories.append(lexical.parent)
    if executable_basename(resolved) == stock_name and resolved.parent not in directories:
        directories.append(resolved.parent)
    for directory in directories:
        for alias in aliases:
            candidate = directory / alias
            try:
                candidate_resolved = candidate.resolve(strict=True)
            except OSError:
                continue
            if (
                any(inside(candidate_resolved, approved) for approved in approved_roots)
                and not forbidden_tree(candidate_resolved)
                and os.access(candidate_resolved, os.X_OK)
                and files_are_same_artifact(resolved, candidate_resolved, digest_cache)
            ):
                return True
    return False


def trace_audit(root_arg: str, build_root_arg: str, trace_arg: str) -> int:
    findings = Findings()
    root = Path(root_arg).resolve()
    build_root = Path(build_root_arg).resolve()
    trace = Path(trace_arg)
    if not inside(build_root, root / "build"):
        findings.error("audited build root is outside the checkout build directory")
        return findings.emit()
    if trace.is_symlink() or not trace.is_file():
        findings.error("exec trace is missing or is not a regular file")
        return findings.emit()
    try:
        trace_size = trace.stat().st_size
    except OSError as error:
        findings.error(f"cannot stat exec trace: {error}")
        return findings.emit()
    if trace_size > MAX_TRACE_BYTES:
        findings.error(f"exec trace exceeds the {MAX_TRACE_BYTES}-byte parser bound")
        return findings.emit()

    event_count = 0
    trustc_count = 0
    targo_count = 0
    digest_cache: dict[tuple[int, int, int, int], str] = {}
    approved_roots = (root, build_root)
    try:
        stream = trace.open("rb", buffering=0)
    except OSError as error:
        findings.error(f"cannot read exec trace: {error}")
        return findings.emit()
    with stream:
        number = 0
        while True:
            raw_line = stream.readline(MAX_TRACE_LINE_BYTES + 1)
            if not raw_line:
                break
            number += 1
            if len(raw_line) > MAX_TRACE_LINE_BYTES:
                findings.error(
                    f"trace line {number}: record exceeds the {MAX_TRACE_LINE_BYTES}-byte bound"
                )
                return findings.emit()
            try:
                line = raw_line.decode("utf-8", errors="strict").rstrip("\r\n")
            except UnicodeError as error:
                findings.error(f"trace line {number}: invalid UTF-8: {error}")
                continue
            path_text, error = parse_exec_path(line)
            if error:
                findings.error(f"trace line {number}: {error}")
                continue
            if path_text is None:
                continue
            event_count += 1
            lexical = Path(path_text)
            if not lexical.is_absolute():
                findings.error(
                    f"trace line {number}: relative exec path cannot be canonicalized: {path_text!r}"
                )
                continue
            try:
                resolved = lexical.resolve(strict=True)
                metadata = resolved.stat()
            except OSError as error:
                findings.error(
                    f"trace line {number}: executed path cannot be authenticated after build: {error}"
                )
                continue
            if not stat.S_ISREG(metadata.st_mode) or not os.access(resolved, os.X_OK):
                findings.error(f"trace line {number}: executed path is no longer a regular executable")
                continue
            if forbidden_tree(lexical) or forbidden_tree(resolved):
                findings.error(f"trace line {number}: executed rustup/genesis-stage0 path: {path_text}")
                continue
            lexical_name = executable_basename(lexical)
            resolved_name = executable_basename(resolved)
            names = {lexical_name, resolved_name}
            approved = any(inside(resolved, approved_root) for approved_root in approved_roots)
            for stock_name in sorted(names & STOCK_NAMES):
                if not approved:
                    findings.error(
                        f"trace line {number}: executed external stock-Rust command name: {path_text}"
                    )
                elif not stock_alias_is_authenticated(
                    lexical, resolved, stock_name, approved_roots, digest_cache
                ):
                    findings.error(
                        f"trace line {number}: stock-compatible {stock_name} is not the same "
                        f"artifact as a sibling Trust frontend: {path_text}"
                    )
            if names & TRUST_NAMES and not approved:
                findings.error(
                    f"trace line {number}: executed unauthenticated external Trust frontend: {path_text}"
                )
            if "trustc" in names and approved:
                trustc_count += 1
            if ("targo" in names or "tcargo" in names) and approved:
                targo_count += 1

    if event_count == 0:
        findings.error("exec trace contains no successful exec events")
    if trustc_count == 0:
        findings.error("exec trace contains no authenticated Trust compiler execution")
    if targo_count == 0:
        findings.error("exec trace contains no authenticated Targo execution")
    if not findings.errors:
        findings.note(
            f"exec trace authenticated {event_count} successful execs ({trustc_count} trustc, {targo_count} targo)"
        )
    return findings.emit()


def stage2_output(root_arg: str, build_root_arg: str) -> int:
    findings = Findings()
    root = Path(root_arg).resolve()
    build_root = Path(build_root_arg).resolve()
    candidates = []
    if build_root.is_dir() and inside(build_root, root / "build"):
        candidates = list(build_root.glob("*/stage2/bin/trustc")) + list(
            build_root.glob("*/stage2/bin/trustc.exe")
        )
    valid: list[Path] = []
    for candidate in candidates:
        if candidate.is_symlink():
            continue
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            continue
        if (
            inside(resolved, build_root)
            and not forbidden_tree(resolved)
            and resolved.is_file()
            and os.access(resolved, os.X_OK)
        ):
            valid.append(resolved)
    if len(valid) != 1:
        findings.error(f"expected exactly one fresh stage2 trustc, found {len(valid)}")
    else:
        findings.note(f"fresh stage2 compiler output: {valid[0]}")
    return findings.emit()


def make_audit_dir(parent_arg: str) -> int:
    lexical_parent = Path(parent_arg)
    if lexical_parent.is_symlink():
        print("ERROR: audit parent must not be a symlink", file=sys.stderr)
        return 1
    lexical_parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    parent = lexical_parent.resolve()
    try:
        parent_stat = parent.stat()
    except OSError as error:
        print(f"ERROR: cannot authenticate audit parent: {error}", file=sys.stderr)
        return 1
    if (
        not stat.S_ISDIR(parent_stat.st_mode)
        or parent_stat.st_uid != os.getuid()
        or stat.S_IMODE(parent_stat.st_mode) & 0o022
    ):
        print("ERROR: audit parent must be owner-controlled and not group/world-writable", file=sys.stderr)
        return 1
    directory = Path(tempfile.mkdtemp(prefix="off-stock-audit.", dir=parent))
    os.chmod(directory, 0o700)
    for child in ("home", "tmp", "cargo-home", "rustup-home", "xdg-config"):
        (directory / child).mkdir(mode=0o700)
    trace = directory / "exec.trace"
    descriptor = os.open(trace, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    os.close(descriptor)
    os.mkfifo(directory / "exec.trace.pipe", 0o600)
    print(directory)
    return 0


def file_identity(path_arg: str) -> int:
    path = Path(path_arg)
    if path.is_symlink() or not path.is_file():
        return 1
    metadata = path.stat()
    if metadata.st_uid != os.getuid() or stat.S_IMODE(metadata.st_mode) != 0o600:
        return 1
    print(f"{metadata.st_dev}:{metadata.st_ino}:{metadata.st_uid}:{stat.S_IMODE(metadata.st_mode):o}")
    return 0


def executable_identity(path_arg: str) -> int:
    path = Path(path_arg)
    if path.is_symlink() or not path.is_file() or not os.access(path, os.X_OK):
        return 1
    try:
        metadata = path.stat()
        digest = sha256_file(path)
    except OSError:
        return 1
    if not stat.S_ISREG(metadata.st_mode):
        return 1
    print(
        f"{metadata.st_dev}:{metadata.st_ino}:{metadata.st_uid}:"
        f"{stat.S_IMODE(metadata.st_mode):o}:{metadata.st_size}:{metadata.st_mtime_ns}:{digest}"
    )
    return 0


def collect_trace(
    pipe_arg: str, output_arg: str, limit_arg: str, ready_arg: str | None = None
) -> int:
    pipe = Path(pipe_arg)
    output = Path(output_arg)
    try:
        limit = int(limit_arg)
    except ValueError:
        print("ERROR: invalid trace byte limit", file=sys.stderr)
        return 2
    if limit <= 0 or pipe.is_symlink() or output.is_symlink():
        print("ERROR: unsafe trace collector inputs", file=sys.stderr)
        return 2
    try:
        pipe_stat = pipe.stat()
        output_stat = output.stat()
    except OSError as error:
        print(f"ERROR: cannot authenticate trace collector inputs: {error}", file=sys.stderr)
        return 1
    if not stat.S_ISFIFO(pipe_stat.st_mode) or not stat.S_ISREG(output_stat.st_mode):
        print("ERROR: trace collector requires a FIFO and regular output", file=sys.stderr)
        return 1
    if (
        pipe_stat.st_uid != os.getuid()
        or output_stat.st_uid != os.getuid()
        or stat.S_IMODE(pipe_stat.st_mode) != 0o600
        or stat.S_IMODE(output_stat.st_mode) != 0o600
    ):
        print("ERROR: trace collector inputs must be owner-private", file=sys.stderr)
        return 1
    if output_stat.st_size != 0:
        print("ERROR: pre-created trace output is not empty", file=sys.stderr)
        return 1

    total = 0
    exceeded = False
    try:
        nofollow = getattr(os, "O_NOFOLLOW", 0)
        source_fd = os.open(pipe, os.O_RDONLY | nofollow)
        destination_fd = os.open(output, os.O_WRONLY | nofollow)
        source_stat = os.fstat(source_fd)
        destination_stat = os.fstat(destination_fd)
        if (
            (source_stat.st_dev, source_stat.st_ino) != (pipe_stat.st_dev, pipe_stat.st_ino)
            or (destination_stat.st_dev, destination_stat.st_ino)
            != (output_stat.st_dev, output_stat.st_ino)
            or not stat.S_ISFIFO(source_stat.st_mode)
            or not stat.S_ISREG(destination_stat.st_mode)
        ):
            os.close(source_fd)
            os.close(destination_fd)
            print("ERROR: trace collector inputs changed before open", file=sys.stderr)
            return 1
        os.ftruncate(destination_fd, 0)
        with os.fdopen(source_fd, "rb", buffering=0) as source, os.fdopen(
            destination_fd, "wb", buffering=0
        ) as destination:
            if ready_arg is not None:
                ready = Path(ready_arg)
                if ready.is_symlink() or os.path.lexists(ready):
                    print("ERROR: unsafe trace collector readiness path", file=sys.stderr)
                    return 1
                ready_fd = os.open(
                    ready,
                    os.O_WRONLY | os.O_CREAT | os.O_EXCL | nofollow,
                    0o600,
                )
                os.write(ready_fd, b"ready\n")
                os.fsync(ready_fd)
                os.close(ready_fd)
            while True:
                chunk = source.read(1024 * 1024)
                if not chunk:
                    break
                remaining = max(0, limit - total)
                if remaining:
                    destination.write(chunk[:remaining])
                total += len(chunk)
                if total > limit:
                    exceeded = True
            destination.flush()
            os.fsync(destination.fileno())
    except OSError as error:
        print(f"ERROR: bounded trace collection failed: {error}", file=sys.stderr)
        return 1
    if exceeded:
        print(f"ERROR: exec trace exceeded the {limit}-byte limit", file=sys.stderr)
        return 1
    return 0


def wait_ready(path_arg: str, pid_arg: str, timeout_ms_arg: str) -> int:
    path = Path(path_arg)
    try:
        pid = int(pid_arg)
        timeout_ms = int(timeout_ms_arg)
    except ValueError:
        print("ERROR: invalid collector readiness arguments", file=sys.stderr)
        return 2
    if pid <= 0 or timeout_ms <= 0 or timeout_ms > 60_000:
        print("ERROR: collector readiness arguments are out of bounds", file=sys.stderr)
        return 2
    deadline = time.monotonic() + timeout_ms / 1000
    while time.monotonic() < deadline:
        try:
            metadata = path.stat()
        except FileNotFoundError:
            pass
        except OSError as error:
            print(f"ERROR: cannot inspect collector readiness: {error}", file=sys.stderr)
            return 1
        else:
            if (
                not path.is_symlink()
                and stat.S_ISREG(metadata.st_mode)
                and metadata.st_uid == os.getuid()
                and stat.S_IMODE(metadata.st_mode) == 0o600
                and metadata.st_size == len(b"ready\n")
            ):
                return 0
            print("ERROR: collector readiness marker is not owner-private", file=sys.stderr)
            return 1
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            print("ERROR: trace collector exited before becoming ready", file=sys.stderr)
            return 1
        except PermissionError:
            print("ERROR: cannot authenticate trace collector process", file=sys.stderr)
            return 1
        time.sleep(0.01)
    print("ERROR: timed out waiting for trace collector readiness", file=sys.stderr)
    return 1


def usage() -> int:
    print(
        "usage: off_stock_rust_audit.py "
        "preflight ROOT | trace ROOT BUILD_ROOT TRACE | stage2-output ROOT BUILD_ROOT | "
        "make-audit-dir PARENT | file-identity PATH | executable-identity PATH | "
        "collect-trace FIFO OUTPUT LIMIT [READY] | wait-ready READY PID TIMEOUT_MS",
        file=sys.stderr,
    )
    return 2


def main(argv: list[str]) -> int:
    if len(argv) == 3 and argv[1] == "preflight":
        return preflight(argv[2])
    if len(argv) == 5 and argv[1] == "trace":
        return trace_audit(argv[2], argv[3], argv[4])
    if len(argv) == 4 and argv[1] == "stage2-output":
        return stage2_output(argv[2], argv[3])
    if len(argv) == 3 and argv[1] == "make-audit-dir":
        return make_audit_dir(argv[2])
    if len(argv) == 3 and argv[1] == "file-identity":
        return file_identity(argv[2])
    if len(argv) == 3 and argv[1] == "executable-identity":
        return executable_identity(argv[2])
    if len(argv) in {5, 6} and argv[1] == "collect-trace":
        ready = argv[5] if len(argv) == 6 else None
        return collect_trace(argv[2], argv[3], argv[4], ready)
    if len(argv) == 5 and argv[1] == "wait-ready":
        return wait_ready(argv[2], argv[3], argv[4])
    return usage()


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
