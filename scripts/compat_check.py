#!/usr/bin/env -S python3 -I -S -E
"""Run a receipt-bound crates.io native compatibility corpus.

This gate intentionally exercises Targo's explicit unverified compatibility
lane. It does not relabel native proc-macro compilation as verified proof.
Every dependency graph is locked, fetched, described offline, and then built
offline with an isolated target/home/temp environment. Each generated fixture
has an empty ``main`` and one dependency, so the gate proves compilation of the
resolved graph; it does not prove that every proc macro in that graph was
invoked. The JSON receipt binds the exact source commit, Stage2 provenance
receipt, tools, corpus, lockfiles, resolved package checksums, commands, and
output digests.

This Python/shell runner is deliberately diagnostic-only: Python startup occurs
before repository code can authenticate or scrub the interpreter. A complete
run may replace the complete diagnostic receipt; it is never release-gate
authority. Every other outcome is retained as an adjacent non-passing attempt.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import errno
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from typing import Any


RECEIPT_SCHEMA = "trust.crates-io-native-compatibility-diagnostic.v2"
CORPUS_SCHEMA = "trust.crates-io-corpus.v1"
PROVENANCE_SCHEMA = "trust.stage-tool-provenance.v2"
CRATE_NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")
COMPILER_COMMIT_RE = re.compile(r"^commit-hash:\s*([0-9a-f]{40})$", re.MULTILINE)
HOST_TRIPLE_RE = re.compile(r"^[A-Za-z0-9_.-]+$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
SYSTEM_GIT_CANDIDATES = (Path("/usr/bin/git"), Path("/bin/git"))
MAX_LOCAL_EXCLUDE_BYTES = 64 * 1024
MAX_GIT_STREAM_BYTES = 64 * 1024 * 1024
GIT_TIMEOUT_SECONDS = 30.0


class GateError(RuntimeError):
    """A fail-closed preflight or corpus error."""


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run_text(
    argv: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
) -> str:
    completed = subprocess.run(
        argv,
        cwd=cwd,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        detail = "\n".join(
            part
            for part in (
                completed.stdout.decode("utf-8", "replace").strip(),
                completed.stderr.decode("utf-8", "replace").strip(),
            )
            if part
        )
        raise GateError(f"command failed ({completed.returncode}): {' '.join(argv)}: {detail}")
    return completed.stdout.decode("utf-8", "replace").strip()


def strict_json_loads(raw: str | bytes, label: str) -> Any:
    """Parse JSON while rejecting duplicate object keys at every depth."""

    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise GateError(f"{label} contains duplicate object key {key!r}")
            result[key] = value
        return result

    try:
        return json.loads(raw, object_pairs_hook=unique_object)
    except (json.JSONDecodeError, UnicodeDecodeError) as error:
        raise GateError(f"{label} is not strict JSON: {error}") from error


def controlled_git_executable() -> Path:
    for candidate in SYSTEM_GIT_CANDIDATES:
        try:
            info = candidate.stat()
        except OSError:
            continue
        if stat.S_ISREG(info.st_mode) and info.st_mode & 0o111:
            resolved = candidate.resolve(strict=True)
            resolved_info = resolved.stat()
            if resolved.is_absolute() and stat.S_ISREG(resolved_info.st_mode) and resolved_info.st_mode & 0o111:
                return resolved
    raise GateError("no controlled Git executable exists at /usr/bin/git or /bin/git")


def provenance_git_environment() -> dict[str, str]:
    """Return a closed, fixed Git environment with no caller-selected authority."""

    return {
        "LC_ALL": "C",
        "LANG": "C",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_SYSTEM": os.devnull,
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_NO_LAZY_FETCH": "1",
        "GIT_ATTR_NOSYSTEM": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_TERMINAL_PROMPT": "0",
    }


def controlled_git_argv(
    root: Path, *args: str, pathspec_mode: str = "literal"
) -> list[str]:
    root = root.resolve(strict=True)
    marker = root / ".git"
    try:
        marker_info = marker.lstat()
    except OSError as error:
        raise GateError(f"source root has no exact Git marker {marker}: {error}") from error
    if stat.S_ISLNK(marker_info.st_mode) or not (
        stat.S_ISDIR(marker_info.st_mode) or stat.S_ISREG(marker_info.st_mode)
    ):
        raise GateError(f"source Git marker is a symlink or unsupported file: {marker}")
    if stat.S_ISDIR(marker_info.st_mode):
        git_dir = marker.resolve(strict=True)
    else:
        if marker_info.st_size > 4096:
            raise GateError(f"source Git marker file is too large: {marker}")
        try:
            marker_text = marker.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise GateError(f"could not read source Git marker {marker}: {error}") from error
        if not marker_text.endswith("\n") or marker_text.count("\n") != 1:
            raise GateError(f"source Git marker is not one canonical gitdir record: {marker}")
        git_dir_text = marker_text.removesuffix("\n").removeprefix("gitdir: ")
        if not git_dir_text or f"gitdir: {git_dir_text}\n" != marker_text:
            raise GateError(f"source Git marker has invalid gitdir syntax: {marker}")
        git_dir_path = Path(git_dir_text)
        git_dir = (
            git_dir_path if git_dir_path.is_absolute() else root / git_dir_path
        ).resolve(strict=True)
    if not git_dir.is_dir():
        raise GateError(f"source Git directory is not a directory: {git_dir}")
    pathspec_flag = {
        "literal": "--literal-pathspecs",
        "glob": "--glob-pathspecs",
        "explicit-magic": "--noglob-pathspecs",
    }.get(pathspec_mode)
    if pathspec_flag is None:
        raise GateError(f"unsupported controlled Git pathspec mode: {pathspec_mode}")
    return [
        str(controlled_git_executable()),
        "--no-pager",
        pathspec_flag,
        "--git-dir",
        str(git_dir),
        "--work-tree",
        str(root),
        "-c",
        "core.bare=false",
        "-c",
        f"core.worktree={root}",
        "-c",
        "core.fsmonitor=false",
        "-c",
        "core.untrackedCache=false",
        "-c",
        "core.trustctime=true",
        "-c",
        "core.checkStat=default",
        "-c",
        "core.ignoreStat=false",
        "-c",
        "core.autocrlf=false",
        "-c",
        "core.eol=lf",
        "-c",
        "core.safecrlf=true",
        "-c",
        "core.ignoreCase=false",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "core.filemode=true",
        "-c",
        "core.symlinks=true",
        "-c",
        "core.sparseCheckout=false",
        "-c",
        "core.excludesFile=/dev/null",
        "-c",
        "core.attributesFile=/dev/null",
        "-c",
        "core.quotePath=true",
        "-c",
        "color.ui=false",
        "-c",
        "status.showUntrackedFiles=all",
        "-C",
        str(root),
        *args,
    ]


def controlled_git_bytes(
    root: Path, *args: str, pathspec_mode: str = "literal"
) -> bytes:
    argv = controlled_git_argv(root, *args, pathspec_mode=pathspec_mode)
    with tempfile.TemporaryFile() as stdout_file, tempfile.TemporaryFile() as stderr_file:
        process = subprocess.Popen(
            argv,
            cwd=root,
            env=provenance_git_environment(),
            stdin=subprocess.DEVNULL,
            stdout=stdout_file,
            stderr=stderr_file,
            start_new_session=(os.name == "posix"),
        )
        deadline = time.monotonic() + GIT_TIMEOUT_SECONDS
        while process.poll() is None:
            if (
                os.fstat(stdout_file.fileno()).st_size > MAX_GIT_STREAM_BYTES
                or os.fstat(stderr_file.fileno()).st_size > MAX_GIT_STREAM_BYTES
            ):
                if os.name == "posix":
                    os.killpg(process.pid, signal.SIGKILL)
                else:
                    process.kill()
                process.wait()
                raise GateError(
                    f"controlled Git {' '.join(args)} exceeded the bounded output limit"
                )
            if time.monotonic() >= deadline:
                if os.name == "posix":
                    os.killpg(process.pid, signal.SIGKILL)
                else:
                    process.kill()
                process.wait()
                raise GateError(f"controlled Git {' '.join(args)} timed out")
            time.sleep(0.005)
        if (
            os.fstat(stdout_file.fileno()).st_size > MAX_GIT_STREAM_BYTES
            or os.fstat(stderr_file.fileno()).st_size > MAX_GIT_STREAM_BYTES
        ):
            raise GateError(
                f"controlled Git {' '.join(args)} exceeded the bounded output limit"
            )
        stdout_file.seek(0)
        stderr_file.seek(0)
        stdout = stdout_file.read(MAX_GIT_STREAM_BYTES + 1)
        stderr = stderr_file.read(MAX_GIT_STREAM_BYTES + 1)
        returncode = process.returncode
    if returncode != 0:
        detail = stderr.decode("utf-8", "replace").strip()
        raise GateError(f"controlled Git {' '.join(args)} failed ({returncode}): {detail}")
    if stderr:
        raise GateError(f"controlled Git {' '.join(args)} wrote unexpected stderr")
    return stdout


def controlled_git_text(
    root: Path, *args: str, pathspec_mode: str = "literal"
) -> str:
    stdout = controlled_git_bytes(root, *args, pathspec_mode=pathspec_mode)
    try:
        text = stdout.decode("utf-8", "strict")
    except UnicodeDecodeError as error:
        raise GateError(f"controlled Git {' '.join(args)} output was not UTF-8") from error
    if any(ord(character) < 32 and character not in "\n\t" for character in text):
        raise GateError(f"controlled Git {' '.join(args)} output contained control bytes")
    if text and not text.endswith("\n"):
        raise GateError(f"controlled Git {' '.join(args)} output lacked a canonical newline")
    return text[:-1] if text else ""


def gitlink_inventory(root: Path) -> list[tuple[Path, str]]:
    output = controlled_git_bytes(root, "ls-files", "--stage", "-z")
    if not output:
        return []
    if not output.endswith(b"\0"):
        raise GateError("Git index inventory lacked a terminal NUL")
    result: list[tuple[Path, str]] = []
    for record in output[:-1].split(b"\0"):
        try:
            metadata, raw_path = record.split(b"\t", 1)
            mode, object_id, stage = metadata.decode("ascii", "strict").split(" ")
        except (ValueError, UnicodeError) as error:
            raise GateError("Git index inventory contains a malformed record") from error
        if stage != "0" or not re.fullmatch(r"[0-9a-f]{40}", object_id):
            raise GateError("Git index inventory contains an unmerged or malformed entry")
        if mode != "160000":
            continue
        try:
            path = Path(raw_path.decode("utf-8", "strict"))
        except UnicodeDecodeError as error:
            raise GateError("submodule path is not UTF-8") from error
        if (
            not path.parts
            or path.is_absolute()
            or any(part in {"", ".", ".."} for part in path.parts)
        ):
            raise GateError("submodule path is not canonical")
        result.append((path, object_id))
    result.sort(key=lambda item: str(item[0]))
    if len({path for path, _object_id in result}) != len(result):
        raise GateError("Git index contains duplicate gitlinks")
    return result


def require_git_status_authority(root: Path) -> None:
    exclude_path_text = controlled_git_text(root, "rev-parse", "--git-path", "info/exclude")
    exclude_path = Path(exclude_path_text)
    if not exclude_path.is_absolute():
        exclude_path = root / exclude_path
    try:
        info = exclude_path.lstat()
    except FileNotFoundError:
        info = None
    if info is not None:
        if (
            stat.S_ISLNK(info.st_mode)
            or not stat.S_ISREG(info.st_mode)
            or info.st_size > MAX_LOCAL_EXCLUDE_BYTES
        ):
            raise GateError("local Git info/exclude is not a bounded exact regular file")
        try:
            exclusions = exclude_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise GateError(f"could not read local Git info/exclude: {error}") from error
        if any(
            line.strip() and not line.startswith("#")
            for line in exclusions.splitlines()
        ):
            raise GateError("local Git info/exclude contains material uncommitted rules")

    attributes_path_text = controlled_git_text(
        root, "rev-parse", "--git-path", "info/attributes"
    )
    attributes_path = Path(attributes_path_text)
    if not attributes_path.is_absolute():
        attributes_path = root / attributes_path
    try:
        attributes_info = attributes_path.lstat()
    except FileNotFoundError:
        attributes_info = None
    if attributes_info is not None:
        if (
            stat.S_ISLNK(attributes_info.st_mode)
            or not stat.S_ISREG(attributes_info.st_mode)
            or attributes_info.st_size > MAX_LOCAL_EXCLUDE_BYTES
        ):
            raise GateError("local Git info/attributes is not a bounded exact regular file")
        try:
            attributes = attributes_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise GateError(f"could not read local Git info/attributes: {error}") from error
        if any(
            line.strip() and not line.startswith("#")
            for line in attributes.splitlines()
        ):
            raise GateError("local Git info/attributes contains material uncommitted rules")

    config_names = controlled_git_bytes(
        root, "config", "--includes", "--name-only", "--null", "--list"
    )
    if config_names and not config_names.endswith(b"\0"):
        raise GateError("Git configuration inventory lacked a terminal NUL")
    for raw_name in config_names.split(b"\0"):
        if not raw_name:
            continue
        try:
            name = raw_name.decode("utf-8", "strict").lower()
        except UnicodeDecodeError as error:
            raise GateError("Git configuration name is not UTF-8") from error
        if name.startswith("filter.") and name.endswith(
            (".clean", ".process", ".required")
        ):
            raise GateError(f"effective Git clean/process filter authority is forbidden: {name}")

    hidden_ignore_files = controlled_git_text(
        root,
        "ls-files",
        "--others",
        "--ignored",
        "--exclude-standard",
        "--",
        ":(icase,glob)**/.gitignore",
        ":(icase,glob)**/.gitattributes",
        pathspec_mode="explicit-magic",
    )
    if hidden_ignore_files:
        raise GateError(
            "untracked .gitignore authority or untracked .gitattributes authority is hidden by ignore rules"
        )

    index = controlled_git_text(root, "ls-files", "-v")
    if any(not line.startswith("H ") for line in index.splitlines()):
        raise GateError(
            "Git index contains skip-worktree, assume-unchanged, unmerged, or hidden entries"
        )


def command_receipt(
    argv: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
) -> tuple[dict[str, Any], bytes, bytes]:
    started = time.monotonic_ns()
    completed = subprocess.run(
        argv,
        cwd=cwd,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    elapsed_ms = (time.monotonic_ns() - started) // 1_000_000
    record: dict[str, Any] = {
        "argv": argv,
        "cwd_scope": "ephemeral-crate-root",
        "duration_ms": elapsed_ms,
        "exit_code": completed.returncode,
        "stdout_bytes": len(completed.stdout),
        "stdout_sha256": sha256_bytes(completed.stdout),
        "stderr_bytes": len(completed.stderr),
        "stderr_sha256": sha256_bytes(completed.stderr),
    }
    if completed.returncode != 0:
        record["stderr_excerpt"] = completed.stderr.decode("utf-8", "replace")[-1000:]
    return record, completed.stdout, completed.stderr


def git_identity(
    root: Path, *, _visited: set[Path] | None = None
) -> dict[str, Any]:
    root = root.resolve(strict=True)
    visited = set() if _visited is None else _visited
    if root in visited or len(visited) >= 1024:
        raise GateError(f"repeated, cyclic, or over-bounded submodule worktree: {root}")
    visited.add(root)
    top_level = Path(controlled_git_text(root, "rev-parse", "--show-toplevel")).resolve(strict=True)
    if top_level != root:
        raise GateError(f"--repo-root must name the exact Git top level {top_level}")
    head = controlled_git_text(root, "rev-parse", "--verify", "HEAD^{commit}")
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        raise GateError(f"source HEAD is not a canonical SHA-1 commit: {head!r}")
    require_git_status_authority(root)
    status = controlled_git_text(
        root,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        "--ignore-submodules=none",
    )
    if status:
        raise GateError("compatibility evidence requires a clean source tree")
    submodules: list[dict[str, Any]] = []
    for relative, expected_head in gitlink_inventory(root):
        candidate = root
        for part in relative.parts:
            candidate = candidate / part
            try:
                info = candidate.lstat()
            except OSError as error:
                raise GateError(f"required submodule is not initialized: {candidate}: {error}") from error
            if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
                raise GateError(f"submodule path is not an exact directory: {candidate}")
        submodule_root = candidate.resolve(strict=True)
        try:
            submodule_root.relative_to(root)
        except ValueError as error:
            raise GateError(f"submodule escapes parent worktree: {submodule_root}") from error
        identity = git_identity(submodule_root, _visited=visited)
        if identity["head"] != expected_head:
            raise GateError(
                f"submodule {relative} HEAD {identity['head']} does not match gitlink {expected_head}"
            )
        submodules.append(
            {
                "path": relative.as_posix(),
                "head": expected_head,
                "source_tree_clean": True,
            }
        )
    return {
        "head": head,
        "source_tree_clean": True,
        "git_executable": str(controlled_git_executable()),
        "git_environment_inherited": False,
        "git_config_inherited": False,
        "recursive_submodules": submodules,
    }


def parse_corpus(crate_list: Path) -> list[str]:
    entries: list[str] = []
    for line_number, raw in enumerate(crate_list.read_text(encoding="utf-8").splitlines(), 1):
        value = raw.strip()
        if not value or value.startswith("#"):
            continue
        if not CRATE_NAME_RE.fullmatch(value):
            raise GateError(f"invalid crate name at {crate_list}:{line_number}: {value!r}")
        if value in entries:
            raise GateError(f"duplicate crate name at {crate_list}:{line_number}: {value}")
        entries.append(value)
    if not entries:
        raise GateError(f"crate corpus is empty: {crate_list}")
    return entries


def load_corpus(crate_list: Path, metadata_path: Path) -> tuple[dict[str, Any], list[str]]:
    if not crate_list.is_file():
        raise GateError(f"crate list does not exist: {crate_list}")
    if not metadata_path.is_file():
        raise GateError(f"corpus metadata does not exist: {metadata_path}")
    metadata = strict_json_loads(
        metadata_path.read_text(encoding="utf-8"), "corpus metadata"
    )
    if metadata.get("schema") != CORPUS_SCHEMA:
        raise GateError(f"corpus metadata must use {CORPUS_SCHEMA}")
    entries = parse_corpus(crate_list)
    actual_digest = sha256_file(crate_list)
    if metadata.get("crate_list_sha256") != actual_digest:
        raise GateError("crate list digest does not match corpus metadata")
    if metadata.get("entry_count") != len(entries):
        raise GateError("crate list entry count does not match corpus metadata")
    if metadata.get("crate_list") != crate_list.name:
        raise GateError("corpus metadata crate_list must name the adjacent list file")
    return metadata, entries


def default_targo(root: Path) -> Path:
    candidates = sorted(root.glob("build/*/stage2/bin/targo"))
    executable = [path for path in candidates if path.is_file() and os.access(path, os.X_OK)]
    if len(executable) != 1:
        rendered = ", ".join(str(path) for path in executable) or "none"
        raise GateError(f"could not select one Stage2 Targo (found {rendered}); pass --targo")
    return executable[0]


def tool_identity(targo: Path, source_head: str) -> tuple[dict[str, Any], Path]:
    targo = targo.resolve()
    if not targo.is_file() or not os.access(targo, os.X_OK):
        raise GateError(f"Targo is not executable: {targo}")
    trustc = targo.with_name("trustc")
    if not trustc.is_file() or not os.access(trustc, os.X_OK):
        raise GateError(f"Stage2 Trust compiler is not an executable sibling of Targo: {trustc}")
    targo_version = run_text([str(targo), "-V"])
    trustc_verbose = run_text([str(trustc), "-Vv"])
    commit_match = COMPILER_COMMIT_RE.search(trustc_verbose)
    compiler_commit = commit_match.group(1) if commit_match else None
    if compiler_commit != source_head:
        raise GateError(
            f"Stage2 compiler commit {compiler_commit!r} does not match source HEAD {source_head}"
        )
    sysroot = Path(run_text([str(trustc), "--print", "sysroot"])).resolve()
    expected_sysroot = targo.parent.parent.resolve()
    if sysroot != expected_sysroot:
        raise GateError(f"Trust compiler reports foreign sysroot {sysroot}; expected {expected_sysroot}")
    return (
        {
            "targo": {
                "path_scope": "local-diagnostic",
                "path": str(targo),
                "sha256": sha256_file(targo),
                "version": targo_version,
            },
            "trustc": {
                "path_scope": "local-diagnostic",
                "path": str(trustc.resolve()),
                "sha256": sha256_file(trustc),
                "version_verbose": trustc_verbose,
                "source_commit": compiler_commit,
                "reported_sysroot": str(sysroot),
            },
        },
        expected_sysroot,
    )


def validate_stage_provenance(
    path: Path,
    *,
    root: Path,
    source_head: str,
    sysroot: Path,
    trustc_sha256: str,
) -> dict[str, Any]:
    if not path.is_file():
        raise GateError(f"Stage2 provenance receipt is missing: {path}")
    raw = path.read_bytes()
    receipt = strict_json_loads(raw, "Stage2 provenance receipt")
    errors: list[str] = []
    if receipt.get("schema") != PROVENANCE_SCHEMA:
        errors.append(f"schema is not {PROVENANCE_SCHEMA}")
    if receipt.get("status") not in {"internal-release-ready", "release-ready"}:
        errors.append("receipt is not immutable internal/public release provenance")
    if receipt.get("stage") != 2:
        errors.append("receipt does not describe Stage2")
    host = receipt.get("host")
    if not isinstance(host, str) or not HOST_TRIPLE_RE.fullmatch(host):
        errors.append("receipt host triple is absent or non-canonical")
        host = "invalid-host"
    if receipt.get("path_scope") != "repository-root-relative":
        errors.append("receipt paths are not repository-root-relative")
    if receipt.get("tool_binding_status") != "ready" or receipt.get("errors") != []:
        errors.append("receipt tool binding is not ready and error-free")
    if receipt.get("source_tree_clean") is not True:
        errors.append("source tree was not clean during the Stage2 build")
    if receipt.get("trust_from_trust") is not True:
        errors.append("Stage2 receipt is not Trust-from-Trust")
    source_lineage = receipt.get("source_lineage")
    if not isinstance(source_lineage, dict) or (
        source_lineage.get("status") != "immutable_release"
        or source_lineage.get("stable_across_build") is not True
        or source_lineage.get("errors") != []
    ):
        errors.append("receipt source lineage is not immutable, stable, and error-free")
    bootstrap_lineage = receipt.get("bootstrap_lineage")
    if not isinstance(bootstrap_lineage, dict) or (
        bootstrap_lineage.get("status") != "trust_from_trust"
        or bootstrap_lineage.get("stable_across_build") is not True
        or bootstrap_lineage.get("errors") != []
    ):
        errors.append("receipt bootstrap lineage is not stable Trust-from-Trust")
    build_authority = receipt.get("build_authority")
    if not isinstance(build_authority, dict) or (
        build_authority.get("status") != "ready"
        or build_authority.get("stable_across_build") is not True
        or build_authority.get("errors") != []
    ):
        errors.append("receipt native build authority is not stable and ready")
    compiler = receipt.get("compiler")
    if not isinstance(compiler, dict):
        errors.append("compiler binding is missing")
    else:
        if compiler.get("source_commit") != source_head:
            errors.append("compiler source commit does not match current HEAD")
        if compiler.get("compiler_sha256") != trustc_sha256:
            errors.append("compiler digest does not match the selected Trust compiler")
        if compiler.get("sysroot_matches") is not True:
            errors.append("compiler sysroot binding was rejected")
    verification = receipt.get("bootstrap_compiler_verification")
    expected_verification = {
        "mode": "disabled",
        "flag": "-Ztrust-verify=off",
        "reason": "bootstrap stability",
        "counts_as_self_proof": False,
    }
    if verification != expected_verification:
        errors.append("bootstrap verification disclosure is absent or does not fail closed")
    expected_stage_root = (root / "build" / host / "stage2").resolve()
    if sysroot != expected_stage_root:
        errors.append(
            f"selected sysroot {sysroot} is not repository Stage2 {expected_stage_root}"
        )
    if Path(path).parent.resolve() != sysroot:
        errors.append(f"receipt is not owned by selected sysroot {sysroot}")
    if errors:
        raise GateError("invalid Stage2 provenance receipt: " + "; ".join(errors))

    verifier = root / "scripts" / "recreate_bootstrap.py"
    if not verifier.is_file() or verifier.is_symlink():
        raise GateError(f"Stage2 provenance diagnostic verifier is missing: {verifier}")
    interpreter = Path(sys.executable).resolve(strict=True)
    interpreter_info = interpreter.stat()
    if not stat.S_ISREG(interpreter_info.st_mode) or not interpreter_info.st_mode & 0o111:
        raise GateError(f"current Python interpreter is not an executable regular file: {interpreter}")
    verifier_argv = [
        str(interpreter),
        "-I",
        "-S",
        "-E",
        str(verifier),
        "--verify-stage-provenance",
        "--require-immutable-lineage",
        "--stage",
        "2",
        "--host",
        host,
    ]
    verifier_output = run_text(
        verifier_argv,
        cwd=root,
        env={"LC_ALL": "C", "LANG": "C", "TZ": "UTC", "PYTHONHASHSEED": "0"},
    )
    return {
        "path_scope": "local-diagnostic",
        "path": str(path.resolve()),
        "sha256": sha256_bytes(raw),
        "schema": receipt.get("schema"),
        "status": receipt.get("status"),
        "stage": 2,
        "host": host,
        "diagnostically_checked_for_compatibility": True,
        "diagnostic_verifier": {
            "argv": [
                str(interpreter),
                "-I",
                "-S",
                "-E",
                "scripts/recreate_bootstrap.py",
                "--verify-stage-provenance",
                "--require-immutable-lineage",
                "--stage",
                "2",
                "--host",
                host,
            ],
            "interpreter_sha256": sha256_file(interpreter),
            "runner_execution_authenticated": False,
            "stdout_sha256": sha256_bytes(verifier_output.encode("utf-8")),
        },
        "bootstrap_compiler_verification": verification,
    }


def isolated_environment(
    *, crate_root: Path, cargo_home: Path, targo: Path, trustc: Path
) -> dict[str, str]:
    home = crate_root / "home"
    temp = crate_root / "tmp"
    target = crate_root / "target"
    for path in (home, temp, target, cargo_home):
        path.mkdir(parents=True, exist_ok=True)
    return {
        "CARGO": str(targo),
        "CARGO_HOME": str(cargo_home),
        "CARGO_TARGET_DIR": str(target),
        "HOME": str(home),
        "LC_ALL": "C",
        "PATH": f"{targo.parent}:/usr/bin:/bin:/usr/sbin:/sbin",
        "RUSTC": str(trustc),
        "RUSTUP_HOME": str(crate_root / "rustup-home-empty"),
        "TMPDIR": str(temp),
    }


def resolved_packages(metadata: dict[str, Any]) -> list[dict[str, Any]]:
    packages: list[dict[str, Any]] = []
    for package in metadata.get("packages", []):
        packages.append(
            {
                "name": package.get("name"),
                "version": package.get("version"),
                "source": package.get("source"),
                "checksum": package.get("checksum"),
            }
        )
    return sorted(packages, key=lambda item: (str(item["name"]), str(item["version"])))


def validate_resolved_metadata(crate_name: str, metadata: dict[str, Any]) -> None:
    """Require an exact checksummed registry graph for the requested crate."""
    packages = metadata.get("packages")
    if not isinstance(packages, list) or not packages:
        raise GateError("cargo metadata contains no package graph")
    requested_rows = [
        package
        for package in packages
        if isinstance(package, dict)
        and package.get("name") == crate_name
        and str(package.get("source", "")).startswith("registry+")
    ]
    if len(requested_rows) != 1:
        raise GateError(
            f"metadata does not resolve exactly one registry package for {crate_name}"
        )
    for package in packages:
        if not isinstance(package, dict):
            raise GateError("cargo metadata contains a malformed package row")
        source = package.get("source")
        checksum = package.get("checksum")
        if isinstance(source, str) and source.startswith("registry+"):
            if not isinstance(checksum, str) or not SHA256_RE.fullmatch(checksum):
                raise GateError(
                    "registry package lacks a canonical checksum: "
                    f"{package.get('name')} {package.get('version')}"
                )
        elif source is not None:
            raise GateError(
                "compatibility graph contains a non-registry dependency source: "
                f"{package.get('name')} {source}"
            )


def require_evidence_cache_mode(cache_mode: str) -> None:
    if cache_mode != "isolated":
        raise GateError(
            "compatibility evidence requires one isolated CARGO_HOME per crate; "
            "--cache-mode run cannot produce a passing receipt"
        )


def evidence_exit_code(*, complete: bool, failed: int) -> int:
    return 0 if complete and failed == 0 else 1


def write_fixture(crate_root: Path, crate_name: str) -> tuple[Path, str]:
    source = crate_root / "src"
    source.mkdir(parents=True, exist_ok=True)
    manifest = (
        "[package]\n"
        f'name = "trust-compat-{crate_name.replace("_", "-")}"\n'
        'version = "0.0.0"\n'
        'edition = "2021"\n'
        'publish = false\n\n'
        "[dependencies]\n"
        f'{crate_name} = "*"\n'
    )
    manifest_path = crate_root / "Cargo.toml"
    manifest_path.write_text(manifest, encoding="utf-8")
    (source / "main.rs").write_text("fn main() {}\n", encoding="utf-8")
    return manifest_path, sha256_bytes(manifest.encode("utf-8"))


def run_crate(
    crate_name: str,
    *,
    index: int,
    work_root: Path,
    cargo_home_root: Path,
    cache_mode: str,
    targo: Path,
    trustc: Path,
) -> dict[str, Any]:
    crate_root = work_root / f"{index:03d}-{crate_name}"
    crate_root.mkdir(parents=True)
    manifest, manifest_sha = write_fixture(crate_root, crate_name)
    cargo_home = cargo_home_root if cache_mode == "run" else crate_root / "cargo-home"
    env = isolated_environment(
        crate_root=crate_root, cargo_home=cargo_home, targo=targo, trustc=trustc
    )
    commands: list[dict[str, Any]] = []
    metadata_payload: dict[str, Any] | None = None
    command_specs = [
        [str(targo), "generate-lockfile", "--manifest-path", str(manifest)],
        [str(targo), "fetch", "--locked", "--manifest-path", str(manifest)],
        [
            str(targo),
            "metadata",
            "--locked",
            "--offline",
            "--format-version",
            "1",
            "--manifest-path",
            str(manifest),
        ],
        [
            str(targo),
            "--unverified",
            "build",
            "--locked",
            "--offline",
            "--manifest-path",
            str(manifest),
        ],
    ]
    error: str | None = None
    for command_index, argv in enumerate(command_specs):
        record, stdout, stderr = command_receipt(argv, cwd=crate_root, env=env)
        if command_index == 3:
            banner_present = b"UNVERIFIED" in stdout or b"UNVERIFIED" in stderr
            record["mandatory_unverified_banner_present"] = banner_present
            if record["exit_code"] == 0 and not banner_present:
                error = "explicit native build omitted the mandatory UNVERIFIED banner"
        commands.append(record)
        if record["exit_code"] != 0:
            error = f"command {command_index + 1} exited {record['exit_code']}"
            break
        if error is not None:
            break
        if command_index == 2:
            try:
                metadata_payload = strict_json_loads(stdout, f"{crate_name} Cargo metadata")
            except json.JSONDecodeError as parse_error:
                error = f"cargo metadata did not emit JSON: {parse_error}"
                break
            try:
                validate_resolved_metadata(crate_name, metadata_payload)
            except GateError as metadata_error:
                error = str(metadata_error)
                break

    lock_path = crate_root / "Cargo.lock"
    if not lock_path.is_file() and error is None:
        error = "Cargo.lock was not produced"
    result: dict[str, Any] = {
        "crate": crate_name,
        "status": "passed" if error is None else "failed",
        "manifest_sha256": manifest_sha,
        "lock_sha256": sha256_file(lock_path) if lock_path.is_file() else None,
        "commands": commands,
        "resolved_packages": resolved_packages(metadata_payload or {}),
    }
    if error is not None:
        result["error"] = error
    return result


def serialize_json(payload: dict[str, Any]) -> bytes:
    try:
        rendered = json.dumps(
            payload,
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
    except (TypeError, ValueError) as error:
        raise GateError(f"receipt is not strict JSON: {error}") from error
    return (rendered + "\n").encode("utf-8")


def _secure_directory_flags() -> int:
    required = ("O_DIRECTORY", "O_NOFOLLOW")
    missing = [name for name in required if not hasattr(os, name)]
    dir_fd_functions = (os.open, os.mkdir, os.stat, os.unlink, os.rename)
    unsupported = [
        function.__name__
        for function in dir_fd_functions
        if function not in os.supports_dir_fd
    ]
    if missing or unsupported:
        detail = ", ".join(missing + unsupported)
        raise GateError(f"secure receipt publication is unavailable: missing {detail}")
    return os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW


def _open_secure_parent(path: Path) -> tuple[Path, int]:
    """Open/create every parent component without following symlinks."""

    absolute = Path(os.path.abspath(os.fspath(path)))
    if not absolute.name:
        raise GateError("receipt path must name a file")
    flags = _secure_directory_flags()
    anchor = absolute.anchor
    if not anchor:
        raise GateError(f"receipt path has no absolute anchor: {absolute}")
    directory_fd = os.open(anchor, flags)
    try:
        for component in absolute.parent.parts[1:]:
            try:
                next_fd = os.open(component, flags, dir_fd=directory_fd)
            except FileNotFoundError:
                try:
                    os.mkdir(component, 0o755, dir_fd=directory_fd)
                except FileExistsError:
                    # Another process created the component. The no-follow
                    # open below decides whether it is an admissible directory.
                    pass
                try:
                    next_fd = os.open(component, flags, dir_fd=directory_fd)
                except OSError as error:
                    raise GateError(
                        f"receipt parent component is not a real directory: "
                        f"{absolute.parent} ({error})"
                    ) from error
            except OSError as error:
                if error.errno in {errno.ELOOP, errno.ENOTDIR}:
                    raise GateError(
                        f"receipt parent component is a symlink or non-directory: "
                        f"{absolute.parent}"
                    ) from error
                raise
            os.close(directory_fd)
            directory_fd = next_fd
        return absolute, directory_fd
    except BaseException:
        os.close(directory_fd)
        raise


def _require_regular_or_absent(directory_fd: int, filename: str, display: Path) -> None:
    try:
        info = os.stat(filename, dir_fd=directory_fd, follow_symlinks=False)
    except FileNotFoundError:
        return
    if stat.S_ISLNK(info.st_mode):
        raise GateError(f"receipt destination is a symlink: {display}")
    if not stat.S_ISREG(info.st_mode):
        raise GateError(f"receipt destination is not a regular file: {display}")


def _create_unique_temporary(directory_fd: int, filename: str) -> tuple[str, int]:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
    for _attempt in range(100):
        temporary = f".{filename}.{secrets.token_hex(16)}.tmp"
        try:
            descriptor = os.open(temporary, flags, 0o600, dir_fd=directory_fd)
        except FileExistsError:
            continue
        return temporary, descriptor
    raise GateError("could not allocate a unique same-directory receipt temporary")


def _atomic_write_bytes(path: Path, payload: bytes) -> Path:
    absolute, directory_fd = _open_secure_parent(path)
    temporary: str | None = None
    try:
        _require_regular_or_absent(directory_fd, absolute.name, absolute)
        temporary, descriptor = _create_unique_temporary(directory_fd, absolute.name)
        try:
            with os.fdopen(descriptor, "wb") as stream:
                os.fchmod(stream.fileno(), 0o644)
                stream.write(payload)
                stream.flush()
                os.fsync(stream.fileno())
        except BaseException:
            try:
                os.close(descriptor)
            except OSError:
                pass
            raise
        _require_regular_or_absent(directory_fd, absolute.name, absolute)
        os.replace(
            temporary,
            absolute.name,
            src_dir_fd=directory_fd,
            dst_dir_fd=directory_fd,
        )
        temporary = None
        os.fsync(directory_fd)
        return absolute
    finally:
        if temporary is not None:
            try:
                os.unlink(temporary, dir_fd=directory_fd)
            except FileNotFoundError:
                pass
        os.close(directory_fd)


def atomic_json(path: Path, payload: dict[str, Any]) -> Path:
    """Serialize first, then durably replace one non-symlink destination."""

    return _atomic_write_bytes(path, serialize_json(payload))


def is_full_passing_receipt(payload: dict[str, Any]) -> bool:
    """Compatibility shim: this unauthenticated runner never emits release authority."""

    _ = payload
    return False


def is_complete_passing_diagnostic(payload: dict[str, Any]) -> bool:
    """Return whether payload is a complete, passing diagnostic corpus run."""

    if (
        payload.get("schema") != RECEIPT_SCHEMA
        or payload.get("status") != "diagnostic-passed"
        or payload.get("classification") != "diagnostic-only"
        or payload.get("runner_execution_authenticated") is not False
        or payload.get("release_gate_admissible") is not False
    ):
        return False
    if payload.get("lane") != native_compat_lane_claims():
        return False
    source = payload.get("source")
    corpus = payload.get("corpus")
    isolation = payload.get("isolation")
    stability = payload.get("input_stability")
    provenance = payload.get("stage_provenance")
    summary = payload.get("summary")
    results = payload.get("results")
    if not all(
        isinstance(value, dict)
        for value in (source, corpus, isolation, stability, provenance, summary)
    ) or not isinstance(results, list):
        return False
    if source.get("source_tree_clean") is not True:
        return False
    if corpus.get("complete") is not True:
        return False
    count = corpus.get("entry_count")
    executed = corpus.get("executed_entry_count")
    entries = corpus.get("entries")
    if (
        not isinstance(count, int)
        or isinstance(count, bool)
        or count < 1
        or executed != count
        or not isinstance(entries, list)
        or len(entries) != count
        or any(not isinstance(entry, str) or not entry for entry in entries)
        or len(entries) != len(set(entries))
    ):
        return False
    if isolation.get("cache_mode") != "isolated":
        return False
    if set(stability) != {
        "source_stable",
        "corpus_stable",
        "tools_stable",
        "stage_provenance_stable",
    } or any(value is not True for value in stability.values()):
        return False
    if provenance.get("verified_before_and_after_run") is not True:
        return False
    if (
        summary.get("total") != count
        or summary.get("passed") != count
        or summary.get("failed") != 0
        or len(results) != count
        or any(
            not isinstance(result, dict) or result.get("status") != "passed"
            for result in results
        )
        or [result.get("crate") for result in results] != entries
    ):
        return False
    return isinstance(payload.get("tools"), dict) and not payload.get("errors")


def nonpassing_attempt_path(path: Path) -> Path:
    suffix = path.suffix or ".json"
    stem = path.name[: -len(path.suffix)] if path.suffix else path.name
    return path.with_name(f"{stem}.last-nonpassing-attempt{suffix}")


def publish_compatibility_receipt(path: Path, payload: dict[str, Any]) -> tuple[Path, bool]:
    """Publish a complete diagnostic or an adjacent non-passing attempt.

    This runner never publishes release authority. A non-passing or malformed
    attempt cannot replace an earlier complete diagnostic.
    """

    serialized = serialize_json(payload)
    diagnostic, directory_fd = _open_secure_parent(path)
    try:
        _require_regular_or_absent(directory_fd, diagnostic.name, diagnostic)
    finally:
        os.close(directory_fd)
    complete_diagnostic = is_complete_passing_diagnostic(payload)
    destination = diagnostic if complete_diagnostic else nonpassing_attempt_path(diagnostic)
    return _atomic_write_bytes(destination, serialized), complete_diagnostic


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--targo", type=Path, help="Stage2 Targo executable")
    result.add_argument(
        "--crate-list", type=Path, default=Path("tests/compat/top_crates.txt")
    )
    result.add_argument("--corpus-meta", type=Path)
    result.add_argument(
        "--receipt",
        type=Path,
        default=Path("build/evidence/crates-io-native-compatibility.json"),
    )
    result.add_argument("--jobs", type=int, default=1)
    result.add_argument(
        "--cache-mode",
        choices=("isolated", "run"),
        default="isolated",
        help="isolated: one ephemeral CARGO_HOME per crate (required for evidence); "
        "run: legacy shared-cache spelling, rejected for evidence",
    )
    result.add_argument("--only", action="append", default=[], metavar="CRATE")
    result.add_argument("--keep-work-dir", action="store_true")
    result.add_argument("--repo-root", type=Path)
    return result


def native_compat_lane_claims() -> dict[str, Any]:
    """Describe exactly what the generated one-dependency fixtures exercise."""

    return {
        "name": "crates-io-native-unverified",
        "verification": "disabled",
        "targo_authorization": "--unverified",
        "compiler_off_switch": "-Ztrust-verify=off",
        "fixture_shape": "generated binary with an empty main and one wildcard dependency",
        "covers": [
            "crates.io dependency resolution",
            "locked Cargo-offline native compilation of each selected dependency graph",
            "build-script compilation and execution where Cargo invokes graph build scripts",
            "proc-macro package compilation where selected graphs contain proc-macro targets",
        ],
        "does_not_cover": [
            "an inventory or independent attestation of proc-macro invocation",
            "verified downstream proc macros",
            "proof of dependency behavior",
            "hosts other than the recorded host",
            "ecosystem superiority or exhaustive crates.io compatibility",
            "network or filesystem hermeticity of build scripts and native tools",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if args.jobs < 1:
        print("ERROR: --jobs must be positive", file=sys.stderr)
        return 2
    root = (args.repo_root or Path(__file__).resolve().parent.parent).resolve()
    crate_list = args.crate_list if args.crate_list.is_absolute() else root / args.crate_list
    if args.corpus_meta is None:
        metadata_path = crate_list.with_name(f"{crate_list.stem}.meta.json")
    else:
        metadata_path = (
            args.corpus_meta
            if args.corpus_meta.is_absolute()
            else root / args.corpus_meta
        )
    receipt_path = args.receipt if args.receipt.is_absolute() else root / args.receipt
    started_at = utc_now()
    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "status": "diagnostic-rejected",
        "classification": "diagnostic-only",
        "runner_execution_authenticated": False,
        "release_gate_admissible": False,
        "started_at": started_at,
        "lane": native_compat_lane_claims(),
    }
    work_root: Path | None = None
    exit_code = 2
    try:
        require_evidence_cache_mode(args.cache_mode)
        source = git_identity(root)
        corpus_meta, all_entries = load_corpus(crate_list, metadata_path)
        crate_list_sha256 = sha256_file(crate_list)
        metadata_sha256 = sha256_file(metadata_path)
        selected = list(all_entries)
        if args.only:
            unknown = sorted(set(args.only) - set(all_entries))
            if unknown:
                raise GateError(f"--only names are not in the corpus: {', '.join(unknown)}")
            selected = [entry for entry in all_entries if entry in set(args.only)]
        complete = selected == all_entries
        targo = (args.targo or default_targo(root)).resolve()
        tools, sysroot = tool_identity(targo, source["head"])
        provenance = validate_stage_provenance(
            sysroot / "tool-provenance.json",
            root=root,
            source_head=source["head"],
            sysroot=sysroot,
            trustc_sha256=tools["trustc"]["sha256"],
        )
        receipt.update(
            {
                "source": source,
                "tools": tools,
                "stage_provenance": provenance,
                "corpus": {
                    **corpus_meta,
                    "metadata_sha256": metadata_sha256,
                    "entries": list(all_entries),
                    "executed_entry_count": len(selected),
                    "complete": complete,
                },
                "isolation": {
                    "ambient_environment_replaced": True,
                    "cache_mode": args.cache_mode,
                    "per_crate_home": True,
                    "per_crate_cargo_home": True,
                    "per_crate_tmp": True,
                    "per_crate_target": True,
                    "cargo_dependency_network_after_fetch": "offline",
                    "build_script_network_sandboxed": False,
                },
            }
        )
        work_root = Path(tempfile.mkdtemp(prefix="trust-compat-"))
        cargo_home_root = work_root / "run-cargo-home"
        run_args = {
            "work_root": work_root,
            "cargo_home_root": cargo_home_root,
            "cache_mode": args.cache_mode,
            "targo": targo,
            "trustc": targo.with_name("trustc").resolve(),
        }
        indexed = list(enumerate(selected, 1))
        if args.jobs == 1:
            results = [run_crate(name, index=index, **run_args) for index, name in indexed]
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
                futures = {
                    executor.submit(run_crate, name, index=index, **run_args): index
                    for index, name in indexed
                }
                unordered = [future.result() for future in concurrent.futures.as_completed(futures)]
            order = {name: index for index, name in indexed}
            results = sorted(unordered, key=lambda item: order[item["crate"]])
        passed = sum(result["status"] == "passed" for result in results)
        failed = len(results) - passed
        receipt.update(
            {
                "summary": {"total": len(results), "passed": passed, "failed": failed},
                "results": results,
            }
        )

        # A 123-crate run is long enough for a source checkout, corpus, receipt,
        # or selected toolchain to change underneath it.  Recompute every
        # diagnostic input before classifying the receipt; a preflight-only
        # binding would otherwise bless mixed-run evidence.
        source_after = git_identity(root)
        if source_after != source:
            raise GateError("source HEAD or clean-tree state changed during compatibility run")
        corpus_meta_after, all_entries_after = load_corpus(crate_list, metadata_path)
        if (
            corpus_meta_after != corpus_meta
            or all_entries_after != all_entries
            or sha256_file(crate_list) != crate_list_sha256
            or sha256_file(metadata_path) != metadata_sha256
        ):
            raise GateError("corpus metadata or crate list changed during compatibility run")
        tools_after, sysroot_after = tool_identity(targo, source["head"])
        if tools_after != tools or sysroot_after != sysroot:
            raise GateError("selected Targo/Trust compiler identity changed during compatibility run")
        provenance_after = validate_stage_provenance(
            sysroot / "tool-provenance.json",
            root=root,
            source_head=source["head"],
            sysroot=sysroot,
            trustc_sha256=tools["trustc"]["sha256"],
        )
        if provenance_after["sha256"] != provenance["sha256"]:
            raise GateError("Stage2 provenance receipt changed during compatibility run")
        receipt["stage_provenance"] = {
            **provenance_after,
            "verified_before_and_after_run": True,
        }
        receipt["input_stability"] = {
            "source_stable": True,
            "corpus_stable": True,
            "tools_stable": True,
            "stage_provenance_stable": True,
        }
        receipt["status"] = (
            "diagnostic-passed"
            if complete and failed == 0
            else "diagnostic-partial-passed"
            if failed == 0
            else "diagnostic-failed"
        )
        receipt["finished_at"] = utc_now()
        for result in results:
            print(f"{result['crate']}\t{result['status']}")
        print(
            f"compatibility attempt: {receipt['status']} ({passed}/{len(results)} passed)",
            file=sys.stderr,
        )
        exit_code = evidence_exit_code(complete=complete, failed=failed)
    except (GateError, OSError, json.JSONDecodeError) as error:
        receipt.update(
            {
                "status": "diagnostic-rejected",
                "finished_at": utc_now(),
                "errors": [str(error)],
            }
        )
        print(f"ERROR: {error}", file=sys.stderr)
        exit_code = 2
    finally:
        try:
            published_path, complete_diagnostic = publish_compatibility_receipt(
                receipt_path, receipt
            )
        except (GateError, OSError) as error:
            print(f"ERROR: could not publish compatibility attempt: {error}", file=sys.stderr)
            exit_code = 2
        else:
            if complete_diagnostic:
                print(f"complete diagnostic receipt: {published_path}", file=sys.stderr)
            else:
                print(
                    f"non-passing attempt: {published_path} "
                    f"(complete diagnostic receipt left untouched)",
                    file=sys.stderr,
                )
                if exit_code == 0:
                    print(
                        "ERROR: successful exit was refused because the receipt "
                        "is not a complete diagnostic",
                        file=sys.stderr,
                    )
                    exit_code = 2
        if work_root is not None:
            if args.keep_work_dir:
                print(f"work directory retained: {work_root}", file=sys.stderr)
            else:
                shutil.rmtree(work_root, ignore_errors=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
