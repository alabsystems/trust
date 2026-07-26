#!/usr/bin/env python3
"""Collect one bounded downstream-verifier diagnostic receipt.

This command is intentionally fixture-specific.  It measures the vendored,
checksum-pinned crates.io source for ``lambda_calculus 3.5.0`` and nothing
else.  A successful receipt is evidence about one selected crate on one host;
it is not an ecosystem sample, a compatibility claim, or superiority proof.
The Python process startup is not independently authenticated, so this receipt
is diagnostic input and must never be accepted as release-gate proof.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import io
import json
import os
import selectors
import signal
import stat
import subprocess
import sys
import tarfile
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any


def _require_python_311() -> None:
    if sys.version_info >= (3, 11):
        return
    candidates = (
        "/opt/homebrew/bin/python3.14",
        "/opt/homebrew/bin/python3.13",
        "/opt/homebrew/bin/python3.12",
        "/opt/homebrew/bin/python3.11",
        "/usr/local/bin/python3.14",
        "/usr/local/bin/python3.13",
        "/usr/local/bin/python3.12",
        "/usr/local/bin/python3.11",
        "/usr/bin/python3.14",
        "/usr/bin/python3.13",
        "/usr/bin/python3.12",
        "/usr/bin/python3.11",
    )
    for candidate in candidates:
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            os.execv(candidate, [candidate, *sys.argv])
    raise SystemExit(
        "collect_lambda_calculus_diagnostic.py requires Python >=3.11 (tomllib); "
        f"found {sys.version.split()[0]}"
    )


_require_python_311()
import tomllib  # noqa: E402  (loaded only after the version gate/re-exec)


SCHEMA = "trust.lambda-calculus-downstream-diagnostic.v1"
ATTEMPT_KIND = "one-published-crate-non-representative-diagnostic"
PROVENANCE_SCHEMA = "trust.stage-tool-provenance.v2"
PROVE_SCHEMA = "trust.prove-scorecard.v1"
SOURCE_SCHEMA = "trust.published-crate-source-selection.v1"
ACCEPTED_PROVENANCE = {"internal-release-ready", "release-ready"}
FIXTURE_REL = Path("crates/trust-clean/fixtures/fold-crate-lambda-calculus-3.5.0")
PROVENANCE_VERIFIER_REL = Path("scripts/recreate_bootstrap.py")
SOURCE_SELECTION_REL = Path("metadata/source-selection.json")
ARCHIVE_SHA256 = "168030aef659e9a35ba517952982bb0212fda53d531837e3f18c399f9d28dba8"
ARCHIVE_URL = "https://static.crates.io/crates/lambda_calculus/lambda_calculus-3.5.0.crate"
ARCHIVE_ROOT = "lambda_calculus-3.5.0"
MAX_ARCHIVE_BYTES = 16 * 1024 * 1024
FIXED_PATH = "/usr/bin:/bin:/usr/sbin:/sbin"
GIT_CONFIG_OVERRIDES = (
    "core.fsmonitor=false",
    "core.untrackedCache=false",
    "core.hooksPath=/dev/null",
    "core.filemode=true",
    "core.symlinks=true",
    "core.sparseCheckout=false",
    "core.excludesFile=/dev/null",
)
TOOL_PROBES: dict[str, tuple[str, ...]] = {
    "trustc": ("-vV",),
    "targo": ("-vV",),
    "targo-trust": ("--version",),
    "trustd": ("--version",),
}

CLAIM_BOUNDARY = {
    "kind": ATTEMPT_KIND,
    "crate": "lambda_calculus",
    "version": "3.5.0",
    "projects_sampled": 1,
    "selection": (
        "A deliberately selected, zero-dependency, safe Rust crate whose recursive ADT "
        "exercises the structural-fold lane; selection is documented in PROVENANCE.md."
    ),
    "proof_scope": (
        "The compiler transcript and full manifest cover the direct published lib.rs compile. "
        "The scorecard covers the mechanically selected non-data core subset only."
    ),
    "non_claims": [
        "not a representative or random ecosystem sample",
        "not proof of downstream ecosystem coverage",
        "not proof of Cargo/build-script/proc-macro compatibility",
        "not proof that every function or obligation was verified",
        "not evidence that Trust is superior to Rust or another verifier",
        "not authenticated release-gate evidence; Python startup authority remains ambient",
    ],
}


class EvidenceError(RuntimeError):
    """A condition that invalidates the diagnostic receipt."""


def reject_constant(value: str) -> None:
    raise EvidenceError(f"non-finite JSON number is forbidden: {value}")


def reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise EvidenceError(f"duplicate JSON object key: {key!r}")
        value[key] = item
    return value


def strict_json_bytes(data: bytes, label: str) -> Any:
    try:
        text = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{label} is not UTF-8: {error}") from error
    try:
        return json.loads(
            text,
            object_pairs_hook=reject_duplicate_pairs,
            parse_constant=reject_constant,
        )
    except EvidenceError:
        raise
    except json.JSONDecodeError as error:
        raise EvidenceError(f"{label} is malformed JSON: {error}") from error


def strict_json_file(path: Path, label: str) -> Any:
    try:
        return strict_json_bytes(path.read_bytes(), label)
    except OSError as error:
        raise EvidenceError(f"could not read {label} at {path}: {error}") from error


def canonical_json_bytes(value: Any) -> bytes:
    try:
        rendered = json.dumps(
            value,
            sort_keys=True,
            indent=2,
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError) as error:
        raise EvidenceError(f"document is not strict JSON: {error}") from error
    return (rendered + "\n").encode("utf-8")


def compact_json_bytes(value: Any) -> bytes:
    try:
        rendered = json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError) as error:
        raise EvidenceError(f"manifest is not strict JSON: {error}") from error
    return (rendered + "\n").encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def regular_file(path: Path, label: str, *, executable: bool = False) -> os.stat_result:
    try:
        info = path.lstat()
    except OSError as error:
        raise EvidenceError(f"cannot inspect {label} at {path}: {error}") from error
    if not stat.S_ISREG(info.st_mode):
        raise EvidenceError(f"{label} must be a regular non-symlink file: {path}")
    if executable and not os.access(path, os.X_OK):
        raise EvidenceError(f"{label} is not executable: {path}")
    return info


def file_record(path: Path, label: str, *, executable: bool = False) -> dict[str, Any]:
    info = regular_file(path, label, executable=executable)
    return {"path": str(path), "size": info.st_size, "sha256": sha256_file(path)}


def relative_file_record(root: Path, path: Path, label: str) -> dict[str, Any]:
    record = file_record(path, label)
    record["path"] = path.relative_to(root).as_posix()
    return record


def require_unchanged(path: Path, before: dict[str, Any], label: str, *, executable: bool = False) -> None:
    if file_record(path, label, executable=executable) != before:
        raise EvidenceError(f"{label} changed during collection")


def canonical_commit(value: Any, label: str) -> str:
    if not isinstance(value, str) or len(value) not in (40, 64):
        raise EvidenceError(f"{label} is not a canonical 40- or 64-hex commit")
    if any(character not in "0123456789abcdef" for character in value):
        raise EvidenceError(f"{label} is not lowercase hexadecimal")
    return value


def nonnegative_int(value: Any, label: str) -> int:
    if type(value) is not int or value < 0:
        raise EvidenceError(f"{label} must be a non-negative integer")
    return value


def resolve_system_git() -> Path:
    for candidate in (Path("/usr/bin/git"), Path("/bin/git")):
        if candidate.exists():
            resolved = candidate.resolve(strict=True)
            regular_file(resolved, "system Git", executable=True)
            return resolved
    raise EvidenceError("no fixed-path system Git is available")


def resolve_system_curl() -> Path:
    for candidate in (Path("/usr/bin/curl"), Path("/bin/curl")):
        if candidate.exists():
            resolved = candidate.resolve(strict=True)
            regular_file(resolved, "system curl", executable=True)
            return resolved
    raise EvidenceError("no fixed-path system curl is available for published-source acquisition")


def controlled_git_environment(repo: Path) -> dict[str, str]:
    return {
        "PATH": FIXED_PATH,
        "HOME": str(repo),
        "LC_ALL": "C",
        "LANG": "C",
        "TZ": "UTC",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_TERMINAL_PROMPT": "0",
    }


def controlled_git_argv(git: Path, repo: Path, arguments: list[str]) -> list[str]:
    command = [str(git)]
    for override in (*GIT_CONFIG_OVERRIDES, f"core.worktree={repo}"):
        command.extend(("-c", override))
    command.extend(("-C", str(repo), *arguments))
    return command


def git_output(git: Path, repo: Path, arguments: list[str], *, timeout: int = 30) -> bytes:
    try:
        result = subprocess.run(
            controlled_git_argv(git, repo, arguments),
            env=controlled_git_environment(repo),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise EvidenceError(f"could not run Git {' '.join(arguments)}: {error}") from error
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise EvidenceError(f"Git {' '.join(arguments)} failed: {detail}")
    return result.stdout


def require_no_local_excludes(repo: Path, git: Path) -> None:
    raw = git_output(git, repo, ["rev-parse", "--git-path", "info/exclude"])
    text = raw.decode("utf-8", errors="strict").strip()
    path = Path(text) if os.path.isabs(text) else repo / text
    try:
        info = path.lstat()
    except FileNotFoundError:
        return
    except OSError as error:
        raise EvidenceError(f"cannot inspect local Git excludes at {path}: {error}") from error
    if not stat.S_ISREG(info.st_mode) or info.st_size > 64 * 1024:
        raise EvidenceError("local Git info/exclude must be a bounded regular non-symlink file")
    try:
        contents = path.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise EvidenceError(f"cannot read local Git excludes at {path}: {error}") from error
    if any(line and not line.startswith("#") for line in map(str.strip, contents.splitlines())):
        raise EvidenceError(
            "local Git info/exclude contains material rules; only tracked .gitignore authority is accepted"
        )


def require_visible_index(repo: Path, git: Path) -> None:
    raw = git_output(git, repo, ["ls-files", "-v", "-z"])
    hidden = [entry for entry in raw.split(b"\0") if entry and not entry.startswith(b"H ")]
    if hidden:
        rendered = hidden[0].decode("utf-8", errors="replace")
        raise EvidenceError(
            "Git index contains skip-worktree, assume-unchanged, fsmonitor-valid, "
            f"unmerged, or otherwise hidden entries: {rendered}"
        )


def clean_repository(repo: Path, git: Path) -> dict[str, Any]:
    require_no_local_excludes(repo, git)
    require_visible_index(repo, git)
    top = Path(git_output(git, repo, ["rev-parse", "--show-toplevel"]).decode().strip()).resolve()
    if top != repo:
        raise EvidenceError(f"--repo-root is not the Git top level: {repo} (top level: {top})")
    head = canonical_commit(
        git_output(git, repo, ["rev-parse", "--verify", "HEAD^{commit}"]).decode().strip(),
        "Git HEAD",
    )
    status = git_output(
        git,
        repo,
        ["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none"],
    )
    if status:
        entries = [part.decode("utf-8", errors="replace") for part in status.split(b"\0") if part]
        raise EvidenceError(f"source tree is not clean at {head}: {', '.join(entries[:8])}")

    raw_submodules = git_output(git, repo, ["submodule", "status", "--recursive"])
    submodules: list[dict[str, str]] = []
    for raw_line in raw_submodules.decode("utf-8", errors="strict").splitlines():
        if not raw_line:
            continue
        marker = raw_line[0]
        fields = raw_line[1:].split()
        if marker != " " or len(fields) < 2:
            raise EvidenceError(f"submodule is missing, conflicted, or not at its indexed commit: {raw_line}")
        commit = canonical_commit(fields[0], f"submodule {fields[1]} commit")
        relative = fields[1]
        path = (repo / relative).resolve()
        try:
            path.relative_to(repo)
        except ValueError as error:
            raise EvidenceError(f"submodule escapes repository: {relative}") from error
        actual = canonical_commit(
            git_output(git, path, ["rev-parse", "--verify", "HEAD^{commit}"]).decode().strip(),
            f"submodule {relative} HEAD",
        )
        if actual != commit:
            raise EvidenceError(f"submodule {relative} HEAD differs from the indexed commit")
        require_no_local_excludes(path, git)
        require_visible_index(path, git)
        nested_status = git_output(
            git,
            path,
            ["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none"],
        )
        if nested_status:
            raise EvidenceError(f"submodule {relative} is dirty")
        submodules.append({"path": relative, "commit": commit})
    submodules.sort(key=lambda row: row["path"])
    tree = git_output(git, repo, ["rev-parse", "HEAD^{tree}"]).decode().strip()
    return {
        "head": head,
        "tree": tree,
        "submodules": submodules,
        "clean": True,
        "git_config_overrides": [*GIT_CONFIG_OVERRIDES, f"core.worktree={repo}"],
        "local_excludes": "comments-or-empty-only",
        "index_visibility": "all-entries-H",
    }


def require_safe_output_scope(repo: Path, git: Path, output: Path) -> None:
    try:
        relative = output.relative_to(repo).as_posix()
    except ValueError:
        return
    require_no_local_excludes(repo, git)
    require_visible_index(repo, git)
    tracked = subprocess.run(
        controlled_git_argv(git, repo, ["ls-files", "--error-unmatch", "--", relative]),
        env=controlled_git_environment(repo),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    if tracked.returncode == 0:
        raise EvidenceError(f"in-repository output is tracked and must not be overwritten: {relative}")
    if tracked.returncode != 1:
        detail = tracked.stderr.decode("utf-8", errors="replace").strip()
        raise EvidenceError(f"could not establish tracked-output policy: {detail}")
    result = subprocess.run(
        controlled_git_argv(
            git,
            repo,
            ["check-ignore", "--verbose", "--no-index", "--", relative],
        ),
        env=controlled_git_environment(repo),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode == 1:
        raise EvidenceError(
            "an in-repository output must be Git-ignored so publication cannot dirty exact HEAD"
        )
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise EvidenceError(f"could not establish output ignore policy: {detail}")
    try:
        ignored = result.stdout.decode("utf-8", errors="strict").rstrip("\n")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"Git ignore provenance is not UTF-8: {error}") from error
    if "\n" in ignored or "\r" in ignored or "\t" not in ignored:
        raise EvidenceError("Git ignore provenance is missing or malformed")
    rule, reported = ignored.split("\t", 1)
    fields = rule.split(":", 2)
    if len(fields) != 3 or reported != relative or not fields[1].isdigit() or int(fields[1]) <= 0:
        raise EvidenceError("Git ignore provenance does not bind the requested output")
    source = Path(fields[0])
    if (
        source.is_absolute()
        or source.name != ".gitignore"
        or any(part in ("", ".", "..") for part in source.parts)
        or not fields[2]
    ):
        raise EvidenceError("output ignore authority is not a repo-relative .gitignore rule")
    current = repo
    for index, part in enumerate(source.parts):
        current = current / part
        try:
            info = current.lstat()
        except OSError as error:
            raise EvidenceError(f"cannot inspect ignore authority {source}: {error}") from error
        leaf = index + 1 == len(source.parts)
        if stat.S_ISLNK(info.st_mode) or (leaf and not stat.S_ISREG(info.st_mode)) or (
            not leaf and not stat.S_ISDIR(info.st_mode)
        ):
            raise EvidenceError("output ignore authority is not an exact regular .gitignore")
    git_output(git, repo, ["ls-files", "--error-unmatch", "--", source.as_posix()])


def require_in_repo_output_ancestors(repo: Path, output: Path) -> None:
    """Reject an ignored lexical output whose directory chain escapes via symlink."""
    try:
        relative_parent = output.relative_to(repo).parent
    except ValueError:
        return
    current = repo
    for component in relative_parent.parts:
        if component in ("", ".", ".."):
            raise EvidenceError("in-repository output has an unsafe parent component")
        current /= component
        try:
            info = current.lstat()
        except FileNotFoundError:
            # Later components cannot exist without this parent. atomic_publish
            # creates the missing suffix and then revalidates the entire chain.
            return
        except OSError as error:
            raise EvidenceError(f"cannot inspect output ancestor {current}: {error}") from error
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
            raise EvidenceError(
                f"in-repository output ancestor must be a real non-symlink directory: {current}"
            )


@dataclass(frozen=True)
class Capture:
    command: list[str]
    exit_code: int
    stdout: bytes
    stderr: bytes

    def record(self, *, include_text: bool = True) -> dict[str, Any]:
        result: dict[str, Any] = {
            "command": self.command,
            "exit_code": self.exit_code,
            "stdout": {"size": len(self.stdout), "sha256": sha256_bytes(self.stdout)},
            "stderr": {"size": len(self.stderr), "sha256": sha256_bytes(self.stderr)},
        }
        if include_text:
            try:
                result["stdout"]["utf8"] = self.stdout.decode("utf-8", errors="strict")
                result["stderr"]["utf8"] = self.stderr.decode("utf-8", errors="strict")
            except UnicodeDecodeError as error:
                raise EvidenceError(f"captured command output is not UTF-8: {error}") from error
        return result


def run_capture(
    command: list[str],
    *,
    cwd: Path,
    environment: dict[str, str],
    scratch: Path,
    label: str,
    timeout: int,
    max_output_bytes: int,
) -> Capture:
    # Keep both streams in bounded memory while the child is live. Redirecting
    # to ordinary files and checking their size after wait() lets a noisy or
    # hostile tool consume unbounded disk until the timeout.
    del scratch  # retained in the call contract for compatibility
    process: subprocess.Popen[bytes] | None = None
    selector = selectors.DefaultSelector()
    streams: dict[int, tuple[str, bytearray]] = {}

    def terminate() -> None:
        assert process is not None
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                process.kill()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()

    try:
        process = subprocess.Popen(
            command,
            cwd=cwd,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
        assert process.stdout is not None and process.stderr is not None
        for name, stream in (("stdout", process.stdout), ("stderr", process.stderr)):
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ)
            streams[stream.fileno()] = (name, bytearray())

        deadline = time.monotonic() + timeout
        post_exit_deadline: float | None = None
        while selector.get_map() or process.poll() is None:
            now = time.monotonic()
            if process.poll() is None:
                if now >= deadline:
                    terminate()
                    raise EvidenceError(f"{label} exceeded its {timeout}s timeout")
            elif post_exit_deadline is None:
                post_exit_deadline = now + 0.5
            elif selector.get_map() and now >= post_exit_deadline:
                terminate()
                raise EvidenceError(
                    f"{label} spawned a background descendant that retained an output stream"
                )

            remaining = max(0.0, deadline - now)
            wait = min(0.1, remaining)
            if post_exit_deadline is not None:
                wait = min(wait, max(0.0, post_exit_deadline - now))
            events = selector.select(wait) if selector.get_map() else []
            if not events and not selector.get_map():
                time.sleep(min(0.01, wait))
                continue
            for key, _ in events:
                stream = key.fileobj
                descriptor = stream.fileno()
                try:
                    chunk = os.read(descriptor, 64 * 1024)
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(stream)
                    stream.close()
                    continue
                name, retained = streams[descriptor]
                if len(retained) + len(chunk) > max_output_bytes:
                    terminate()
                    raise EvidenceError(
                        f"{label} {name} exceeds the {max_output_bytes}-byte limit"
                    )
                retained.extend(chunk)

        exit_code = process.wait()
    except EvidenceError:
        raise
    except OSError as error:
        if process is not None:
            terminate()
        raise EvidenceError(f"could not run {label}: {error}") from error
    finally:
        selector.close()
        if process is not None:
            for stream in (process.stdout, process.stderr):
                if stream is not None and not stream.closed:
                    stream.close()
    stdout = bytes(next(buffer for name, buffer in streams.values() if name == "stdout"))
    stderr = bytes(next(buffer for name, buffer in streams.values() if name == "stderr"))
    return Capture(command, exit_code, stdout, stderr)


def scrubbed_environment(
    stage_root: Path, scratch: Path
) -> tuple[dict[str, str], dict[str, str], dict[str, Any]]:
    home = scratch / "home"
    temporary = scratch / "tmp"
    cargo_home = scratch / "cargo-home"
    rustup_home = scratch / "rustup-home"
    for directory in (home, temporary, cargo_home, rustup_home):
        directory.mkdir(mode=0o700)
    provenance_environment = {
        "PATH": FIXED_PATH,
        "HOME": str(home),
        "TMPDIR": str(temporary),
        "TMP": str(temporary),
        "TEMP": str(temporary),
        "LC_ALL": "C",
        "LANG": "C",
        "TZ": "UTC",
        "PYTHONNOUSERSITE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    library_paths: list[str] = []
    for candidate in [stage_root / "lib", *sorted((stage_root / "lib/rustlib").glob("*/lib"))]:
        if candidate.is_dir():
            library_paths.append(str(candidate))
    library_variable = "DYLD_LIBRARY_PATH" if sys.platform == "darwin" else "LD_LIBRARY_PATH"
    if library_paths:
        provenance_environment[library_variable] = os.pathsep.join(library_paths)
    measurement_environment = dict(provenance_environment)
    measurement_environment.update(
        {
            "PATH": f"{stage_root / 'bin'}:{FIXED_PATH}",
            "CARGO_HOME": str(cargo_home),
            "RUSTUP_HOME": str(rustup_home),
            "CARGO_NET_OFFLINE": "true",
        }
    )
    provenance_value_hashes = {
        name: sha256_bytes(value.encode("utf-8"))
        for name, value in sorted(provenance_environment.items())
    }
    measurement_value_hashes = {
        name: sha256_bytes(value.encode("utf-8"))
        for name, value in sorted(measurement_environment.items())
    }
    authority = {
        "schema": "trust.downstream-diagnostic-environment.v1",
        "policy": "closed-values-no-ambient-inheritance",
        "fixed_system_path": FIXED_PATH,
        "stage_bin_prepended": True,
        "derived_stage_library_paths": library_paths,
        "runtime_library_variable": library_variable,
        "provenance_verification_value_sha256_by_name": provenance_value_hashes,
        "provenance_verification_canonical_sha256": sha256_bytes(
            compact_json_bytes(provenance_value_hashes)
        ),
        "measurement_value_sha256_by_name": measurement_value_hashes,
        "measurement_canonical_sha256": sha256_bytes(
            compact_json_bytes(measurement_value_hashes)
        ),
        "excluded_ambient_names": sorted(os.environ),
    }
    return measurement_environment, provenance_environment, authority


def resolve_stage_root(repo: Path, argument: str | None) -> Path:
    if argument:
        lexical = Path(argument).expanduser()
        if lexical.is_symlink():
            raise EvidenceError("--stage2-root must not be a symlink")
        stage_root = lexical.resolve(strict=True)
    else:
        candidates = sorted(
            path.resolve()
            for path in (repo / "build").glob("*/stage2")
            if path.is_dir() and not path.is_symlink()
        )
        if len(candidates) != 1:
            raise EvidenceError(
                "could not select exactly one repository-local build/*/stage2; "
                f"found {len(candidates)} (pass --stage2-root)"
            )
        stage_root = candidates[0]
    try:
        relative = stage_root.relative_to(repo)
    except ValueError as error:
        raise EvidenceError("Stage2 root must be repository-local") from error
    if len(relative.parts) != 3 or relative.parts[0] != "build" or relative.parts[2] != "stage2":
        raise EvidenceError("Stage2 root must match repository-local build/*/stage2")
    return stage_root


def resolve_tools(stage_root: Path) -> dict[str, Path]:
    tools: dict[str, Path] = {}
    binary_dir = stage_root / "bin"
    for name in TOOL_PROBES:
        path = binary_dir / name
        regular_file(path, name, executable=True)
        if path.resolve(strict=True) != path:
            raise EvidenceError(f"{name} must be the exact non-symlink Stage2 sibling: {path}")
        tools[name] = path
    if len({path.parent for path in tools.values()}) != 1:
        raise EvidenceError("trustc, targo, targo-trust, and trustd are not exact siblings")
    return tools


def parse_identity(capture: Capture, label: str) -> str:
    if capture.exit_code != 0:
        raise EvidenceError(f"{label} identity probe exited {capture.exit_code}")
    if capture.stderr:
        raise EvidenceError(f"{label} identity probe wrote unexpected stderr")
    try:
        text = capture.stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{label} identity is not UTF-8: {error}") from error
    if not text.strip():
        raise EvidenceError(f"{label} identity is empty")
    return text.rstrip("\n")


def identity_field(identity: str, field: str, label: str) -> str:
    prefix = f"{field}:"
    values = [line[len(prefix) :].strip() for line in identity.splitlines() if line.startswith(prefix)]
    if len(values) != 1 or not values[0]:
        raise EvidenceError(f"{label} identity must contain exactly one non-empty {field!r} field")
    return values[0]


def validate_tool_identities(
    captures: dict[str, Capture], identities: dict[str, str], head: str
) -> None:
    expected_prefixes = {
        "trustc": "rustc ",
        "targo": "targo ",
        "targo-trust": "targo-trust ",
        "trustd": "trustd ",
    }
    for name, prefix in expected_prefixes.items():
        if not identities[name].splitlines()[0].startswith(prefix):
            raise EvidenceError(f"{name} identity does not identify the expected sibling")
    for name, field in (
        ("trustc", "commit-hash"),
        ("targo", "commit-hash"),
        ("targo-trust", "trust-repo-commit-hash"),
        ("trustd", "trust-repo-commit-hash"),
    ):
        if identity_field(identities[name], field, name) != head:
            raise EvidenceError(f"{name} identity is not bound to exact Git HEAD {head}")
    # Keep the parameter used: callers cannot accidentally validate different captures.
    if set(captures) != set(TOOL_PROBES):
        raise EvidenceError("internal tool identity capture set is incomplete")


def validate_stage_provenance(
    value: Any,
    *,
    repo: Path,
    stage_root: Path,
    git_state: dict[str, Any],
    tools: dict[str, Path],
    tool_records: dict[str, dict[str, Any]],
    identities: dict[str, str],
) -> dict[str, Any]:
    if not isinstance(value, dict) or value.get("schema") != PROVENANCE_SCHEMA:
        raise EvidenceError("Stage2 provenance does not use trust.stage-tool-provenance.v2")
    if value.get("status") not in ACCEPTED_PROVENANCE:
        raise EvidenceError(f"Stage2 provenance status is not accepted: {value.get('status')!r}")
    if value.get("stage") != 2 or value.get("source_tree_clean") is not True:
        raise EvidenceError("Stage2 provenance is not a clean Stage2 receipt")
    if value.get("path_scope") != "repository-root-relative":
        raise EvidenceError("Stage2 provenance paths are not repository-root-relative")
    if value.get("tool_binding_status") != "ready" or value.get("errors") != []:
        raise EvidenceError("Stage2 provenance tool binding is not ready and error-free")
    if value.get("trust_from_trust") is not True:
        raise EvidenceError("Stage2 provenance is not Trust-from-Trust")
    expected_stage = stage_root.relative_to(repo).as_posix()
    if value.get("stage_root") != expected_stage:
        raise EvidenceError("Stage2 provenance names a different sysroot")

    lineage = value.get("source_lineage")
    if not isinstance(lineage, dict) or (
        lineage.get("schema") != "trust.source-lineage.v1"
        or lineage.get("status") != "immutable_release"
        or lineage.get("source_tree_clean") is not True
        or lineage.get("stable_across_build") is not True
        or lineage.get("errors") != []
    ):
        raise EvidenceError("Stage2 provenance source lineage is not immutable and clean")
    repositories = lineage.get("repositories")
    if not isinstance(repositories, list):
        raise EvidenceError("Stage2 provenance has no recursive repository inventory")
    recorded: dict[str, str] = {}
    for row in repositories:
        if not isinstance(row, dict) or not isinstance(row.get("path"), str):
            raise EvidenceError("Stage2 provenance contains a malformed repository row")
        path = row["path"]
        if path in recorded:
            raise EvidenceError(f"Stage2 provenance repeats repository {path}")
        recorded[path] = canonical_commit(row.get("head"), f"provenance repository {path} HEAD")
        for flag in (
            "has_staged_changes",
            "has_unstaged_changes",
        ):
            if row.get(flag) is not False:
                raise EvidenceError(f"Stage2 provenance repository {path} has {flag}")
        for list_field in (
            "untracked_files",
            "conflict_paths",
            "assume_unchanged_paths",
            "skip_worktree_paths",
            "fsmonitor_valid_paths",
            "working_tree_mismatch_paths",
        ):
            if row.get(list_field) != []:
                raise EvidenceError(f"Stage2 provenance repository {path} has non-empty {list_field}")
    current = {".": git_state["head"]}
    current.update({row["path"]: row["commit"] for row in git_state["submodules"]})
    if recorded != current:
        raise EvidenceError("Stage2 provenance recursive source closure differs from current Git state")

    compiler = value.get("compiler")
    if not isinstance(compiler, dict):
        raise EvidenceError("Stage2 provenance has no compiler binding")
    trustc = tools["trustc"]
    if (
        compiler.get("path") != trustc.relative_to(repo).as_posix()
        or compiler.get("compiler_sha256") != tool_records["trustc"]["sha256"]
        or compiler.get("source_commit") != git_state["head"]
        or compiler.get("compiler_verbose") != identities["trustc"]
    ):
        raise EvidenceError("Stage2 provenance compiler identity/hash/source binding differs")

    rows = value.get("tools")
    if not isinstance(rows, list):
        raise EvidenceError("Stage2 provenance has no tool rows")
    by_name: dict[str, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("name"), str):
            raise EvidenceError("Stage2 provenance contains a malformed tool row")
        name = row["name"]
        if name in by_name:
            raise EvidenceError(f"Stage2 provenance repeats tool {name}")
        by_name[name] = row
    for name in ("targo", "targo-trust", "trustd"):
        row = by_name.get(name)
        if row is None:
            raise EvidenceError(f"Stage2 provenance does not bind required sibling {name}")
        if (
            row.get("path") != tools[name].relative_to(repo).as_posix()
            or row.get("sha256") != tool_records[name]["sha256"]
            or row.get("status") != "bound"
            or row.get("version_probe_ok") is not True
            or row.get("version") != identities[name].splitlines()[0]
        ):
            raise EvidenceError(f"Stage2 provenance {name} identity/hash/path binding differs")
    return {"host": value.get("host"), "status": value["status"]}


def tree_manifest(root: Path, label: str, *, json_only: bool = False) -> dict[str, Any]:
    if not root.is_dir() or root.is_symlink():
        raise EvidenceError(f"{label} must be a real directory: {root}")
    rows: list[dict[str, Any]] = []
    def_paths: set[str] = set()
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root).as_posix()
        info = path.lstat()
        if stat.S_ISDIR(info.st_mode):
            continue
        if not stat.S_ISREG(info.st_mode):
            raise EvidenceError(f"{label} contains a symlink or non-regular file: {relative}")
        if json_only and path.suffix != ".json":
            raise EvidenceError(f"{label} contains non-JSON output: {relative}")
        if "\n" in relative or "\r" in relative or "\t" in relative:
            raise EvidenceError(f"{label} contains an unsafe path: {relative!r}")
        if json_only:
            value = strict_json_file(path, f"{label} {relative}")
            if not isinstance(value, dict):
                raise EvidenceError(f"{label} dump is not a JSON object: {relative}")
            def_path = value.get("def_path")
            if not isinstance(def_path, str) or not def_path:
                raise EvidenceError(f"{label} dump has no non-empty def_path: {relative}")
            if def_path in def_paths:
                raise EvidenceError(f"{label} repeats function identity {def_path!r}")
            def_paths.add(def_path)
        row = relative_file_record(root, path, f"{label} {relative}")
        if json_only:
            row["def_path"] = def_path
        rows.append(row)
    manifest = compact_json_bytes(rows)
    return {
        "root": str(root),
        "count": len(rows),
        "bytes": sum(row["size"] for row in rows),
        "manifest_encoding": (
            "canonical-json-dump-rows-v1" if json_only else "canonical-json-file-rows-v1"
        ),
        "manifest_sha256": sha256_bytes(manifest),
        "files": rows,
        **({"def_paths": sorted(def_paths)} if json_only else {}),
    }


def validate_source_selection(fixture: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    selection_path = fixture / SOURCE_SELECTION_REL
    selection = strict_json_file(selection_path, "published source selection")
    if not isinstance(selection, dict) or selection.get("schema") != SOURCE_SCHEMA:
        raise EvidenceError("source selection does not use the canonical schema")
    if selection.get("crate") != "lambda_calculus":
        raise EvidenceError("source selection names a different crate")
    archive = selection.get("archive")
    if not isinstance(archive, dict) or (
        archive.get("sha256") != ARCHIVE_SHA256 or archive.get("url") != ARCHIVE_URL
    ):
        raise EvidenceError("source selection does not carry the reviewed crates.io checksum pin")
    declared = selection.get("selection")
    if not isinstance(declared, dict) or (
        declared.get("version") != "3.5.0"
        or declared.get("edition") != "2024"
        or declared.get("features") != ["encoding"]
        or declared.get("dependencies") != 0
        or declared.get("kind") != "published-crates-io-tarball-verbatim-source"
    ):
        raise EvidenceError("source selection metadata differs from the reviewed crate/default feature")

    source = fixture / "SOURCE"
    manifest = tree_manifest(source, "vendored SOURCE")
    pinned = selection.get("source_tree")
    if not isinstance(pinned, dict):
        raise EvidenceError("source selection has no source-tree pin")
    canonical_commit(pinned.get("vcs_commit"), "source selection publisher VCS commit")
    for key in ("file_count", "bytes", "manifest_encoding", "manifest_sha256"):
        actual_key = "count" if key == "file_count" else key
        if pinned.get(key) != manifest.get(actual_key):
            raise EvidenceError(f"vendored SOURCE differs from pinned {key}")

    cargo_toml = source / "Cargo.toml"
    try:
        cargo = tomllib.loads(cargo_toml.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise EvidenceError(f"could not parse vendored Cargo.toml: {error}") from error
    package = cargo.get("package")
    if not isinstance(package, dict) or (
        package.get("name") != "lambda_calculus"
        or package.get("version") != "3.5.0"
        or str(package.get("edition")) != "2024"
    ):
        raise EvidenceError("vendored Cargo.toml package identity differs")
    features = cargo.get("features")
    if not isinstance(features, dict) or features.get("default") != ["encoding"]:
        raise EvidenceError("vendored Cargo.toml default feature selection differs")
    dependencies = cargo.get("dependencies", {})
    if dependencies != {}:
        raise EvidenceError("vendored lambda_calculus selection unexpectedly has dependencies")
    vcs = strict_json_file(source / ".cargo_vcs_info.json", "vendored cargo VCS metadata")
    vcs_commit = vcs.get("git", {}).get("sha1") if isinstance(vcs, dict) else None
    if vcs_commit != pinned.get("vcs_commit"):
        raise EvidenceError("vendored Cargo VCS commit differs from source selection")
    return selection, manifest


def source_fetch_environment(scratch: Path) -> dict[str, str]:
    home = scratch / "source-fetch-home"
    temporary = scratch / "source-fetch-tmp"
    home.mkdir(mode=0o700)
    temporary.mkdir(mode=0o700)
    return {
        "PATH": FIXED_PATH,
        "HOME": str(home),
        "TMPDIR": str(temporary),
        "TMP": str(temporary),
        "TEMP": str(temporary),
        "LC_ALL": "C",
        "LANG": "C",
        "TZ": "UTC",
    }


def require_archive_size(archive: Path, label: str) -> os.stat_result:
    info = regular_file(archive, label)
    if info.st_size <= 0 or info.st_size > MAX_ARCHIVE_BYTES:
        raise EvidenceError(
            f"{label} size {info.st_size} is outside 1..={MAX_ARCHIVE_BYTES}"
        )
    return info


def acquire_published_archive(
    supplied: str | None,
    *,
    repo: Path,
    scratch: Path,
    timeout: int,
    max_output_bytes: int,
) -> tuple[Path, dict[str, Any], tuple[Path, dict[str, Any]] | None]:
    if supplied is not None:
        lexical = Path(supplied).expanduser()
        if lexical.is_symlink():
            raise EvidenceError("--source-archive must be a regular non-symlink file")
        try:
            archive = lexical.resolve(strict=True)
        except OSError as error:
            raise EvidenceError(f"could not resolve --source-archive {lexical}: {error}") from error
        require_archive_size(archive, "supplied published-source archive")
        record = file_record(archive, "supplied published-source archive")
        return (
            archive,
            {
                "kind": "caller-supplied-archive-with-collector-owned-checksum-pin",
                "input": record,
                "network_fetch_performed": False,
            },
            None,
        )

    curl = resolve_system_curl()
    curl_record = file_record(curl, "system curl", executable=True)
    archive = scratch / "lambda_calculus-3.5.0.crate"
    command = [
        str(curl),
        "--disable",
        "--fail",
        "--silent",
        "--show-error",
        "--location",
        "--proto",
        "=https",
        "--proto-redir",
        "=https",
        "--connect-timeout",
        "30",
        "--max-time",
        str(timeout),
        "--max-filesize",
        str(MAX_ARCHIVE_BYTES),
        "--output",
        str(archive),
        ARCHIVE_URL,
    ]
    capture = run_capture(
        command,
        cwd=repo,
        environment=source_fetch_environment(scratch),
        scratch=scratch,
        label="published-source-fetch",
        timeout=timeout + 5,
        max_output_bytes=max_output_bytes,
    )
    if capture.exit_code != 0:
        raise EvidenceError(f"checksum-pinned crates.io archive fetch exited {capture.exit_code}")
    if capture.stdout:
        raise EvidenceError("checksum-pinned crates.io archive fetch wrote unexpected stdout")
    require_archive_size(archive, "fetched published-source archive")
    return (
        archive,
        {
            "kind": "fixed-url-https-fetch",
            "network_fetch_performed": True,
            "tool": curl_record,
            "capture": capture.record(),
        },
        (curl, curl_record),
    )


def validate_published_archive(
    archive: Path, source_manifest: dict[str, Any]
) -> dict[str, Any]:
    info = require_archive_size(archive, "checksum-pinned published-source archive")
    try:
        archive_bytes = archive.read_bytes()
    except OSError as error:
        raise EvidenceError(f"could not read published-source archive {archive}: {error}") from error
    observed_sha256 = sha256_bytes(archive_bytes)
    if observed_sha256 != ARCHIVE_SHA256:
        raise EvidenceError(
            "published-source archive does not match the collector-owned crates.io checksum pin"
        )

    rows: list[dict[str, Any]] = []
    names: set[str] = set()
    casefolded_names: set[str] = set()
    try:
        with tarfile.open(fileobj=io.BytesIO(archive_bytes), mode="r:gz") as package:
            for member in package.getmembers():
                name = member.name
                path = PurePosixPath(name)
                parts = path.parts
                if (
                    not name
                    or name.startswith("/")
                    or "\\" in name
                    or path.as_posix() != name
                    or len(parts) < 2
                    or parts[0] != ARCHIVE_ROOT
                    or any(part in ("", ".", "..") for part in parts)
                    or any(character in name for character in ("\0", "\n", "\r", "\t"))
                ):
                    raise EvidenceError(f"published-source archive contains unsafe path {name!r}")
                relative = PurePosixPath(*parts[1:]).as_posix()
                folded = relative.casefold()
                if relative in names or folded in casefolded_names:
                    raise EvidenceError(
                        f"published-source archive repeats or case-collides path {relative!r}"
                    )
                names.add(relative)
                casefolded_names.add(folded)
                if not member.isfile():
                    raise EvidenceError(
                        f"published-source archive member is not a regular file: {relative}"
                    )
                extracted = package.extractfile(member)
                if extracted is None:
                    raise EvidenceError(
                        f"could not read published-source archive member: {relative}"
                    )
                contents = extracted.read()
                if len(contents) != member.size:
                    raise EvidenceError(
                        f"published-source archive member was truncated: {relative}"
                    )
                rows.append(
                    {
                        "path": relative,
                        "size": len(contents),
                        "sha256": sha256_bytes(contents),
                    }
                )
    except (OSError, tarfile.TarError) as error:
        raise EvidenceError(f"could not parse checksum-pinned published-source archive: {error}") from error

    rows.sort(key=lambda row: row["path"])
    archive_manifest = {
        "root": ARCHIVE_ROOT,
        "count": len(rows),
        "bytes": sum(row["size"] for row in rows),
        "manifest_encoding": "canonical-json-file-rows-v1",
        "manifest_sha256": sha256_bytes(compact_json_bytes(rows)),
        "files": rows,
    }
    for key in ("count", "bytes", "manifest_encoding", "manifest_sha256", "files"):
        if archive_manifest[key] != source_manifest.get(key):
            raise EvidenceError(
                "vendored SOURCE does not exactly match the checksum-pinned crates.io archive"
            )
    return {
        "url": ARCHIVE_URL,
        "expected_sha256": ARCHIVE_SHA256,
        "observed_sha256": observed_sha256,
        "size": len(archive_bytes),
        "format": "gzip-compressed-tar",
        "member_policy": "one exact top-level root; regular files only; no duplicate or unsafe paths",
        "member_manifest": archive_manifest,
        "vendored_source_comparison": "exact-path-size-sha256-match",
        "status": "verified",
    }


def validate_generated_outputs(
    generated: Path, max_transcript_bytes: int
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    full = tree_manifest(generated / "full", "fresh full dump population", json_only=True)
    core = tree_manifest(generated / "core", "fresh core dump population", json_only=True)
    if full["count"] == 0 or core["count"] == 0:
        raise EvidenceError("fresh dump population is vacuous")
    full_rows = {row["path"]: row for row in full["files"]}
    core_rows = {row["path"]: row for row in core["files"]}
    expected_core = {path: row for path, row in full_rows.items() if "data__" not in path}
    if core_rows != expected_core:
        raise EvidenceError("fresh core dumps are not the exact mechanical non-data subset")

    def read_count(name: str, expected: int) -> None:
        path = generated / name
        regular_file(path, name)
        try:
            value = int(path.read_text(encoding="utf-8").strip())
        except (OSError, UnicodeError, ValueError) as error:
            raise EvidenceError(f"could not parse {name}: {error}") from error
        if value != expected:
            raise EvidenceError(f"{name} does not match the observed manifest")

    read_count("full.count", full["count"])
    read_count("core.count", core["count"])
    artifacts: dict[str, Any] = {}
    for name in (
        "compiler.argv",
        "compiler.env",
        "compiler.stdout",
        "compiler.stderr",
        "compiler.exit-code",
        "full.count",
        "core.count",
    ):
        path = generated / name
        artifacts[name] = file_record(path, f"generated {name}")
        artifacts[name]["path"] = name
    output_library = generated / "out.rlib"
    if output_library.exists() or output_library.is_symlink():
        artifacts["out.rlib"] = file_record(output_library, "generated out.rlib")
        artifacts["out.rlib"]["path"] = "out.rlib"
    known = {"full", "core", *artifacts}
    for path in generated.iterdir():
        if path.name not in known:
            raise EvidenceError(f"regeneration produced an unaccounted output: {path.name}")
    if (generated / "compiler.exit-code").read_text(encoding="utf-8") != "0\n":
        raise EvidenceError("compiler transcript records a nonzero exit")
    for name in ("compiler.stdout", "compiler.stderr"):
        if artifacts[name]["size"] > max_transcript_bytes:
            raise EvidenceError(
                f"{name} exceeds the {max_transcript_bytes}-byte evidence limit"
            )
    environment_rows = (generated / "compiler.env").read_text(encoding="utf-8").splitlines()
    compiler_environment: dict[str, str] = {}
    for row in environment_rows:
        name, separator, value = row.partition("=")
        if not separator or not name or name in compiler_environment:
            raise EvidenceError("compiler.env contains a malformed or duplicate row")
        compiler_environment[name] = value
    transcript = {
        "argv": (generated / "compiler.argv").read_text(encoding="utf-8").splitlines(),
        "environment": compiler_environment,
        "stdout": {
            **artifacts["compiler.stdout"],
            "utf8": (generated / "compiler.stdout").read_text(encoding="utf-8"),
        },
        "stderr": {
            **artifacts["compiler.stderr"],
            "utf8": (generated / "compiler.stderr").read_text(encoding="utf-8"),
        },
        "exit_code": 0,
    }
    return full, core, {"files": artifacts, "compiler_transcript": transcript}


def validate_prove_scorecard(
    value: Any, expected_def_paths: list[str], budget: int
) -> dict[str, Any]:
    if not isinstance(value, dict) or value.get("schema") != PROVE_SCHEMA:
        raise EvidenceError("prove output does not use trust.prove-scorecard.v1")
    if value.get("status") != "measured" or value.get("bridge_gate_error") is not None:
        raise EvidenceError("prove output is not an accepted measured scorecard")
    if value.get("budget_secs_per_function") != budget:
        raise EvidenceError("prove output does not bind the requested per-function budget")
    scorecard = value.get("scorecard")
    if not isinstance(scorecard, dict):
        raise EvidenceError("prove output has no scorecard")
    expected_total = len(expected_def_paths)
    total = nonnegative_int(scorecard.get("total"), "prove scorecard total")
    if total != expected_total:
        raise EvidenceError(
            f"prove denominator {total} differs from fresh core dump count {expected_total}"
        )
    if nonnegative_int(scorecard.get("kernel_rejected"), "kernel_rejected") != 0:
        raise EvidenceError("prove scorecard contains a kernel rejection")
    if scorecard.get("rejections") != []:
        raise EvidenceError("prove scorecard contains rejection records")
    if not isinstance(scorecard.get("bridge_agreement"), dict):
        raise EvidenceError("prove scorecard has no attached bridge-agreement result")
    safety_faithfulness_subtypes = (
        "safety_vc_faithful_overflow",
        "safety_vc_faithful_usub",
        "safety_vc_faithful_signed_overflow",
        "safety_vc_faithful_bounds",
        "safety_vc_faithful_div",
        "safety_vc_faithful_rem",
        "safety_vc_faithful_negation",
        "safety_vc_faithful_shift",
    )
    for field in (
        "inhabited",
        "type_grounded_not_inhabited",
        "not_grounded",
        "fully_faithful",
        "fully_faithful_via_trustir",
        "fully_faithful_mirsem_fallback",
        "safety_vc_faithful",
        *safety_faithfulness_subtypes,
        "declined",
        "total_obligations",
        "postcondition_obligations",
        "safety_obligations",
        "safety_discharged",
        "loop_headers_detected",
        "loop_headers_recognized",
    ):
        nonnegative_int(scorecard.get(field), f"prove scorecard {field}")
    if scorecard["postcondition_obligations"] + scorecard["safety_obligations"] != scorecard["total_obligations"]:
        raise EvidenceError("prove scorecard obligation partition is inconsistent")
    if scorecard["safety_discharged"] > scorecard["safety_obligations"]:
        raise EvidenceError("prove scorecard overstates discharged safety obligations")
    if scorecard["loop_headers_recognized"] > scorecard["loop_headers_detected"]:
        raise EvidenceError("prove scorecard recognizes more loop headers than it detected")
    for field in (
        "inhabited",
        "type_grounded_not_inhabited",
        "not_grounded",
        "fully_faithful",
        "fully_faithful_via_trustir",
        "fully_faithful_mirsem_fallback",
        "safety_vc_faithful",
        *safety_faithfulness_subtypes,
        "declined",
    ):
        if scorecard[field] > total:
            raise EvidenceError(f"prove scorecard {field} exceeds the declared population")
    if scorecard["fully_faithful"] != (
        scorecard["fully_faithful_via_trustir"]
        + scorecard["fully_faithful_mirsem_fallback"]
    ):
        raise EvidenceError("prove scorecard fully-faithful witness partition is inconsistent")
    for field in safety_faithfulness_subtypes:
        if scorecard[field] > scorecard["safety_vc_faithful"]:
            raise EvidenceError(
                f"prove scorecard {field} exceeds its safety_vc_faithful parent tally"
            )

    expected_set = set(expected_def_paths)
    observed_paths: dict[str, set[str]] = {}
    for field, expected_length in (
        ("proven", scorecard["inhabited"]),
        ("declined_paths", scorecard["declined"]),
    ):
        paths = scorecard.get(field)
        if not isinstance(paths, list) or not all(isinstance(path, str) for path in paths):
            raise EvidenceError(f"prove scorecard {field} is not a string list")
        if len(paths) != expected_length or len(set(paths)) != len(paths):
            raise EvidenceError(f"prove scorecard {field} does not match its tally")
        observed_paths[field] = set(paths)
        if not observed_paths[field].issubset(expected_set):
            raise EvidenceError(f"prove scorecard {field} names a function outside the fresh core")
    overlap = observed_paths["proven"] & observed_paths["declined_paths"]
    if overlap:
        raise EvidenceError(
            f"prove scorecard marks a function both proven and declined: {sorted(overlap)[0]}"
        )

    if (
        scorecard["inhabited"]
        + scorecard["type_grounded_not_inhabited"]
        + scorecard["not_grounded"]
        + scorecard["declined"]
        != total
    ):
        raise EvidenceError("prove scorecard function outcome partition is inconsistent")
    return value


@dataclass(frozen=True)
class OutputSnapshot:
    """Identity and contents of an output read through its anchored parent."""

    path: str
    device: int
    inode: int
    mode: int
    size: int
    modified_ns: int
    changed_ns: int
    sha256: str


def _stable_stat_identity(info: os.stat_result) -> tuple[int, int, int, int, int, int]:
    return (
        info.st_dev,
        info.st_ino,
        info.st_mode,
        info.st_size,
        info.st_mtime_ns,
        info.st_ctime_ns,
    )


def _same_captured_receipt(
    expected: OutputSnapshot, captured: OutputSnapshot | None
) -> bool:
    if captured is None:
        return False
    # Moving a leaf can update ctime on some filesystems. The atomic capture
    # must preserve every other inode/content identity field; the full digest
    # prevents an equal-size byte replacement from being admitted.
    return (
        expected.path,
        expected.device,
        expected.inode,
        expected.mode,
        expected.size,
        expected.modified_ns,
        expected.sha256,
    ) == (
        captured.path,
        captured.device,
        captured.inode,
        captured.mode,
        captured.size,
        captured.modified_ns,
        captured.sha256,
    )


class AnchoredOutput:
    """Bind output publication to a no-symlink directory descriptor chain.

    All existing ancestors are opened before measurement and retained until the
    receipt is published.  Publication therefore cannot be redirected by
    renaming an ancestor or replacing it with a directory symlink.  Missing
    parent components are created relative to the deepest held descriptor.
    """

    def __init__(self, path: Path) -> None:
        if not path.is_absolute() or path.anchor != os.path.sep:
            raise EvidenceError(f"output must be an absolute POSIX path: {path}")
        components = path.parts[1:]
        if not components or any(component in ("", ".", "..") for component in components):
            raise EvidenceError(f"output has an unsafe path component: {path}")
        self.path = path
        self._parent_components = components[:-1]
        self._leaf = components[-1]
        self._directory_fds: list[int] = []
        self._opened_components: list[str] = []
        self._closed = False

        flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0) | getattr(os, "O_CLOEXEC", 0)
        try:
            root_fd = os.open(os.path.sep, flags)
        except OSError as error:
            raise EvidenceError(f"cannot anchor output filesystem root: {error}") from error
        self._directory_fds.append(root_fd)
        try:
            for component in self._parent_components:
                child_fd = self._open_existing_directory(
                    self._directory_fds[-1], component
                )
                if child_fd is None:
                    break
                self._directory_fds.append(child_fd)
                self._opened_components.append(component)
            self.verify_chain()
        except BaseException:
            self.close()
            raise

    @staticmethod
    def _open_existing_directory(parent_fd: int, component: str) -> int | None:
        try:
            before = os.stat(component, dir_fd=parent_fd, follow_symlinks=False)
        except FileNotFoundError:
            return None
        except OSError as error:
            raise EvidenceError(f"cannot inspect output ancestor {component!r}: {error}") from error
        if stat.S_ISLNK(before.st_mode) or not stat.S_ISDIR(before.st_mode):
            raise EvidenceError(
                f"output ancestor must be a real non-symlink directory: {component!r}"
            )

        flags = (
            os.O_RDONLY
            | getattr(os, "O_DIRECTORY", 0)
            | getattr(os, "O_CLOEXEC", 0)
            | getattr(os, "O_NOFOLLOW", 0)
        )
        try:
            descriptor = os.open(component, flags, dir_fd=parent_fd)
        except FileNotFoundError as error:
            raise EvidenceError(
                f"output ancestor changed concurrently while being anchored: {component!r}"
            ) from error
        except OSError as error:
            raise EvidenceError(
                f"cannot safely open output ancestor {component!r}: {error}"
            ) from error
        after = os.fstat(descriptor)
        if (
            not stat.S_ISDIR(after.st_mode)
            or (before.st_dev, before.st_ino) != (after.st_dev, after.st_ino)
        ):
            os.close(descriptor)
            raise EvidenceError(
                f"output ancestor changed concurrently while being anchored: {component!r}"
            )
        return descriptor

    def __enter__(self) -> AnchoredOutput:
        return self

    def __exit__(self, _type: Any, _value: Any, _traceback: Any) -> None:
        self.close()

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        for descriptor in reversed(self._directory_fds):
            try:
                os.close(descriptor)
            except OSError:
                pass
        self._directory_fds.clear()

    def _require_open(self) -> None:
        if self._closed:
            raise EvidenceError("output directory anchor is already closed")

    def verify_chain(self) -> None:
        """Prove each held child is still linked from its held parent."""
        self._require_open()
        for index, component in enumerate(self._opened_components):
            parent_fd = self._directory_fds[index]
            child_fd = self._directory_fds[index + 1]
            try:
                linked = os.stat(component, dir_fd=parent_fd, follow_symlinks=False)
                opened = os.fstat(child_fd)
            except OSError as error:
                raise EvidenceError(
                    f"output ancestor changed concurrently: {component!r}: {error}"
                ) from error
            if (
                stat.S_ISLNK(linked.st_mode)
                or not stat.S_ISDIR(linked.st_mode)
                or not stat.S_ISDIR(opened.st_mode)
                or (linked.st_dev, linked.st_ino) != (opened.st_dev, opened.st_ino)
            ):
                raise EvidenceError(
                    f"output ancestor changed concurrently after anchoring: {component!r}"
                )

    def _ensure_parent(self) -> int:
        self.verify_chain()
        for component in self._parent_components[len(self._opened_components) :]:
            parent_fd = self._directory_fds[-1]
            try:
                os.mkdir(component, 0o755, dir_fd=parent_fd)
            except FileExistsError as error:
                raise EvidenceError(
                    f"previously missing output ancestor appeared concurrently: {component!r}"
                ) from error
            except OSError as error:
                raise EvidenceError(
                    f"cannot create output ancestor {component!r}: {error}"
                ) from error
            child_fd = self._open_existing_directory(parent_fd, component)
            if child_fd is None:
                raise EvidenceError(
                    f"new output ancestor disappeared concurrently: {component!r}"
                )
            self._directory_fds.append(child_fd)
            self._opened_components.append(component)
        self.verify_chain()
        return self._directory_fds[-1]

    def snapshot(self) -> OutputSnapshot | None:
        self.verify_chain()
        if len(self._opened_components) != len(self._parent_components):
            return None
        parent_fd = self._directory_fds[-1]
        return self._snapshot_entry(parent_fd, self._leaf)

    def _snapshot_entry(self, parent_fd: int, leaf: str) -> OutputSnapshot | None:
        try:
            before = os.stat(leaf, dir_fd=parent_fd, follow_symlinks=False)
        except FileNotFoundError:
            return None
        except OSError as error:
            raise EvidenceError(f"cannot inspect accepted output receipt: {error}") from error
        if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
            raise EvidenceError("accepted output receipt must be a regular non-symlink file")
        flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
        try:
            descriptor = os.open(leaf, flags, dir_fd=parent_fd)
        except OSError as error:
            raise EvidenceError(f"cannot safely open accepted output receipt: {error}") from error
        try:
            opened = os.fstat(descriptor)
            if (
                not stat.S_ISREG(opened.st_mode)
                or (before.st_dev, before.st_ino) != (opened.st_dev, opened.st_ino)
            ):
                raise EvidenceError("accepted output receipt changed concurrently while opening")
            digest = hashlib.sha256()
            while True:
                chunk = os.read(descriptor, 1024 * 1024)
                if not chunk:
                    break
                digest.update(chunk)
            after = os.fstat(descriptor)
            if _stable_stat_identity(opened) != _stable_stat_identity(after):
                raise EvidenceError("accepted output receipt changed concurrently while reading")
            return OutputSnapshot(
                path=str(self.path),
                device=after.st_dev,
                inode=after.st_ino,
                mode=after.st_mode,
                size=after.st_size,
                modified_ns=after.st_mtime_ns,
                changed_ns=after.st_ctime_ns,
                sha256=digest.hexdigest(),
            )
        finally:
            os.close(descriptor)

    def publish(self, data: bytes, previous: OutputSnapshot | None) -> None:
        parent_fd = self._ensure_parent()
        if self.snapshot() != previous:
            raise EvidenceError("output receipt changed concurrently; refusing to overwrite it")

        descriptor = -1
        temporary: str | None = None
        previous_entry: str | None = None
        create_flags = (
            os.O_WRONLY
            | os.O_CREAT
            | os.O_EXCL
            | getattr(os, "O_CLOEXEC", 0)
            | getattr(os, "O_NOFOLLOW", 0)
        )
        for counter in range(128):
            candidate = f".trust-receipt-{os.getpid()}-{counter}.tmp"
            try:
                descriptor = os.open(candidate, create_flags, 0o600, dir_fd=parent_fd)
                temporary = candidate
                break
            except FileExistsError:
                continue
            except OSError as error:
                raise EvidenceError(f"cannot create receipt temporary: {error}") from error
        if temporary is None:
            raise EvidenceError("could not allocate a unique receipt temporary")
        try:
            with os.fdopen(descriptor, "wb") as handle:
                descriptor = -1
                os.fchmod(handle.fileno(), 0o644)
                handle.write(data)
                handle.flush()
                os.fsync(handle.fileno())
            self.verify_chain()
            if self.snapshot() != previous:
                raise EvidenceError("output receipt changed concurrently; refusing to overwrite it")

            # Capture the exact prior leaf at one rename linearization point.
            # Publishing then uses a no-replace hard link, so a writer racing
            # after that capture is rejected rather than silently overwritten.
            if previous is not None:
                for counter in range(128):
                    candidate = f".trust-receipt-{os.getpid()}-{counter}.previous"
                    try:
                        reservation = os.open(
                            candidate,
                            create_flags,
                            0o600,
                            dir_fd=parent_fd,
                        )
                    except FileExistsError:
                        continue
                    except OSError as error:
                        raise EvidenceError(
                            f"cannot reserve prior receipt capture: {error}"
                        ) from error
                    os.close(reservation)
                    previous_entry = candidate
                    break
                if previous_entry is None:
                    raise EvidenceError("could not reserve a prior receipt capture")
                try:
                    os.rename(
                        self._leaf,
                        previous_entry,
                        src_dir_fd=parent_fd,
                        dst_dir_fd=parent_fd,
                    )
                except OSError as error:
                    os.unlink(previous_entry, dir_fd=parent_fd)
                    previous_entry = None
                    raise EvidenceError(
                        f"could not atomically capture prior output receipt: {error}"
                    ) from error
                captured = self._snapshot_entry(parent_fd, previous_entry)
                if not _same_captured_receipt(previous, captured):
                    try:
                        os.link(
                            previous_entry,
                            self._leaf,
                            src_dir_fd=parent_fd,
                            dst_dir_fd=parent_fd,
                            follow_symlinks=False,
                        )
                        os.unlink(previous_entry, dir_fd=parent_fd)
                        previous_entry = None
                    except FileExistsError:
                        pass
                    raise EvidenceError(
                        "output receipt changed at publication linearization; refusing to overwrite it"
                    )

            try:
                os.link(
                    temporary,
                    self._leaf,
                    src_dir_fd=parent_fd,
                    dst_dir_fd=parent_fd,
                    follow_symlinks=False,
                )
            except FileExistsError as error:
                raise EvidenceError(
                    "output receipt appeared concurrently at publication; refusing to overwrite it"
                ) from error
            os.unlink(temporary, dir_fd=parent_fd)
            temporary = None
            os.fsync(parent_fd)
            if previous_entry is not None:
                os.unlink(previous_entry, dir_fd=parent_fd)
                previous_entry = None
                os.fsync(parent_fd)
        finally:
            if descriptor >= 0:
                os.close(descriptor)
            if temporary is not None:
                try:
                    os.unlink(temporary, dir_fd=parent_fd)
                except FileNotFoundError:
                    pass
            if previous_entry is not None:
                # Restore only into an empty name. Never clobber the writer that
                # made publication fail. If the name is occupied, retain the
                # hidden prior capture for manual recovery.
                try:
                    os.link(
                        previous_entry,
                        self._leaf,
                        src_dir_fd=parent_fd,
                        dst_dir_fd=parent_fd,
                        follow_symlinks=False,
                    )
                except FileExistsError:
                    pass
                else:
                    os.unlink(previous_entry, dir_fd=parent_fd)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".", help="clean Trust Git checkout")
    parser.add_argument("--stage2-root", help="exact repository-local build/*/stage2")
    parser.add_argument("--output", required=True, help="accepted JSON receipt to atomically publish")
    parser.add_argument(
        "--source-archive",
        help=(
            "optional pre-downloaded lambda_calculus-3.5.0.crate; the collector still "
            "enforces its built-in crates.io SHA-256 pin and exact SOURCE comparison"
        ),
    )
    parser.add_argument("--source-fetch-timeout-secs", type=int, default=120)
    parser.add_argument("--prove-budget-secs", type=int, default=30)
    parser.add_argument("--compile-timeout-secs", type=int, default=3600)
    parser.add_argument("--prove-timeout-secs", type=int, default=7200)
    parser.add_argument("--provenance-timeout-secs", type=int, default=600)
    parser.add_argument("--max-output-bytes", type=int, default=128 * 1024 * 1024)
    arguments = parser.parse_args(argv)
    for field in (
        "prove_budget_secs",
        "source_fetch_timeout_secs",
        "compile_timeout_secs",
        "prove_timeout_secs",
        "provenance_timeout_secs",
        "max_output_bytes",
    ):
        if getattr(arguments, field) <= 0:
            parser.error(f"--{field.replace('_', '-')} must be positive")
    return arguments


def collect(
    arguments: argparse.Namespace,
    repo: Path,
    output: Path,
    git: Path,
    output_target: AnchoredOutput,
) -> int:
    require_safe_output_scope(repo, git, output)
    previous_output = output_target.snapshot()
    git_record = file_record(git, "system Git", executable=True)
    python = Path(sys.executable).resolve(strict=True)
    python_record = file_record(python, "collector Python", executable=True)
    git_state = clean_repository(repo, git)
    fixture = repo / FIXTURE_REL
    regenerate = fixture / "regenerate.sh"
    provenance_verifier = repo / PROVENANCE_VERIFIER_REL
    collector = Path(__file__).resolve(strict=True)
    for path, label, executable in (
        (regenerate, "fixture regeneration command", True),
        (provenance_verifier, "Stage2 provenance verifier", False),
        (collector, "diagnostic collector", False),
    ):
        regular_file(path, label, executable=executable)
    source_selection, source_manifest = validate_source_selection(fixture)

    stage_root = resolve_stage_root(repo, arguments.stage2_root)
    tools = resolve_tools(stage_root)
    tool_records = {
        name: file_record(path, name, executable=True) for name, path in tools.items()
    }
    provenance_path = stage_root / "tool-provenance.json"
    provenance_record = file_record(provenance_path, "Stage2 provenance")
    provenance_value = strict_json_file(provenance_path, "Stage2 provenance")
    input_records = {
        "collector": file_record(collector, "diagnostic collector"),
        "regenerate": file_record(regenerate, "fixture regeneration command", executable=True),
        "source_selection": file_record(fixture / SOURCE_SELECTION_REL, "source selection"),
        "fixture_provenance": file_record(fixture / "PROVENANCE.md", "fixture provenance"),
        "provenance_verifier": file_record(provenance_verifier, "Stage2 provenance verifier"),
    }

    with tempfile.TemporaryDirectory(prefix="trust-lambda-diagnostic-") as temporary:
        # macOS exposes /var as a symlink to /private/var.  Bind commands to the
        # canonical scratch spelling so the shell producer and collector agree.
        scratch = Path(temporary).resolve(strict=True)
        environment, provenance_environment, environment_authority = scrubbed_environment(
            stage_root, scratch
        )
        source_archive, source_acquisition, curl_authority = acquire_published_archive(
            arguments.source_archive,
            repo=repo,
            scratch=scratch,
            timeout=arguments.source_fetch_timeout_secs,
            max_output_bytes=arguments.max_output_bytes,
        )
        source_archive_record = file_record(
            source_archive, "checksum-pinned published-source archive"
        )
        published_archive = validate_published_archive(source_archive, source_manifest)
        identity_captures: dict[str, Capture] = {}
        identities: dict[str, str] = {}
        for name, probe in TOOL_PROBES.items():
            capture = run_capture(
                [str(tools[name]), *probe],
                cwd=repo,
                environment=environment,
                scratch=scratch,
                label=f"identity-{name}",
                timeout=30,
                max_output_bytes=arguments.max_output_bytes,
            )
            identity_captures[name] = capture
            identities[name] = parse_identity(capture, name)
        validate_tool_identities(identity_captures, identities, git_state["head"])
        provenance_metadata = validate_stage_provenance(
            provenance_value,
            repo=repo,
            stage_root=stage_root,
            git_state=git_state,
            tools=tools,
            tool_records=tool_records,
            identities=identities,
        )
        host = provenance_metadata["host"]
        if not isinstance(host, str) or not host:
            raise EvidenceError("Stage2 provenance has no host")

        provenance_command = [
            str(python),
            str(provenance_verifier),
            "--verify-stage-provenance",
            "--require-immutable-lineage",
            "--stage",
            "2",
            "--host",
            host,
        ]
        provenance_capture = run_capture(
            provenance_command,
            cwd=repo,
            environment=provenance_environment,
            scratch=scratch,
            label="provenance-verification",
            timeout=arguments.provenance_timeout_secs,
            max_output_bytes=arguments.max_output_bytes,
        )
        if provenance_capture.exit_code != 0:
            raise EvidenceError("canonical Stage2 provenance verification failed")

        generated = scratch / "generated"
        regenerate_command = [
            str(regenerate),
            "--trustc",
            str(tools["trustc"]),
            "--output-root",
            str(generated),
        ]
        regeneration_capture = run_capture(
            regenerate_command,
            cwd=repo,
            environment=provenance_environment,
            scratch=scratch,
            label="regeneration",
            timeout=arguments.compile_timeout_secs,
            max_output_bytes=arguments.max_output_bytes,
        )
        if regeneration_capture.exit_code != 0:
            raise EvidenceError(f"fresh fixture regeneration exited {regeneration_capture.exit_code}")
        full_manifest, core_manifest, generated_evidence = validate_generated_outputs(
            generated, arguments.max_output_bytes
        )
        expected_compiler_argv = [
            str(tools["trustc"]),
            "-Ztrust-dump=mir-only:<dir>",
            f"-Ztrust-dump=mir-only:{generated / 'full'}",
            "-Ztrust-policy=advisory",
            "--edition",
            "2024",
            "--cfg",
            'feature="encoding"',
            "--crate-type",
            "lib",
            "-o",
            str(generated / "out.rlib"),
            str(fixture / "SOURCE/src/lib.rs"),
        ]
        if generated_evidence["compiler_transcript"]["argv"] != expected_compiler_argv:
            raise EvidenceError("regeneration used an unexpected compiler command")
        expected_compiler_environment = {
            "PATH": FIXED_PATH,
            "HOME": str(generated / "compiler-home"),
            "TMPDIR": str(generated / "compiler-tmp"),
            "TMP": str(generated / "compiler-tmp"),
            "TEMP": str(generated / "compiler-tmp"),
            "LC_ALL": "C",
            "LANG": "C",
            "TZ": "UTC",
            "CARGO_NET_OFFLINE": "true",
        }
        runtime_paths = environment_authority["derived_stage_library_paths"]
        if runtime_paths:
            expected_compiler_environment[
                environment_authority["runtime_library_variable"]
            ] = os.pathsep.join(runtime_paths)
        if generated_evidence["compiler_transcript"]["environment"] != expected_compiler_environment:
            raise EvidenceError("regeneration used an unexpected compiler environment")

        prove_command = [
            str(tools["targo"]),
            "trust",
            "prove",
            "--kernel",
            "--dump-dir",
            str(generated / "core"),
            f"--budget-secs={arguments.prove_budget_secs}",
            "--format=json",
        ]
        prove_capture = run_capture(
            prove_command,
            cwd=repo,
            environment=environment,
            scratch=scratch,
            label="prove-core",
            timeout=arguments.prove_timeout_secs,
            max_output_bytes=arguments.max_output_bytes,
        )
        if prove_capture.exit_code != 0:
            raise EvidenceError(f"targo trust prove exited {prove_capture.exit_code}")
        prove_value = strict_json_bytes(prove_capture.stdout, "targo trust prove stdout")
        prove_value = validate_prove_scorecard(
            prove_value, core_manifest["def_paths"], arguments.prove_budget_secs
        )

        final_full_manifest, final_core_manifest, final_generated_evidence = (
            validate_generated_outputs(generated, arguments.max_output_bytes)
        )
        if (
            final_full_manifest != full_manifest
            or final_core_manifest != core_manifest
            or final_generated_evidence != generated_evidence
        ):
            raise EvidenceError("generated dumps or compiler transcripts changed during proof")

        provenance_capture_after = run_capture(
            provenance_command,
            cwd=repo,
            environment=provenance_environment,
            scratch=scratch,
            label="provenance-verification-after",
            timeout=arguments.provenance_timeout_secs,
            max_output_bytes=arguments.max_output_bytes,
        )
        if provenance_capture_after.exit_code != 0:
            raise EvidenceError("canonical Stage2 provenance verification failed after measurement")

        # Re-check every mutable authority before publishing.  A failed attempt
        # never writes OUTPUT, so an older accepted receipt remains byte-exact.
        final_git_state = clean_repository(repo, git)
        if final_git_state != git_state:
            raise EvidenceError("Git commit or recursive source closure changed during collection")
        require_unchanged(git, git_record, "system Git", executable=True)
        require_unchanged(python, python_record, "collector Python", executable=True)
        require_unchanged(
            source_archive,
            source_archive_record,
            "checksum-pinned published-source archive",
        )
        if curl_authority is not None:
            curl_path, curl_record = curl_authority
            require_unchanged(curl_path, curl_record, "system curl", executable=True)
        for name, path in tools.items():
            require_unchanged(path, tool_records[name], name, executable=True)
        require_unchanged(provenance_path, provenance_record, "Stage2 provenance")
        for name, path in (
            ("collector", collector),
            ("regenerate", regenerate),
            ("source_selection", fixture / SOURCE_SELECTION_REL),
            ("fixture_provenance", fixture / "PROVENANCE.md"),
            ("provenance_verifier", provenance_verifier),
        ):
            require_unchanged(path, input_records[name], name, executable=name == "regenerate")
        final_selection, final_source_manifest = validate_source_selection(fixture)
        if final_selection != source_selection or final_source_manifest != source_manifest:
            raise EvidenceError("vendored source selection changed during collection")
        final_published_archive = validate_published_archive(
            source_archive, final_source_manifest
        )
        if final_published_archive != published_archive:
            raise EvidenceError("published-source archive verification changed during collection")

        receipt: dict[str, Any] = {
            "schema": SCHEMA,
            "status": "measured",
            "runner_execution_authenticated": False,
            "release_gate_admissible": False,
            "runner_authority": {
                "scope": "diagnostic-only",
                "python_startup_authenticated": False,
                "residual_authority": (
                    "the current Python interpreter started before this collector could scrub "
                    "PYTHONHOME, PYTHONPATH, user-site, or sitecustomize authority"
                ),
                "policy": "never accept this receipt as release proof",
            },
            "created_at_utc": dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z"),
            "claim_boundary": CLAIM_BOUNDARY,
            "git": git_state,
            "system_git": git_record,
            "collector_python": python_record,
            "environment_authority": environment_authority,
            "stage2": {
                "root": stage_root.relative_to(repo).as_posix(),
                "provenance": {
                    **provenance_metadata,
                    "path": provenance_path.relative_to(repo).as_posix(),
                    "size": provenance_record["size"],
                    "sha256": provenance_record["sha256"],
                    "document": provenance_value,
                },
                "provenance_verification": {
                    "before": provenance_capture.record(),
                    "after": provenance_capture_after.record(),
                },
                "tools": {
                    name: {
                        "path": path.relative_to(repo).as_posix(),
                        "size": tool_records[name]["size"],
                        "sha256": tool_records[name]["sha256"],
                        "identity": identities[name],
                        "identity_probe": identity_captures[name].record(),
                    }
                    for name, path in tools.items()
                },
            },
            "inputs": {
                "collector": {
                    **input_records["collector"],
                    "path": collector.relative_to(repo).as_posix(),
                },
                "regenerate": {
                    **input_records["regenerate"],
                    "path": regenerate.relative_to(repo).as_posix(),
                },
                "source_selection": {
                    **input_records["source_selection"],
                    "path": (fixture / SOURCE_SELECTION_REL).relative_to(repo).as_posix(),
                },
                "fixture_provenance": {
                    **input_records["fixture_provenance"],
                    "path": (fixture / "PROVENANCE.md").relative_to(repo).as_posix(),
                },
                "provenance_verifier": {
                    **input_records["provenance_verifier"],
                    "path": provenance_verifier.relative_to(repo).as_posix(),
                },
            },
            "source": {
                "selection": source_selection,
                "manifest": source_manifest,
                "archive_acquisition": source_acquisition,
                "published_archive": published_archive,
                "archive_rechecked_after_measurement": True,
            },
            "regeneration": {
                "capture": regeneration_capture.record(),
                "compiler": generated_evidence["compiler_transcript"],
                "output_files": generated_evidence["files"],
                "full_dump_manifest": full_manifest,
                "core_dump_manifest": core_manifest,
                "core_selection_rule": "basename does not contain data__",
                "fresh_unique_scratch": True,
                "tracked_fixture_dumps_modified": False,
            },
            "proof": {
                "scope": "fresh mechanically selected core dump population",
                "budget_secs_per_function": arguments.prove_budget_secs,
                "wall_timeout_secs": arguments.prove_timeout_secs,
                "capture": prove_capture.record(),
                "scorecard": prove_value,
            },
            "commands": {
                "source_archive_fetch": (
                    source_acquisition.get("capture", {}).get("command")
                    if source_acquisition["network_fetch_performed"]
                    else None
                ),
                "provenance_verification_before_and_after": provenance_command,
                "regeneration": regenerate_command,
                "compiler": expected_compiler_argv,
                "proof": prove_command,
            },
            "limits": {
                "source_fetch_timeout_secs": arguments.source_fetch_timeout_secs,
                "max_source_archive_bytes": MAX_ARCHIVE_BYTES,
                "compile_timeout_secs": arguments.compile_timeout_secs,
                "provenance_timeout_secs": arguments.provenance_timeout_secs,
                "prove_timeout_secs": arguments.prove_timeout_secs,
                "prove_budget_secs_per_function": arguments.prove_budget_secs,
                "max_output_bytes_per_stream": arguments.max_output_bytes,
            },
        }
        rendered = canonical_json_bytes(receipt)
        # Parse our own bytes with the strict reader before publication.
        validated = strict_json_bytes(rendered, "candidate diagnostic receipt")
        if validated.get("claim_boundary") != CLAIM_BOUNDARY:
            raise EvidenceError("candidate receipt lost its non-representative claim boundary")
        if validated.get("proof", {}).get("scorecard", {}).get("scorecard", {}).get("total") != core_manifest["count"]:
            raise EvidenceError("candidate receipt proof denominator is inconsistent")
        require_in_repo_output_ancestors(repo, output)
        output_target.publish(rendered, previous_output)
        print(
            f"published {SCHEMA}: one non-representative crate, "
            f"full={full_manifest['count']} core={core_manifest['count']} -> {output}"
        )
    return 0


def main(argv: list[str] | None = None) -> int:
    arguments = parse_args(sys.argv[1:] if argv is None else argv)
    repo = Path(arguments.repo_root).expanduser().resolve(strict=True)
    output = Path(os.path.abspath(Path(arguments.output).expanduser()))
    git = resolve_system_git()
    # Keep the legacy lexical check for a precise policy error, then retain the
    # descriptor anchor across the entire measurement and final publication.
    require_in_repo_output_ancestors(repo, output)
    with AnchoredOutput(output) as output_target:
        return collect(arguments, repo, output, git, output_target)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except EvidenceError as error:
        print(f"collect_lambda_calculus_diagnostic.py: FAILED CLOSED: {error}", file=sys.stderr)
        raise SystemExit(1)
