#!/usr/bin/env python3
"""Fail-closed check for parent-pinned submodule commit reachability.

This release gate verifies that each commit recorded by the parent checkout's
submodule gitlinks is contained in at least one fetched remote-tracking branch
or durable ``refs/pins/<sha>`` archival ref in the corresponding submodule. It
does not fetch or push. If a parent points at a local-only submodule commit, a
fresh recursive clone may fail to reproduce that pin; this script reports that
condition and exits non-zero.

``refs/pins/*`` is the repository's branch-free retention namespace. The
historical-pin audit fetches that namespace explicitly and anchors orphaned
commits there, so a server-side garbage collection cannot destroy a published
superproject pin. Suggesting that an old detached commit be pushed to ``main``
would overwrite the release branch and is never an acceptable repair.
"""

from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_REMOTE = "origin"


@dataclass(frozen=True)
class SubmodulePin:
    path: str
    sha: str
    state: str


@dataclass(frozen=True)
class PinCheck:
    path: str
    sha: str
    status: str
    remote_refs: tuple[str, ...] = ()
    remote: str = DEFAULT_REMOTE
    remote_url: str = ""
    publish_ref: str = ""
    suggested_command: str = ""
    detail: str = ""

    @property
    def ok(self) -> bool:
        return self.status == "reachable"

    def as_dict(self) -> dict[str, object]:
        return {
            "path": self.path,
            "sha": self.sha,
            "status": self.status,
            "remote_refs": list(self.remote_refs),
            "remote": self.remote,
            "remote_url": self.remote_url,
            "publish_ref": self.publish_ref,
            "suggested_command": self.suggested_command,
            "detail": self.detail,
        }


@dataclass(frozen=True)
class AuditResult:
    repo_root: Path
    pins: tuple[PinCheck, ...]
    source: str

    @property
    def failed(self) -> tuple[PinCheck, ...]:
        return tuple(check for check in self.pins if not check.ok)

    @property
    def ok(self) -> bool:
        return not self.failed

    def as_dict(self) -> dict[str, object]:
        failed = self.failed
        return {
            "repo_root": str(self.repo_root),
            "source": self.source,
            "summary": {
                "checked": len(self.pins),
                "reachable": len(self.pins) - len(failed),
                "failed": len(failed),
            },
            "pins": [pin.as_dict() for pin in self.pins],
        }


class GitError(RuntimeError):
    pass


def run_git(
    repo: Path,
    args: Sequence[str],
    *,
    check: bool = True,
    extra_config: Sequence[str] = (),
) -> subprocess.CompletedProcess[str]:
    command = ["git", *extra_config, *args]
    completed = subprocess.run(
        command,
        cwd=repo,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if check and completed.returncode != 0:
        rendered = " ".join(shlex.quote(part) for part in command)
        raise GitError(
            f"{rendered} failed in {repo}: {completed.stderr.strip() or completed.stdout.strip()}"
        )
    return completed


def parse_cached_submodule_status(output: str) -> tuple[SubmodulePin, ...]:
    pins: list[SubmodulePin] = []
    for line in output.splitlines():
        if not line.strip():
            continue
        state = line[0]
        parts = line[1:].strip().split()
        if len(parts) < 2:
            raise GitError(f"could not parse submodule status line: {line!r}")
        sha, path = parts[0], parts[1]
        if len(sha) != 40 or any(char not in "0123456789abcdefABCDEF" for char in sha):
            raise GitError(f"could not parse submodule sha in line: {line!r}")
        pins.append(SubmodulePin(path=path, sha=sha.lower(), state=state))
    return tuple(pins)


def parent_pins(repo_root: Path) -> tuple[SubmodulePin, ...]:
    # --cached checks the parent index/HEAD gitlinks, not whatever submodule
    # worktrees currently have checked out. This is the release-reproducibility
    # surface a fresh clone will try to reproduce.
    status = run_git(repo_root, ["submodule", "status", "--cached", "--recursive"])
    return parse_cached_submodule_status(status.stdout)


def git_dir_exists(path: Path) -> bool:
    result = run_git(path, ["rev-parse", "--show-toplevel"], check=False)
    if result.returncode != 0:
        return False
    try:
        return Path(result.stdout.strip()).resolve() == path.resolve()
    except OSError:
        return False


def remote_names(path: Path) -> tuple[str, ...]:
    result = run_git(path, ["remote"], check=False)
    if result.returncode != 0:
        return ()
    return tuple(remote for remote in result.stdout.splitlines() if remote)


def preferred_remote(path: Path) -> str:
    names = remote_names(path)
    if DEFAULT_REMOTE in names:
        return DEFAULT_REMOTE
    return names[0] if names else DEFAULT_REMOTE


def remote_url(path: Path, remote: str) -> str:
    result = run_git(path, ["remote", "get-url", remote], check=False)
    if result.returncode != 0:
        return ""
    return result.stdout.strip()


def durable_refs_containing(path: Path, sha: str) -> tuple[str, ...]:
    result = run_git(
        path,
        [
            "for-each-ref",
            "--contains",
            sha,
            "--format=%(refname:short)",
            "refs/remotes",
            "refs/pins",
        ],
        check=False,
    )
    if result.returncode != 0:
        raise GitError(result.stderr.strip() or result.stdout.strip())
    return tuple(ref for ref in result.stdout.splitlines() if ref)


def shell_join(parts: Iterable[str]) -> str:
    return " ".join(shlex.quote(part) for part in parts)


def pin_ref(sha: str) -> str:
    return f"refs/pins/{sha}"


def publish_command(path: str, remote: str, sha: str) -> str:
    return shell_join(["git", "-C", path, "push", remote, f"{sha}:{pin_ref(sha)}"])


def check_pin(repo_root: Path, pin: SubmodulePin) -> PinCheck:
    submodule_path = repo_root / pin.path
    remote = preferred_remote(submodule_path) if submodule_path.exists() else DEFAULT_REMOTE
    url = remote_url(submodule_path, remote) if submodule_path.exists() else ""
    publish_ref = pin_ref(pin.sha)
    command = publish_command(pin.path, remote, pin.sha)

    if not submodule_path.exists():
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="missing-submodule-worktree",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=shell_join(
                [
                    "python3",
                    "scripts/recreate_bootstrap.py",
                    "--require-seed",
                    "--no-build",
                ]
            ),
            detail="submodule path is missing; initialize it before checking remote reachability",
        )

    if not git_dir_exists(submodule_path):
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="uninitialized-submodule",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=shell_join(
                [
                    "python3",
                    "scripts/recreate_bootstrap.py",
                    "--require-seed",
                    "--no-build",
                ]
            ),
            detail="submodule path is not a Git worktree",
        )

    object_check = run_git(
        submodule_path,
        ["cat-file", "-e", f"{pin.sha}^{{commit}}"],
        check=False,
    )
    if object_check.returncode != 0:
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="missing-commit-object",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=shell_join(["git", "-C", pin.path, "fetch", "--all", "--tags", "--prune"]),
            detail="pinned commit object is not present in the initialized submodule",
        )

    try:
        refs = durable_refs_containing(submodule_path, pin.sha)
    except GitError as error:
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="remote-reachability-error",
            remote=remote,
            remote_url=url,
            publish_ref=publish_ref,
            suggested_command=command,
            detail=str(error),
        )

    if refs:
        return PinCheck(
            path=pin.path,
            sha=pin.sha,
            status="reachable",
            remote_refs=refs,
            remote=remote,
            remote_url=url,
        )

    return PinCheck(
        path=pin.path,
        sha=pin.sha,
        status="not-reachable-from-fetched-remotes",
        remote=remote,
        remote_url=url,
        publish_ref=publish_ref,
        suggested_command=command,
        detail="pinned commit is present locally but not contained in refs/remotes/* or refs/pins/*",
    )


def audit(repo_root: Path) -> AuditResult:
    pins = parent_pins(repo_root)
    checks = tuple(check_pin(repo_root, pin) for pin in pins)
    return AuditResult(
        repo_root=repo_root,
        pins=checks,
        source="git submodule status --cached --recursive",
    )


def render_text(result: AuditResult) -> str:
    lines: list[str] = []
    lines.append(f"Submodule remote reachability check: {result.repo_root}")
    lines.append(f"source: {result.source}")
    lines.append(
        "summary: checked={checked} reachable={reachable} failed={failed}".format(
            checked=len(result.pins),
            reachable=len(result.pins) - len(result.failed),
            failed=len(result.failed),
        )
    )

    if result.ok:
        lines.append(
            "PASS: every parent-pinned submodule commit is reachable from fetched "
            "remote branches or durable pin refs"
        )
        return "\n".join(lines)

    lines.append(
        "FAIL: parent-pinned submodule commit(s) are not reproducible from fetched "
        "remote branches or durable pin refs"
    )
    for check in result.failed:
        lines.append("")
        lines.append(f"- {check.path} @ {check.sha}")
        lines.append(f"  status: {check.status}")
        if check.remote_url:
            lines.append(f"  remote: {check.remote} {check.remote_url}")
        else:
            lines.append(f"  remote: {check.remote}")
        if check.detail:
            lines.append(f"  detail: {check.detail}")
        if check.suggested_command:
            lines.append(f"  next command: {check.suggested_command}")

    lines.append("")
    lines.append(
        "This audit does not emit a recursive fetch/update command. Materialize missing "
        "gitlinks through the canonical recreator; inspect and fetch any stale existing "
        "repository explicitly so local work is not reset."
    )
    return "\n".join(lines)


def render_json(result: AuditResult) -> str:
    return json.dumps(result.as_dict(), indent=2, sort_keys=True)


def self_git(repo: Path, args: Sequence[str], *, allow_file: bool = False) -> None:
    config = [
        "-c",
        "user.name=Trust Submodule Check",
        "-c",
        "user.email=trust-submodule-check@example.invalid",
    ]
    if allow_file:
        config.extend(["-c", "protocol.file.allow=always"])
    run_git(repo, args, extra_config=config)


def write_file(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def commit_file(repo: Path, relative: str, text: str, message: str) -> None:
    write_file(repo / relative, text)
    self_git(repo, ["add", relative])
    self_git(repo, ["commit", "-m", message])


def assert_self_check_case(
    *,
    cases: list[dict[str, object]],
    name: str,
    result: AuditResult,
    expected_status: str,
    expected_ok: bool,
    expected_publish_ref: str | None = None,
    expected_ref_prefix: str | None = None,
) -> None:
    observed_statuses = [pin.status for pin in result.pins]
    only_pin = result.pins[0] if len(result.pins) == 1 else None
    publish_ref_matches = (
        expected_publish_ref is None
        or (only_pin is not None and only_pin.publish_ref == expected_publish_ref)
    )
    containing_ref_matches = (
        expected_ref_prefix is None
        or (
            only_pin is not None
            and any(ref.startswith(expected_ref_prefix) for ref in only_pin.remote_refs)
        )
    )
    passed = (
        len(result.pins) == 1
        and observed_statuses == [expected_status]
        and result.ok is expected_ok
        and publish_ref_matches
        and containing_ref_matches
    )
    cases.append(
        {
            "name": name,
            "expected_status": expected_status,
            "expected_ok": expected_ok,
            "expected_publish_ref": expected_publish_ref,
            "expected_ref_prefix": expected_ref_prefix,
            "observed_statuses": observed_statuses,
            "observed_ok": result.ok,
            "observed_publish_ref": only_pin.publish_ref if only_pin is not None else None,
            "observed_remote_refs": list(only_pin.remote_refs) if only_pin is not None else [],
            "passed": passed,
            "pins": [pin.as_dict() for pin in result.pins],
        }
    )


def render_self_check_report(cases: Sequence[dict[str, object]]) -> dict[str, object]:
    failed = [case for case in cases if not case["passed"]]
    return {
        "summary": {
            "checked": len(cases),
            "passed": len(cases) - len(failed),
            "failed": len(failed),
        },
        "cases": list(cases),
    }


def self_check(*, json_output: bool = False) -> int:
    cases: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="trust-submodule-reachability-") as tmp:
        root = Path(tmp)
        source = root / "sub-source"
        bare = root / "submodule.git"
        super_repo = root / "super"

        source.mkdir()
        self_git(source, ["init", "-b", "main"])
        commit_file(source, "README.md", "reachable\n", "initial submodule commit")
        self_git(root, ["clone", "--bare", str(source), str(bare)])

        super_repo.mkdir()
        self_git(super_repo, ["init", "-b", "main"])
        self_git(super_repo, ["submodule", "add", str(bare), "deps/sub"], allow_file=True)
        self_git(super_repo, ["commit", "-m", "add reachable submodule"])

        reachable = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="reachable remote-tracking pin",
            result=reachable,
            expected_status="reachable",
            expected_ok=True,
        )

        submodule = super_repo / "deps" / "sub"
        commit_file(submodule, "LOCAL_ONLY.txt", "local-only\n", "local-only submodule commit")
        self_git(super_repo, ["add", "deps/sub"])
        self_git(super_repo, ["commit", "-m", "pin local-only submodule commit"])

        unreachable = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="local-only parent pin",
            result=unreachable,
            expected_status="not-reachable-from-fetched-remotes",
            expected_ok=False,
            expected_publish_ref=pin_ref(
                run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
            ),
        )

        pinned_sha = run_git(submodule, ["rev-parse", "HEAD"]).stdout.strip()
        self_git(submodule, ["push", "origin", f"{pinned_sha}:{pin_ref(pinned_sha)}"])
        self_git(submodule, ["fetch", "origin", f"+{pin_ref(pinned_sha)}:{pin_ref(pinned_sha)}"])
        pinned = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="branch-free durable pin ref",
            result=pinned,
            expected_status="reachable",
            expected_ok=True,
            expected_ref_prefix="pins/",
        )

        missing_object_sha = "1" * 40
        self_git(
            super_repo,
            ["update-index", "--cacheinfo", f"160000,{missing_object_sha},deps/sub"],
        )
        self_git(super_repo, ["commit", "-m", "pin missing submodule object"])
        missing_object = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="missing pinned commit object",
            result=missing_object,
            expected_status="missing-commit-object",
            expected_ok=False,
        )

        self_git(super_repo, ["submodule", "deinit", "-f", "deps/sub"])
        (super_repo / "deps" / "sub").mkdir(parents=True, exist_ok=True)
        uninitialized = audit(super_repo)
        assert_self_check_case(
            cases=cases,
            name="uninitialized submodule worktree",
            result=uninitialized,
            expected_status="uninitialized-submodule",
            expected_ok=False,
        )

    report = render_self_check_report(cases)
    failed = report["summary"]["failed"]  # type: ignore[index]
    if json_output:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif failed:
        print(json.dumps(report, indent=2, sort_keys=True), file=sys.stderr)
        print("FAIL: submodule reachability self-check failed", file=sys.stderr)
    else:
        statuses = ", ".join(str(case["expected_status"]) for case in cases)
        print(f"PASS: self-check covered submodule pin states: {statuses}")
    return 0 if not failed else 1


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="targo trust repo submodule-reachability",
        description=(
            "Fail closed when parent-pinned submodule commits are not contained "
            "in fetched refs/remotes/* or durable refs/pins/*."
        )
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=REPO_ROOT,
        help="Trust checkout root to audit (default: repository containing this script)",
    )
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument(
        "--self-check",
        action="store_true",
        help=(
            "run an isolated local Git self-check instead of auditing this checkout; "
            "combine with --json for machine-readable assertions"
        ),
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_check:
        return self_check(json_output=args.json)

    repo_root = args.repo_root.resolve()
    try:
        result = audit(repo_root)
    except GitError as error:
        payload = {
            "repo_root": str(repo_root),
            "summary": {"checked": 0, "reachable": 0, "failed": 1},
            "error": str(error),
        }
        if args.json:
            print(json.dumps(payload, indent=2, sort_keys=True))
        else:
            print(f"FAIL: could not audit submodule reachability: {error}", file=sys.stderr)
        return 1

    if args.json:
        print(render_json(result))
    else:
        output = render_text(result)
        if result.ok:
            print(output)
        else:
            print(output, file=sys.stderr)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
