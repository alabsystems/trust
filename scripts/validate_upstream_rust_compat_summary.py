#!/usr/bin/env python3
"""Check a fresh upstream-Rust summary against its retained run inputs.

This is a consistency diagnostic, not an independent G1 suite or semantic oracle.
It deliberately requires the scorecard and proof files beside the summary, but
always refuses release acceptance: those files share one unauthenticated producer.
"""

from __future__ import annotations

import argparse
from datetime import date, datetime, timezone
import hashlib
import json
import os
import shutil
from pathlib import Path
import re
import shlex
import stat
import subprocess
import sys


def require_tomllib() -> None:
    if sys.version_info >= (3, 11):
        return
    for minor in (14, 13, 12, 11):
        candidate = shutil.which(f"python3.{minor}")
        if candidate:
            os.execv(candidate, [candidate, *sys.argv])
    raise SystemExit("ERROR: summary validation requires Python >=3.11 (tomllib)")


require_tomllib()
import tomllib  # noqa: E402


OID = re.compile(r"[0-9a-f]{40}\Z")
TARGET = re.compile(r"(aarch64|x86_64)-[a-z0-9_-]+\Z")
COMPILETEST_PREFIXES = tuple(f"tests/{name}/" for name in (
    "assembly", "assembly-llvm", "auxiliary", "build-std", "codegen",
    "codegen-llvm", "codegen-units", "coverage", "coverage-run-rustdoc",
    "crashes", "debuginfo", "incremental", "mir-opt", "pretty",
    "run-make-cargo", "run-make", "run-pass", "run-pass-valgrind",
    "rustdoc", "rustdoc-gui", "rustdoc-html", "rustdoc-json",
    "rustdoc-js", "rustdoc-js-std", "rustdoc-ui", "ui", "ui-fulldeps",
))


class Refusal(Exception):
    pass


def check(condition: bool, message: str) -> None:
    if not condition:
        raise Refusal(message)


def mapping(value: object, label: str) -> dict:
    check(type(value) is dict, f"{label} must be an object")
    return value


def number(value: object, label: str) -> int:
    check(type(value) is int and value >= 0, f"{label} must be a non-negative integer")
    return value


def duplicate_keys(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        check(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_constant(value: str) -> None:
    raise Refusal(f"non-finite JSON number: {value}")


def load_json(path: Path) -> dict:
    try:
        data = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=duplicate_keys,
                          parse_constant=reject_constant)
    except (OSError, UnicodeError, ValueError) as exc:
        raise Refusal(f"cannot read valid JSON at {path}: {exc}") from exc
    return mapping(data, str(path))


def load_toml(path: Path) -> dict:
    try:
        with path.open("rb") as stream:
            return mapping(tomllib.load(stream), str(path))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise Refusal(f"cannot read valid TOML at {path}: {exc}") from exc


def git(root: Path, *args: str, input: bytes | None = None) -> bytes:
    git_env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    git_env["GIT_ATTR_NOSYSTEM"] = "1"
    result = subprocess.run(
        ["git", "--no-replace-objects", "-C", str(root), f"--work-tree={root}",
         "-c", "core.fsmonitor=false", "-c", "core.untrackedCache=false",
         "-c", "core.ignoreCase=false", "-c", "core.sparseCheckout=false",
         "-c", f"core.attributesFile={os.devnull}", *args],
        capture_output=True, env=git_env, input=input,
    )
    check(result.returncode == 0, f"git {' '.join(args)} failed: {result.stderr.decode(errors='replace').strip()}")
    return result.stdout


def file_state(value: os.stat_result) -> tuple[int, int, int, int, int, int]:
    return (value.st_dev, value.st_ino, value.st_mode, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns)


def committed_crlf_checkout_matches(root: Path, raw_path: bytes, path: Path,
                                    oid: bytes, before: os.stat_result) -> bool:
    info_path = Path(os.fsdecode(git(root, "rev-parse", "--git-path", "info/attributes").strip()))
    if not info_path.is_absolute():
        info_path = root / info_path
    check(not info_path.is_symlink() and (not info_path.exists() or not info_path.read_bytes().strip()),
          "repository is dirty: local attributes override is present")
    records = git(root, "check-attr", "--source=HEAD", "-z", "text", "eol", "filter",
                  "--", os.fsdecode(raw_path)).split(b"\0")
    check(len(records) == 10 and records[-1] == b"",
          "repository is dirty: malformed committed attributes")
    attrs = {}
    for index in range(0, 9, 3):
        check(records[index] == raw_path and records[index + 1] not in attrs,
              "repository is dirty: malformed committed attributes")
        attrs[records[index + 1]] = records[index + 2]
    check(attrs.get(b"text") in (b"set", b"unspecified", b"auto")
          and attrs.get(b"eol") == b"crlf" and attrs.get(b"filter") == b"unspecified"
          and len(attrs) == 3,
          f"repository is dirty: tracked bytes changed: {path}")
    blob = git(root, "cat-file", "blob", oid.decode("ascii"))
    worktree_bytes = path.read_bytes()
    check(file_state(path.lstat()) == file_state(before),
          f"repository is dirty: tracked file changed while reading: {path}")
    if worktree_bytes != blob.replace(b"\n", b"\r\n"):
        return False
    if attrs[b"text"] == b"auto":
        normalized = git(root, "-c", "core.autocrlf=false", "-c", "core.eol=lf",
                         "-c", "core.safecrlf=false", "--attr-source=HEAD",
                         "hash-object", f"--path={os.fsdecode(raw_path)}", "--stdin",
                         input=worktree_bytes).strip()
        return normalized == oid
    return True


def clean_checkout(root: Path) -> str:
    check(not git(root, "status", "--porcelain=v1", "--untracked-files=all",
                  "--ignore-submodules=none").strip(), "repository is dirty")
    head = git(root, "rev-parse", "HEAD").decode("ascii").strip()
    check(OID.fullmatch(head) is not None, "repository is dirty: invalid HEAD")

    tree: dict[bytes, tuple[bytes, bytes]] = {}
    for record in git(root, "ls-tree", "-r", "-z", "HEAD").split(b"\0"):
        if not record:
            continue
        try:
            metadata, path = record.split(b"\t", 1)
            mode, kind, oid = metadata.split(b" ")
        except ValueError as exc:
            raise Refusal("repository is dirty: malformed HEAD tree") from exc
        check(mode in (b"100644", b"100755", b"120000", b"160000")
              and kind == (b"commit" if mode == b"160000" else b"blob")
              and OID.fullmatch(oid.decode("ascii")) is not None
              and path not in tree, "repository is dirty: malformed HEAD tree")
        tree[path] = (mode, oid)

    index: dict[bytes, tuple[bytes, bytes]] = {}
    for record in git(root, "ls-files", "--stage", "-z").split(b"\0"):
        if not record:
            continue
        try:
            metadata, path = record.split(b"\t", 1)
            mode, oid, stage = metadata.split(b" ")
        except ValueError as exc:
            raise Refusal("repository is dirty: malformed index") from exc
        check(stage == b"0" and path not in index, "repository is dirty: index differs from HEAD")
        index[path] = (mode, oid)
    check(index == tree, "repository is dirty: index differs from HEAD")

    checked_dirs = {root}
    try:
        for raw_path, (mode, oid) in tree.items():
            parts = raw_path.split(b"/")
            check(all(part not in (b"", b".", b"..") for part in parts),
                  "repository is dirty: invalid tracked path")
            path = root
            for part in parts[:-1]:
                path /= os.fsdecode(part)
                if path not in checked_dirs:
                    check(stat.S_ISDIR(path.lstat().st_mode),
                          f"repository is dirty: tracked directory changed: {path}")
                    checked_dirs.add(path)
            path /= os.fsdecode(parts[-1])
            before = path.lstat()
            if mode == b"160000":
                check(stat.S_ISDIR(before.st_mode),
                      f"repository is dirty: submodule path changed: {path}")
                marker = path / ".git"
                check(marker.exists(),
                      f"repository is dirty: submodule is not initialized: {path}")
                marker_mode = marker.lstat().st_mode
                check(stat.S_ISREG(marker_mode) or stat.S_ISDIR(marker_mode),
                      f"repository is dirty: submodule is not initialized: {path}")
                check(clean_checkout(path).encode("ascii") == oid,
                      f"repository is dirty: submodule pin differs: {path}")
                continue
            if mode == b"120000":
                check(stat.S_ISLNK(before.st_mode),
                      f"repository is dirty: tracked mode changed: {path}")
                data = os.fsencode(os.readlink(path))
                digest = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
            else:
                check(stat.S_ISREG(before.st_mode)
                      and bool(before.st_mode & 0o111) == (mode == b"100755"),
                      f"repository is dirty: tracked mode changed: {path}")
                digest_hash = hashlib.sha1(f"blob {before.st_size}\0".encode())
                with path.open("rb") as stream:
                    check(file_state(os.fstat(stream.fileno())) == file_state(before),
                          f"repository is dirty: tracked file changed while reading: {path}")
                    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                        digest_hash.update(chunk)
                digest = digest_hash.hexdigest()
            check(file_state(path.lstat()) == file_state(before),
                  f"repository is dirty: tracked file changed while reading: {path}")
            if digest.encode("ascii") != oid:
                check(mode != b"120000" and committed_crlf_checkout_matches(
                    root, raw_path, path, oid, before),
                    f"repository is dirty: tracked bytes changed: {path}")
    except OSError as exc:
        raise Refusal(f"repository is dirty: cannot inspect tracked path: {exc}") from exc

    # Only version-controlled .gitignore rules may exclude untracked files here.
    untracked = git(root, "ls-files", "--others", "-z",
                    "--exclude-per-directory=.gitignore")
    if untracked:
        first_path = os.fsdecode(untracked.split(b"\0", 1)[0])
        raise Refusal(f"repository is dirty: untracked file: {first_path}")
    ignored = git(root, "ls-files", "--others", "--ignored", "--directory", "-z",
                  "--exclude-per-directory=.gitignore")
    for path in ignored.split(b"\0"):
        if path == b".gitignore" or path.endswith(b"/.gitignore"):
            raise Refusal(f"repository is dirty: untracked ignore file: {os.fsdecode(path)}")
    return head


def repo_path(root: Path, value: object, label: str) -> Path:
    check(type(value) is str and bool(value), f"{label} must be a non-empty path")
    path = Path(value)
    resolved = (path if path.is_absolute() else root / path).resolve()
    check(resolved.is_relative_to(root), f"{label} escapes repository: {value}")
    return resolved


def flag(argv: list[str], name: str) -> str:
    positions = [index for index, item in enumerate(argv) if item == name]
    check(len(positions) == 1 and positions[0] + 1 < len(argv), f"runner argv requires one {name} value")
    return argv[positions[0] + 1]


def required_flag(argv: list[str], name: str) -> None:
    check(argv.count(name) == 1, f"runner argv requires exactly one {name}")


def upstream_tree(root: Path, pin: str) -> dict[str, str]:
    check(OID.fullmatch(pin) is not None, "baseline upstream revision must end in a full Git SHA")
    check(git(root, "cat-file", "-t", pin).strip() == b"commit", "pinned upstream object is not a commit")
    entries: dict[str, str] = {}
    for record in git(root, "ls-tree", "-r", "-z", pin, "--", "tests").split(b"\0"):
        if not record:
            continue
        try:
            metadata, raw_path = record.split(b"\t", 1)
            mode, kind, oid = metadata.decode("ascii").split(" ")
            path = raw_path.decode("utf-8")
        except (UnicodeError, ValueError) as exc:
            raise Refusal(f"malformed pinned upstream tests tree record: {exc}") from exc
        check(kind == "blob" and mode in ("100644", "100755", "120000"),
              f"unsupported upstream tests tree entry: {path}")
        check(path not in entries and OID.fullmatch(oid) is not None,
              f"duplicate or invalid pinned upstream test entry: {path}")
        entries[path] = oid
    check(bool(entries), "pinned upstream tests tree is empty")
    return entries


def primary_paths(source_files: dict[str, str]) -> list[str]:
    # Mirror the producer's compiletest-path projection, then compare its
    # emitted population with this Git-derived calculation.
    primary = set()
    for path in source_files:
        if not path.startswith(COMPILETEST_PREFIXES):
            continue
        if path.startswith("tests/run-make/"):
            parts = path.split("/")
            if len(parts) >= 3:
                primary.add("/".join(parts[:3]))
        elif path.endswith((".rs", ".js")):
            primary.add(path)
    return sorted(primary)


def require_matching_fields(record: dict, expected: dict[str, object], label: str) -> None:
    for key, value in expected.items():
        check(record.get(key) == value, f"{label}.{key} must equal {value!r}")


def validate(root: Path, summary_path: Path, target_triple: str, host_triple: str) -> None:
    check(TARGET.fullmatch(target_triple) is not None, f"unsupported target triple: {target_triple}")
    check(TARGET.fullmatch(host_triple) is not None, f"unsupported host triple: {host_triple}")
    check(host_triple == target_triple,
          "clean upstream summary requires native host and target to match")
    head = clean_checkout(root)
    baseline = load_toml(repo_path(root, "tests/upstream-rust/baseline.toml", "baseline"))
    alignment = load_toml(repo_path(root, "release/trust-version.toml", "release alignment"))
    revision = mapping(baseline.get("upstream"), "baseline.upstream").get("revision")
    check(type(revision) is str and ":" in revision, "baseline upstream revision is missing")
    pin = revision.rsplit(":", 1)[1]
    check(mapping(alignment.get("rust_alignment"), "rust_alignment").get("revision") == revision,
          "release rust_alignment revision differs from upstream baseline")
    source_files = upstream_tree(root, pin)

    summary = load_json(summary_path)
    check(summary.get("schema_version") == baseline.get("schema_version") == "0.1.0",
          "summary and baseline schema versions differ")
    check(summary.get("baseline_id") == baseline.get("id"), "summary baseline_id differs from pinned baseline")
    date_text = summary.get("generated_on")
    check(type(date_text) is str and re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}", date_text) is not None,
          "summary generated_on is not a canonical ISO date")
    try:
        generated_on = date.fromisoformat(date_text)
    except (TypeError, ValueError) as exc:
        raise Refusal("summary generated_on is not a valid ISO date") from exc
    check(generated_on <= datetime.now(timezone.utc).date(),
          "summary generated_on is in the future")
    check(summary.get("repo_head") == head and summary.get("repo_dirty") is False,
          "summary is stale or was produced from a dirty checkout")
    upstream_revision = summary.get("upstream_revision")
    check(type(upstream_revision) is str and upstream_revision.endswith(f":{pin}"),
          "summary upstream revision differs from pinned baseline")
    arch = target_triple.split("-", 1)[0]
    require_matching_fields(summary, {"target_arch": arch, "architecture": arch,
                                      "target": target_triple, "target_triple": target_triple,
                                      "host_triple": host_triple}, "summary")
    check(summary.get("host") in (host_triple, host_triple.split("-", 1)[0]),
          "summary host differs from stage2 compiler host")
    run_id = summary.get("run_id")
    check(type(run_id) is str and bool(run_id), "summary run_id is missing")

    runner = mapping(summary.get("runner"), "summary.runner")
    require_matching_fields(runner, {"python_used": False, "implementation": "rust",
                                     "entrypoint": "targo trust domination upstream-tests",
                                     "command": "trust-upstream-compat port", "run_id": run_id,
                                     "release": True, "execute": True, "proof_mode": "full",
                                     "proof_scope": "upstream_rust", "target_arch": arch,
                                     "target": target_triple, "target_triple": target_triple,
                                     "host": summary["host"], "host_triple": host_triple},
                            "runner")
    contract = mapping(runner.get("release_evidence_contract"), "release_evidence_contract")
    require_matching_fields(contract, {"satisfied": True, "requires_release": True,
                                       "requires_execute": True, "requires_summary_out": True,
                                       "requires_proof_mode": "full", "release": True,
                                       "execute": True, "proof_mode": "full",
                                       "proof_scope": "upstream_rust", "target_arch": arch,
                                       "target": target_triple, "target_triple": target_triple,
                                       "host": summary["host"], "host_triple": host_triple,
                                       "run_id": run_id}, "release_evidence_contract")
    check(repo_path(root, runner.get("summary_out"), "runner.summary_out") == summary_path,
          "runner summary_out differs from supplied summary")
    check(repo_path(root, contract.get("summary_out"), "contract.summary_out") == summary_path,
          "release contract summary_out differs from supplied summary")
    out_dir = repo_path(root, runner.get("out_dir"), "runner.out_dir")
    check(repo_path(root, contract.get("out_dir"), "contract.out_dir") == out_dir,
          "release contract out_dir differs from runner")
    argv = runner.get("argv")
    check(type(argv) is list and all(type(item) is str for item in argv), "runner.argv must be strings")
    check(argv[:4] == ["targo", "trust", "domination", "upstream-tests"],
          "runner.argv is not the canonical upstream Rust entrypoint")
    runner_values = {"--baseline", "--upstream-fixes", "--test-exceptions", "--summary-out",
                     "--run-id", "--target-arch", "--target", "--target-triple", "--host",
                     "--host-triple", "--upstream-revision", "--upstream-remote", "--out-dir",
                     "--proof-scope", "--proof-mode"}
    runner_switches = {"--release", "--execute", "--no-apply", "--no-fetch"}
    seen_options = set()
    index = 4
    while index < len(argv):
        option = argv[index]
        check(option in runner_values or option in runner_switches,
              f"runner argv contains unsupported or narrowing option: {option}")
        check(option not in seen_options, f"runner argv repeats {option}")
        seen_options.add(option)
        if option in runner_values:
            check(index + 1 < len(argv) and bool(argv[index + 1])
                  and not argv[index + 1].startswith("--"),
                  f"runner argv {option} lacks a value")
            index += 2
        else:
            index += 1
    for switch in ("--release", "--execute", "--no-apply"):
        required_flag(argv, switch)
    for name, value in (("--proof-mode", "full"), ("--proof-scope", "upstream-rust"),
                        ("--run-id", run_id), ("--target-arch", arch),
                        ("--target", target_triple), ("--target-triple", target_triple),
                        ("--host", summary["host"]),
                        ("--host-triple", host_triple)):
        check(flag(argv, name) == value, f"runner argv {name} differs from retained metadata")
    check(repo_path(root, flag(argv, "--summary-out"), "argv.summary_out") == summary_path,
          "runner argv summary-out differs from supplied summary")
    check(repo_path(root, flag(argv, "--out-dir"), "argv.out_dir") == out_dir,
          "runner argv out-dir differs from retained scorecard")
    check(flag(argv, "--upstream-revision").rsplit(":", 1)[-1] == pin,
          "runner argv requests a different upstream pin")
    check(upstream_revision == f"{flag(argv, '--upstream-remote')}:{pin}",
          "summary upstream remote differs from runner argv")

    scorecard = load_json(repo_path(root, str(out_dir / "scorecard.json"), "scorecard"))
    require_matching_fields(scorecard, {"executed": True, "proof_mode": "full",
                                        "proof_scope": "upstream_rust", "proof_artifacts_complete": True,
                                        "execution_exit_status": 0, "resolved_upstream_revision": pin,
                                        "local_repository_revision": head,
                                        "upstream_test_files": len(source_files),
                                        "imported_files": len(source_files),
                                        "validation_failures": [], "missing_proof_artifacts": [],
                                        "invalid_proof_artifacts": []}, "scorecard")
    check(mapping(scorecard.get("upstream_revision_drift"), "revision drift").get("drifted_from_baseline") is False,
          "scorecard upstream revision drifted from baseline")
    check(scorecard.get("baseline_revision") == pin, "scorecard baseline revision differs")
    telemetry = mapping(scorecard.get("execution_telemetry"), "execution telemetry")
    require_matching_fields(telemetry, {"executor": "rust-bootstrap", "proof_scope": "upstream_rust",
                                        "exit_status": 0, "upstream_exit_status": 0,
                                        "trust_added_manifest_executed": False,
                                        "trust_added_proof_inventory_tests": 0}, "execution telemetry")
    totals = mapping(scorecard.get("totals"), "scorecard totals")
    for key in ("failed", "tool_failures", "excepted"):
        check(number(totals.get(key), f"scorecard.totals.{key}") == 0,
              f"scorecard has {key} rows")

    validation = mapping(scorecard.get("proof_artifact_validation"), "proof artifact validation")
    require_matching_fields(validation, {"complete": True, "missing": [], "invalid": []},
                            "proof artifact validation")
    artifact_records = mapping(validation.get("artifacts"), "proof artifact records")
    proof = repo_path(root, str(out_dir / "proof"), "proof directory")
    artifacts = {}
    for name in ("inventory.json", "results.json", "proof-summary.json"):
        path = repo_path(root, str(proof / name), f"proof artifact {name}")
        raw = path.read_bytes()
        record = mapping(artifact_records.get(name), f"proof artifact {name}")
        require_matching_fields(record, {"exists": True, "valid": True, "size_bytes": len(raw),
                                         "sha256": hashlib.sha256(raw).hexdigest()}, name)
        check(repo_path(root, record.get("path"), f"{name}.path") == path,
              f"proof artifact {name} path differs from retained file")
        artifacts[name] = load_json(path)
    inventory = artifacts["inventory.json"]
    results = artifacts["results.json"]
    proof_totals = artifacts["proof-summary.json"]
    check(validation.get("summary_totals") == proof_totals == runner.get("proof_totals"),
          "proof totals disagree between summary, scorecard, and proof artifact")
    require_matching_fields(inventory, {"upstream_revision": pin, "local_revision": head},
                            "proof inventory")
    rows = inventory.get("tests")
    outcomes = results.get("results")
    check(type(rows) is list and type(outcomes) is list and bool(rows),
          "proof inventory/results are empty or malformed")
    expected_paths = scorecard.get("primary_upstream_tests")
    check(type(expected_paths) is list and all(type(path) is str for path in expected_paths)
          and expected_paths == sorted(set(expected_paths)),
          "scorecard primary upstream paths are malformed")
    check(expected_paths == primary_paths(source_files),
          "scorecard primary test population differs from pinned Git tree")
    check(len(rows) == len(outcomes) == len(expected_paths),
          "proof inventory/result population is partial")
    ids = set()
    paths = set()
    for row in rows:
        row = mapping(row, "proof inventory row")
        test_id = row.get("id")
        path = row.get("path")
        check(type(test_id) is str and test_id not in ids, "proof inventory has duplicate/missing id")
        check(type(path) is str and path not in paths,
              "proof inventory path is missing or duplicate")
        source_path = f"{path}/rmake.rs" if path.startswith("tests/run-make/") else path
        check(source_path in source_files, "proof inventory source is absent from pinned tree")
        check(row.get("source") == "upstream_rust" and row.get("revision") == pin
              and row.get("source_git_blob") == source_files[source_path],
              f"proof inventory source binding differs for {path}")
        ids.add(test_id)
        paths.add(path)
    check(paths == set(expected_paths), "proof inventory differs from scorecard primary paths")
    result_ids = set()
    for row in outcomes:
        row = mapping(row, "proof result row")
        test_id = row.get("test_id")
        check(type(test_id) is str and test_id not in result_ids and row.get("outcome") == "passed"
              and row.get("exception_id") is None, "proof result is duplicate, missing, or not clean-pass")
        result_ids.add(test_id)
    check(result_ids == ids, "proof results do not biject inventory")
    count = len(ids)
    require_matching_fields(proof_totals, {"total": count, "upstream": count,
                                           "trust_added": 0, "passed": count,
                                           "upstream_inapplicable": 0, "excepted": 0,
                                           "unaccounted": 0}, "proof totals")
    check(number(telemetry.get("upstream_proof_inventory_tests"), "upstream proof telemetry") == count,
          "execution telemetry inventory count differs")
    check(number(telemetry.get("proof_inventory_tests"), "total proof telemetry") == count,
          "execution telemetry total inventory count differs")

    case = load_json(repo_path(root, str(proof / "case-evidence.json"), "case evidence"))
    require_matching_fields(case, {"upstream_revision": pin, "local_revision": head,
                                   "aggregate_exit_status": 0, "proof_scope": "upstream_rust",
                                   "aggregate_exit_supplies_individual_outcomes": False},
                            "case evidence")
    check(case.get("test_input_closure_before") == case.get("test_input_closure_after")
          and type(case.get("test_input_closure_before")) is dict,
          "case evidence input closure changed or is missing")
    check(mapping(case.get("test_input_admission"), "case input admission").get("unresolved") == [],
          "case evidence has unresolved input admission")
    expected = case.get("expected")
    observed = case.get("observations")
    reconciled = case.get("reconciled")
    check(type(expected) is list and type(observed) is list and type(reconciled) is list
          and len(expected) == len(reconciled) == count,
          "case evidence population is partial")
    expected_by_id = {}
    expected_names = set()
    for row in expected:
        row = mapping(row, "expected case row")
        test_id = row.get("test_id")
        names = row.get("names")
        check(type(test_id) is str and test_id in ids and test_id not in expected_by_id
              and type(row.get("path")) is str and row.get("path") in paths
              and row.get("unresolved") == []
              and type(names) is list and bool(names)
              and all(type(name) is str and bool(name) for name in names),
              "case evidence has missing, duplicate, or unresolved expected cases")
        for name in names:
            identity = (row["path"], name)
            check(identity not in expected_names, "case evidence has duplicate expected case identity")
            expected_names.add(identity)
        expected_by_id[test_id] = row
    check(set(expected_by_id) == ids, "case evidence expected IDs differ from proof inventory")
    observed_names = set()
    for row in observed:
        row = mapping(row, "observed case row")
        check(type(row.get("path")) is str and type(row.get("name")) is str,
              "case observation identity is malformed")
        identity = (row["path"], row["name"])
        check(identity in expected_names and identity not in observed_names
              and row.get("outcome") == "passed" and row.get("complete_suite") is True,
              "case evidence has missing, duplicate, or non-passing observations")
        observed_names.add(identity)
    check(observed_names == expected_names, "case evidence omitted expected observations")
    reconciled_ids = set()
    for row in reconciled:
        row = mapping(row, "reconciled case row")
        test_id = row.get("test_id")
        check(type(test_id) is str and test_id in ids and test_id not in reconciled_ids
              and row.get("outcome") == "passed",
              "case evidence reconciled rows are missing, duplicate, or not passing")
        reconciled_ids.add(test_id)
    check(reconciled_ids == ids, "case evidence reconciled IDs differ from proof inventory")
    execution_log = repo_path(root, str(out_dir / "execution.log"), "execution log").read_bytes()
    check(case.get("log_sha256") == hashlib.sha256(execution_log).hexdigest(),
          "case evidence log digest differs from execution log")
    lines = execution_log.decode("utf-8").splitlines()
    command_text = case.get("execution_command")
    check(type(command_text) is str and lines and lines[0] == f"$ {command_text}",
          "execution log command differs from case evidence")
    command = shlex.split(command_text)
    check(len(command) >= 2 and command[1] == "test", "case evidence did not run bootstrap test")
    launcher = Path(command[0]).resolve()
    check(launcher in (root / "build/bootstrap/debug/bootstrap",
                       root / "build/bootstrap/bootstrap")
          and launcher.is_file() and os.access(launcher, os.X_OK),
          "case evidence launcher is not the repo-local Rust bootstrap binary")
    value_options = {"--src", "--stage", "--host", "--target", "--config", "--jobs", "-j", "--set"}
    bare_options = {"--trust-vanilla", "--no-fail-fast", "--force-rerun", "-v",
                    "--verbose", "--run=always"}
    index = 2
    while index < len(command):
        option = command[index]
        check(option.split("=", 1)[0] not in ("--skip", "--exclude", "--test-args")
              or option.startswith("--test-args=--test-threads="),
              f"bootstrap command contains unsupported or narrowing option: {option}")
        if option in value_options:
            check(index + 1 < len(command), f"bootstrap option {option} lacks a value")
            if option == "--set":
                check(command[index + 1] == "rust.verbose-tests=true",
                      "bootstrap --set changes the full-suite configuration")
            index += 2
        else:
            allowed = option in bare_options or option.startswith("--config=") or (
                option.startswith("--jobs=") and option[7:].isdigit()
                and int(option[7:]) > 0) or (
                option.startswith("--test-args=--test-threads=")
                and option.rsplit("=", 1)[1].isdigit()
                and int(option.rsplit("=", 1)[1]) > 0)
            check(allowed, f"bootstrap command contains unsupported or narrowing option: {option}")
            index += 1
    for switch in ("--trust-vanilla", "--no-fail-fast", "--force-rerun"):
        required_flag(command, switch)
    check(command.count("--set") == 1, "bootstrap command must set verbose-tests exactly once")
    for name, value in (("--stage", "2"), ("--host", host_triple),
                        ("--target", target_triple)):
        check(flag(command, name) == value, f"executed suite {name} differs from summary")
    check(repo_path(root, flag(command, "--src"), "execution --src") == root,
          "executed suite source root differs from checkout")
    check("# upstream_exit_status=0" in lines and "# exit_status=0" in lines,
          "execution log lacks successful completion footer")

    baseline_rows = baseline.get("entries")
    summary_rows = summary.get("results")
    check(type(baseline_rows) is list and type(summary_rows) is list and bool(baseline_rows),
          "baseline or summary result rows are missing")
    summary_rows = [mapping(row, "summary row") for row in summary_rows]
    baseline_ids = [mapping(row, "baseline row").get("id") for row in baseline_rows]
    result_ids = [mapping(row, "summary row").get("baseline_entry_id") for row in summary_rows]
    check(all(type(value) is str and bool(value) for value in baseline_ids + result_ids)
          and len(set(baseline_ids)) == len(baseline_ids) and set(result_ids) == set(baseline_ids)
          and len(set(result_ids)) == len(result_ids), "summary rows do not biject baseline")
    check(all(row.get("outcome") == "compatible" and row.get("exception_id") is None
              and row.get("upstream_fix_id") is None for row in summary_rows),
          "summary contains unknown, divergent, or waived compatibility rows")
    require_matching_fields(mapping(summary.get("totals"), "summary totals"),
                            {"total": len(baseline_rows), "compatible": len(baseline_rows),
                             "divergent": 0, "excepted": 0, "fixed_upstream": 0, "unknown": 0},
                            "summary totals")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    parser.add_argument("--target-triple", required=True)
    parser.add_argument("--host-triple", required=True)
    args = parser.parse_args()
    try:
        root = args.repo_root.resolve(strict=True)
        summary = repo_path(root, str(args.summary), "summary")
        validate(root, summary, args.target_triple, args.host_triple)
    except (OSError, UnicodeError, ValueError, RuntimeError, RecursionError, Refusal) as exc:
        print(f"ERROR: upstream Rust summary rejected: {exc}", file=sys.stderr)
        return 1
    print("DIAGNOSTIC: retained summary/source/target/proof files are structurally consistent")
    print("ERROR: upstream Rust release evidence lacks independent Rust-owned execution and complete-denominator attestation; authored logs, closure rows, and hashes cannot prove G1", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
