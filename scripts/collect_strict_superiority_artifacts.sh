#!/usr/bin/env bash
# Collect strict-superiority evidence artifacts without turning failed commands
# into release claims. This script is an orchestrator only; the JSON reports it
# writes remain subject to `targo trust domination` validation.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TARGO="${TARGO:-$ROOT/targo-trust/target/debug/targo-trust}"
RUN_ID="${RUN_ID:-strict-superiority-$(date -u +%Y%m%dT%H%M%SZ)}"
OUT_DIR="${OUT_DIR:-$ROOT/reports/strict-superiority/$RUN_ID}"
REPETITIONS="${REPETITIONS:-3}"
MIN_PERF_ADVANTAGE_PCT="${MIN_PERF_ADVANTAGE_PCT:-0}"
LOG="$OUT_DIR/commands.log"
PYTHON_BIN="${PYTHON_BIN:-python3}"
MANIFEST="${TRUST_STRICT_ARTIFACT_MANIFEST:-$OUT_DIR/release-artifact-manifest.json}"
MANIFEST_RECORDS="$OUT_DIR/.release-artifact-manifest.records.jsonl"
STAGE2_PREFLIGHT_LOG="$OUT_DIR/stage2-toolchain-preflight.log"
PLAN_ONLY=false
MANIFEST_STARTED_AT=""
REVIEWED_COMMIT=""

mkdir -p "$OUT_DIR"

usage() {
  cat <<'USAGE'
Usage: scripts/collect_strict_superiority_artifacts.sh [--plan]

Environment:
  TARGO                         targo-trust binary to run
  RUN_ID                         stable run id for report paths
  OUT_DIR                        artifact directory
  REPETITIONS                    repeated benchmark samples per row
  MIN_PERF_ADVANTAGE_PCT         domination performance threshold
  PYTHON_BIN                     Python interpreter for manifest serialization
  TRUST_STRICT_ARTIFACT_MANIFEST release artifact manifest output path
  TRUST_X86_64_TRIPLE            x86_64 target triple
  TRUST_AARCH64_TRIPLE           AArch64 target triple
  TRUST_PROOF_UNSAFE_MEMORY_REPORT
                                 prebuilt trust.proof-unsafe-memory-report.v1 JSON override
  TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR
                                 directory written by `targo trust report --unsafe-memory`
                                 (default: reports/proof under this checkout)
  TRUST_STAGE2_SYSROOT           optional explicit repo-local build/<host>/stage2 sysroot
                                 validated before evidence collection

The script writes a fail-closed release artifact manifest for real runs and
exits nonzero when any required artifact is missing, malformed, produced by a
nonzero command, dirty, commit-mismatched, or otherwise non-admissible. Use
--plan to print the exact commands without running them. Upstream compatibility
collection uses --no-apply so a release evidence run cannot mutate the reviewed
checkout or produce dirty provenance as a side effect.
USAGE
}

log() {
  printf '%s\n' "$*" | tee -a "$LOG" >&2
}

die() {
  log "ERROR: $*"
  exit 1
}

timestamp_utc() {
  date -u +%Y-%m-%dT%H:%M:%SZ
}

reviewed_commit() {
  git -C "$ROOT" rev-parse HEAD 2>/dev/null || printf 'unknown\n'
}

repo_dirty() {
  if git -C "$ROOT" diff --quiet --ignore-submodules=none \
    && git -C "$ROOT" diff --cached --quiet --ignore-submodules=none \
    && [[ -z "$(git -C "$ROOT" status --porcelain=v1 --untracked-files=all --ignore-submodules=none)" ]]; then
    printf 'false\n'
  else
    printf 'true\n'
  fi
}

command_display() {
  local arg
  local quoted
  local display=""
  for arg in "$@"; do
    printf -v quoted '%q' "$arg"
    display="${display:+$display }$quoted"
  done
  printf '%s' "$display"
}

require_python() {
  if ! command -v "$PYTHON_BIN" >/dev/null 2>&1; then
    die "python interpreter not found: $PYTHON_BIN"
  fi
}

record_artifact() {
  local id="$1"
  local path="$2"
  local architecture="$3"
  local kind="$4"
  local required="$5"
  local command="$6"
  local exit_code="$7"
  shift 7
  "$PYTHON_BIN" - "$MANIFEST_RECORDS" "$id" "$kind" "$path" "$architecture" "$required" \
    "$command" "$exit_code" "$REVIEWED_COMMIT" "$ROOT" "$@" <<'PY'
import hashlib
import json
import os
import re
import sys

records_path, artifact_id, kind, path, architecture, required_text, command, exit_code_text, reviewed_commit, repo_root = sys.argv[1:11]
reasons = list(sys.argv[11:])
required = required_text == "true"
try:
    exit_code = int(exit_code_text)
except ValueError:
    exit_code = None
    reasons.append(f"invalid command exit code `{exit_code_text}`")

if exit_code != 0:
    reasons.append(f"command exited {exit_code_text}")

exists = os.path.isfile(path)
size_bytes = None
sha256 = None
schema = None
commit_bindings = []
dirty_bindings = []
json_error = None
payload = None
evidence_requirements = []

SHA256_URI = re.compile(r"^sha256:[0-9a-f]{64}$")
FULL_SHA = re.compile(r"^[0-9a-fA-F]{40}$")


def add_requirement(requirement_id, status, message, **details):
    evidence_requirements.append(
        {
            "id": requirement_id,
            "status": status,
            "message": message,
            "details": details,
        }
    )
    if status == "fail":
        reasons.append(message)


def pass_requirement(requirement_id, message, **details):
    add_requirement(requirement_id, "pass", message, **details)


def fail_requirement(requirement_id, message, **details):
    add_requirement(requirement_id, "fail", message, **details)


def is_nonempty_string(value):
    return isinstance(value, str) and bool(value.strip())


def is_int_counter(value):
    return isinstance(value, int) and not isinstance(value, bool)


def safe_relative_path(value):
    if not is_nonempty_string(value):
        return None
    if "\0" in value or os.path.isabs(value):
        return None
    normalized = os.path.normpath(value)
    if normalized in {"", "."} or normalized == ".." or normalized.startswith(f"..{os.sep}"):
        return None
    return normalized


def file_sha256(path_value):
    with open(path_value, "rb") as handle:
        return hashlib.sha256(handle.read()).hexdigest()


def resolve_artifact_reference(base_dir, reference):
    normalized = safe_relative_path(reference)
    if normalized is None:
        return None, []
    candidates = []
    for root in (base_dir, repo_root):
        candidate = os.path.abspath(os.path.join(root, normalized))
        if candidate not in candidates:
            candidates.append(candidate)
    for candidate in candidates:
        if os.path.isfile(candidate):
            return candidate, candidates
    return None, candidates


def require_sha256_uri(value, requirement_id, label):
    if not isinstance(value, str) or not SHA256_URI.match(value):
        fail_requirement(
            requirement_id,
            f"{label} must be a canonical sha256:<64 lowercase hex> binding",
            value=value,
        )
        return None
    return value[len("sha256:") :]


def validate_hash_bound_file(requirement_id, base_dir, label, reference, expected_sha256):
    expected = require_sha256_uri(expected_sha256, f"{requirement_id}.sha256", f"{label} sha256")
    resolved, candidates = resolve_artifact_reference(base_dir, reference)
    if safe_relative_path(reference) is None:
        fail_requirement(
            f"{requirement_id}.path",
            f"{label} path must be a nonempty safe relative path",
            path=reference,
        )
        return
    if resolved is None:
        fail_requirement(
            f"{requirement_id}.exists",
            f"{label} artifact is missing or not a regular file",
            path=reference,
            candidates=candidates,
        )
        return
    size = os.path.getsize(resolved)
    if size == 0:
        fail_requirement(
            f"{requirement_id}.nonempty",
            f"{label} artifact is empty",
            path=reference,
            resolved_path=resolved,
        )
        return
    actual = file_sha256(resolved)
    if expected is None:
        return
    if actual != expected:
        fail_requirement(
            f"{requirement_id}.hash",
            f"{label} sha256 does not match artifact bytes",
            path=reference,
            expected=f"sha256:{expected}",
            actual=f"sha256:{actual}",
        )
        return
    pass_requirement(
        requirement_id,
        f"{label} artifact exists and matches its sha256 binding",
        path=reference,
        resolved_path=resolved,
        sha256=f"sha256:{actual}",
        size_bytes=size,
    )


def validate_unsafe_memory_report(payload, report_path):
    base_dir = os.path.dirname(os.path.abspath(report_path))
    if payload.get("repo_dirty") is not False:
        fail_requirement(
            "proof-unsafe-memory.repo-clean",
            "unsafe-memory report must set repo_dirty = false",
            value=payload.get("repo_dirty"),
        )
    else:
        pass_requirement("proof-unsafe-memory.repo-clean", "unsafe-memory report is bound to a clean repo")

    producer = payload.get("producer")
    producer_ok = (
        isinstance(producer, dict)
        and producer.get("command") == "targo trust report --unsafe-memory"
        and producer.get("native") is True
        and producer.get("python_used") is not True
    )
    if producer_ok:
        pass_requirement(
            "proof-unsafe-memory.native-producer",
            "unsafe-memory report declares the native unsafe-memory producer",
            command=producer.get("command"),
        )
    else:
        fail_requirement(
            "proof-unsafe-memory.native-producer",
            "unsafe-memory report must declare native producer command `targo trust report --unsafe-memory`",
            producer=producer,
        )

    validate_hash_bound_file(
        "proof-unsafe-memory.proof-report",
        base_dir,
        "unsafe-memory proof report",
        payload.get("proof_report_path"),
        payload.get("proof_report_hash"),
    )

    coverage = payload.get("coverage")
    coverage_pairs = [
        ("unsafe_blocks_total", "unsafe_blocks_proved"),
        ("unsafe_operations_total", "unsafe_operations_proved"),
        ("memory_obligations_total", "memory_obligations_proved"),
    ]
    if not isinstance(coverage, dict):
        fail_requirement(
            "proof-unsafe-memory.coverage",
            "unsafe-memory report must include structured coverage counters",
            coverage=coverage,
        )
    else:
        coverage_ok = True
        details = {}
        for total_key, proved_key in coverage_pairs:
            total = coverage.get(total_key)
            proved = coverage.get(proved_key)
            details[total_key] = total
            details[proved_key] = proved
            if not is_int_counter(total) or not is_int_counter(proved) or total <= 0 or proved != total:
                coverage_ok = False
        if coverage_ok:
            pass_requirement(
                "proof-unsafe-memory.coverage",
                "unsafe-memory coverage is positive and fully proved",
                **details,
            )
        else:
            fail_requirement(
                "proof-unsafe-memory.coverage",
                "unsafe-memory coverage counters must be positive and fully proved",
                **details,
            )

    unsupported = payload.get("unsupported")
    if unsupported == []:
        pass_requirement("proof-unsafe-memory.unsupported", "unsafe-memory unsupported set is empty")
    else:
        fail_requirement(
            "proof-unsafe-memory.unsupported",
            "unsafe-memory report must not contain unsupported obligations",
            unsupported=unsupported,
        )


def artifact_binding_for(obligation, aliases):
    artifacts = obligation.get("artifacts")
    if not isinstance(artifacts, dict):
        artifacts = obligation.get("artifact_bindings")
    if not isinstance(artifacts, dict):
        return None, None
    for alias in aliases:
        value = artifacts.get(alias)
        if value is not None:
            return value, alias
    return None, None


def solver_identity(obligation):
    solver = obligation.get("solver_identity")
    if is_nonempty_string(solver):
        return solver
    solver = obligation.get("solver")
    if is_nonempty_string(solver):
        return solver
    if isinstance(solver, dict):
        for key in ("identity", "name", "id"):
            value = solver.get(key)
            if is_nonempty_string(value):
                return value
    return None


def validate_concurrency_artifact_binding(base_dir, obligation_id, role, aliases, obligation):
    binding, alias = artifact_binding_for(obligation, aliases)
    if not isinstance(binding, dict):
        fail_requirement(
            f"proof-concurrency.{obligation_id}.{role}.binding",
            f"proof-concurrency obligation {obligation_id} must bind a structured {role} artifact",
            artifact_role=role,
            aliases=aliases,
        )
        return
    validate_hash_bound_file(
        f"proof-concurrency.{obligation_id}.{role}",
        base_dir,
        f"proof-concurrency obligation {obligation_id} {role}",
        binding.get("path"),
        binding.get("sha256"),
    )


def validate_concurrency_report(payload, report_path):
    fail_requirement(
        "proof-concurrency.authenticated-validator-availability",
        "no Trust-owned authenticated concurrency validator/replayer is implemented; JSON declarations and artifact hashes cannot establish proof authority",
    )
    if payload.get("proof_authority") == "trust_kernel_authenticated_replay" and payload.get("proof_pass") is True:
        pass_requirement(
            "proof-concurrency.authority-declaration",
            "proof-concurrency report declares the reserved authenticated-replay authority contract",
        )
    else:
        fail_requirement(
            "proof-concurrency.authority-declaration",
            "proof-concurrency artifact/demo audits with authority none or proof_pass false are non-proof",
            proof_authority=payload.get("proof_authority"),
            proof_pass=payload.get("proof_pass"),
        )

    validation = payload.get("validation")
    validation_ok = (
        isinstance(validation, dict)
        and validation.get("status") == "validated"
        and validation.get("authenticated") is True
        and validation.get("artifacts_authenticated") is True
        and validation.get("certificates_checked") is True
        and validation.get("transcripts_replayed") is True
        and validation.get("dispatches_authenticated") is True
    )
    if validation_ok:
        pass_requirement(
            "proof-concurrency.validation-declaration",
            "proof-concurrency report declares authenticated validation and replay",
        )
    else:
        fail_requirement(
            "proof-concurrency.validation-declaration",
            "proof-concurrency report must declare authenticated certificate validation, transcript replay, and dispatch authentication",
            validation=validation,
        )
    base_dir = os.path.dirname(os.path.abspath(report_path))
    if payload.get("repo_dirty") is not False:
        fail_requirement(
            "proof-concurrency.repo-clean",
            "proof-concurrency report must set repo_dirty = false",
            value=payload.get("repo_dirty"),
        )
    else:
        pass_requirement("proof-concurrency.repo-clean", "proof-concurrency report is bound to a clean repo")

    metadata = payload.get("repo_dirty_metadata")
    metadata_clean = (
        isinstance(metadata, dict)
        and (
            metadata.get("clean") is True
            or metadata.get("repo_dirty") is False
            or metadata.get("dirty") is False
        )
        and metadata.get("repo_dirty") is not True
        and metadata.get("dirty") is not True
        and metadata.get("clean") is not False
    )
    if metadata_clean:
        pass_requirement(
            "proof-concurrency.repo-dirty-metadata",
            "proof-concurrency report includes clean repo dirty metadata",
            metadata=metadata,
        )
    else:
        fail_requirement(
            "proof-concurrency.repo-dirty-metadata",
            "proof-concurrency report must include clean repo_dirty_metadata",
            metadata=metadata,
        )

    runner = payload.get("runner")
    runner_ok = (
        isinstance(runner, dict)
        and runner.get("implementation") == "rust"
        and runner.get("entrypoint") == "targo trust proof-concurrency"
        and runner.get("python_used") is False
    )
    if runner_ok:
        pass_requirement(
            "proof-concurrency.native-runner",
            "proof-concurrency report declares the native Rust runner",
            runner=runner,
        )
    else:
        fail_requirement(
            "proof-concurrency.native-runner",
            "proof-concurrency report must declare Rust-owned `targo trust proof-concurrency` runner",
            runner=runner,
        )

    obligations = payload.get("obligations")
    if not isinstance(obligations, list) or not obligations:
        fail_requirement(
            "proof-concurrency.obligations",
            "proof-concurrency obligations must be a nonempty array",
            obligations=obligations,
        )
        obligations = []
    else:
        pass_requirement(
            "proof-concurrency.obligations",
            "proof-concurrency report has structured obligations",
            obligation_count=len(obligations),
        )

    summary = payload.get("summary")
    zero_counters = [
        "failed",
        "unknown",
        "skipped",
        "unsupported",
        "runtime_checked",
        "timed_out",
        "manual_pass",
    ]
    summary_ok = isinstance(summary, dict)
    if summary_ok:
        expected_total = len(obligations)
        total = summary.get("total_obligations")
        proved = summary.get("proved")
        summary_ok = (
            is_int_counter(total)
            and total == expected_total
            and is_int_counter(proved)
            and proved == expected_total
        )
        for counter in zero_counters:
            value = summary.get(counter)
            if not is_int_counter(value) or value != 0:
                summary_ok = False
    if summary_ok:
        pass_requirement(
            "proof-concurrency.summary",
            "proof-concurrency summary exactly matches proved obligations and zero non-proof counters",
            summary=summary,
        )
    else:
        fail_requirement(
            "proof-concurrency.summary",
            "proof-concurrency summary counters must match obligations and keep all non-proof counters at zero",
            summary=summary,
            obligation_count=len(obligations),
        )

    required_kinds = {"data_race_free", "atomic_ordering", "happens_before"}
    seen_kinds = set()
    for index, obligation in enumerate(obligations):
        obligation_id = obligation.get("id") if isinstance(obligation, dict) else None
        if not is_nonempty_string(obligation_id):
            obligation_id = f"index-{index}"
            fail_requirement(
                f"proof-concurrency.{obligation_id}.id",
                "proof-concurrency obligation must include a nonempty id",
                index=index,
                obligation=obligation,
            )
        if not isinstance(obligation, dict):
            fail_requirement(
                f"proof-concurrency.{obligation_id}.object",
                f"proof-concurrency obligation {obligation_id} must be a JSON object",
                obligation=obligation,
            )
            continue

        kind_value = obligation.get("kind")
        if kind_value in required_kinds:
            seen_kinds.add(kind_value)
            pass_requirement(
                f"proof-concurrency.{obligation_id}.kind",
                f"proof-concurrency obligation {obligation_id} has a required kind",
                kind=kind_value,
            )
        else:
            fail_requirement(
                f"proof-concurrency.{obligation_id}.kind",
                f"proof-concurrency obligation {obligation_id} kind must be one of the required proof kinds",
                kind=kind_value,
                required=sorted(required_kinds),
            )

        if obligation.get("status") == "proved":
            pass_requirement(
                f"proof-concurrency.{obligation_id}.status",
                f"proof-concurrency obligation {obligation_id} is proved",
            )
        else:
            fail_requirement(
                f"proof-concurrency.{obligation_id}.status",
                f"proof-concurrency obligation {obligation_id} must have status = proved",
                status=obligation.get("status"),
            )

        source_field = obligation.get("source")
        if is_nonempty_string(source_field):
            pass_requirement(
                f"proof-concurrency.{obligation_id}.source-field",
                f"proof-concurrency obligation {obligation_id} includes source attribution",
                source=source_field,
            )
        else:
            fail_requirement(
                f"proof-concurrency.{obligation_id}.source-field",
                f"proof-concurrency obligation {obligation_id} must include nonempty source attribution",
                source=source_field,
            )

        memory_model = obligation.get("memory_model")
        if is_nonempty_string(memory_model):
            pass_requirement(
                f"proof-concurrency.{obligation_id}.memory-model",
                f"proof-concurrency obligation {obligation_id} includes a memory model",
                memory_model=memory_model,
            )
        else:
            fail_requirement(
                f"proof-concurrency.{obligation_id}.memory-model",
                f"proof-concurrency obligation {obligation_id} must include a nonempty memory_model",
                memory_model=memory_model,
            )

        identity = solver_identity(obligation)
        if is_nonempty_string(identity) and identity.lower() not in {"manual", "manual-pass", "stub", "demo"}:
            pass_requirement(
                f"proof-concurrency.{obligation_id}.solver",
                f"proof-concurrency obligation {obligation_id} includes a concrete solver identity",
                solver_identity=identity,
            )
        else:
            fail_requirement(
                f"proof-concurrency.{obligation_id}.solver",
                f"proof-concurrency obligation {obligation_id} must include a concrete non-manual solver identity",
                solver_identity=identity,
            )

        validate_concurrency_artifact_binding(
            base_dir,
            obligation_id,
            "source",
            ["source", "source_file", "source_artifact"],
            obligation,
        )
        validate_concurrency_artifact_binding(
            base_dir,
            obligation_id,
            "proof",
            ["proof", "proof_transcript", "transcript"],
            obligation,
        )
        validate_concurrency_artifact_binding(
            base_dir,
            obligation_id,
            "cert",
            ["cert", "certificate", "checked_certificate"],
            obligation,
        )
        validate_concurrency_artifact_binding(
            base_dir,
            obligation_id,
            "dispatch",
            ["dispatch", "solver_dispatch"],
            obligation,
        )

    missing_kinds = sorted(required_kinds - seen_kinds)
    if missing_kinds:
        fail_requirement(
            "proof-concurrency.required-kinds",
            "proof-concurrency report must include data_race_free, atomic_ordering, and happens_before obligations",
            missing_kinds=missing_kinds,
        )
    else:
        pass_requirement(
            "proof-concurrency.required-kinds",
            "proof-concurrency report covers all required proof kinds",
            required_kinds=sorted(required_kinds),
        )

if not exists:
    reasons.append("artifact missing")
else:
    size_bytes = os.path.getsize(path)
    if size_bytes == 0:
        reasons.append("artifact empty")
    with open(path, "rb") as handle:
        sha256 = hashlib.sha256(handle.read()).hexdigest()
    try:
        with open(path, "r", encoding="utf-8") as handle:
            payload = json.load(handle)
    except Exception as exc:  # noqa: BLE001 - report the concrete parser failure in the manifest.
        payload = None
        json_error = str(exc)
        if path.endswith(".json") or kind.startswith("trust."):
            reasons.append(f"artifact is not valid JSON: {exc}")
    if isinstance(payload, dict):
        schema_value = payload.get("schema") or payload.get("schema_version")
        if isinstance(schema_value, str):
            schema = schema_value
        elif kind.startswith("trust.") and kind != "trust.domination.report.v1":
            reasons.append("JSON report does not declare schema or schema_version")

        def walk(value, trail="$"):
            if isinstance(value, dict):
                for key, child in value.items():
                    child_trail = f"{trail}.{key}"
                    if key in {"repo_head", "candidate_commit", "reviewed_commit"} and isinstance(child, str):
                        commit_bindings.append({"field": child_trail, "value": child})
                    if key == "repo_dirty" and child is True:
                        dirty_bindings.append(child_trail)
                    walk(child, child_trail)
            elif isinstance(value, list):
                for index, child in enumerate(value):
                    walk(child, f"{trail}[{index}]")

        walk(payload)

commit_required = kind != "trust.domination.report.v1"
if exists and json_error is None and commit_required:
    if not commit_bindings:
        reasons.append("JSON report does not bind repo_head, candidate_commit, or reviewed_commit")
    else:
        for binding in commit_bindings:
            value = binding["value"]
            if not FULL_SHA.match(value):
                reasons.append(f"{binding['field']} is not a full 40-hex commit")
            elif reviewed_commit != "unknown" and value.lower() != reviewed_commit.lower():
                reasons.append(f"{binding['field']} does not match reviewed commit {reviewed_commit}")

for binding in dirty_bindings:
    reasons.append(f"{binding} is true")

if exists and json_error is None and kind.startswith("trust."):
    if schema != kind:
        reasons.append(f"JSON schema `{schema}` does not match expected `{kind}`")

if exists and json_error is None:
    if kind in {"trust.proof-unsafe-memory-report.v1", "trust.proof-concurrency.authenticated-validation-report.v1"} and not isinstance(payload, dict):
        reasons.append(f"{kind} artifact must be a JSON object")
    elif kind == "trust.proof-unsafe-memory-report.v1":
        validate_unsafe_memory_report(payload, path)
    elif kind == "trust.proof-concurrency.authenticated-validation-report.v1":
        validate_concurrency_report(payload, path)

deduped_reasons = []
for reason in reasons:
    if reason not in deduped_reasons:
        deduped_reasons.append(reason)

record = {
    "id": artifact_id,
    "kind": kind,
    "path": path,
    "path_relative": os.path.relpath(path, repo_root) if os.path.isabs(path) else path,
    "architecture": architecture or None,
    "required": required,
    "command": command,
    "exit_code": exit_code,
    "reviewed_commit": reviewed_commit,
    "exists": exists,
    "size_bytes": size_bytes,
    "sha256": sha256,
    "schema": schema,
    "commit_bindings": commit_bindings,
    "dirty_bindings": dirty_bindings,
    "evidence_requirements": evidence_requirements,
    "admissible": not deduped_reasons,
    "admissibility_reasons": deduped_reasons,
}
os.makedirs(os.path.dirname(records_path), exist_ok=True)
with open(records_path, "a", encoding="utf-8") as handle:
    handle.write(json.dumps(record, sort_keys=True) + "\n")
PY
}

run_artifact() {
  local id="$1"
  local path="$2"
  local architecture="$3"
  local kind="$4"
  shift 4
  local display
  display="$(command_display "$@")"
  log "::: $display"
  if [[ "$PLAN_ONLY" == true ]]; then
    return 0
  fi
  "$@" 2>&1 | tee -a "$LOG"
  local rc=${PIPESTATUS[0]}
  record_artifact "$id" "$path" "$architecture" "$kind" true "$display" "$rc"
}

capture_json_artifact() {
  local id="$1"
  local output="$2"
  local architecture="$3"
  local kind="$4"
  shift 4
  local display
  display="$(command_display "$@")"
  mkdir -p "$(dirname "$output")"
  log "::: $display > $output"
  if [[ "$PLAN_ONLY" == true ]]; then
    return 0
  fi
  "$@" >"$output" 2> >(tee -a "$LOG" >&2)
  local rc=$?
  record_artifact "$id" "$output" "$architecture" "$kind" true "$display > $output" "$rc"
}

record_missing_artifact() {
  local id="$1"
  local path="$2"
  local architecture="$3"
  local kind="$4"
  local reason="$5"
  record_artifact "$id" "$path" "$architecture" "$kind" true "$reason" 64 "$reason"
}

write_manifest() {
  local completed_at
  completed_at="$(timestamp_utc)"
  "$PYTHON_BIN" - "$MANIFEST_RECORDS" "$MANIFEST" "$RUN_ID" "$OUT_DIR" "$LOG" \
    "$REVIEWED_COMMIT" "$(repo_dirty)" "$MANIFEST_STARTED_AT" "$completed_at" <<'PY'
import json
import os
import sys

records_path, manifest_path, run_id, out_dir, log_path, reviewed_commit, repo_dirty_text, started_at, completed_at = sys.argv[1:10]
artifacts = []
if os.path.exists(records_path):
    with open(records_path, "r", encoding="utf-8") as handle:
        artifacts = [json.loads(line) for line in handle if line.strip()]

required = [artifact for artifact in artifacts if artifact["required"]]
non_admissible = [artifact for artifact in required if not artifact["admissible"]]
manifest = {
    "schema_version": "trust.strict-superiority.artifact-manifest.v1",
    "run_id": run_id,
    "reviewed_commit": reviewed_commit,
    "repo_dirty": repo_dirty_text == "true",
    "started_at": started_at,
    "completed_at": completed_at,
    "out_dir": out_dir,
    "commands_log": log_path,
    "artifact_count": len(artifacts),
    "required_artifact_count": len(required),
    "admissible_required_artifact_count": len(required) - len(non_admissible),
    "non_admissible_required_count": len(non_admissible),
    "non_admissible_required_ids": [artifact["id"] for artifact in non_admissible],
    "artifacts": artifacts,
}
os.makedirs(os.path.dirname(manifest_path), exist_ok=True)
with open(manifest_path, "w", encoding="utf-8") as handle:
    json.dump(manifest, handle, indent=2, sort_keys=True)
    handle.write("\n")
if non_admissible:
    for artifact in non_admissible:
        reasons = "; ".join(artifact["admissibility_reasons"])
        print(f"non-admissible artifact {artifact['id']}: {reasons}", file=sys.stderr)
    sys.exit(1)
PY
}

run() {
  log "::: $*"
  if [[ "$PLAN_ONLY" == true ]]; then
    return 0
  fi
  "$@" 2>&1 | tee -a "$LOG"
  local rc=${PIPESTATUS[0]}
  if [[ $rc -ne 0 ]]; then
    die "command failed with exit $rc: $*"
  fi
}

host_triple() {
  rustc -vV | awk '/^host:/ {print $2; exit}'
}

host_arch() {
  local arch
  arch="$(uname -m)"
  case "$arch" in
    arm64) printf 'aarch64\n' ;;
    amd64) printf 'x86_64\n' ;;
    *) printf '%s\n' "$arch" ;;
  esac
}

default_triple_for() {
  local arch="$1"
  local system
  system="$(uname -s)"
  case "$system:$arch" in
    Darwin:x86_64) printf 'x86_64-apple-darwin\n' ;;
    Darwin:aarch64) printf 'aarch64-apple-darwin\n' ;;
    Linux:x86_64) printf 'x86_64-unknown-linux-gnu\n' ;;
    Linux:aarch64) printf 'aarch64-unknown-linux-gnu\n' ;;
    *) printf '%s-unknown-unknown\n' "$arch" ;;
  esac
}

require_targo() {
  if [[ ! -x "$TARGO" ]]; then
    if [[ "$PLAN_ONLY" == true ]]; then
      log "targo binary not found at $TARGO; planned run would build targo-trust first"
      return 0
    fi
    log "targo binary not found at $TARGO; building targo-trust"
    run cargo build --manifest-path "$ROOT/targo-trust/Cargo.toml" --bin targo-trust
  fi
}

preflight_stage2_toolchain() {
  local preflight="$ROOT/scripts/check_upstream_rust_test_toolchain.sh"
  if [[ "$PLAN_ONLY" == true ]]; then
    log "::: bash $preflight"
    return 0
  fi
  [[ -f "$preflight" ]] || die "stage2 toolchain preflight script not found: $preflight"
  log "::: bash $preflight > $STAGE2_PREFLIGHT_LOG"
  if bash "$preflight" >"$STAGE2_PREFLIGHT_LOG" 2>&1; then
    sed -n '1,80p' "$STAGE2_PREFLIGHT_LOG" | tee -a "$LOG" >&2
  else
    local rc=$?
    sed -n '1,160p' "$STAGE2_PREFLIGHT_LOG" | tee -a "$LOG" >&2
    die "stage2 toolchain preflight failed with exit $rc; see $STAGE2_PREFLIGHT_LOG"
  fi
}

collect_upstream_compat() {
  local arch="$1"
  local triple="$2"
  local arch_dir="$OUT_DIR/upstream-rust/$arch"
  local summary="$arch_dir/compat-summary.json"
  local porting_dir="$arch_dir/porting"
  mkdir -p "$arch_dir"
  run_artifact "upstream-rust-$arch" "$summary" "$arch" "trust.compatibility.v1" \
    "$TARGO" trust domination upstream-tests \
    --release \
    --proof-mode full \
    --execute \
    --no-apply \
    --summary-out "$summary" \
    --out-dir "$porting_dir" \
    --run-id "$RUN_ID-upstream-$arch" \
    --target-arch "$arch" \
    --target "$triple" \
    --target-triple "$triple" \
    --host "$(host_arch)" \
    --host-triple "$(host_triple)"
}

collect_program_index_proof() {
  run_artifact "program-index-proof-design" "$OUT_DIR/program-index/proof-design/report.json" "" \
    "trust.compile-verify-program-index.report.v1" \
    "$TARGO" trust benchmark program-index \
    --run-id "$RUN_ID-proof-design" \
    --report-dir "$OUT_DIR/program-index/proof-design" \
    --suite proof-design \
    --slots trust-verify \
    --require-slots
}

collect_program_index_perf() {
  local mode="$1"
  local report_dir="$OUT_DIR/program-index/$mode"
  run_artifact "program-index-$mode" "$report_dir/report.json" "" \
    "trust.compile-verify-program-index.report.v1" \
    "$TARGO" trust benchmark program-index \
    --run-id "$RUN_ID-$mode" \
    --report-dir "$report_dir" \
    --slots upstream-rustc trust-noverify \
    --compile-measurement "$mode" \
    --runtime-parity \
    --repetitions "$REPETITIONS" \
    --require-slots
}

collect_unsafe_memory_report() {
  local output_dir="$OUT_DIR/proof"
  local output="$output_dir/unsafe-memory.json"
  local source_dir="${TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR:-$ROOT/reports/proof}"
  mkdir -p "$output_dir"
  if [[ "$PLAN_ONLY" == true ]]; then
    if [[ -n "${TRUST_PROOF_UNSAFE_MEMORY_REPORT:-}" ]]; then
      log "::: copy unsafe-memory proof bundle from $TRUST_PROOF_UNSAFE_MEMORY_REPORT to $output_dir"
    else
      log "::: $(command_display "$TARGO" trust report --unsafe-memory)"
      log "::: copy unsafe-memory proof bundle from $source_dir to $output_dir"
    fi
    return 0
  fi

  local source_wrapper=""
  local display=""
  local rc=0
  if [[ -z "${TRUST_PROOF_UNSAFE_MEMORY_REPORT:-}" ]]; then
    display="$(command_display "$TARGO" trust report --unsafe-memory)"
    log "::: $display"
    "$TARGO" trust report --unsafe-memory 2>&1 | tee -a "$LOG"
    rc=${PIPESTATUS[0]}
    source_wrapper="$source_dir/unsafe-memory.json"
  else
    source_wrapper="$TRUST_PROOF_UNSAFE_MEMORY_REPORT"
    display="copy unsafe-memory proof bundle from $source_wrapper to $output_dir"
    log "::: $display"
  fi

  if [[ $rc -eq 0 ]]; then
    if copy_unsafe_memory_bundle "$source_wrapper" "$output_dir"; then
      rc=0
    else
      rc=$?
    fi
  fi
  record_artifact "proof-unsafe-memory" "$output" "" "trust.proof-unsafe-memory-report.v1" \
    true "$display" "$rc"
}

copy_unsafe_memory_bundle() {
  local source_wrapper="$1"
  local output_dir="$2"
  local source_dir
  source_dir="$(dirname "$source_wrapper")"
  mkdir -p "$output_dir"
  cp "$source_wrapper" "$output_dir/unsafe-memory.json" 2> >(tee -a "$LOG" >&2) || return $?
  local sibling
  for sibling in report.json report.ndjson report.html; do
    if [[ -f "$source_dir/$sibling" ]]; then
      cp "$source_dir/$sibling" "$output_dir/$sibling" 2> >(tee -a "$LOG" >&2) || return $?
    fi
  done
  return 0
}

collect_product_proof() {
  capture_json_artifact "product-proof-release" "$OUT_DIR/release/product-proof.json" "" \
    "trust.release-report.v1" \
    "$TARGO" trust release check \
      --profile product-proof \
      --visibility public \
      --repo-root "$ROOT" \
      --json
}

collect_proof_concurrency() {
  capture_json_artifact "proof-concurrency" "$OUT_DIR/proof/concurrency.json" "" \
    "trust.proof-concurrency.authenticated-validation-report.v1" \
    "$TARGO" trust proof-concurrency --format json
}

render_domination_report() {
  local args=(
    trust domination
    --json
    --min-performance-advantage-pct "$MIN_PERF_ADVANTAGE_PCT"
    --compat-summary "$OUT_DIR/upstream-rust/x86_64/compat-summary.json"
    --compat-summary "$OUT_DIR/upstream-rust/aarch64/compat-summary.json"
    --proof-program-index-report "$OUT_DIR/program-index/proof-design/report.json"
    --program-index-benchmark-report "$OUT_DIR/program-index/cold-artifact/report.json"
    --program-index-benchmark-report "$OUT_DIR/program-index/warm-incremental/report.json"
    --product-proof-release-report "$OUT_DIR/release/product-proof.json"
    --proof-unsafe-memory-report "$OUT_DIR/proof/unsafe-memory.json"
  )
  capture_json_artifact "domination" "$OUT_DIR/domination.json" "" \
    "trust.domination.report.v1" "$TARGO" "${args[@]}"
}

main() {
  case "${1:-}" in
    --help|-h)
      usage
      return 0
      ;;
    --plan)
      PLAN_ONLY=true
      shift
      ;;
  esac
  if [[ $# -ne 0 ]]; then
    usage >&2
    return 2
  fi
  : >"$LOG"
  if [[ "$PLAN_ONLY" != true ]]; then
    require_python
    : >"$MANIFEST_RECORDS"
  fi
  MANIFEST_STARTED_AT="$(timestamp_utc)"
  REVIEWED_COMMIT="$(reviewed_commit)"
  require_targo
  log "strict-superiority run_id=$RUN_ID"
  log "out_dir=$OUT_DIR"
  log "targo=$TARGO"
  log "reviewed_commit=$REVIEWED_COMMIT"
  log "manifest=$MANIFEST"
  preflight_stage2_toolchain

  collect_upstream_compat x86_64 "${TRUST_X86_64_TRIPLE:-$(default_triple_for x86_64)}"
  collect_upstream_compat aarch64 "${TRUST_AARCH64_TRIPLE:-$(default_triple_for aarch64)}"
  collect_program_index_proof
  collect_program_index_perf cold-artifact
  collect_program_index_perf warm-incremental
  collect_unsafe_memory_report
  collect_product_proof
  collect_proof_concurrency
  render_domination_report

  if [[ "$PLAN_ONLY" == true ]]; then
    log "strict-superiority artifact manifest would be written to $MANIFEST"
    return 0
  fi
  if write_manifest 2> >(tee -a "$LOG" >&2); then
    log "release artifact manifest written to $MANIFEST"
  else
    die "release artifact manifest rejected one or more required artifacts"
  fi
  log "strict-superiority artifacts written to $OUT_DIR"
}

main "$@"
