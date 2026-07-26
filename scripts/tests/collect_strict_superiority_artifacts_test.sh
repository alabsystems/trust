#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COLLECTOR="$ROOT/scripts/collect_strict_superiority_artifacts.sh"
TMP_ROOT="$(mktemp -d)"
STAGE2_TEST_ROOT="$ROOT/build/collect-strict-stage2-test-$$"
STAGE2_SYSROOT="$STAGE2_TEST_ROOT/stage2"

cleanup() {
  rm -rf "$TMP_ROOT"
  rm -rf "$STAGE2_TEST_ROOT"
}
trap cleanup EXIT

write_json_report() {
  local path="$1"
  local schema_field="$2"
  local schema="$3"
  local commit_field="$4"
  local commit="$5"
  local arch="${6:-}"
  mkdir -p "$(dirname "$path")"
  python3 - "$path" "$schema_field" "$schema" "$commit_field" "$commit" "$arch" <<'PY'
import json
import sys

path, schema_field, schema, commit_field, commit, arch = sys.argv[1:7]
payload = {
    schema_field: schema,
    commit_field: commit,
    "repo_dirty": False,
    "runner": {
        "implementation": "rust",
        "entrypoint": "targo trust strict-superiority fake",
        "python_used": False,
    },
}
if arch:
    payload["target_arch"] = arch
with open(path, "w", encoding="utf-8") as handle:
    json.dump(payload, handle)
    handle.write("\n")
PY
}

write_fake_targo() {
  local fake="$1"
  cat >"$fake" <<'SH'
#!/usr/bin/env bash
set -euo pipefail

commit="${FAKE_REVIEWED_COMMIT:?}"

write_json() {
  local path="$1"
  local schema_field="$2"
  local schema="$3"
  local commit_field="$4"
  local arch="${5:-}"
  mkdir -p "$(dirname "$path")"
  python3 - "$path" "$schema_field" "$schema" "$commit_field" "$commit" "$arch" <<'PY'
import json
import sys

path, schema_field, schema, commit_field, commit, arch = sys.argv[1:7]
payload = {
    schema_field: schema,
    commit_field: commit,
    "repo_dirty": False,
    "runner": {
        "implementation": "rust",
        "entrypoint": "targo trust strict-superiority fake",
        "python_used": False,
    },
}
if arch:
    payload["target_arch"] = arch
with open(path, "w", encoding="utf-8") as handle:
    json.dump(payload, handle)
    handle.write("\n")
PY
}

if [[ "${1:-}" == "trust" && "${2:-}" == "domination" && "${3:-}" == "upstream-tests" ]]; then
  shift 3
  summary_out=""
  out_dir=""
  target_arch=""
  no_apply=0
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --summary-out)
        summary_out="$2"
        shift 2
        ;;
      --out-dir)
        out_dir="$2"
        shift 2
        ;;
      --target-arch)
        target_arch="$2"
        shift 2
        ;;
      --no-apply)
        no_apply=1
        shift
        ;;
      *)
        shift
        ;;
    esac
  done
  if [[ -z "$summary_out" || -z "$out_dir" || "$no_apply" -ne 1 ]]; then
    echo "upstream compat fake requires --summary-out, --out-dir, and --no-apply" >&2
    exit 2
  fi
  mkdir -p "$out_dir"
  printf 'isolated porting artifacts for %s\n' "$target_arch" >"$out_dir/scorecard.md"
  write_json "$summary_out" schema_version trust.compatibility.v1 repo_head "$target_arch"
  exit 0
fi

if [[ "${1:-}" == "trust" && "${2:-}" == "benchmark" && "${3:-}" == "program-index" ]]; then
  shift 3
  report_dir=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --report-dir)
        report_dir="$2"
        shift 2
        ;;
      *)
        shift
        ;;
    esac
  done
  write_json "$report_dir/report.json" schema trust.compile-verify-program-index.report.v1 repo_head
  exit 0
fi

if [[ "${1:-}" == "trust" && "${2:-}" == "release" && "${3:-}" == "check" ]]; then
  python3 - "$commit" <<'PY'
import json
import sys

commit = sys.argv[1]
json.dump(
    {
        "schema_version": "trust.release-report.v1",
        "candidate_commit": commit,
        "repo_dirty": False,
        "runner": {
            "implementation": "rust",
            "entrypoint": "targo trust release check",
            "python_used": False,
        },
        "status": "pass",
    },
    sys.stdout,
)
print()
PY
  exit 0
fi

if [[ "${1:-}" == "trust" && "${2:-}" == "report" && "${3:-}" == "--unsafe-memory" ]]; then
  if [[ $# -ne 3 ]]; then
    echo "unsafe-memory fake only accepts exact targo trust report --unsafe-memory" >&2
    exit 2
  fi
  if [[ "${FAKE_UNSAFE_REPORT_FAIL:-}" == "1" ]]; then
    echo "unsafe-memory fake failure requested" >&2
    exit 2
  fi
  proof_dir="${TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR:-reports/proof}"
  mkdir -p "$proof_dir"
  python3 - "$proof_dir" "$commit" <<'PY'
import hashlib
import json
import os
import sys

proof_dir, commit = sys.argv[1:3]
report_path = os.path.join(proof_dir, "report.json")
with open(report_path, "w", encoding="utf-8") as handle:
    json.dump(
        {
            "schema_version": "trust.report.fake.v1",
            "repo_head": commit,
            "repo_dirty": False,
        },
        handle,
    )
    handle.write("\n")
with open(report_path, "rb") as handle:
    digest = hashlib.sha256(handle.read()).hexdigest()
with open(os.path.join(proof_dir, "unsafe-memory.json"), "w", encoding="utf-8") as handle:
    json.dump(
        {
            "schema": "trust.proof-unsafe-memory-report.v1",
            "candidate_commit": commit,
            "repo_dirty": False,
            "producer": {
                "command": "targo trust report --unsafe-memory",
                "native": True,
            },
            "proof_report_path": "report.json",
            "proof_report_hash": f"sha256:{digest}",
            "coverage": {
                "unsafe_blocks_total": 1,
                "unsafe_blocks_proved": 1,
                "unsafe_operations_total": 1,
                "unsafe_operations_proved": 1,
                "memory_obligations_total": 1,
                "memory_obligations_proved": 1,
            },
            "unsupported": [],
        },
        handle,
    )
    handle.write("\n")
PY
  exit 0
fi

if [[ "${1:-}" == "trust" && "${2:-}" == "proof-concurrency" ]]; then
  if [[ "${FAKE_CONCURRENCY_NARRATIVE_ONLY:-}" == "1" ]]; then
    python3 - "$commit" <<'PY'
import json
import sys

commit = sys.argv[1]
json.dump(
    {
        "schema": "trust.proof-concurrency.authenticated-validation-report.v1",
        "repo_head": commit,
        "repo_dirty": False,
        "notes": "manual review says the concurrency examples pass",
    },
    sys.stdout,
)
print()
PY
    exit 0
  fi
  python3 - "$commit" "${OUT_DIR:-reports/strict-superiority/fake}" "${FAKE_CONCURRENCY_MISSING_DISPATCH:-}" <<'PY'
import hashlib
import json
import os
import sys

commit, out_dir, missing_dispatch = sys.argv[1:4]
report_dir = os.path.join(out_dir, "proof")
artifact_dir = os.path.join(report_dir, "concurrency-artifacts")
os.makedirs(artifact_dir, exist_ok=True)

specs = [
    ("race_free_arc_mutex", "data_race_free", "Arc<Mutex<T>> critical section", "rust-sync-release-v1"),
    ("atomic_release_acquire", "atomic_ordering", "Atomic release/acquire handoff", "rust-atomics-release-v1"),
    ("channel_happens_before", "happens_before", "mpsc send happens-before recv", "rust-channel-release-v1"),
]

roles = [
    ("source", "source.rs"),
    ("proof", "proof"),
    ("cert", "cert"),
    ("dispatch", "dispatch"),
]

def artifact_binding(obligation_id, role, extension):
    rel_path = f"concurrency-artifacts/{obligation_id}.{extension}"
    abs_path = os.path.join(report_dir, rel_path)
    body = f"{obligation_id}:{role}:structured test artifact\n".encode("utf-8")
    if not (missing_dispatch == "1" and obligation_id == "channel_happens_before" and role == "dispatch"):
        with open(abs_path, "wb") as handle:
            handle.write(body)
    return {
        "path": rel_path,
        "sha256": "sha256:" + hashlib.sha256(body).hexdigest(),
    }

obligations = []
for obligation_id, kind, source, memory_model in specs:
    obligations.append(
        {
            "id": obligation_id,
            "kind": kind,
            "status": "proved",
            "source": source,
            "memory_model": memory_model,
            "solver": {
                "identity": "trust-concurrency-prover-release-v1",
                "version": "test-fixture",
            },
            "artifacts": {
                role: artifact_binding(obligation_id, role, extension)
                for role, extension in roles
            },
        }
    )

json.dump(
    {
        "schema": "trust.proof-concurrency.authenticated-validation-report.v1",
        "repo_head": commit,
        "repo_dirty": False,
        "repo_dirty_metadata": {"clean": True, "repo_dirty": False},
        "runner": {
            "implementation": "rust",
            "entrypoint": "targo trust proof-concurrency",
            "python_used": False,
        },
        "summary": {
            "total_obligations": len(obligations),
            "proved": len(obligations),
            "failed": 0,
            "unknown": 0,
            "skipped": 0,
            "unsupported": 0,
            "runtime_checked": 0,
            "timed_out": 0,
            "manual_pass": 0,
        },
        "obligations": obligations,
    },
    sys.stdout,
)
print()
PY
  exit 0
fi

if [[ "${1:-}" == "trust" && "${2:-}" == "domination" ]]; then
  python3 - <<'PY'
import json
import sys

json.dump(
    {
        "schema": "trust.domination.report.v1",
        "status": "strictly_superior",
    },
    sys.stdout,
)
print()
PY
  exit 0
fi

echo "unexpected fake targo invocation: $*" >&2
exit 2
SH
  chmod +x "$fake"
}

write_fake_stage2_sysroot() {
  local sysroot="$1"
  local commit="$2"
  local bin="$sysroot/bin"
  mkdir -p "$bin" "$sysroot/lib/rustlib/test-target/lib"

  cat >"$bin/trustc" <<SH
#!/usr/bin/env bash
set -euo pipefail
name="\$(basename "\$0")"
if [[ "\${1:-}" == "-Vv" ]]; then
  printf '%s 1.96.0-dev\\n' "\$name"
  printf 'binary: %s\\n' "\$name"
  printf 'commit-hash: $commit\\n'
  printf 'commit-date: 2026-06-03\\n'
  printf 'host: aarch64-apple-darwin\\n'
  printf 'release: 1.96.0-dev\\n'
  exit 0
fi
printf '%s 1.96.0-dev\\n' "\$name"
SH
  chmod +x "$bin/trustc"
  cp "$bin/trustc" "$bin/rustc"

  cat >"$bin/targo" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ "${1:-}" == "trust" && "${2:-}" == "domination" && "${3:-}" == "upstream-tests" && "${4:-}" == "--help" ]]; then
  printf 'targo trust domination upstream-tests dispatches trust-upstream-compat port\n'
  exit 0
fi
printf '%s 1.96.0-dev\n' "$(basename "$0")"
SH
  chmod +x "$bin/targo"
  cp "$bin/targo" "$bin/cargo"

  cat >"$bin/targo-trust" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf '%s 0.1.0\n' "$(basename "$0")"
SH
  chmod +x "$bin/targo-trust"

  cat >"$bin/trustdoc" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
name="$(basename "$0")"
if [[ "${1:-}" == "-Vv" ]]; then
  printf '%s 1.96.0-dev\n' "$name"
  printf 'binary: %s\n' "$name"
else
  printf '%s 1.96.0-dev\n' "$name"
fi
SH
  chmod +x "$bin/trustdoc"

  cat >"$bin/trustfmt" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf '%s 1.96.0-dev\n' "$(basename "$0")"
SH
  chmod +x "$bin/trustfmt"
  cp "$bin/trustfmt" "$bin/targo-fmt"
  cp "$bin/trustfmt" "$bin/tippy"
  cp "$bin/trustfmt" "$bin/targo-tippy"
  cp "$bin/trustfmt" "$bin/tippy-driver"
  cp "$bin/trustfmt" "$bin/trust-analyzer"

  printf 'fake libstd\n' >"$sysroot/lib/rustlib/test-target/lib/libstd-fake.rlib"
}

assert_manifest_blocks_missing_concurrency_validator() {
  local manifest="$1"
  python3 - "$manifest" <<'PY'
import json
import sys

manifest_path = sys.argv[1]
with open(manifest_path, "r", encoding="utf-8") as handle:
    manifest = json.load(handle)
assert manifest["schema_version"] == "trust.strict-superiority.artifact-manifest.v1"
assert manifest["required_artifact_count"] == 9
assert manifest["non_admissible_required_count"] == 1
assert manifest["non_admissible_required_ids"] == ["proof-concurrency"]
artifacts = {artifact["id"]: artifact for artifact in manifest["artifacts"]}
expected = {
    "upstream-rust-x86_64",
    "upstream-rust-aarch64",
    "program-index-proof-design",
    "program-index-cold-artifact",
    "program-index-warm-incremental",
    "proof-unsafe-memory",
    "product-proof-release",
    "proof-concurrency",
    "domination",
}
assert set(artifacts) == expected
assert artifacts["upstream-rust-x86_64"]["architecture"] == "x86_64"
assert artifacts["upstream-rust-aarch64"]["architecture"] == "aarch64"
assert "--no-apply" in artifacts["upstream-rust-x86_64"]["command"]
assert "--out-dir" in artifacts["upstream-rust-x86_64"]["command"]
assert "/upstream-rust/x86_64/porting" in artifacts["upstream-rust-x86_64"]["command"]
assert "--no-apply" in artifacts["upstream-rust-aarch64"]["command"]
assert "--out-dir" in artifacts["upstream-rust-aarch64"]["command"]
assert "/upstream-rust/aarch64/porting" in artifacts["upstream-rust-aarch64"]["command"]
for artifact_id, artifact in artifacts.items():
    assert artifact["exit_code"] == 0, artifact
    if artifact_id == "proof-concurrency":
        assert not artifact["admissible"], artifact
        assert any(
            requirement["id"] == "proof-concurrency.authenticated-validator-availability"
            and requirement["status"] == "fail"
            for requirement in artifact["evidence_requirements"]
        ), artifact
    else:
        assert artifact["admissible"], artifact
    assert artifact["sha256"], artifact
    assert artifact["reviewed_commit"] == manifest["reviewed_commit"]
PY
}

assert_manifest_failed_on_missing_unsafe() {
  local manifest="$1"
  python3 - "$manifest" <<'PY'
import json
import sys

manifest_path = sys.argv[1]
with open(manifest_path, "r", encoding="utf-8") as handle:
    manifest = json.load(handle)
assert manifest["non_admissible_required_count"] == 2
assert set(manifest["non_admissible_required_ids"]) == {
    "proof-unsafe-memory",
    "proof-concurrency",
}
artifact = next(item for item in manifest["artifacts"] if item["id"] == "proof-unsafe-memory")
assert not artifact["admissible"]
assert artifact["exit_code"] != 0
assert "artifact missing" in artifact["admissibility_reasons"]
PY
}

assert_manifest_failed_on_concurrency_dispatch() {
  local manifest="$1"
  python3 - "$manifest" <<'PY'
import json
import sys

manifest_path = sys.argv[1]
with open(manifest_path, "r", encoding="utf-8") as handle:
    manifest = json.load(handle)
assert manifest["non_admissible_required_count"] == 1
assert manifest["non_admissible_required_ids"] == ["proof-concurrency"]
artifact = next(item for item in manifest["artifacts"] if item["id"] == "proof-concurrency")
assert not artifact["admissible"]
assert any(
    requirement["id"] == "proof-concurrency.channel_happens_before.dispatch.exists"
    and requirement["status"] == "fail"
    for requirement in artifact["evidence_requirements"]
), artifact["evidence_requirements"]
assert any("dispatch artifact is missing" in reason for reason in artifact["admissibility_reasons"])
PY
}

assert_manifest_failed_on_concurrency_narrative() {
  local manifest="$1"
  python3 - "$manifest" <<'PY'
import json
import sys

manifest_path = sys.argv[1]
with open(manifest_path, "r", encoding="utf-8") as handle:
    manifest = json.load(handle)
assert manifest["non_admissible_required_count"] == 1
assert manifest["non_admissible_required_ids"] == ["proof-concurrency"]
artifact = next(item for item in manifest["artifacts"] if item["id"] == "proof-concurrency")
assert not artifact["admissible"]
assert any(
    requirement["id"] == "proof-concurrency.obligations"
    and requirement["status"] == "fail"
    for requirement in artifact["evidence_requirements"]
), artifact["evidence_requirements"]
assert any("obligations must be a nonempty array" in reason for reason in artifact["admissibility_reasons"])
PY
}

run_complete_fixture_still_blocks_concurrency_case() {
  local case_dir="$TMP_ROOT/success"
  local fake="$case_dir/targo"
  local unsafe_source_dir="$case_dir/native-proof"
  mkdir -p "$case_dir"
  write_fake_targo "$fake"
  if env \
    TARGO="$fake" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-success \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$unsafe_source_dir" \
    "$COLLECTOR"; then
    echo "collector unexpectedly admitted concurrency evidence without a real validator" >&2
    exit 1
  fi
  assert_manifest_blocks_missing_concurrency_validator \
    "$case_dir/out/release-artifact-manifest.json"
  test -f "$case_dir/out/proof/report.json"
}

run_missing_unsafe_case() {
  local case_dir="$TMP_ROOT/missing-unsafe"
  local fake="$case_dir/targo"
  local unsafe_source_dir="$case_dir/native-proof"
  mkdir -p "$case_dir"
  write_fake_targo "$fake"
  if env \
    TARGO="$fake" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-missing-unsafe \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    FAKE_UNSAFE_REPORT_FAIL=1 \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$unsafe_source_dir" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector unexpectedly succeeded without native unsafe-memory proof output" >&2
    exit 1
  fi
  assert_manifest_failed_on_missing_unsafe "$case_dir/out/release-artifact-manifest.json"
}

run_missing_concurrency_dispatch_case() {
  local case_dir="$TMP_ROOT/missing-concurrency-dispatch"
  local fake="$case_dir/targo"
  local unsafe_source_dir="$case_dir/native-proof"
  mkdir -p "$case_dir"
  write_fake_targo "$fake"
  if env \
    TARGO="$fake" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-missing-concurrency-dispatch \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    FAKE_CONCURRENCY_MISSING_DISPATCH=1 \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$unsafe_source_dir" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector unexpectedly succeeded without concurrency dispatch artifact" >&2
    exit 1
  fi
  assert_manifest_failed_on_concurrency_dispatch "$case_dir/out/release-artifact-manifest.json"
}

run_narrative_concurrency_case() {
  local case_dir="$TMP_ROOT/narrative-concurrency"
  local fake="$case_dir/targo"
  local unsafe_source_dir="$case_dir/native-proof"
  mkdir -p "$case_dir"
  write_fake_targo "$fake"
  if env \
    TARGO="$fake" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-narrative-concurrency \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    FAKE_CONCURRENCY_NARRATIVE_ONLY=1 \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$unsafe_source_dir" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector unexpectedly accepted narrative-only concurrency proof evidence" >&2
    exit 1
  fi
  assert_manifest_failed_on_concurrency_narrative "$case_dir/out/release-artifact-manifest.json"
}

run_plan_case() {
  local case_dir="$TMP_ROOT/plan"
  mkdir -p "$case_dir"
  env \
    TARGO="$case_dir/nonexistent-targo" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-plan \
    "$COLLECTOR" --plan
  test ! -f "$case_dir/out/release-artifact-manifest.json"
  grep -q -- "--proof-mode full" "$case_dir/out/commands.log"
  grep -q -- "--no-apply" "$case_dir/out/commands.log"
  grep -q -- "--out-dir" "$case_dir/out/commands.log"
  grep -q -- "trust report --unsafe-memory" "$case_dir/out/commands.log"
  grep -q -- "check_upstream_rust_test_toolchain.sh" "$case_dir/out/commands.log"
  grep -q "strict-superiority artifact manifest would be written" "$case_dir/out/commands.log"
}

bash -n "$COLLECTOR"
bash -n "$0"
if command -v shellcheck >/dev/null 2>&1; then
  shellcheck "$COLLECTOR" "$0"
fi

HEAD_COMMIT="$(git -C "$ROOT" rev-parse HEAD)"
write_fake_stage2_sysroot "$STAGE2_SYSROOT" "$HEAD_COMMIT"
run_complete_fixture_still_blocks_concurrency_case
run_missing_unsafe_case
run_missing_concurrency_dispatch_case
run_narrative_concurrency_case
run_plan_case
