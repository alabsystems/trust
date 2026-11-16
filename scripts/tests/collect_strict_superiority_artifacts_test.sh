#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COLLECTOR="$ROOT/scripts/collect_strict_superiority_artifacts.sh"
mkdir -p "$ROOT/reports/strict-superiority" "$ROOT/build"
TMP_ROOT="$(mktemp -d "$ROOT/reports/strict-superiority/collector-test.XXXXXX")"
STAGE2_TEST_ROOT="$(mktemp -d "$ROOT/build/collect-strict-stage2-test.XXXXXX")"
# The collector selects the OS from the host and the architecture from the
# validated stage2. Keep the synthetic stages on that OS so each architecture
# has a native execution case and an opposite-architecture refusal case.
case "$(uname -s)" in
  Darwin) FIXTURE_TARGET_OS=apple-darwin ;;
  Linux) FIXTURE_TARGET_OS=unknown-linux-gnu ;;
  *) echo "unsupported collector test host" >&2; exit 1 ;;
esac
ARM_STAGE2_TRIPLE="aarch64-$FIXTURE_TARGET_OS"
X86_STAGE2_TRIPLE="x86_64-$FIXTURE_TARGET_OS"
STAGE2_SYSROOT="$STAGE2_TEST_ROOT/$ARM_STAGE2_TRIPLE/stage2"
X86_STAGE2_SYSROOT="$STAGE2_TEST_ROOT/$X86_STAGE2_TRIPLE/stage2"
EXTERNAL_OUT_ROOT="$(mktemp -d)"

cleanup() {
  rm -rf "$TMP_ROOT"
  rm -rf "$STAGE2_TEST_ROOT"
  rm -rf "$EXTERNAL_OUT_ROOT"
}
trap cleanup EXIT

write_fake_targo() {
  local fake="$1"
  cat >"$fake" <<'SH'
#!/usr/bin/env bash
set -euo pipefail

if [[ "${1:-}" == "--version" ]]; then
  printf 'targo-trust 0.1.0\n'
  exit 0
fi

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
  write_json "$summary_out" schema_version 0.1.0 repo_head "$target_arch"
  if [[ "${FAKE_MUTATE_DISPATCHER_AFTER_UPSTREAM:-0}" == 1 ]]; then
    printf '\n# changed after preflight\n' >>"$0"
  fi
  if [[ "${FAKE_REMOVE_DISPATCHER_AFTER_UPSTREAM:-0}" == 1 ]]; then
    rm -- "$0"
  fi
  if [[ -n "${FAKE_SYMLINK_DISPATCHER_AFTER_UPSTREAM:-}" ]]; then
    cp "$0" "$FAKE_SYMLINK_DISPATCHER_AFTER_UPSTREAM"
    rm -- "$0"
    ln -s "$FAKE_SYMLINK_DISPATCHER_AFTER_UPSTREAM" "$0"
  fi
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
  python3 - "$proof_dir" "$commit" "${FAKE_REVIEWED_TREE:?}" "${FAKE_UNSAFE_TREE_MODE:-valid}" <<'PY'
import hashlib
import json
import os
import sys

proof_dir, commit, tree, tree_mode = sys.argv[1:5]
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
wrapper = {
    "schema": "trust.proof-unsafe-memory-report.v1",
    "candidate_commit": commit,
    "candidate_tree": tree,
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
}
if tree_mode == "missing":
    del wrapper["candidate_tree"]
elif tree_mode == "mismatch":
    wrapper["candidate_tree"] = "0" * 40
elif tree_mode != "valid":
    raise ValueError(f"unknown unsafe tree mode: {tree_mode}")
with open(os.path.join(proof_dir, "unsafe-memory.json"), "w", encoding="utf-8") as handle:
    json.dump(wrapper, handle)
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
  local host_name
  host_name="$(basename "$(dirname "$sysroot")")"
  mkdir -p "$bin" "$sysroot/lib/rustlib/$host_name/lib"

  cat >"$bin/trustc" <<SH
#!/usr/bin/env bash
set -euo pipefail
name="\$(basename "\$0")"
if [[ "\${1:-}" == "-Vv" ]]; then
  printf '%s 1.96.0-dev\\n' "\$name"
  printf 'binary: %s\\n' "\$name"
  printf 'commit-hash: $commit\\n'
  printf 'commit-date: 2026-06-03\\n'
  printf 'host: $host_name\\n'
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
  cp "$bin/targo-trust" "$bin/trustd"

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

  printf 'fake libstd\n' >"$sysroot/lib/rustlib/$host_name/lib/libstd-fake.rlib"
}

assert_override_withheld() {
  local manifest="$1"
  local selected="$2"
  local validated="$3"
  python3 - "$manifest" "$selected" "$validated" <<'PY'
import hashlib
import json
import sys

manifest_path, selected, validated = sys.argv[1:]
with open(manifest_path, encoding="utf-8") as stream:
    manifest = json.load(stream)
def digest(path):
    with open(path, "rb") as stream:
        return "sha256:" + hashlib.sha256(stream.read()).hexdigest()
assert manifest["dispatcher"] == {
    "validated_stage2_path": validated,
    "validated_stage2_sha256": digest(validated),
    "selected_path": selected,
    "selected_sha256_before": digest(selected),
    "selected_sha256_after": digest(selected),
    "content_match": True,
    "identity_match": False,
    "drift_reason": None,
}, manifest["dispatcher"]
assert manifest["required_artifact_count"] == 9, manifest
assert manifest["admissible_required_artifact_count"] == 0, manifest
assert manifest["non_admissible_required_count"] == 9, manifest
assert set(manifest["non_admissible_required_ids"]) == {
    artifact["id"] for artifact in manifest["artifacts"]
}, manifest
for artifact in manifest["artifacts"]:
    assert not artifact["admissible"], artifact
    assert any("dispatcher override differs from validated stage2 dispatcher" in reason
               for reason in artifact["admissibility_reasons"]), artifact
PY
}

assert_manifest_blocks_unreplayed_evidence() {
  local manifest="$1"
  python3 - "$manifest" <<'PY'
import json
import sys

manifest_path = sys.argv[1]
with open(manifest_path, "r", encoding="utf-8") as handle:
    manifest = json.load(handle)
assert manifest["schema_version"] == "trust.strict-superiority.artifact-manifest.v1"
assert manifest["required_artifact_count"] == 9
assert manifest["non_admissible_required_count"] == 9
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
assert set(manifest["non_admissible_required_ids"]) == expected
assert artifacts["upstream-rust-x86_64"]["architecture"] == "x86_64"
assert artifacts["upstream-rust-aarch64"]["architecture"] == "aarch64"
assert "skipped nonnative upstream suite" in artifacts["upstream-rust-x86_64"]["command"]
assert "--no-apply" in artifacts["upstream-rust-aarch64"]["command"]
assert "--out-dir" in artifacts["upstream-rust-aarch64"]["command"]
assert "/upstream-rust/aarch64/porting" in artifacts["upstream-rust-aarch64"]["command"]
for artifact_id, artifact in artifacts.items():
    if artifact_id == "upstream-rust-x86_64":
        assert artifact["exit_code"] == 64, artifact
        assert not artifact["exists"], artifact
        assert any("skipped nonnative upstream suite" in reason
                   for reason in artifact["admissibility_reasons"]), artifact
    else:
        assert artifact["exit_code"] == 0, artifact
    if artifact_id.startswith("upstream-rust-"):
        assert not artifact["admissible"], artifact
        assert any(
            requirement["id"] == "upstream-rust.independent-attestation"
            and requirement["status"] == "fail"
            for requirement in artifact["evidence_requirements"]
        ), artifact
        if artifact_id == "upstream-rust-aarch64":
            assert any("post-run upstream summary validation refused" in reason
                       for reason in artifact["admissibility_reasons"]), artifact
            assert not any("JSON schema" in reason for reason in artifact["admissibility_reasons"]), artifact
    elif artifact_id == "proof-concurrency":
        assert not artifact["admissible"], artifact
        assert any(
            requirement["id"] == "proof-concurrency.authenticated-validator-availability"
            and requirement["status"] == "fail"
            for requirement in artifact["evidence_requirements"]
        ), artifact
    elif artifact_id == "proof-unsafe-memory":
        assert not artifact["admissible"], artifact
        requirements = {item["id"]: item for item in artifact["evidence_requirements"]}
        assert requirements["proof-unsafe-memory.candidate-tree"]["status"] == "pass", artifact
        assert requirements["proof-unsafe-memory.proof-report"]["status"] == "pass", artifact
        assert requirements["proof-unsafe-memory.coverage"]["status"] == "pass", artifact
        assert requirements["proof-unsafe-memory.authenticated-proof-replay"]["status"] == "fail", artifact
    else:
        assert all("dispatcher override differs from validated stage2 dispatcher" in reason
                   for reason in artifact["admissibility_reasons"]), artifact
    if artifact["exists"]:
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
assert manifest["non_admissible_required_count"] == 9
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
assert manifest["non_admissible_required_count"] == 9
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
assert manifest["non_admissible_required_count"] == 9
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

run_hash_matched_fake_unsafe_case() {
  local case_dir="$TMP_ROOT/success"
  local fake="$case_dir/targo"
  local unsafe_source_dir="$case_dir/native-proof"
  mkdir -p "$case_dir/spoof-path"
  cat >"$case_dir/spoof-path/trustc" <<SH
#!/bin/sh
printf 'host: $X86_STAGE2_TRIPLE\n'
SH
  chmod +x "$case_dir/spoof-path/trustc"
  write_fake_targo "$fake"
  if env \
    PATH="$case_dir/spoof-path:$PATH" \
    TARGO="$fake" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-success \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$unsafe_source_dir" \
    "$COLLECTOR"; then
    echo "collector unexpectedly admitted unreplayed unsafe/concurrency evidence" >&2
    exit 1
  fi
  assert_manifest_blocks_unreplayed_evidence \
    "$case_dir/out/release-artifact-manifest.json"
  assert_override_withheld "$case_dir/out/release-artifact-manifest.json" \
    "$fake" "$STAGE2_SYSROOT/bin/targo-trust"
  grep -q -- "--host-triple $ARM_STAGE2_TRIPLE" "$case_dir/out/commands.log"
  if grep -q -- "--host-triple $X86_STAGE2_TRIPLE" "$case_dir/out/commands.log"; then
    echo "collector used spoofed PATH trustc for host metadata" >&2
    exit 1
  fi
  if grep -q "upstream-tests.*--target x86_64" "$case_dir/out/commands.log"; then
    echo "collector attempted nonnative x86_64 execution" >&2
    exit 1
  fi
  grep -q "skipped nonnative upstream suite" "$case_dir/out/commands.log"
  grep -q "upstream Rust compatibility summary validation failed" \
    "$case_dir/out/upstream-rust/aarch64/summary-validation.log"
  test -f "$case_dir/out/proof/report.json"
}

run_invalid_unsafe_tree_case() {
  local mode="$1"
  local case_dir="$TMP_ROOT/unsafe-tree-$mode"
  local fake="$case_dir/targo"
  mkdir -p "$case_dir"
  write_fake_targo "$fake"
  if env \
    TARGO="$fake" \
    OUT_DIR="$case_dir/out" \
    RUN_ID="manifest-unsafe-tree-$mode" \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    FAKE_UNSAFE_TREE_MODE="$mode" \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector unexpectedly admitted $mode unsafe candidate tree" >&2
    exit 1
  fi
  python3 - "$case_dir/out/release-artifact-manifest.json" "$mode" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
mode = sys.argv[2]
artifact = next(item for item in manifest["artifacts"] if item["id"] == "proof-unsafe-memory")
assert not artifact["admissible"], artifact
assert "proof-unsafe-memory" in manifest["non_admissible_required_ids"], manifest
requirements = {item["id"]: item for item in artifact["evidence_requirements"]}
tree = requirements["proof-unsafe-memory.candidate-tree"]
assert tree["status"] == "fail", tree
assert tree["details"]["candidate_tree"] == (None if mode == "missing" else "0" * 40), tree
assert requirements["proof-unsafe-memory.proof-report"]["status"] == "pass", artifact
assert requirements["proof-unsafe-memory.authenticated-proof-replay"]["status"] == "fail", artifact
PY
  assert_override_withheld "$case_dir/out/release-artifact-manifest.json" \
    "$fake" "$STAGE2_SYSROOT/bin/targo-trust"
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
  if [[ ! -f "$case_dir/out/release-artifact-manifest.json" ]]; then
    sed -n '1,160p' "$case_dir/stderr.log" >&2
    echo "collector did not write a manifest for missing unsafe-memory output" >&2
    exit 1
  fi
  assert_manifest_failed_on_missing_unsafe "$case_dir/out/release-artifact-manifest.json"
  assert_override_withheld "$case_dir/out/release-artifact-manifest.json" \
    "$fake" "$STAGE2_SYSROOT/bin/targo-trust"
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
  assert_override_withheld "$case_dir/out/release-artifact-manifest.json" \
    "$fake" "$STAGE2_SYSROOT/bin/targo-trust"
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
  assert_override_withheld "$case_dir/out/release-artifact-manifest.json" \
    "$fake" "$STAGE2_SYSROOT/bin/targo-trust"
}

run_other_host_import_case() {
  local case_dir="$TMP_ROOT/other-host-import"
  local fake="$case_dir/targo"
  local imported="$case_dir/x86_64-other-host.json"
  mkdir -p "$case_dir"
  write_fake_targo "$fake"
  python3 - "$imported" "$HEAD_COMMIT" "$X86_STAGE2_TRIPLE" <<'PY'
import json
import sys

path, commit, triple = sys.argv[1:]
with open(path, "w", encoding="utf-8") as stream:
    json.dump({"schema_version": "0.1.0", "repo_head": commit, "repo_dirty": False,
               "target_arch": "x86_64", "architecture": "x86_64",
               "target": triple, "target_triple": triple,
               "host": "x86_64", "host_triple": triple, "results": []}, stream)
PY
  if env \
    TARGO="$fake" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-other-host-import \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_UPSTREAM_X86_64_SUMMARY="$imported" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector unexpectedly admitted diagnostic other-host import" >&2
    exit 1
  fi
  python3 - "$case_dir/out/release-artifact-manifest.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
artifact = next(item for item in manifest["artifacts"] if item["id"] == "upstream-rust-x86_64")
assert artifact["exists"] and artifact["exit_code"] == 0, artifact
assert not artifact["admissible"], artifact
assert any("other-host summary is diagnostic only" in reason
           for reason in artifact["admissibility_reasons"]), artifact
assert any(item["id"] == "upstream-rust.independent-attestation"
           and item["status"] == "fail" for item in artifact["evidence_requirements"]), artifact
assert "upstream-rust-aarch64" in manifest["non_admissible_required_ids"], manifest
PY
  cmp -s "$imported" "$case_dir/out/upstream-rust/x86_64/compat-summary.json"
  assert_override_withheld "$case_dir/out/release-artifact-manifest.json" \
    "$fake" "$STAGE2_SYSROOT/bin/targo-trust"
  if grep -q "upstream-tests.*--target x86_64" "$case_dir/out/commands.log"; then
    echo "collector ran nonnative x86_64 suite after import" >&2
    exit 1
  fi

  local wrong_import="$case_dir/wrong-host.json"
  python3 - "$imported" "$wrong_import" "$ARM_STAGE2_TRIPLE" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    summary = json.load(stream)
summary["host_triple"] = sys.argv[3]
with open(sys.argv[2], "w", encoding="utf-8") as stream:
    json.dump(summary, stream)
PY
  if env \
    TARGO="$fake" \
    OUT_DIR="$case_dir/wrong-out" \
    RUN_ID=manifest-wrong-host-import \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_UPSTREAM_X86_64_SUMMARY="$wrong_import" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/wrong-stdout.log" 2>"$case_dir/wrong-stderr.log"; then
    echo "collector unexpectedly accepted wrong-host import" >&2
    exit 1
  fi
  python3 - "$case_dir/wrong-out/release-artifact-manifest.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
artifact = next(item for item in manifest["artifacts"] if item["id"] == "upstream-rust-x86_64")
assert artifact["exit_code"] == 64 and not artifact["exists"], artifact
assert any("other-host diagnostic import refused" in reason
           for reason in artifact["admissibility_reasons"]), artifact
PY
  assert_override_withheld "$case_dir/wrong-out/release-artifact-manifest.json" \
    "$fake" "$STAGE2_SYSROOT/bin/targo-trust"
}

run_native_x86_case() {
  local case_dir="$TMP_ROOT/native-x86"
  local fake="$case_dir/targo"
  mkdir -p "$case_dir"
  write_fake_targo "$fake"
  if env \
    TARGO="$fake" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-native-x86 \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    TRUST_STAGE2_SYSROOT="$X86_STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector unexpectedly admitted synthetic x86 suite" >&2
    exit 1
  fi
  python3 - "$case_dir/out/release-artifact-manifest.json" "$X86_STAGE2_TRIPLE" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
artifacts = {item["id"]: item for item in manifest["artifacts"]}
x86 = artifacts["upstream-rust-x86_64"]
arm = artifacts["upstream-rust-aarch64"]
assert x86["exit_code"] == 0 and x86["exists"] and not x86["admissible"], x86
assert arm["exit_code"] == 64 and not arm["exists"] and not arm["admissible"], arm
assert "--host-triple " + sys.argv[2] in x86["command"], x86
assert any(item["id"] == "upstream-rust.independent-attestation"
           and item["status"] == "fail" for item in x86["evidence_requirements"]), x86
PY
  assert_override_withheld "$case_dir/out/release-artifact-manifest.json" \
    "$fake" "$X86_STAGE2_SYSROOT/bin/targo-trust"
  if grep -q "upstream-tests.*--target aarch64" "$case_dir/out/commands.log"; then
    echo "collector attempted nonnative AArch64 suite on x86 stage2" >&2
    exit 1
  fi
}

run_cross_stage2_override_case() {
  local case_dir="$TMP_ROOT/cross-stage2-override"
  local selected="$X86_STAGE2_SYSROOT/bin/targo-trust"
  mkdir -p "$case_dir"
  write_fake_targo "$selected"
  if env \
    TARGO="$selected" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-cross-stage2-override \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector admitted a dispatcher from another stage2 sysroot" >&2
    exit 1
  fi
  assert_override_withheld "$case_dir/out/release-artifact-manifest.json" \
    "$selected" "$STAGE2_SYSROOT/bin/targo-trust"
  grep -q "dispatcher override differs from validated stage2 dispatcher" \
    "$case_dir/out/commands.log"
}

run_invalid_override_case() {
  local case_dir="$TMP_ROOT/invalid-override"
  mkdir -p "$case_dir"
  if env \
    TARGO="$case_dir/missing-targo-trust" \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-invalid-override \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector accepted a missing dispatcher override" >&2
    exit 1
  fi
  grep -q "TARGO override could not be resolved" "$case_dir/stderr.log"
  test ! -f "$case_dir/out/release-artifact-manifest.json"
}

run_default_stage2_dispatcher_case() {
  local case_dir="$TMP_ROOT/default-stage2-dispatcher"
  local stage2_dispatcher="$STAGE2_SYSROOT/bin/targo-trust"
  mkdir -p "$case_dir"
  write_fake_targo "$stage2_dispatcher"
  if env -u TARGO \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-default-stage2-dispatcher \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector admitted fake stage2 reports as release evidence" >&2
    exit 1
  fi
  if [[ ! -f "$case_dir/out/release-artifact-manifest.json" ]]; then
    sed -n '1,160p' "$case_dir/stderr.log" >&2
    echo "collector did not write a manifest for the default stage2 dispatcher" >&2
    exit 1
  fi
  python3 - "$case_dir/out/release-artifact-manifest.json" "$stage2_dispatcher" <<'PY'
import hashlib
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
dispatcher = sys.argv[2]
with open(dispatcher, "rb") as stream:
    sha256 = "sha256:" + hashlib.sha256(stream.read()).hexdigest()
assert manifest["dispatcher"] == {
    "validated_stage2_path": dispatcher,
    "validated_stage2_sha256": sha256,
    "selected_path": dispatcher,
    "selected_sha256_before": sha256,
    "selected_sha256_after": sha256,
    "content_match": True,
    "identity_match": True,
    "drift_reason": None,
}, manifest["dispatcher"]
assert set(manifest["non_admissible_required_ids"]) == {
    "upstream-rust-x86_64", "upstream-rust-aarch64", "proof-unsafe-memory",
    "proof-concurrency",
}, manifest
for artifact in manifest["artifacts"]:
    if artifact["id"] not in {"upstream-rust-x86_64"}:
        assert artifact["command"].startswith(dispatcher + " trust "), artifact
    assert not any("dispatcher override differs" in reason
                   for reason in artifact["admissibility_reasons"]), artifact
PY
  if grep -q 'targo-trust/target/debug/targo-trust' "$case_dir/out/commands.log"; then
    echo "collector fell back to the debug dispatcher" >&2
    exit 1
  fi
}

run_changed_stage2_dispatcher_case() {
  local case_dir="$TMP_ROOT/changed-stage2-dispatcher"
  local dispatcher="$STAGE2_SYSROOT/bin/targo-trust"
  mkdir -p "$case_dir"
  write_fake_targo "$dispatcher"
  if env -u TARGO \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-changed-stage2-dispatcher \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    FAKE_MUTATE_DISPATCHER_AFTER_UPSTREAM=1 \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector admitted reports after its dispatcher changed" >&2
    exit 1
  fi
  python3 - "$case_dir/out/release-artifact-manifest.json" "$dispatcher" <<'PY'
import hashlib
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
with open(sys.argv[2], "rb") as stream:
    after = "sha256:" + hashlib.sha256(stream.read()).hexdigest()
dispatcher = manifest["dispatcher"]
assert dispatcher["validated_stage2_path"] == sys.argv[2], dispatcher
assert dispatcher["selected_path"] == sys.argv[2], dispatcher
assert dispatcher["validated_stage2_sha256"] == dispatcher["selected_sha256_before"], dispatcher
assert dispatcher["selected_sha256_before"] != after, dispatcher
assert dispatcher["selected_sha256_after"] == after, dispatcher
assert dispatcher["content_match"] is False, dispatcher
assert dispatcher["identity_match"] is False, dispatcher
assert "selected dispatcher changed during artifact collection" in dispatcher["drift_reason"]
assert manifest["required_artifact_count"] == 9, manifest
assert manifest["non_admissible_required_count"] == 9, manifest
for artifact in manifest["artifacts"]:
    assert artifact["admissible"] is False, artifact
    assert dispatcher["drift_reason"] in artifact["admissibility_reasons"], artifact
PY
  grep -q "selected dispatcher changed during artifact collection" "$case_dir/stderr.log"
}

run_missing_stage2_dispatcher_case() {
  local case_dir="$TMP_ROOT/missing-stage2-dispatcher"
  local dispatcher="$STAGE2_SYSROOT/bin/targo-trust"
  mkdir -p "$case_dir"
  write_fake_targo "$dispatcher"
  if env -u TARGO \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-missing-stage2-dispatcher \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    FAKE_REMOVE_DISPATCHER_AFTER_UPSTREAM=1 \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector admitted reports after its dispatcher disappeared" >&2
    exit 1
  fi
  python3 - "$case_dir/out/release-artifact-manifest.json" "$dispatcher" <<'PY'
import json
import os
import re
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
dispatcher = manifest["dispatcher"]
assert not os.path.exists(sys.argv[2])
assert re.fullmatch(r"sha256:[0-9a-f]{64}", dispatcher["selected_sha256_before"])
assert dispatcher["selected_sha256_after"] is None, dispatcher
assert dispatcher["content_match"] is False, dispatcher
assert dispatcher["identity_match"] is False, dispatcher
assert "after=unavailable" in dispatcher["drift_reason"], dispatcher
assert manifest["non_admissible_required_count"] == manifest["required_artifact_count"] == 9
for artifact in manifest["artifacts"]:
    assert artifact["admissible"] is False, artifact
    assert dispatcher["drift_reason"] in artifact["admissibility_reasons"], artifact
PY
  grep -q "selected dispatcher identity unavailable" "$case_dir/stderr.log"
}

run_symlinked_stage2_dispatcher_case() {
  local case_dir="$TMP_ROOT/symlinked-stage2-dispatcher"
  local dispatcher="$STAGE2_SYSROOT/bin/targo-trust"
  local replacement="$case_dir/identical-targo-trust"
  mkdir -p "$case_dir"
  write_fake_targo "$dispatcher"
  if env -u TARGO \
    OUT_DIR="$case_dir/out" \
    RUN_ID=manifest-symlinked-stage2-dispatcher \
    FAKE_REVIEWED_COMMIT="$HEAD_COMMIT" \
    FAKE_SYMLINK_DISPATCHER_AFTER_UPSTREAM="$replacement" \
    TRUST_STAGE2_SYSROOT="$STAGE2_SYSROOT" \
    TRUST_PROOF_UNSAFE_MEMORY_SOURCE_DIR="$case_dir/native-proof" \
    "$COLLECTOR" >"$case_dir/stdout.log" 2>"$case_dir/stderr.log"; then
    echo "collector admitted a symlinked dispatcher with identical bytes" >&2
    exit 1
  fi
  python3 - "$case_dir/out/release-artifact-manifest.json" "$dispatcher" "$replacement" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
dispatcher_path = Path(sys.argv[2])
replacement = Path(sys.argv[3])
assert dispatcher_path.is_symlink()
assert dispatcher_path.resolve() == replacement
with replacement.open("rb") as stream:
    same_bytes = "sha256:" + hashlib.sha256(stream.read()).hexdigest()
dispatcher = manifest["dispatcher"]
assert dispatcher["selected_sha256_before"] == same_bytes, dispatcher
assert dispatcher["selected_sha256_after"] is None, dispatcher
assert dispatcher["content_match"] is False, dispatcher
assert dispatcher["identity_match"] is False, dispatcher
assert "after=unavailable" in dispatcher["drift_reason"], dispatcher
assert manifest["non_admissible_required_count"] == manifest["required_artifact_count"] == 9
for artifact in manifest["artifacts"]:
    assert artifact["admissible"] is False, artifact
    assert dispatcher["drift_reason"] in artifact["admissibility_reasons"], artifact
PY
  grep -q "dispatcher no longer resolves to its selected path" "$case_dir/stderr.log"
}

run_external_out_dir_refusal_case() {
  local stderr="$TMP_ROOT/external-out-stderr.log"
  if env OUT_DIR="$EXTERNAL_OUT_ROOT/should-not-exist" "$COLLECTOR" --plan \
    >/dev/null 2>"$stderr"; then
    echo "collector accepted external OUT_DIR" >&2
    exit 1
  fi
  grep -q "OUT_DIR must resolve inside this checkout" "$stderr"
  test ! -e "$EXTERNAL_OUT_ROOT/should-not-exist"

  ln -s "$EXTERNAL_OUT_ROOT" "$TMP_ROOT/escaped-out-dir"
  if env OUT_DIR="$TMP_ROOT/escaped-out-dir/child" "$COLLECTOR" --plan \
    >/dev/null 2>"$stderr"; then
    echo "collector accepted symlink-escaped OUT_DIR" >&2
    exit 1
  fi
  grep -q "OUT_DIR must resolve inside this checkout" "$stderr"
  test ! -e "$EXTERNAL_OUT_ROOT/child"
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
  grep -q -- "--compat-summary" "$case_dir/out/commands.log"
  grep -q "native-only upstream collection" "$case_dir/out/commands.log"
  grep -q "otherwise skip nonnative" "$case_dir/out/commands.log"
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
FAKE_REVIEWED_TREE="$(git -C "$ROOT" rev-parse "${HEAD_COMMIT}^{tree}")"
export FAKE_REVIEWED_TREE
write_fake_stage2_sysroot "$STAGE2_SYSROOT" "$HEAD_COMMIT"
write_fake_stage2_sysroot "$X86_STAGE2_SYSROOT" "$HEAD_COMMIT"
run_hash_matched_fake_unsafe_case
run_invalid_unsafe_tree_case missing
run_invalid_unsafe_tree_case mismatch
run_missing_unsafe_case
run_missing_concurrency_dispatch_case
run_narrative_concurrency_case
run_other_host_import_case
run_native_x86_case
run_cross_stage2_override_case
run_invalid_override_case
run_default_stage2_dispatcher_case
run_changed_stage2_dispatcher_case
run_missing_stage2_dispatcher_case
run_symlinked_stage2_dispatcher_case
run_external_out_dir_refusal_case
run_plan_case
