#!/usr/bin/env bash
# Kernel-check AY's quantified projection semantic theorem and require its
# load-bearing red control to fail. This lane uses Clean proof checking only;
# it does not invoke AY as an SMT oracle.
#
# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Andrew Yates
set -euo pipefail

trust_projection_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
projection_green="$trust_projection_root/proofs/trust-soundness/quantified_projection_certificate.lean"
projection_semantic_red_fragment="$trust_projection_root/proofs/trust-soundness-negative/quantified_projection_accept_without_conclusion.lean"
projection_authority_red_dir="$trust_projection_root/proofs/trust-soundness-negative"
projection_authority_red_controls=(
  "$projection_authority_red_dir/quantified_projection_source_binding_bypass.lean"
  "$projection_authority_red_dir/quantified_projection_query_identity_bypass.lean"
  "$projection_authority_red_dir/quantified_projection_query_feature_bypass.lean"
  "$projection_authority_red_dir/quantified_projection_dispatch_bypass.lean"
  "$projection_authority_red_dir/quantified_projection_missing_semantic_evidence.lean"
  "$projection_authority_red_dir/quantified_projection_literal_true_substitution.lean"
  "$projection_authority_red_dir/quantified_projection_map_shape_bypass.lean"
)
projection_authority_red_failure_counts=(
  14
  16
  4
  3
  3
  1
  2
)
projection_clean_bin="${AY_PROJECTION_CLEAN_BIN:-$trust_projection_root/first-party/clean/cli-runner/target/debug/clean}"

if [[ ! -x "$projection_clean_bin" ]]; then
  echo "BLOCKED: pinned Clean checker is not executable: $projection_clean_bin" >&2
  echo "Build it from this checkout, or set AY_PROJECTION_CLEAN_BIN to a pinned Clean binary." >&2
  echo "  rustup run nightly-2026-06-25 cargo build --manifest-path first-party/clean/cli-runner/Cargo.toml" >&2
  exit 3
fi

projection_tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/ay-projection-proof.XXXXXX")"
trap 'rm -rf -- "$projection_tmp_dir"' EXIT

if ! "$projection_clean_bin" check "$projection_green" \
    >"$projection_tmp_dir/green.out" 2>"$projection_tmp_dir/green.err"; then
  sed -n '1,200p' "$projection_tmp_dir/green.out" >&2
  sed -n '1,200p' "$projection_tmp_dir/green.err" >&2
  echo "FAILED: projection certificate semantic theorem did not kernel-check" >&2
  exit 1
fi

if ! grep -Eq '[[:space:]]0 failed$' "$projection_tmp_dir/green.out"; then
  sed -n '1,200p' "$projection_tmp_dir/green.out" >&2
  echo "FAILED: Clean returned success without an explicit zero-failure summary" >&2
  exit 1
fi

# The semantic control is also a fragment: append it to the exact green model
# so rejection cannot be caused merely by an unknown green declaration.
if [[ ! -f "$projection_semantic_red_fragment" ]]; then
  echo "FAILED: missing projection semantic red control: $projection_semantic_red_fragment" >&2
  exit 1
fi

projection_semantic_red="$projection_tmp_dir/semantic-red.lean"
cp "$projection_green" "$projection_semantic_red"
printf '\n' >>"$projection_semantic_red"
cat "$projection_semantic_red_fragment" >>"$projection_semantic_red"

if "$projection_clean_bin" check --json "$projection_semantic_red" \
    >"$projection_tmp_dir/red.out" 2>"$projection_tmp_dir/red.err"; then
  sed -n '1,200p' "$projection_tmp_dir/red.out" >&2
  echo "FAILED: projection red control unexpectedly kernel-checked" >&2
  exit 1
fi

if ! grep -Eq '"failed_count":[[:space:]]*1' "$projection_tmp_dir/red.out"; then
  sed -n '1,200p' "$projection_tmp_dir/red.out" >&2
  sed -n '1,200p' "$projection_tmp_dir/red.err" >&2
  echo "FAILED: semantic control did not produce exactly one rejection" >&2
  exit 1
fi

if ! grep -Eq '^def accept_without_conclusion_wrong[[:space:]]*:' \
    "$projection_semantic_red_fragment"; then
  echo "FAILED: semantic fragment lost its named red declaration" >&2
  exit 1
fi

if ! grep -Fq '"declaration": "accept_without_conclusion_wrong"' \
    "$projection_tmp_dir/red.out"; then
  sed -n '1,200p' "$projection_tmp_dir/red.out" >&2
  echo "FAILED: semantic JSON did not attribute rejection to the named red declaration" >&2
  exit 1
fi

if grep -Eq 'UnknownIdent|unknown identifier' \
    "$projection_tmp_dir/red.out" "$projection_tmp_dir/red.err"; then
  sed -n '1,200p' "$projection_tmp_dir/red.out" >&2
  sed -n '1,200p' "$projection_tmp_dir/red.err" >&2
  echo "FAILED: semantic control was vacuously rejected by an unknown name" >&2
  exit 1
fi

if ! grep -Eq 'TypeMismatch|KernelCheckFailed|check failed' \
    "$projection_tmp_dir/red.out" "$projection_tmp_dir/red.err"; then
  sed -n '1,200p' "$projection_tmp_dir/red.out" >&2
  sed -n '1,200p' "$projection_tmp_dir/red.err" >&2
  echo "FAILED: red control exited nonzero without a proof-rejection diagnostic" >&2
  exit 1
fi

# The authority controls are fragments so they exercise the exact definitions
# kernel-checked above instead of carrying a second, drift-prone copy of the
# source/query model. Run EACH fragment against a fresh copy of the green model
# and require its own exact failure count. A surplus failure in one fragment
# therefore cannot hide an accidental success in another fragment.
projection_authority_failure_count=0
for projection_control_index in "${!projection_authority_red_controls[@]}"; do
  projection_control="${projection_authority_red_controls[$projection_control_index]}"
  projection_control_failure_count="${projection_authority_red_failure_counts[$projection_control_index]}"
  if [[ ! -f "$projection_control" ]]; then
    echo "FAILED: missing projection authority red control: $projection_control" >&2
    exit 1
  fi

  projection_authority_red="$projection_tmp_dir/authority-red-${projection_control_index}.lean"
  projection_authority_out="$projection_tmp_dir/authority-red-${projection_control_index}.out"
  projection_authority_err="$projection_tmp_dir/authority-red-${projection_control_index}.err"
  cp "$projection_green" "$projection_authority_red"
  printf '\n' >>"$projection_authority_red"
  cat "$projection_control" >>"$projection_authority_red"

  if "$projection_clean_bin" check --json "$projection_authority_red" \
      >"$projection_authority_out" 2>"$projection_authority_err"; then
    sed -n '1,240p' "$projection_authority_out" >&2
    echo "FAILED: authority red fragment unexpectedly kernel-checked: $projection_control" >&2
    exit 1
  fi

  if ! grep -Eq "\"failed_count\":[[:space:]]*${projection_control_failure_count}" \
      "$projection_authority_out"; then
    sed -n '1,240p' "$projection_authority_out" >&2
    sed -n '1,240p' "$projection_authority_err" >&2
    echo "FAILED: authority fragment did not reject exactly ${projection_control_failure_count} declarations: $projection_control" >&2
    exit 1
  fi

  projection_control_named_count=0
  while IFS= read -r projection_control_declaration; do
    projection_control_named_count=$((projection_control_named_count + 1))
    if ! grep -Fq "\"declaration\": \"${projection_control_declaration}\"" \
        "$projection_authority_out"; then
      sed -n '1,240p' "$projection_authority_out" >&2
      echo "FAILED: authority red declaration was not individually rejected: ${projection_control_declaration}" >&2
      exit 1
    fi
  done < <(sed -n 's/^def \([A-Za-z0-9_]*\)[[:space:]]*:.*/\1/p' "$projection_control")

  if [[ "$projection_control_named_count" -ne "$projection_control_failure_count" ]]; then
    echo "FAILED: authority fragment declaration inventory changed: expected ${projection_control_failure_count}, found ${projection_control_named_count}: $projection_control" >&2
    exit 1
  fi

  if grep -Eq 'UnknownIdent|unknown identifier' \
      "$projection_authority_out" "$projection_authority_err"; then
    sed -n '1,240p' "$projection_authority_out" >&2
    sed -n '1,240p' "$projection_authority_err" >&2
    echo "FAILED: authority fragment was vacuously rejected by unknown names: $projection_control" >&2
    exit 1
  fi

  if ! grep -Eq 'TypeMismatch|check failed|KernelCheckFailed' \
      "$projection_authority_out" "$projection_authority_err"; then
    sed -n '1,240p' "$projection_authority_out" >&2
    sed -n '1,240p' "$projection_authority_err" >&2
    echo "FAILED: authority fragment lacked proof-rejection diagnostics: $projection_control" >&2
    exit 1
  fi

  projection_authority_failure_count=$((
    projection_authority_failure_count +
    projection_control_failure_count
  ))
done

sed -n '1,40p' "$projection_tmp_dir/green.out"
echo "RED CONTROL REJECTED: accepting true -> false remains impossible"
echo "AUTHORITY RED CONTROLS REJECTED: ${projection_authority_failure_count}/${projection_authority_failure_count} dependent-evidence bypasses"
