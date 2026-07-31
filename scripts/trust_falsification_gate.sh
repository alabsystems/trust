#!/bin/bash
# Trust falsification self-test (mutation gate).
#
#   proved/*.rs  -> MUST verify (exit 0)
#   mutant/*.rs  -> MUST be rejected by Trust verification (exit 1)
#
# Exit 1 is accepted for a mutant only when stderr contains an explicit Trust
# verification-failure verdict. Argument errors, ordinary Rust errors, crashes,
# timeouts, output-limit failures, and background descendants are tool failures,
# never mutation verdicts.
set -uo pipefail

readonly MAX_TRUSTC_BYTES=$((1024 * 1024 * 1024))
readonly MAX_TIMEOUT_SECS=3600
readonly VERSION_TIMEOUT_SECS=10
readonly MAX_VERSION_STREAM_BYTES=$((64 * 1024))
readonly MAX_VERIFY_STREAM_BYTES=$((64 * 1024 * 1024))
readonly CLEAN_PATH='/usr/bin:/bin:/usr/sbin:/sbin'

TMPDIR_GATE=''
ACTIVE_PROCESS_GROUP=''
RUN_BOUNDED_REASON=''
CAPTURED_TRUSTC_ID=''
CAPTURED_TRUSTC_SHA256=''
CAPTURED_TRUSTC_SIZE=''
CAPTURED_TRUSTC_DIR_ID=''
FIXTURE_VERDICT=''

gate_error() {
  printf 'ERROR: %s\n' "$*" >&2
}

validate_timeout_value() {
  local value=${1-}
  [[ $value =~ ^[1-9][0-9]*$ ]] || return 1
  ((${#value} <= 4 && 10#$value <= MAX_TIMEOUT_SECS))
}

portable_file_size() {
  local path=$1 value platform
  platform=$(uname -s 2>/dev/null) || return 1
  case $platform in
    Darwin) value=$(stat -f '%z' "$path" 2>/dev/null) || return 1 ;;
    Linux) value=$(stat -c '%s' "$path" 2>/dev/null) || return 1 ;;
    *)
      value=$(stat -f '%z' "$path" 2>/dev/null) || value=''
      if [[ ! $value =~ ^[0-9]+$ ]]; then
        value=$(stat -c '%s' "$path" 2>/dev/null) || return 1
      fi
      ;;
  esac
  [[ $value =~ ^[0-9]+$ ]] || return 1
  printf '%s\n' "$value"
}

portable_file_identity() {
  local path=$1 value platform
  # Device, inode, size, mode, uid, gid, mtime, and ctime. SHA-256 is captured
  # separately; ctime makes ordinary same-inode mutation/restore detectable.
  platform=$(uname -s 2>/dev/null) || return 1
  case $platform in
    Darwin) value=$(stat -f '%d:%i:%z:%p:%u:%g:%Fm:%Fc' "$path" 2>/dev/null) || return 1 ;;
    Linux) value=$(stat -c '%d:%i:%s:%f:%u:%g:%y:%z' "$path" 2>/dev/null) || return 1 ;;
    *)
      value=$(stat -f '%d:%i:%z:%p:%u:%g:%Fm:%Fc' "$path" 2>/dev/null) || value=''
      if [[ ! $value =~ ^[0-9]+:[0-9]+:[0-9]+:[0-9A-Fa-f]+:[0-9]+:[0-9]+:.+ ]]; then
        value=$(stat -c '%d:%i:%s:%f:%u:%g:%y:%z' "$path" 2>/dev/null) || return 1
      fi
      ;;
  esac
  [[ $value =~ ^[0-9]+:[0-9]+:[0-9]+:[0-9A-Fa-f]+:[0-9]+:[0-9]+:.+ ]] || return 1
  printf '%s\n' "$value"
}

path_has_no_symlink_components() {
  local path=$1 component current=''
  [[ $path == /* ]] || return 1
  local -a components=()
  IFS='/' read -r -a components <<< "$path"
  for component in "${components[@]}"; do
    [[ -n $component ]] || continue
    current="$current/$component"
    [[ ! -L $current ]] || return 1
  done
}

canonical_existing_path() {
  local path=$1 parent base physical_parent
  [[ $path == /* ]] || return 1
  parent=${path%/*}
  base=${path##*/}
  [[ -n $parent && -n $base ]] || return 1
  physical_parent=$(cd -P "$parent" 2>/dev/null && pwd -P) || return 1
  printf '%s/%s\n' "$physical_parent" "$base"
}

validate_trustc_path() {
  local repo_root=$1 trustc=$2 relative host canonical size
  [[ $trustc == /* ]] || {
    gate_error "TRUSTC must be an absolute canonical path"
    return 1
  }
  relative=${trustc#"$repo_root/build/"}
  [[ $relative != "$trustc" ]] || {
    gate_error "TRUSTC is outside the repository build tree: $trustc"
    return 1
  }
  host=${relative%%/*}
  [[ -n $host && $host != '.' && $host != '..' && $relative == "$host/stage2/bin/trustc" ]] || {
    gate_error "TRUSTC must be exactly $repo_root/build/<host>/stage2/bin/trustc"
    return 1
  }
  path_has_no_symlink_components "$trustc" || {
    gate_error "TRUSTC path contains a symlink component: $trustc"
    return 1
  }
  canonical=$(canonical_existing_path "$trustc") || {
    gate_error "cannot resolve TRUSTC path: $trustc"
    return 1
  }
  [[ $canonical == "$trustc" ]] || {
    gate_error "TRUSTC path is not canonical: $trustc resolves as $canonical"
    return 1
  }
  [[ -f $trustc && ! -L $trustc && -x $trustc ]] || {
    gate_error "TRUSTC is not a non-symlink regular executable: $trustc"
    return 1
  }
  size=$(portable_file_size "$trustc") || {
    gate_error "cannot determine TRUSTC size: $trustc"
    return 1
  }
  ((size > 0 && size <= MAX_TRUSTC_BYTES)) || {
    gate_error "TRUSTC size $size is outside 1..=$MAX_TRUSTC_BYTES bytes"
    return 1
  }
}

bounded_sha256() {
  local path=$1 size=$2 output digest
  ((size >= 0 && size <= MAX_TRUSTC_BYTES)) || return 1
  if command -v shasum >/dev/null 2>&1; then
    output=$(head -c "$size" "$path" | shasum -a 256) || return 1
  elif command -v sha256sum >/dev/null 2>&1; then
    output=$(head -c "$size" "$path" | sha256sum) || return 1
  else
    gate_error 'neither shasum nor sha256sum is available'
    return 1
  fi
  digest=${output%%[[:space:]]*}
  [[ $digest =~ ^[0-9a-f]{64}$ ]] || return 1
  printf '%s\n' "$digest"
}

capture_trustc_snapshot() {
  local trustc=$1 before after dir_before dir_after size digest
  before=$(portable_file_identity "$trustc") || return 1
  dir_before=$(portable_file_identity "${trustc%/*}") || return 1
  size=$(portable_file_size "$trustc") || return 1
  ((size > 0 && size <= MAX_TRUSTC_BYTES)) || return 1
  digest=$(bounded_sha256 "$trustc" "$size") || return 1
  after=$(portable_file_identity "$trustc") || return 1
  dir_after=$(portable_file_identity "${trustc%/*}") || return 1
  [[ $before == "$after" && $dir_before == "$dir_after" ]] || {
    gate_error "TRUSTC or its stage2 bin directory changed while it was hashed"
    return 1
  }
  CAPTURED_TRUSTC_ID=$after
  CAPTURED_TRUSTC_SHA256=$digest
  CAPTURED_TRUSTC_SIZE=$size
  CAPTURED_TRUSTC_DIR_ID=$dir_after
}

file_size_or_zero() {
  local value
  value=$(portable_file_size "$1" 2>/dev/null) || value=0
  printf '%s\n' "$value"
}

terminate_process_group() {
  local pgid=$1 iteration
  [[ $pgid =~ ^[1-9][0-9]*$ ]] || return 1
  kill -TERM -- "-$pgid" 2>/dev/null || true
  for iteration in 1 2 3 4 5 6 7 8 9 10; do
    kill -0 -- "-$pgid" 2>/dev/null || return 0
    sleep 0.05
  done
  kill -KILL -- "-$pgid" 2>/dev/null || true
  return 0
}

run_bounded_process() {
  local timeout=$1 max_stream_bytes=$2 stdout_path=$3 stderr_path=$4
  shift 4
  local pid pgid='' rc=0 started stdout_size stderr_size blocks iteration monitor_was_set=0
  RUN_BOUNDED_REASON=''
  validate_timeout_value "$timeout" || {
    RUN_BOUNDED_REASON='invalid-timeout'
    return 123
  }
  [[ $max_stream_bytes =~ ^[1-9][0-9]*$ ]] || {
    RUN_BOUNDED_REASON='invalid-output-limit'
    return 123
  }
  : > "$stdout_path" || return 123
  : > "$stderr_path" || return 123
  chmod 600 "$stdout_path" "$stderr_path" || return 123
  # `ulimit -f` caps EVERY file the process tree writes, not just the two
  # redirected streams — the stream budget itself is enforced by the explicit
  # size checks below. The kernel backstop therefore gets 8x headroom: the
  # verifier legitimately materializes files larger than one diagnostic stream
  # (solver-snapshot fallbacks on non-APFS volumes, proof-unit bundles), and a
  # 64 MiB backstop killed every fixture with SIGXFSZ the moment the solver
  # binary crossed it. NOTE `ulimit -f` counts 512-BYTE blocks on macOS (and
  # POSIXly everywhere): the old `/1024` divisor silently HALVED the intended
  # budget.
  blocks=$((((max_stream_bytes * 8) + 511) / 512))

  [[ $- == *m* ]] && monitor_was_set=1
  set -m
  (
    ulimit -c 0
    ulimit -f "$blocks" || exit 123
    exec "$@"
  ) >"$stdout_path" 2>"$stderr_path" &
  pid=$!
  ((monitor_was_set == 1)) || set +m

  # Job control gives the background subshell its own process group on both
  # macOS and Linux. Verify that invariant before ever using a negative PID.
  for iteration in 1 2 3 4 5 6 7 8 9 10; do
    if ! kill -0 "$pid" 2>/dev/null; then
      break
    fi
    pgid=$(ps -o pgid= -p "$pid" 2>/dev/null | tr -d '[:space:]')
    [[ -n $pgid ]] && break
    sleep 0.01
  done
  if kill -0 "$pid" 2>/dev/null && [[ $pgid != "$pid" ]]; then
    kill -KILL "$pid" 2>/dev/null || true
    wait "$pid" 2>/dev/null || true
    RUN_BOUNDED_REASON='process-group-setup-failed'
    return 123
  fi

  ACTIVE_PROCESS_GROUP=$pid
  started=$SECONDS
  while kill -0 "$pid" 2>/dev/null; do
    stdout_size=$(file_size_or_zero "$stdout_path")
    stderr_size=$(file_size_or_zero "$stderr_path")
    if ((stdout_size >= max_stream_bytes || stderr_size >= max_stream_bytes)); then
      terminate_process_group "$pid"
      wait "$pid" 2>/dev/null || true
      ACTIVE_PROCESS_GROUP=''
      RUN_BOUNDED_REASON='output-limit'
      return 122
    fi
    if ((SECONDS - started >= timeout)); then
      terminate_process_group "$pid"
      wait "$pid" 2>/dev/null || true
      ACTIVE_PROCESS_GROUP=''
      RUN_BOUNDED_REASON='timeout'
      return 124
    fi
    sleep 0.1
  done
  if wait "$pid" 2>/dev/null; then
    rc=0
  else
    rc=$?
  fi
  ACTIVE_PROCESS_GROUP=''

  stdout_size=$(file_size_or_zero "$stdout_path")
  stderr_size=$(file_size_or_zero "$stderr_path")
  if ((stdout_size >= max_stream_bytes || stderr_size >= max_stream_bytes)); then
    terminate_process_group "$pid"
    RUN_BOUNDED_REASON='output-limit'
    return 122
  fi
  # A direct child that exits while descendants retain the group is a tool
  # protocol violation. Reap the complete group and reject the invocation.
  if kill -0 -- "-$pid" 2>/dev/null; then
    terminate_process_group "$pid"
    RUN_BOUNDED_REASON='background-descendant'
    return 123
  fi
  return "$rc"
}

contains_tool_error() {
  local stderr_path=$1
  LC_ALL=C grep -Eqi \
    'unknown unstable option|unrecognized option|only accepted on the nightly|requires -Z[[:space:]]*unstable-options|is not supported by trust-cg|unsupported by trust-cg|error\[E[0-9]{4}\]|internal compiler error|thread .* panicked|failed to run linker|linking with .* failed|couldn.t read|multiple input filenames|^error: (expected|unexpected|unclosed|mismatched|invalid)' \
    "$stderr_path"
}

# A REFUTATION PROPER: the verifier exhibited a violated obligation. Only these two
# spellings are evidence that the compiler CAUGHT something.
contains_trust_counterexample_verdict() {
  local stderr_path=$1
  LC_ALL=C grep -Eq \
    'Trust verification found [1-9][0-9]* guaranteed Level 0 safety violation|Level 0 summary: [1-9][0-9]* failed' \
    "$stderr_path"
}

# INCOMPLETENESS: the strict/full scope refused the build because some obligation was not
# DISCHARGED — no counterexample, nothing caught. Distinct from a refutation, and the
# distinction is load-bearing (see `classify_verdict`).
contains_trust_incompleteness_verdict() {
  local stderr_path=$1
  LC_ALL=C grep -Eq \
    'Trust (strict|full|memory-safe) verification failed|strict Trust verification requires every Level 0 obligation|obligation\(s\) were not fully verified' \
    "$stderr_path"
}

# Trust (2026-07-30): `refuted` and `incomplete` are DIFFERENT ANSWERS and were previously
# one label. The old `contains_trust_rejection_verdict` matched
# `Trust (strict|full|memory-safe) verification failed` — which is the INCOMPLETENESS header,
# printed whenever an obligation is merely undischarged — so any declined proof read as a
# refutation.
#
# On the `proved/` lane that only mislabelled a failure. On the `mutant/` lane it was a HOLE
# IN THE GATE'S CENTRAL CLAIM: a mutant the verifier never caught, but merely declined to
# discharge, scored PASS and was counted in "N mutants explicitly refuted". The gate could
# report a green mutation score while catching nothing.
#
# Counterexample is checked FIRST because a real refutation prints the header too.
classify_verdict() {
  local rc=$1 stderr_path=$2
  if ((rc == 0)); then
    printf 'proved\n'
    return 0
  fi
  if ((rc == 1)) && ! contains_tool_error "$stderr_path"; then
    if contains_trust_counterexample_verdict "$stderr_path"; then
      printf 'refuted\n'
      return 0
    fi
    if contains_trust_incompleteness_verdict "$stderr_path"; then
      printf 'incomplete\n'
      return 0
    fi
  fi
  printf 'tool-error\n'
  return 0
}

sanitize_parent_environment() {
  PATH=$CLEAN_PATH
  export PATH
  unset LIBRARY_PATH LD_LIBRARY_PATH LD_PRELOAD LD_AUDIT
  unset DYLD_LIBRARY_PATH DYLD_FALLBACK_LIBRARY_PATH DYLD_FRAMEWORK_PATH
  unset DYLD_FALLBACK_FRAMEWORK_PATH DYLD_INSERT_LIBRARIES
  unset CFLAGS CXXFLAGS CPPFLAGS LDFLAGS CPATH C_INCLUDE_PATH CPLUS_INCLUDE_PATH
  unset RUSTFLAGS RUSTDOCFLAGS RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER
  unset CARGO_BUILD_RUSTC_WRAPPER CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER
  unset GIT_DIR GIT_WORK_TREE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_INDEX_FILE
  unset GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_CEILING_DIRECTORIES GIT_DISCOVERY_ACROSS_FILESYSTEM
  unset GIT_CONFIG GIT_CONFIG_GLOBAL GIT_CONFIG_SYSTEM GIT_CONFIG_NOSYSTEM GIT_EXEC_PATH
  unset GIT_SSH GIT_SSH_COMMAND GIT_PROXY_COMMAND
}

gate_git() {
  env -i PATH="$CLEAN_PATH" LC_ALL=C LANG=C HOME=/nonexistent \
    GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null \
    git "$@"
}

git_head_commit() {
  local repo_root=$1 head
  head=$(gate_git -C "$repo_root" rev-parse --verify 'HEAD^{commit}' 2>/dev/null) || return 1
  [[ $head =~ ^[0-9a-f]{40}$ ]] || return 1
  printf '%s\n' "$head"
}

require_clean_checkout() {
  local repo_root=$1 label=$2 status_path=$3
  gate_git -C "$repo_root" status --porcelain=v1 --untracked-files=all --ignore-submodules=none > "$status_path" || {
    gate_error "could not inspect checkout state $label"
    return 1
  }
  if [[ -s $status_path ]]; then
    gate_error "checkout is not clean $label: $(LC_ALL=C sed -n '1p' "$status_path")"
    return 1
  fi
}

resolve_default_trustc() {
  local repo_root=$1 candidate
  candidate="$repo_root/build/host/stage2/bin/trustc"
  # `build/host` is an internal convenience symlink in standard checkouts. It
  # may select the default, but authority is recorded only under the resolved
  # exact build/<triple>/stage2/bin/trustc path. Explicit TRUSTC never receives
  # this exception and is validated literally.
  canonical_existing_path "$candidate"
}

validate_version_commit() {
  local trustc=$1 expected_head=$2 stdout_path=$3 stderr_path=$4 rc commit count
  if run_bounded_process "$VERSION_TIMEOUT_SECS" "$MAX_VERSION_STREAM_BYTES" "$stdout_path" "$stderr_path" \
    env -i PATH="$CLEAN_PATH" HOME="$TMPDIR_GATE/home" TMPDIR="$TMPDIR_GATE/tmp" \
      LC_ALL=C LANG=C TZ=UTC "$trustc" -Vv; then
    rc=0
  else
    rc=$?
  fi
  if ((rc != 0)); then
    gate_error "bounded trustc -Vv probe failed (rc=$rc, reason=${RUN_BOUNDED_REASON:-tool-exit})"
    return 1
  fi
  count=$(LC_ALL=C grep -c '^commit-hash: ' "$stdout_path" 2>/dev/null || true)
  [[ $count == 1 ]] || {
    gate_error "trustc -Vv must contain exactly one commit-hash line"
    return 1
  }
  commit=$(LC_ALL=C sed -n 's/^commit-hash: //p' "$stdout_path")
  [[ $commit =~ ^[0-9a-f]{40}$ ]] || {
    gate_error "trustc commit is not an exact full 40-hex hash: $commit"
    return 1
  }
  [[ $commit == "$expected_head" ]] || {
    gate_error "trustc commit $commit does not match repository HEAD $expected_head"
    return 1
  }
}

verify_fixture() {
  local trustc=$1 fixture=$2 output_stem=$3 timeout=$4
  local stdout_path="$TMPDIR_GATE/$output_stem.stdout" stderr_path="$TMPDIR_GATE/$output_stem.stderr"
  local artifact="$TMPDIR_GATE/work/$output_stem.rmeta" rc
  FIXTURE_VERDICT=''
  if run_bounded_process "$timeout" "$MAX_VERIFY_STREAM_BYTES" "$stdout_path" "$stderr_path" \
    env -i PATH="$CLEAN_PATH" HOME="$TMPDIR_GATE/home" TMPDIR="$TMPDIR_GATE/tmp" \
      LC_ALL=C LANG=C TZ=UTC "$trustc" --edition 2021 --crate-type lib --emit=metadata -Cpanic=abort \
      "$fixture" -o "$artifact"; then
    rc=0
  else
    rc=$?
  fi
  case $rc in
    122)
      FIXTURE_VERDICT='output-limit'
      return 0
      ;;
    123)
      FIXTURE_VERDICT=${RUN_BOUNDED_REASON:-process-error}
      return 0
      ;;
    124)
      FIXTURE_VERDICT='timeout'
      return 0
      ;;
  esac
  FIXTURE_VERDICT=$(classify_verdict "$rc" "$stderr_path")
}

cleanup_gate_temp() {
  if [[ -n ${ACTIVE_PROCESS_GROUP:-} ]]; then
    terminate_process_group "$ACTIVE_PROCESS_GROUP" || true
    ACTIVE_PROCESS_GROUP=''
  fi
  if [[ -n ${TMPDIR_GATE:-} && $TMPDIR_GATE == /tmp/trust-falsification.* && -d $TMPDIR_GATE && ! -L $TMPDIR_GATE ]]; then
    rm -rf -- "$TMPDIR_GATE"
  fi
}

validate_fixture_path() {
  local fixture=$1 expected_dir=$2 canonical
  [[ -f $fixture && ! -L $fixture ]] || return 1
  path_has_no_symlink_components "$fixture" || return 1
  canonical=$(canonical_existing_path "$fixture") || return 1
  [[ $canonical == "$fixture" && ${fixture%/*} == "$expected_dir" ]]
}

main() {
  local script_dir repo_root git_root requested_trustc timeout head_before head_after
  local trustc_id_before trustc_sha_before trustc_size_before trustc_dir_before
  local verdict fixture name failed=0 index=0 proved_count=0 mutant_count=0
  local -a proved_files=() mutant_files=()

  (($# == 0)) || {
    gate_error 'trust_falsification_gate.sh does not accept positional arguments'
    return 2
  }
  requested_trustc=${TRUSTC-}
  timeout=${GATE_VERIFY_TIMEOUT_SECS:-180}
  sanitize_parent_environment

  script_dir=$(cd -P "$(dirname "${BASH_SOURCE[0]}")" && pwd -P) || {
    gate_error 'cannot resolve script directory'
    return 2
  }
  repo_root=$(cd -P "$script_dir/.." && pwd -P) || return 2
  git_root=$(gate_git -C "$repo_root" rev-parse --show-toplevel 2>/dev/null) || {
    gate_error "$repo_root is not a Git checkout"
    return 2
  }
  [[ $git_root == "$repo_root" ]] || {
    gate_error "script repository root $repo_root does not match Git root $git_root"
    return 2
  }
  if [[ -z $requested_trustc ]]; then
    requested_trustc=$(resolve_default_trustc "$repo_root") || {
      gate_error "cannot resolve internal default $repo_root/build/host/stage2/bin/trustc"
      return 2
    }
  fi
  validate_timeout_value "$timeout" || {
    gate_error "GATE_VERIFY_TIMEOUT_SECS must be a canonical positive integer in 1..=$MAX_TIMEOUT_SECS"
    return 2
  }

  umask 077
  TMPDIR_GATE=$(mktemp -d /tmp/trust-falsification.XXXXXXXXXX) || {
    gate_error 'could not create private gate directory'
    return 2
  }
  chmod 700 "$TMPDIR_GATE" || return 2
  [[ -d $TMPDIR_GATE && ! -L $TMPDIR_GATE && -O $TMPDIR_GATE ]] || {
    gate_error "temporary gate directory is not private and caller-owned: $TMPDIR_GATE"
    return 2
  }
  mkdir -m 700 "$TMPDIR_GATE/home" "$TMPDIR_GATE/tmp" "$TMPDIR_GATE/work" || return 2
  trap cleanup_gate_temp EXIT
  trap 'cleanup_gate_temp; exit 130' HUP INT TERM

  require_clean_checkout "$repo_root" 'before falsification' "$TMPDIR_GATE/git-status-before" || return 2
  head_before=$(git_head_commit "$repo_root") || {
    gate_error 'repository HEAD is not an exact full 40-hex commit'
    return 2
  }
  validate_trustc_path "$repo_root" "$requested_trustc" || return 2
  capture_trustc_snapshot "$requested_trustc" || {
    gate_error 'could not capture stable bounded TRUSTC identity'
    return 2
  }
  trustc_id_before=$CAPTURED_TRUSTC_ID
  trustc_sha_before=$CAPTURED_TRUSTC_SHA256
  trustc_size_before=$CAPTURED_TRUSTC_SIZE
  trustc_dir_before=$CAPTURED_TRUSTC_DIR_ID
  validate_version_commit "$requested_trustc" "$head_before" \
    "$TMPDIR_GATE/trustc-version.stdout" "$TMPDIR_GATE/trustc-version.stderr" || return 2

  proved_files=("$repo_root"/tests/trust-falsification/proved/*.rs)
  mutant_files=("$repo_root"/tests/trust-falsification/mutant/*.rs)
  [[ -e ${proved_files[0]} && -e ${mutant_files[0]} ]] || {
    gate_error 'falsification gate requires non-empty proved and mutant fixture lanes'
    return 2
  }

  for fixture in "${proved_files[@]}"; do
    ((proved_count += 1, index += 1))
    name=${fixture##*/}
    if ! validate_fixture_path "$fixture" "$repo_root/tests/trust-falsification/proved"; then
      printf 'FAIL  proved   %s  — invalid or symlinked fixture path\n' "$name"
      failed=1
      continue
    fi
    verify_fixture "$requested_trustc" "$fixture" "proved-$index" "$timeout"
    verdict=$FIXTURE_VERDICT
    if [[ $verdict == proved ]]; then
      printf 'PASS  proved   %s  — verified\n' "$name"
    else
      printf 'FAIL  proved   %s  — non-proof result: %s\n' "$name" "$verdict"
      failed=1
    fi
  done

  for fixture in "${mutant_files[@]}"; do
    ((mutant_count += 1, index += 1))
    name=${fixture##*/}
    if ! validate_fixture_path "$fixture" "$repo_root/tests/trust-falsification/mutant"; then
      printf 'FAIL  mutant   %s  — invalid or symlinked fixture path\n' "$name"
      failed=1
      continue
    fi
    verify_fixture "$requested_trustc" "$fixture" "mutant-$index" "$timeout"
    verdict=$FIXTURE_VERDICT
    case $verdict in
      refuted)
        printf 'PASS  mutant   %s  — rejected by an explicit Trust verification verdict\n' "$name"
        ;;
      incomplete)
        # NOT a pass. The verifier declined to discharge the obligation; it did not catch
        # the mutation. Counting this as a refutation is how a gate reports a mutation score
        # it has not earned.
        printf 'FAIL  mutant   %s  — UNCAUGHT MUTANT: verification was incomplete, not refuting\n' "$name"
        failed=1
        ;;
      proved)
        printf 'FAIL  mutant   %s  — SURVIVING MUTANT: verified when it must fail\n' "$name"
        failed=1
        ;;
      *)
        printf 'FAIL  mutant   %s  — non-verdict tool result: %s\n' "$name" "$verdict"
        failed=1
        ;;
    esac
  done

  head_after=$(git_head_commit "$repo_root") || head_after='invalid'
  [[ $head_after == "$head_before" ]] || {
    gate_error "repository HEAD changed during gate: $head_before -> $head_after"
    failed=1
  }
  require_clean_checkout "$repo_root" 'after falsification' "$TMPDIR_GATE/git-status-after" || failed=1
  if capture_trustc_snapshot "$requested_trustc"; then
    [[ $CAPTURED_TRUSTC_ID == "$trustc_id_before" \
      && $CAPTURED_TRUSTC_SHA256 == "$trustc_sha_before" \
      && $CAPTURED_TRUSTC_SIZE == "$trustc_size_before" \
      && $CAPTURED_TRUSTC_DIR_ID == "$trustc_dir_before" ]] || {
      gate_error 'TRUSTC identity, bytes, size, or stage2 bin directory changed during gate'
      failed=1
    }
  else
    gate_error 'could not revalidate TRUSTC after gate'
    failed=1
  fi

  if ((failed == 0)); then
    printf 'FALSIFICATION GATE: GREEN — %d proofs verified and %d mutants explicitly refuted\n' \
      "$proved_count" "$mutant_count"
    return 0
  fi
  printf 'FALSIFICATION GATE: RED — proof, mutation, authority, or tool-integrity failure\n'
  return 1
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then
  main "$@"
fi
