#!/bin/bash
set -euo pipefail

REPO_ROOT=$(cd -P "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
# shellcheck source=../trust_falsification_gate.sh
source "$REPO_ROOT/scripts/trust_falsification_gate.sh"

TEST_ROOT=$(mktemp -d /tmp/trust-falsification-test.XXXXXXXXXX)
TEST_ROOT=$(cd -P "$TEST_ROOT" && pwd -P)
cleanup() {
  if [[ -n ${ACTIVE_PROCESS_GROUP:-} ]]; then
    terminate_process_group "$ACTIVE_PROCESS_GROUP" || true
  fi
  rm -rf -- "$TEST_ROOT"
}
trap cleanup EXIT HUP INT TERM

fail() {
  printf 'FAIL: %s\n' "$*" >&2
  exit 1
}

assert_eq() {
  [[ $1 == "$2" ]] || fail "expected [$2], got [$1]"
}

for valid in 1 9 180 3600; do
  validate_timeout_value "$valid" || fail "valid timeout rejected: $valid"
done
for invalid in '' 0 00 01 -1 1.0 12x 3601 99999; do
  if validate_timeout_value "$invalid"; then
    fail "invalid timeout accepted: [$invalid]"
  fi
done

mkdir -p "$TEST_ROOT/repo/build/test-host/stage2/bin"
FAKE_TRUSTC="$TEST_ROOT/repo/build/test-host/stage2/bin/trustc"
printf '#!/bin/sh\nexit 0\n' > "$FAKE_TRUSTC"
chmod 700 "$FAKE_TRUSTC"
validate_trustc_path "$TEST_ROOT/repo" "$FAKE_TRUSTC" || fail 'canonical stage2 trustc rejected'
ln -s test-host "$TEST_ROOT/repo/build/host"
assert_eq "$(resolve_default_trustc "$TEST_ROOT/repo")" "$FAKE_TRUSTC"
if validate_trustc_path "$TEST_ROOT/repo" "$TEST_ROOT/repo/build/host/stage2/bin/trustc" 2>/dev/null; then
  fail 'explicit TRUSTC path through build/host symlink was accepted'
fi

ln -s "$FAKE_TRUSTC" "$TEST_ROOT/repo/build/test-host/stage2/bin/trustc-link"
if path_has_no_symlink_components "$TEST_ROOT/repo/build/test-host/stage2/bin/trustc-link"; then
  fail 'symlink path component accepted'
fi
if validate_trustc_path "$TEST_ROOT/repo" "$TEST_ROOT/repo/build/test-host/stage2/bin/trustc-link" 2>/dev/null; then
  fail 'non-exact/symlink trustc path accepted'
fi

OVERSIZED="$TEST_ROOT/repo/build/oversized/stage2/bin/trustc"
mkdir -p "${OVERSIZED%/*}"
: > "$OVERSIZED"
chmod 700 "$OVERSIZED"
if command -v truncate >/dev/null 2>&1; then
  truncate -s $((MAX_TRUSTC_BYTES + 1)) "$OVERSIZED"
else
  dd if=/dev/zero of="$OVERSIZED" bs=1 count=0 seek=$((MAX_TRUSTC_BYTES + 1)) 2>/dev/null
fi
if validate_trustc_path "$TEST_ROOT/repo" "$OVERSIZED" 2>/dev/null; then
  fail 'oversized trustc accepted'
fi

capture_trustc_snapshot "$FAKE_TRUSTC" || fail 'stable trustc snapshot failed'
FIRST_SHA=$CAPTURED_TRUSTC_SHA256
printf '#!/bin/sh\nexit 1\n' > "$FAKE_TRUSTC"
chmod 700 "$FAKE_TRUSTC"
capture_trustc_snapshot "$FAKE_TRUSTC" || fail 'modified trustc snapshot failed'
[[ $CAPTURED_TRUSTC_SHA256 != "$FIRST_SHA" ]] || fail 'trustc byte mutation did not change SHA-256'

VERDICT_STDERR="$TEST_ROOT/verdict.stderr"
printf 'error: Trust verification found 1 guaranteed Level 0 safety violation(s) in `f`\n' > "$VERDICT_STDERR"
assert_eq "$(classify_verdict 1 "$VERDICT_STDERR")" refuted
printf 'error[E0308]: mismatched types\nTrust strict verification failed for `f`\n' > "$VERDICT_STDERR"
assert_eq "$(classify_verdict 1 "$VERDICT_STDERR")" tool-error
printf 'error: unrecognized option `bogus`\n' > "$VERDICT_STDERR"
assert_eq "$(classify_verdict 1 "$VERDICT_STDERR")" tool-error
printf 'error: panic=unwind is not supported by trust-cg\n' > "$VERDICT_STDERR"
assert_eq "$(classify_verdict 1 "$VERDICT_STDERR")" tool-error
assert_eq "$(classify_verdict 2 "$VERDICT_STDERR")" tool-error
assert_eq "$(classify_verdict 134 "$VERDICT_STDERR")" tool-error
assert_eq "$(classify_verdict 0 "$VERDICT_STDERR")" proved

set +e
"$REPO_ROOT/scripts/trust_falsification_gate.sh" --unexpected >"$TEST_ROOT/args.stdout" 2>"$TEST_ROOT/args.stderr"
ARGS_RC=$?
set -e
assert_eq "$ARGS_RC" 2
grep -q 'does not accept positional arguments' "$TEST_ROOT/args.stderr" || fail 'unexpected argument error missing'

export GIT_DIR="$TEST_ROOT/forged-git-dir"
export GIT_WORK_TREE="$TEST_ROOT/forged-work-tree"
GIT_HEAD=$(git_head_commit "$REPO_ROOT") || fail 'sanitized Git authority probe failed'
[[ $GIT_HEAD =~ ^[0-9a-f]{40}$ ]] || fail 'sanitized Git authority returned a noncanonical HEAD'
unset GIT_DIR GIT_WORK_TREE

TMPDIR_GATE="$TEST_ROOT/gate"
mkdir -m 700 "$TMPDIR_GATE" "$TMPDIR_GATE/home" "$TMPDIR_GATE/tmp" "$TMPDIR_GATE/work"

PIDFILE="$TEST_ROOT/descendant.pid"
set +e
run_bounded_process 1 65536 "$TEST_ROOT/timeout.stdout" "$TEST_ROOT/timeout.stderr" \
  /bin/bash -c 'sleep 30 & child=$!; printf "%s\n" "$child" > "$1"; wait "$child"' bash "$PIDFILE"
TIMEOUT_RC=$?
set -e
assert_eq "$TIMEOUT_RC" 124
assert_eq "$RUN_BOUNDED_REASON" timeout
[[ -s $PIDFILE ]] || fail 'timeout fixture did not record descendant PID'
DESCENDANT_PID=$(sed -n '1p' "$PIDFILE")
for _ in 1 2 3 4 5 6 7 8 9 10; do
  kill -0 "$DESCENDANT_PID" 2>/dev/null || break
  sleep 0.1
done
if kill -0 "$DESCENDANT_PID" 2>/dev/null; then
  fail "timeout left descendant process alive: $DESCENDANT_PID"
fi

set +e
run_bounded_process 5 4096 "$TEST_ROOT/flood.stdout" "$TEST_ROOT/flood.stderr" \
  /bin/sh -c 'while :; do printf "0123456789abcdef0123456789abcdef\n" >&2; done'
FLOOD_RC=$?
set -e
assert_eq "$FLOOD_RC" 122
assert_eq "$RUN_BOUNDED_REASON" output-limit

FAKE_DRIVER="$TEST_ROOT/fake-trustc"
cat > "$FAKE_DRIVER" <<'FAKE'
#!/bin/sh
if [ "${LIBRARY_PATH+x}${LD_LIBRARY_PATH+x}${LD_PRELOAD+x}${DYLD_INSERT_LIBRARIES+x}" != "" ]; then
  echo 'ambient injection variable survived' >&2
  exit 2
fi
fixture=
for arg do
  case "$arg" in *.rs) fixture=$arg ;; esac
done
case "$fixture" in
  *proved.rs) exit 0 ;;
  *mutant.rs)
    echo 'error: Trust verification found 1 guaranteed Level 0 safety violation(s) in `mutant`' >&2
    exit 1
    ;;
  *tool.rs)
    echo 'error: unrecognized option `forged`' >&2
    exit 1
    ;;
  *crash.rs) exit 134 ;;
  *) exit 2 ;;
esac
FAKE
chmod 700 "$FAKE_DRIVER"
for fixture in proved.rs mutant.rs tool.rs crash.rs; do
  : > "$TEST_ROOT/$fixture"
done
export LIBRARY_PATH=/tmp/trust_link_shims
export LD_LIBRARY_PATH=/attacker
export DYLD_INSERT_LIBRARIES=/attacker/inject.dylib

verify_fixture "$FAKE_DRIVER" "$TEST_ROOT/proved.rs" fake-proved 5
assert_eq "$FIXTURE_VERDICT" proved
verify_fixture "$FAKE_DRIVER" "$TEST_ROOT/mutant.rs" fake-mutant 5
assert_eq "$FIXTURE_VERDICT" refuted
verify_fixture "$FAKE_DRIVER" "$TEST_ROOT/tool.rs" fake-tool 5
assert_eq "$FIXTURE_VERDICT" tool-error
verify_fixture "$FAKE_DRIVER" "$TEST_ROOT/crash.rs" fake-crash 5
assert_eq "$FIXTURE_VERDICT" tool-error

printf 'PASS: trust falsification gate helper tests\n'
