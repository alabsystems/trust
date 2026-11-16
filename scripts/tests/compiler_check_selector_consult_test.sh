#!/usr/bin/env bash
# scoped.compiler-check consults the landing gate's selector (2026-10-14):
# scripts/check_compiler_targets_build.sh skips `x.py check` only when
# `scripts/land_gate.py needs compiler-check` answers "no" (exit 1) for EVERY
# range it judges. Any "yes" (0), any "cannot tell" (2, or anything else), a
# missing selector, or a range it cannot split runs the check, as before.
#
# The fixture is a throwaway repository holding a copy of the lane, a stub
# selector whose answer the test sets (STUB_RC, or STUB_RC_<n> for the n-th
# call), and a stub x.py that records that it ran. Each case changes an
# in-scope path (crates/leaf/src/lib.rs) so IN_SCOPE_RE alone would run x.py.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LANE="$REPO_ROOT/scripts/check_compiler_targets_build.sh"
# Each fixture owns its scheduling environment, independent of the suite's
# outer machine admission. Managed cases below provide their own share.
unset TRUST_PUSHED_REFS BUILD_SLOT_HELD CARGO_BUILD_JOBS
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE

TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "${TMP:?}"' EXIT
FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }

make_repo() {  # make_repo <dir> <with-selector: 1|0>
  local d="$1"
  mkdir -p "$d/scripts" "$d/crates/leaf/src"
  cp "$LANE" "$d/scripts/check_compiler_targets_build.sh"
  cat > "$d/x.py" <<'EOF'
import os, sys
open(os.environ["XPY_MARK"], "w").write(" ".join(sys.argv[1:]))
EOF
  if [ "$2" = 1 ]; then
    cat > "$d/scripts/land_gate.py" <<'EOF'
import os, sys
n = int(open(os.environ["STUB_COUNT"]).read() or 0) + 1 if os.path.exists(os.environ["STUB_COUNT"]) else 1
open(os.environ["STUB_COUNT"], "w").write(str(n))
rc = int(os.environ.get(f"STUB_RC_{n}", os.environ.get("STUB_RC", "2")))
print(f"stub selector call {n}: {sys.argv[1:]} -> {rc}")
sys.exit(rc)
EOF
  fi
  echo "pub fn a() {}" > "$d/crates/leaf/src/lib.rs"
  git -C "$d" init -q -b main && git -C "$d" add -A && git -C "$d" commit -qm base
  git -C "$d" branch base
  echo "pub fn b() {}" >> "$d/crates/leaf/src/lib.rs"
  git -C "$d" commit -qam change
}

run_case() {  # run_case <label> <want: ran|skipped> [env...]
  local label="$1" want="$2"; shift 2
  rm -f "$TMP/xpy" "$TMP/count"
  OUT="$(cd "$D" && env XPY_MARK="$TMP/xpy" STUB_COUNT="$TMP/count" "$@" bash scripts/check_compiler_targets_build.sh base 2>&1)"
  RUN_RC=$?
  local ran=skipped
  [ -f "$TMP/xpy" ] && ran=ran
  if [ "$ran" = "$want" ]; then pass "$label"; else
    fail "$label: x.py $ran, wanted $want"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -15
  fi
}

D="$TMP/with"; make_repo "$D" 1
run_case "the selector says no: SKIPPED, x.py not run" skipped STUB_RC=1
grep -q '^SKIPPED: no required full compiler-check for these ranges' <<<"$OUT" \
  && pass "and the skip says why" || fail "no SKIPPED line: $OUT"
grep -q -- "--development" <<<"$OUT" \
  && pass "and the real caller requests the declared development scope" || fail "missing development policy consultation: $OUT"
grep -q 'Diagnostic SKIP is not compiler-check PASS' <<<"$OUT" \
  && pass "and the diagnostic skip grants no compiler-check pass" || fail "missing diagnostic scope: $OUT"
run_case "the selector says yes: x.py runs" ran STUB_RC=0
run_case "the selector cannot tell (2): x.py runs" ran STUB_RC=2
run_case "the selector crashes (any other code): x.py runs" ran STUB_RC=7

# The actual supported execution components live under src/. They must reach
# the development consultation before the historical generic src fallback.
D="$TMP/src"; make_repo "$D" 1
mkdir -p "$D/src/tools/compiletest/src"
printf '%s\n' 'fn actual_src_case() {}' > "$D/src/tools/compiletest/src/lib.rs"
git -C "$D" add src
git -C "$D" commit -qm src-change
run_case "supported src component consults development before broad fallback" skipped STUB_RC=1
grep -q -- '--development' <<<"$OUT" && pass "actual src caller asked development policy" || fail "src consultation was bypassed"
run_case "unknown/refused src scope keeps full fallback" ran STUB_RC=2
D="$TMP/with"

# Two ranges (a pushed update and a new branch): every one must say no.
HEAD_SHA="$(git -C "$D" rev-parse HEAD)"; BASE_SHA="$(git -C "$D" rev-parse base)"
REFS="refs/heads/main $HEAD_SHA refs/heads/main $BASE_SHA"$'\n'"refs/heads/topic $HEAD_SHA refs/heads/topic 0000000000000000000000000000000000000000"
git -C "$D" update-ref refs/remotes/origin/main "$BASE_SHA"
run2() {  # run2 <label> <want> [env...]
  local label="$1" want="$2"; shift 2
  rm -f "$TMP/xpy" "$TMP/count"
  OUT="$(cd "$D" && env XPY_MARK="$TMP/xpy" STUB_COUNT="$TMP/count" TRUST_PUSHED_REFS="$REFS" "$@" \
    bash scripts/check_compiler_targets_build.sh 2>&1)"
  RUN_RC=$?
  local ran=skipped
  [ -f "$TMP/xpy" ] && ran=ran
  if [ "$ran" = "$want" ]; then pass "$label"; else
    fail "$label: x.py $ran, wanted $want"; printf '%s\n' "$OUT" | sed 's/^/        /' | tail -15
  fi
}
run2 "two ranges, both no: SKIPPED" skipped STUB_RC=1
run2 "two ranges, the second says yes: x.py runs" ran STUB_RC_1=1 STUB_RC_2=0
run2 "two ranges, the first says yes: x.py runs" ran STUB_RC_1=0 STUB_RC_2=1

D="$TMP/without"; make_repo "$D" 0
run_case "no selector in the tree: x.py runs, as before" ran

run_case "unmanaged x.py keeps its ordinary arguments" ran CARGO_BUILD_JOBS=99
[ "$(cat "$TMP/xpy")" = 'check --stage 1' ] \
  && pass "unmanaged invocation is unchanged" || fail "unmanaged arguments changed"
run_case "managed x.py receives explicit admitted -j" ran BUILD_SLOT_HELD=1 CARGO_BUILD_JOBS=6
[ "$RUN_RC" -eq 0 ] && [ "$(cat "$TMP/xpy")" = 'check --stage 1 -j 6' ] \
  && pass "x.py consumes exactly the six admitted jobs" || fail "admitted share not forwarded"
for share in '' 0 -1 six 1.5; do
  run_case "invalid managed share prevents x.py ($share)" skipped BUILD_SLOT_HELD=1 CARGO_BUILD_JOBS="$share"
  [ "$RUN_RC" -eq 2 ] && grep -q 'nothing was judged' <<<"$OUT" \
    && pass "invalid managed share reports NOT JUDGED" || fail "invalid share did not refuse explicitly"
done

if [ "$FAILED" -ne 0 ]; then echo "compiler-check selector consult tests: FAILED"; exit 1; fi
echo "compiler-check selector consult tests: all passed"
