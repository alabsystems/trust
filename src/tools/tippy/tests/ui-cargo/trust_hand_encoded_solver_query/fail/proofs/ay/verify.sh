#!/usr/bin/env bash
# Re-checkable certificate for keep_tail_chars. Discharged by `ay` on
# hand-encoded SMT-LIB2. Run: `bash verify.sh`.
set -u
AY=""
for c in "$HOME/.cargo/bin/ay" "$(command -v ay 2>/dev/null || true)"; do
  if [ -n "$c" ] && [ -x "$c" ]; then AY="$c"; break; fi
done
[ -n "$AY" ] || { echo "FAIL: no runnable ay found" >&2; exit 1; }
cd "$(dirname "$0")"
rc=0
check() {
  local got
  got="$("$AY" "$1.smt2" 2>/dev/null | grep -Ex 'sat|unsat|unknown' | tail -1)"
  [ "$got" = "$2" ] || { echo "FAIL $1 => got '$got', want '$2'"; rc=1; }
}
check kt1_clamp_bound unsat
check kt2_clamp_monotone unsat
check kt_c1_cap_active_sat sat
[ "$rc" -eq 0 ] && echo "ALL PROOFS DISCHARGED"
exit "$rc"
