#!/usr/bin/env bash
# Trust superiority self-test (advisory-lane static-discharge gate).
#
# The falsification gate proves the verifier is USEFUL (every PROVED obligation
# has a mutant that flips to FAILED under batteries-on strict verification). THIS gate proves
# the verifier is SUPERIOR *and* sound in the advisory daily-driver mode (`-Z trust-policy=advisory`):
# for SAFE code Trust statically PROVES safety obligations that stock
# rustc compiles with a *retained* runtime check, ELIMINATING them; for the
# UNSAFE mutant it does NOT eliminate the check (so the bug is still caught at
# runtime — proving the elimination is non-vacuous, not "prove everything").
#
#   superiority/proved/*.rs  -> advisory mode FULLY proved: 0 failed, 0 unknown,
#                               0 timed-out, 0 runtime-checked, >=1 proved
#                               (every check statically discharged = superior).
#   superiority/mutant/*.rs  -> advisory mode NOT fully proved: at least one
#                               obligation failed / unknown / runtime-checked
#                               (the unsafe access is retained, not eliminated).
#
# REQUIRES an executable `ay` SMT solver (AY_PATH or the trustc sibling);
# advisory mode dispatches symbolic obligations to it. `./x.py build` does NOT
# build/place ay, so this script builds it when missing and passes its exact path
# through AY_PATH. Without ay the daily driver has no SMT backend
# and silently runtime-checks everything — the very regression this gate catches.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"
TARGO="${TARGO:-$(dirname "$TRUSTC")/targo}"
AY_BIN="${AY_PATH:-$(dirname "$TRUSTC")/ay}"
FIXTURES="$REPO_ROOT/tests/trust-falsification/superiority"
# The shims dir must EXIST: a missing LIBRARY_PATH entry makes ld warn
# "search path not found", which leaks into diagnostics-sensitive tests.
mkdir -p /tmp/trust_link_shims
export LIBRARY_PATH="/tmp/trust_link_shims:/opt/homebrew/opt/z3/lib:${LIBRARY_PATH:-}"

if [ ! -x "$TRUSTC" ]; then
  echo "ERROR: trustc not found at $TRUSTC (build it: ./x.py build --stage 2 compiler/rustc library/std)"
  exit 2
fi

# Ensure the ay SMT solver is available. Build a debug solver through canonical
# Targo if absent; AY_PATH keeps this gate from mutating the stage2 sysroot.
if [ ! -x "$AY_BIN" ]; then
  echo "INFO: ay solver not available at $AY_BIN — building it (one-time, debug)…"
  if [ -x "$TARGO" ] \
     && ( cd "$REPO_ROOT/first-party/ay" && "$TARGO" --unverified build -p ay --features cli >/dev/null 2>&1 ) \
     && [ -x "$REPO_ROOT/first-party/ay/target/debug/ay" ]; then
    AY_BIN="$REPO_ROOT/first-party/ay/target/debug/ay"
    echo "INFO: using ay at $AY_BIN"
  else
    echo "ERROR: could not build the ay solver through canonical Targo; advisory mode has no SMT backend."
    exit 2
  fi
fi
export AY_PATH="$AY_BIN"

TMPDIR_GATE="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_GATE"' EXIT

# Advisory verify -> echo "proved failed unknown timed runtime rc" (or empty
# when the compile printed NO verification headline at all).
#
# Hardened (2026-07-02, the rev_range_index_bound escape): the old body read only
# the FIRST headline and NEVER checked the compiler's exit status. Two blind
# spots, both observed in the wild:
#   * a multi-function fixture emits one headline PER function — a later
#     function's failure was invisible behind the first function's clean line;
#   * a fixture whose headline is clean can STILL hard-error the build (the
#     strict native-evidence lane: "native typed-TrustIr lowering did not
#     complete" printed `1 proved, 0 failed` and then `error:` + rc=1) — the
#     gate reported it SUPERIOR while the compile was REJECTED.
# Now every headline is summed column-wise and the compiler rc is appended;
# the proved/ judgment requires rc == 0 on top of the clean counts.
counts_of() {
  local out rc
  out="$("$TRUSTC" --edition 2021 --crate-type lib -Z trust-policy=advisory "$1" \
      -o "$TMPDIR_GATE/$(basename "$1").rlib" 2>&1)"
  rc=$?
  printf '%s\n' "$out" \
    | sed -n 's/.*Trust verification: \([0-9]*\) proved, \([0-9]*\) failed, \([0-9]*\) unknown, \([0-9]*\) timed out, \([0-9]*\) runtime-checked.*/\1 \2 \3 \4 \5/p' \
    | awk -v rc="$rc" 'NF == 5 { p += $1; f += $2; u += $3; t += $4; r += $5; n++ }
                       END { if (n > 0) print p, f, u, t, r, rc }'
}

failed=0

# Warm EVERY proved fixture once (discard results). A debug-build ay against the
# deliberately-low per-VC timeout can exceed it on the FIRST (cold) query —
# binary not yet in the OS page cache, solver state cold — and spuriously leave
# an obligation runtime-checked. Warming every fixture (not just the first, which
# may be interval-discharged and never spawn ay) absorbs the cold start so the
# measured runs reflect steady-state capability, not first-spawn latency.
for w in "$FIXTURES"/proved/*.rs; do
  [ -e "$w" ] || continue
  counts_of "$w" >/dev/null 2>&1
done

for f in "$FIXTURES"/proved/*.rs; do
  [ -e "$f" ] || continue
  # Retry once on a non-superior result: a real regression fails BOTH attempts
  # (so it is still caught), while a cold-start solver timeout clears on the warm
  # retry. This never masks a genuine loss of superiority.
  superior=0; proved=0; fl=0; unk=0; tmo=0; rtc=0; rc=0
  for _ in 1 2; do
    c="$(counts_of "$f")"
    [ -z "$c" ] && continue
    read -r proved fl unk tmo rtc rc <<<"$c"
    # Hardened: a clean headline with a NONZERO compiler rc (a hard error after
    # the report — e.g. an incomplete native lowering) is NOT superior.
    if [ "$fl" -eq 0 ] && [ "$unk" -eq 0 ] && [ "$tmo" -eq 0 ] && [ "$rtc" -eq 0 ] && [ "$proved" -ge 1 ] && [ "$rc" -eq 0 ]; then
      superior=1; break
    fi
  done
  if [ -z "$c" ]; then
    echo "FAIL  proved   $(basename "$f")  — no verification summary (compile error?)"; failed=1; continue
  fi
  if [ "$superior" -eq 1 ]; then
    echo "PASS  proved   $(basename "$f")  — SUPERIOR: $proved proved, 0 runtime-checked (all checks eliminated)"
  else
    echo "FAIL  proved   $(basename "$f")  — NOT superior: $proved proved / $fl failed / $unk unknown / $tmo timed / $rtc runtime-checked / rc=$rc"
    failed=1
  fi
done

for f in "$FIXTURES"/mutant/*.rs; do
  [ -e "$f" ] || continue
  c="$(counts_of "$f")"
  if [ -z "$c" ]; then
    echo "FAIL  mutant   $(basename "$f")  — no verification summary (compile error?)"; failed=1; continue
  fi
  read -r proved fl unk tmo rtc rc <<<"$c"
  # Sound iff the unsafe access was NOT statically discharged: something must
  # remain failed/unknown/runtime-checked (the runtime check is retained).
  # (`rc` is not consulted here: fail-closed strict mode makes an undischarged
  # mutant a build error, but the retained-check COUNTS are the judgment.)
  if [ "$fl" -gt 0 ] || [ "$unk" -gt 0 ] || [ "$tmo" -gt 0 ] || [ "$rtc" -gt 0 ]; then
    echo "PASS  mutant   $(basename "$f")  — sound: not fully discharged ($fl failed / $unk unknown / $rtc runtime-checked)"
  else
    echo "FAIL  mutant   $(basename "$f")  — VACUOUS PROOF: unsafe access statically eliminated ($proved proved, 0 retained)"
    failed=1
  fi
done

if [ "$failed" -eq 0 ]; then
  echo "SUPERIORITY GATE: GREEN — safe code is statically discharged (superior to rustc), unsafe code is not (sound)"
  exit 0
else
  echo "SUPERIORITY GATE: RED — lost superiority (safe code regressed) or vacuous proof (unsafe code eliminated)"
  exit 1
fi
