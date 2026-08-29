#!/usr/bin/env bash
# Planted-violation proof for scripts/trust_self_verify.sh's fail-closed exits.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# The lane shipped an `exit 0` for "no stage2 trustc found". A self-verification
# gate that reports SUCCESS when its subject is ABSENT is the fail-open shape the
# whole hardening effort exists to catch, and it is invisible to any caller that
# only reads the exit code. Every refusal below is therefore planted and watched
# to fail; the exit-0 case is planted too, so a gate stuck at nonzero cannot pass
# this file by accident.
#
# The compiler is stubbed because a FALSE PROOF cannot be planted with an honest
# one. The subject under test is the real gate script driven through its real
# CLI — no reimplementation of its logic here. The real-stage2-trustc run is the
# `release.self-verify-oracle` manifest row.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GATE="$REPO_ROOT/scripts/trust_self_verify.sh"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
fails=0

expect_rc() {  # expect_rc <label> <want-rc> <cmd...>
  local label="$1" want="$2"; shift 2
  local out rc
  out="$("$@" 2>&1)"; rc=$?
  if [ "$rc" -eq "$want" ]; then
    echo "  ok   $label (exit $rc)"
  else
    echo "  FAIL $label: exit $rc, want $want"
    printf '%s\n' "$out" | sed 's/^/       | /'
    fails=$((fails + 1))
  fi
}

expect_says() {  # expect_says <label> <regex> <cmd...>
  local label="$1" re="$2"; shift 2
  local out
  out="$("$@" 2>&1)"   # captured, not piped: `cmd | grep -q` + pipefail reports the producer's SIGPIPE
  if printf '%s\n' "$out" | grep -qE "$re"; then echo "  ok   $label"
  else
    echo "  FAIL $label: output never matched /$re/"
    printf '%s\n' "$out" | sed 's/^/       | /'
    fails=$((fails + 1))
  fi
}

# ---- stub compilers -------------------------------------------------------
# `trustc` is invoked as: TRUSTC --edition 2021 --crate-type lib \
#   -Z trust-verify-output=json <sample>.rs -o <out>.rlib
mk_stub() { printf '%s\n' "$2" > "$TMP/$1"; chmod +x "$TMP/$1"; }

mk_stub silent '#!/bin/sh
exit 0'                                   # compiles clean, emits nothing

mk_stub inert '#!/bin/sh
echo "TRUST_JSON:{\"type\":\"function_result\",\"results\":[{\"kind\":\"unreach\",\"outcome\":\"proved\"}]}"
exit 0'                                   # obligations, but never a graded kind

mk_stub lying '#!/bin/sh
echo "TRUST_JSON:{\"type\":\"function_result\",\"results\":[{\"kind\":\"bounds\",\"outcome\":\"proved\"},{\"kind\":\"overflow:add\",\"outcome\":\"proved\"},{\"kind\":\"divzero\",\"outcome\":\"proved\"}]}"
exit 0'                                   # proves every reachable panic

mk_stub honest '#!/bin/sh
for a in "$@"; do case "$a" in *.rs) n="${a##*/}"; n="${n%.rs}";; esac; done
case "$n" in *_unguarded|index_off_by_one) oc=failed ;; *) oc=proved ;; esac
echo "TRUST_JSON:{\"type\":\"function_result\",\"results\":[{\"kind\":\"bounds\",\"outcome\":\"$oc\"},{\"kind\":\"overflow:add\",\"outcome\":\"$oc\"},{\"kind\":\"divzero\",\"outcome\":\"$oc\"}]}"
exit 0'                                   # refutes exactly the unsafe samples

mkdir -p "$TMP/adir"
: > "$TMP/notexec"; chmod 644 "$TMP/notexec"

sc() { echo "SCORECARD=$TMP/sc-$1.md"; }

echo "=== absence of the subject must never be exit 0 ==="
expect_rc "explicit TRUSTC that does not exist" 2 \
  env TRUSTC="$TMP/no/such/trustc" SCORECARD="$TMP/sc1.md" bash "$GATE"
expect_rc "TRUSTC is a directory ([ -x ] alone says yes)" 2 \
  env TRUSTC="$TMP/adir" SCORECARD="$TMP/sc2.md" bash "$GATE"
expect_rc "TRUSTC exists but is not executable" 2 \
  env TRUSTC="$TMP/notexec" SCORECARD="$TMP/sc3.md" bash "$GATE"

# The message must name what was looked for and where, or the exit code is the
# only diagnostic and the next reader rebuilds the wrong thing.
expect_says "refusal names the path it looked at" "$TMP/no/such/trustc" \
  env TRUSTC="$TMP/no/such/trustc" SCORECARD="$TMP/sc4.md" bash "$GATE"
expect_says "refusal says it is not a skip" "NOT a skip|no compiler present" \
  env TRUSTC="$TMP/no/such/trustc" SCORECARD="$TMP/sc5.md" bash "$GATE"

# An explicitly named compiler must be honoured or refused, never silently
# swapped: the release lane names build/host/stage2/bin/trustc, and a fallback
# would measure a different compiler and still report success.
expect_says "explicit TRUSTC is not replaced by a fallback" "set explicitly, so no fallback" \
  env TRUSTC="$TMP/no/such/trustc" SCORECARD="$TMP/sc6.md" bash "$GATE"

echo "=== no build tree at all (the original exit-0 path) ==="
mkdir -p "$TMP/repo/scripts"
cp "$GATE" "$TMP/repo/scripts/"
expect_rc "TRUSTC unset and no build/<host>/stage2 present" 2 \
  env -u TRUSTC SCORECARD="$TMP/sc7.md" bash "$TMP/repo/scripts/trust_self_verify.sh"

echo "=== the scorecard a refusal leaves behind ==="
# Checked first, so "preserved" below cannot pass merely because the gate
# ignores $SCORECARD. A stub labelled SKIPPED reads as a benign outcome.
if grep -q "ERROR (exit 2)" "$TMP/sc7.md" 2>/dev/null; then
  echo "  ok   fresh stub is labelled ERROR, not SKIPPED"
else
  echo "  FAIL refusal stub at $TMP/sc7.md missing/not labelled ERROR"
  fails=$((fails + 1))
fi
echo "REAL RESULT FROM THE LAST GOOD RUN" > "$TMP/keep.md"
env TRUSTC="$TMP/no/such/trustc" SCORECARD="$TMP/keep.md" bash "$GATE" >/dev/null 2>&1
if [ "$(cat "$TMP/keep.md")" = "REAL RESULT FROM THE LAST GOOD RUN" ]; then
  echo "  ok   existing scorecard preserved on refusal"
else
  echo "  FAIL refusal clobbered the existing scorecard with an error stub"
  fails=$((fails + 1))
fi

echo "=== a tripwire that did not fire is not a pass ==="
expect_rc "compiles clean, emits zero obligations" 2 \
  env TRUSTC="$TMP/silent" SCORECARD="$TMP/sc8.md" bash "$GATE"
expect_rc "obligations emitted, but no unsafe sample's graded kind" 2 \
  env TRUSTC="$TMP/inert" SCORECARD="$TMP/sc9.md" bash "$GATE"
expect_says "inert tripwire is named as such" "tripwire INERT" \
  env TRUSTC="$TMP/inert" SCORECARD="$TMP/sc10.md" bash "$GATE"

echo "=== the soundness verdict itself still works ==="
# exit 1 (false proof) must stay DISTINCT from exit 2 (tripwire did not run).
expect_rc "a compiler that proves every reachable panic" 1 \
  env TRUSTC="$TMP/lying" SCORECARD="$TMP/sc11.md" bash "$GATE"
# ...and the gate must still be able to PASS, or every check above is vacuous.
expect_rc "a compiler that refutes exactly the unsafe samples" 0 \
  env TRUSTC="$TMP/honest" SCORECARD="$TMP/sc12.md" bash "$GATE"

echo ""
if [ "$fails" -eq 0 ]; then echo "trust_self_verify: PASS — every refusal planted and observed"; exit 0
else echo "trust_self_verify: FAILED ($fails)"; exit 1; fi
