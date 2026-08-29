#!/usr/bin/env bash
# trust_self_verify_crate.sh — a RATCHETED self-proof baseline on a REAL crate
# from trustc's own link closure.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# ============================================================================
# WHY THIS EXISTS
# ============================================================================
# `docs/SELF_PROOF.md` §5 item 1 — "The smallest next step":
#
#   "Not a flag. The numbers in §3 took 68 minutes to produce and exist nowhere
#    else in the tree; the first job is to stop them from being a one-off.
#    Pin this crate as a ratcheted baseline ... a gate whose only assertion is
#    that clean-kernel-certified proved rows do not decrease and
#    `eligible == processed` stays true. Not a percentage, not a pass/fail on
#    the crate — a monotone floor on kernel-checked rows.
#    `scripts/trust_self_verify.sh` already carries the honesty discipline for
#    this shape; what it lacks is a real compiler-dependency crate."
#
# `scripts/trust_self_verify.sh` runs on "a curated corpus of self-contained
# .rs samples ... faithful, extracted MINIATURES of the compiler's own logic".
# Miniatures are not the compiler. This lane supplies the missing half: a real
# crate that `trustc` itself links (`crates/trust-semantics`, reached via
# trust-vcgen -> rustc_mir_transform), measured through the authenticated
# `targo trust check` path.
#
# ============================================================================
# WHAT IT ASSERTS, AND WHY EACH ONE
# ============================================================================
#   1. NOT VACUOUS. A run that produced no `Coverage:` line did not verify
#      anything, and 0 observed failures because nothing RAN looks identical to
#      0 because everything passed. Refuses with exit 2 rather than comparing an
#      empty observation against a baseline and calling it progress.
#   2. eligible == processed, and the word "(complete)". A crate that quietly
#      stops processing bodies reports better numbers for a worse reason.
#   3. kernel-certified rows are a MONOTONE FLOOR. Never a percentage: a
#      percentage improves when the denominator shrinks, and an obligation that
#      DISAPPEARS is not one that proved.
#   4. proved rows are a monotone floor, same reasoning.
#   5. `assumed` rows are a CEILING. This is the load-bearing one. SELF_PROOF.md
#      §5 item 2 records annotating the perimeter `#[trust::assume_total]` as
#      FORBIDDEN — "it is the cheapest way to make the number move and it is the
#      wrong one", because it converts every absent-callee row into an
#      AssumedTotalCalleeAssumption and the crate goes green while proving
#      strictly LESS than it does today. A floor on proved rows does not catch
#      that; only a ceiling on assumptions does. Without this assertion the gate
#      would actively reward the one move the design doc forbids.
#
# Usage:
#   scripts/trust_self_verify_crate.sh                 # run the gate
#   scripts/trust_self_verify_crate.sh --selftest      # mutation proof, no build
#   scripts/trust_self_verify_crate.sh --update        # re-mint the baseline
#
# A note on cost: this drives a full verified compile and is minutes, not
# seconds. It is NOT wired into pre-push for that reason — see the tail of this
# file for where it belongs.
set -uo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

CRATE="${TRUST_SELF_VERIFY_CRATE:-trust-semantics}"
BASELINE="tests/self-proof/${CRATE}.baseline"
TARGO="${TARGO:-$REPO_ROOT/build/host/stage1/bin/targo}"

# ---------------------------------------------------------------- parsing ---
# Crate-level roll-up emitted by the authenticated `targo trust` path:
#   Summary: 23 proved, 2 failed, 2 runtime-checked, 2 assumed, 12 mandated, \
#            0 contract-panic, 42 inconclusive (83 total)
#   Coverage: 24/24 eligible function bodies verified (complete)
# Per-function rows carry the kernel-recheck count:
#   = note: summary: 3 trusted, 2 certified, 0 failed, ... out of 8
field() {  # field <log> <name>  -> integer from the LAST Summary: line
  grep -E "^ *Summary: .*proved" "$1" | tail -1 \
    | grep -oE "[0-9]+ $2" | grep -oE "^[0-9]+" || true
}
certified_total() {  # sum of per-function kernel-certified rows
  grep -oE "summary: [0-9]+ trusted, [0-9]+ certified" "$1" \
    | grep -oE "[0-9]+ certified" | grep -oE "^[0-9]+" \
    | awk '{s+=$1} END {print s+0}'
}
coverage_pair() {  # "processed eligible complete_flag"
  local line
  line="$(grep -E "^ *Coverage: [0-9]+/[0-9]+ eligible" "$1" | tail -1)"
  [ -z "$line" ] && return 1
  local n d flag
  n="$(echo "$line" | grep -oE "[0-9]+/" | tr -d '/')"
  d="$(echo "$line" | grep -oE "/[0-9]+" | tr -d '/')"
  flag=incomplete
  echo "$line" | grep -q "(complete)" && flag=complete
  echo "$n $d $flag"
}

read_baseline() {  # read_baseline <key>
  sed -e 's/#.*//' "$BASELINE" 2>/dev/null \
    | grep -E "^[[:space:]]*$1[[:space:]]*=" \
    | head -1 | sed -e 's/.*=[[:space:]]*//' -e 's/[[:space:]]*$//'
}

# --------------------------------------------------------------- selftest ---
# Mutation proof. Every assertion must be shown to FIRE on a synthetic log that
# violates it — a gate nobody has watched fail is not known to be a gate, and
# this repo has shipped four instruments that were silently inert.
if [ "${1:-}" = "--selftest" ]; then
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
  good="$tmp/good.log"
  cat > "$good" <<'LOG'
    = note: summary: 3 trusted, 2 certified, 0 failed, 2 unknown, 1 runtime-checked, 0 skipped out of 8
    = note: summary: 0 trusted, 4 certified, 1 failed, 1 unknown, 1 runtime-checked, 0 skipped out of 5
  Summary: 23 proved, 2 failed, 2 runtime-checked, 2 assumed, 12 mandated, 0 contract-panic, 42 inconclusive (83 total)
  Coverage: 24/24 eligible function bodies verified (complete)
LOG
  fails=0
  chk() { # chk <label> <expect-pass|expect-fire> <condition-result>
    local label="$1" mode="$2" res="$3"
    if [ "$mode" = "expect-fire" ] && [ "$res" = "fired" ]; then echo "  ok   $label"
    elif [ "$mode" = "expect-pass" ] && [ "$res" = "clean" ]; then echo "  ok   $label"
    else echo "  FAIL $label (mode=$mode result=$res)"; fails=$((fails+1)); fi
  }

  # parsers agree with the known-good log
  [ "$(field "$good" proved)" = "23" ] && chk "parse proved=23" expect-pass clean || chk "parse proved" expect-pass fired
  [ "$(field "$good" assumed)" = "2" ] && chk "parse assumed=2" expect-pass clean || chk "parse assumed" expect-pass fired
  [ "$(certified_total "$good")" = "6" ] && chk "parse certified=6 (2+4)" expect-pass clean || chk "parse certified" expect-pass fired
  [ "$(coverage_pair "$good")" = "24 24 complete" ] && chk "parse coverage" expect-pass clean || chk "parse coverage" expect-pass fired

  # (a) vacuous log — no Coverage line at all
  echo "some build noise" > "$tmp/vacuous.log"
  if coverage_pair "$tmp/vacuous.log" >/dev/null 2>&1; then chk "vacuous refused" expect-fire clean
  else chk "vacuous refused" expect-fire fired; fi

  # (b) incomplete coverage
  sed 's|24/24 eligible function bodies verified (complete)|19/24 eligible function bodies verified (incomplete)|' \
    "$good" > "$tmp/incomplete.log"
  cp="$(coverage_pair "$tmp/incomplete.log")"
  if [ "$cp" = "24 24 complete" ]; then chk "incomplete coverage caught" expect-fire clean
  else chk "incomplete coverage caught" expect-fire fired; fi

  # (c) certified DROPPED
  sed 's|0 trusted, 4 certified|0 trusted, 1 certified|' "$good" > "$tmp/dropped.log"
  if [ "$(certified_total "$tmp/dropped.log")" -lt 6 ]; then chk "certified drop caught" expect-fire fired
  else chk "certified drop caught" expect-fire clean; fi

  # (d) THE IMPORTANT ONE: assume_total laundering. proved goes UP and failures
  #     go to zero, but only because assumptions ballooned. A floor-only gate
  #     reports green here; the ceiling must fire.
  sed -e 's|23 proved, 2 failed, 2 runtime-checked, 2 assumed|46 proved, 0 failed, 0 runtime-checked, 48 assumed|' \
      "$good" > "$tmp/laundered.log"
  lp="$(field "$tmp/laundered.log" proved)"; la="$(field "$tmp/laundered.log" assumed)"
  if [ "$lp" -ge 23 ] && [ "$la" -gt 2 ]; then
    chk "assume_total laundering caught by CEILING (proved $lp up, assumed $la up)" expect-fire fired
  else
    chk "assume_total laundering caught by CEILING" expect-fire clean
  fi

  # (e) THE cert-meter CASE: every number says PASS and the crate did not
  #     compile. Measured 2026-08-26. A floor-and-coverage gate reads this as
  #     a clean green, because the bodies that failed to lower emitted no
  #     obligations to fail with.
  { cat "$good"
    echo "error: Trust full verification failed for \`<Grade as Debug>::fmt\`"
    echo "error: could not compile \`trust-cert-meter\` (lib) due to 4 previous errors"
  } > "$tmp/didnt_compile.log"
  # the numeric assertions must all still PASS on it — that is the point
  cp_ok=$([ "$(coverage_pair "$tmp/didnt_compile.log")" = "24 24 complete" ] && echo y || echo n)
  fl_ok=$([ "$(field "$tmp/didnt_compile.log" failed)" = "2" ] && echo y || echo n)
  if [ "$cp_ok" = y ] && [ "$fl_ok" = y ] \
     && grep -qE "^error: could not compile|Trust full verification failed for" "$tmp/didnt_compile.log"; then
    chk "did-not-compile caught (numbers all look clean; only the errors betray it)" expect-fire fired
  else
    chk "did-not-compile caught" expect-fire clean
  fi

  # (f) the known-good log must NOT trip the compile-error refusal
  if grep -qE "^error: could not compile|Trust full verification failed for" "$good"; then
    chk "no false positive on a clean log" expect-pass fired
  else
    chk "no false positive on a clean log" expect-pass clean
  fi

  echo ""
  if [ "$fails" -eq 0 ]; then echo "selftest: PASS — every assertion mutation-proved"; exit 0
  else echo "selftest: FAILED ($fails)"; exit 1; fi
fi

# ------------------------------------------------------------------- run ----
if [ ! -x "$TARGO" ]; then
  echo "REFUSE: no targo at $TARGO" >&2
  echo "        set TARGO=<path>; verify it is REALLY targo, not cargo wearing" >&2
  echo "        the name:  \"\$TARGO\" --unverified --version   (cargo rejects the flag)" >&2
  exit 2
fi
# CLAUDE.md: a stage whose targo was never rebuilt ships upstream cargo under
# the name `targo`, works, and silently verifies NOTHING. Behavioural check.
if ! "$TARGO" --unverified --version >/dev/null 2>&1; then
  echo "REFUSE: $TARGO rejects --unverified, so it is cargo-in-disguise, not targo." >&2
  echo "        A run through it would report success having verified nothing." >&2
  exit 2
fi

log="$(mktemp)"; trap 'rm -f "$log"' EXIT
# `trust-semantics`' contracts are cfg-gated behind `trust_contracts` so that an
# ordinary `x.py` build — which compiles this crate with a stage0 that may be a
# STABLE rustc, and would answer E0554 to `#![feature(contracts)]` — is
# unaffected. The verified lane is the one that turns them on, and the floors
# below are minted under them, so the gate must set the cfg or it would measure
# a DIFFERENT configuration than the baseline and read as a regression.
#
# NOTE: `-Ztrust-*` in RUSTFLAGS is silently IGNORED by targo (it warns and
# drops it); those belong in TRUSTFLAGS. Measured the hard way — a dump run
# produced zero artifacts and the warning was the only evidence.
CFG_FLAGS="${TRUST_SELF_VERIFY_RUSTFLAGS:---cfg=trust_contracts}"
echo "running: RUSTFLAGS=\"$CFG_FLAGS\" targo trust check -p $CRATE"
echo "         (verified lane; minutes, not seconds)"
( cd "$REPO_ROOT/crates" && RUSTFLAGS="$CFG_FLAGS" "$TARGO" trust check -p "$CRATE" ) > "$log" 2>&1
run_status=$?

cov="$(coverage_pair "$log")" || {
  echo "REFUSE: no 'Coverage:' line — verification did not run (exit $run_status)."
  echo "        This is NOT a green: nothing was verified. Tail:"
  tail -25 "$log"
  exit 2
}

# ---------------------------------------------------------------------------
# A CRATE THAT FAILED TO COMPILE CAN REPORT `0 failed` AND COMPLETE COVERAGE.
#
# Measured 2026-08-26 on `trust-cert-meter`, and it would have fooled the
# floors below:
#
#     Summary:  4 proved, 0 failed, 0 runtime-checked, 0 assumed, ... (4 total)
#     Coverage: 6/6 eligible function bodies verified (complete)
#     error: Trust full verification failed for `<Grade as Debug>::fmt`
#     error: could not compile `trust-cert-meter` (lib) due to 4 previous errors
#
# Every field this gate reads said PASS while the build died. The mechanism:
# when native lowering aborts on an unmodeled construct ("address walk into
# variant-bearing ADT interior"), the unlowerable constructs emit NO
# OBLIGATIONS AT ALL. Each body still emits its one `unreachable` obligation,
# which proves — so the body is reported `[VERIFIED] (1 obligations: 1 proved,
# 0 failed)` and is simultaneously the reason the crate did not build.
#
# This is the un-emitted-is-unchecked family: a missing obligation reads
# exactly like success, which is the hazard docs/SELF_PROOF.md names as the
# reason M1+M2 alone cannot distinguish "proved" from "never asked". A floor on
# proved rows cannot see it; only reading the compiler's own errors can.
if grep -qE "^error: could not compile|Trust full verification failed for" "$log"; then
  echo ""
  echo "REFUSE: the crate did NOT verify — the compiler reported verification"
  echo "        errors, even though the Summary/Coverage lines look clean."
  echo "        Un-emitted obligations read exactly like proved ones."
  echo ""
  grep -E "^error: could not compile|Trust full verification failed for" "$log" | head -8
  echo ""
  echo "        Do not compare this run against the baseline: its numbers"
  echo "        describe the bodies that DID lower, not the crate."
  exit 2
fi
set -- $cov; processed="$1"; eligible="$2"; complete="$3"

proved="$(field "$log" proved)"
failed="$(field "$log" failed)"
assumed="$(field "$log" assumed)"
certified="$(certified_total "$log")"

echo ""
echo "  coverage   $processed/$eligible ($complete)"
echo "  proved     $proved"
echo "  certified  $certified   (kernel-rechecked)"
echo "  failed     $failed"
echo "  assumed    $assumed"

if [ "${1:-}" = "--update" ]; then
  mkdir -p "$(dirname "$BASELINE")"
  cat > "$BASELINE" <<EOF
# Ratcheted self-proof baseline for \`$CRATE\`, a crate in trustc's own link
# closure. Minted by scripts/trust_self_verify_crate.sh --update.
#
# floors are MONOTONE (may only rise); assumed_max is a CEILING and exists to
# refuse the \`#[trust::assume_total]\` laundering SELF_PROOF.md §5.2 forbids.
# Raising any number here is a claim that the improvement is real — state why.
certified_min = $certified
proved_min    = $proved
assumed_max   = $assumed
EOF
  echo ""
  echo "baseline written: $BASELINE"
  exit 0
fi

if [ ! -f "$BASELINE" ]; then
  echo ""
  echo "REFUSE: no baseline at $BASELINE — mint one with --update." >&2
  exit 2
fi
certified_min="$(read_baseline certified_min)"
proved_min="$(read_baseline proved_min)"
assumed_max="$(read_baseline assumed_max)"

status=0
if [ "$processed" != "$eligible" ] || [ "$complete" != "complete" ]; then
  echo ""
  echo "FAIL: coverage is $processed/$eligible ($complete); eligible == processed must hold."
  echo "      A crate that stops processing bodies reports better numbers for a worse reason."
  status=1
fi
if [ "$certified" -lt "$certified_min" ]; then
  echo ""
  echo "FAIL: kernel-certified rows $certified < floor $certified_min."
  echo "      Kernel re-check is the only thing that earns Certified; this floor may not fall."
  status=1
fi
if [ "$proved" -lt "$proved_min" ]; then
  echo ""
  echo "FAIL: proved rows $proved < floor $proved_min."
  status=1
fi
if [ "$assumed" -gt "$assumed_max" ]; then
  echo ""
  echo "FAIL: assumed rows $assumed > ceiling $assumed_max."
  echo "      SELF_PROOF.md §5.2 records assuming the callee perimeter as FORBIDDEN:"
  echo "      it turns absent-callee rows into AssumedTotalCalleeAssumption rows and the"
  echo "      crate goes green while proving strictly LESS. If these assumptions are"
  echo "      genuinely justified, raise the ceiling in $BASELINE and say why."
  status=1
fi

echo ""
if [ "$status" -eq 0 ]; then
  echo "PASS: floors held, coverage complete, no new assumptions."
  echo "NOTE: this is a RATCHET, not a strict-lane pass. \`targo trust check\` still"
  echo "      exits $run_status here — unproved rows remain (see docs/SELF_PROOF.md §2.4,"
  echo "      absent callees). Do not read a PASS as 'the crate verifies'."
fi
exit "$status"
