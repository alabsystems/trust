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
#                               0 timed-out, 0 runtime-checked, nothing skipped or
#                               conditional, >=1 proved, exit 0
#                               (every check statically discharged = superior).
#   superiority/mutant/*.rs  -> advisory mode NOT fully proved: at least one
#                               obligation failed / unknown / timed out /
#                               runtime-checked (the unsafe access is retained,
#                               not eliminated).
#
# SOLVER (2026-10-06, SUPERIORITY-GATE-DEAD). `trustc` resolves the `ay` SMT
# solver itself and the gate passes nothing. Until plan P4 / T4.1 (2026-10-10)
# that meant the executable `ay` beside it or the tracked
# `-Ztrust-verify-ay-path`; since T4.1 trustc links its ay and spawns none, so the
# sibling check below is a toolchain-completeness preflight kept fail-closed, not
# a solver selection (DECISION_QUEUE T4.1-IMPL-1). It used to `export AY_PATH=…`
# (building a debug ay when the sibling was missing). AY_PATH has been in
# LEGACY_TRUST_SEMANTIC_ENV_VARS (compiler/rustc_session/src/config.rs) since
# 80a35e2c7e (2026-07-14), so a verifying trustc refused every compile and this
# release row measured nothing from then until this fix (docs/KNOWN_HAZARDS.md).
# Now:
#   * every compile runs under `env -i` with a fixed minimal environment, so no
#     ambient variable — a legacy semantic control, a TCG_/TRUST_CG_ codegen
#     control, RUSTFLAGS — reaches the measured compiler;
#   * a lane in which NO proved fixture printed a `Trust verification:` summary
#     cannot be judged, and the gate exits 2 ("GATE CANNOT RUN") naming the first
#     error line instead of printing a wall of per-row FAILs;
#   * every summary line must match the whole line grammar below, or the row FAILs.
#   scripts/tests/gate_legacy_env_test.py keeps any script from exporting a name
#   trustc refuses; scripts/tests/superiority_gates_stub_test.sh drives this gate
#   against a fake compiler.
#
# Exit status: 0 GREEN, 1 RED (a measured row failed), 2 GATE CANNOT RUN.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/host/stage2/bin/trustc}"
FIXTURES="$REPO_ROOT/tests/trust-falsification/superiority"
CLEAN_PATH='/usr/bin:/bin:/usr/sbin:/sbin'
# No z3/LIBRARY_PATH export: the `ay` SMT solver is pure-Rust and stage2 `trustc`
# links no libz3 (verified 2026-08-01: no z3-sys/links="z3" in any Cargo.lock;
# `otool -L trustc` is z3-clean). Re-adding one would resurrect a dead knob.

cannot_run() {
  printf 'GATE CANNOT RUN: %s\n' "$*"
  printf 'SUPERIORITY GATE: CANNOT RUN — no verdict was measured (exit 2)\n'
  exit 2
}

if [ ! -x "$TRUSTC" ]; then
  cannot_run "trustc not found at $TRUSTC (build it: ./x.py build --stage 2 compiler/rustc library/std)"
fi
AY_SIBLING="$(dirname "$TRUSTC")/ay"
if [ ! -x "$AY_SIBLING" ]; then
  cannot_run "no executable ay solver beside trustc at $AY_SIBLING; the toolchain under test is incomplete (this gate no longer builds one or passes a solver path)"
fi

shopt -s nullglob
PROVED_FIXTURES=("$FIXTURES"/proved/*.rs)
MUTANT_FIXTURES=("$FIXTURES"/mutant/*.rs)
shopt -u nullglob
if [ "${#PROVED_FIXTURES[@]}" -eq 0 ] || [ "${#MUTANT_FIXTURES[@]}" -eq 0 ]; then
  cannot_run "a fixture lane under $FIXTURES is empty"
fi

TMPDIR_GATE="$(mktemp -d)" || cannot_run "could not create a temporary directory"
trap 'rm -rf "$TMPDIR_GATE"' EXIT
mkdir -p "$TMPDIR_GATE/home" "$TMPDIR_GATE/tmp" "$TMPDIR_GATE/work" \
  || cannot_run "could not populate $TMPDIR_GATE"

# compile_fixture <fixture.rs> <output-file>: advisory verify, stdout+stderr to
# the file; returns trustc's exit status. The environment is fixed, not
# inherited.
compile_fixture() {
  env -i PATH="$CLEAN_PATH" HOME="$TMPDIR_GATE/home" TMPDIR="$TMPDIR_GATE/tmp" \
    LC_ALL=C LANG=C TZ=UTC \
    "$TRUSTC" --edition 2021 --crate-type lib -Z trust-policy=advisory "$1" \
    -o "$TMPDIR_GATE/work/$(basename "$1").rlib" >"$2" 2>&1
}

# The whole summary line, as trust_verify.rs prints it (`PublishedRowTally`):
#   note: Trust verification: P <proved | conditionally discharged (NOT proved)>,
#     F failed, U unknown, T timed out, R runtime-checked
#     [, A assumed (requires)][, D assumed (instance discharge)][, S skipped]
#     out of N obligation(s)
# with P+F+U+T+R+A+D+S == N. A line that does not match whole, or whose counts
# do not reach N, is MALFORMED and fails its row: a new column or label must be
# taught here before it can count, so format drift fails closed.
SUMMARY_RE='^note: Trust verification: ([0-9]{1,9}) (proved|conditionally discharged \(NOT proved\)), ([0-9]{1,9}) failed, ([0-9]{1,9}) unknown, ([0-9]{1,9}) timed out, ([0-9]{1,9}) runtime-checked(, ([0-9]{1,9}) assumed \(requires\))?(, ([0-9]{1,9}) assumed \(instance discharge\))?(, ([0-9]{1,9}) skipped)? out of ([0-9]{1,9}) obligation\(s\)$'

# summary_counts <output-file> <rc> -> "proved failed unknown timed runtime nonstatic rc",
# summed over every summary line (one per function); "MALFORMED <line>" when a
# line does not parse; empty when the compile printed no summary at all.
#   nonstatic = conditionally-discharged + assumed (instance discharge) + skipped:
#   rows that are neither a static proof nor a retained check. They block
#   SUPERIOR, and never count as a retained check on the mutant lane.
#   `assumed (requires)` is a definition-entry contract premise charged at every
#   in-crate call site; it is neither, and blocks nothing (the same ruling as the
#   falsification gate's armor: docs/DECISION_QUEUE.md FALSIF-ARMOR-ASSUMED).
#
# Hardened (2026-07-02, the rev_range_index_bound escape): every headline is
# summed and the compiler rc is appended, because a multi-function fixture emits
# one headline PER function and a clean headline can still be followed by a hard
# error (the gate once reported SUPERIOR while the compile was REJECTED).
summary_counts() {
  local file=$1 rc=$2 line seen=0
  local p=0 f=0 u=0 t=0 r=0 x=0
  local lp label lf lu lt lr lreq ldis lskip ln
  while IFS= read -r line; do
    if [[ ! $line =~ $SUMMARY_RE ]]; then
      printf 'MALFORMED %s\n' "$line"
      return 0
    fi
    lp=${BASH_REMATCH[1]} label=${BASH_REMATCH[2]} lf=${BASH_REMATCH[3]} lu=${BASH_REMATCH[4]}
    lt=${BASH_REMATCH[5]} lr=${BASH_REMATCH[6]} lreq=${BASH_REMATCH[8]:-0} ldis=${BASH_REMATCH[10]:-0}
    lskip=${BASH_REMATCH[12]:-0} ln=${BASH_REMATCH[13]}
    if ((10#$lp + 10#$lf + 10#$lu + 10#$lt + 10#$lr + 10#$lreq + 10#$ldis + 10#$lskip != 10#$ln)); then
      printf 'MALFORMED %s\n' "$line"
      return 0
    fi
    if [ "$label" = proved ]; then
      p=$((p + 10#$lp))
    else
      x=$((x + 10#$lp))
    fi
    f=$((f + 10#$lf)) u=$((u + 10#$lu)) t=$((t + 10#$lt)) r=$((r + 10#$lr))
    x=$((x + 10#$ldis + 10#$lskip))
    seen=1
  done < <(LC_ALL=C grep -a 'Trust verification: ' "$file")
  if [ "$seen" -eq 1 ]; then
    printf '%s %s %s %s %s %s %s\n' "$p" "$f" "$u" "$t" "$r" "$x" "$rc"
  fi
}

counts_of() {
  local out="$TMPDIR_GATE/compile.out" rc
  compile_fixture "$1" "$out"
  rc=$?
  summary_counts "$out" "$rc"
}

# Warm EVERY proved fixture once (discard results). A debug-build ay against the
# deliberately-low per-VC timeout can exceed it on the FIRST (cold) query —
# binary not yet in the OS page cache, solver state cold — and spuriously leave
# an obligation runtime-checked. Warming every fixture (not just the first, which
# may be interval-discharged and never spawn ay) absorbs the cold start so the
# measured runs reflect steady-state capability, not first-spawn latency.
#
# The warm-up is also the PREFLIGHT: if not one proved fixture printed a summary,
# the compiler did not verify anything (a refused environment, a missing solver,
# a renamed summary) and no row below could mean what it says.
summaries=0
first_silent=''
for w in "${PROVED_FIXTURES[@]}"; do
  compile_fixture "$w" "$TMPDIR_GATE/warm.out"
  if LC_ALL=C grep -aq 'Trust verification: ' "$TMPDIR_GATE/warm.out"; then
    summaries=$((summaries + 1))
  elif [ -z "$first_silent" ]; then
    first_silent="$(basename "$w"): $(LC_ALL=C grep -a -m1 '^error' "$TMPDIR_GATE/warm.out" || true)"
  fi
done
if [ "$summaries" -eq 0 ]; then
  cannot_run "no proved fixture printed a \`Trust verification:\` summary; first: ${first_silent:-<none>}"
fi

failed=0

for f in "${PROVED_FIXTURES[@]}"; do
  # Retry once on a non-superior result: a real regression fails BOTH attempts
  # (so it is still caught), while a cold-start solver timeout clears on the warm
  # retry. This never masks a genuine loss of superiority.
  superior=0; proved=0; fl=0; unk=0; tmo=0; rtc=0; nst=0; rc=0; c=''
  for _ in 1 2; do
    c="$(counts_of "$f")"
    [ -z "$c" ] && continue
    case $c in MALFORMED*) break ;; esac
    read -r proved fl unk tmo rtc nst rc <<<"$c"
    # Hardened: a clean headline with a NONZERO compiler rc (a hard error after
    # the report — e.g. an incomplete native lowering) is NOT superior.
    if [ "$fl" -eq 0 ] && [ "$unk" -eq 0 ] && [ "$tmo" -eq 0 ] && [ "$rtc" -eq 0 ] && [ "$nst" -eq 0 ] \
       && [ "$proved" -ge 1 ] && [ "$rc" -eq 0 ]; then
      superior=1; break
    fi
  done
  if [ -z "$c" ]; then
    echo "FAIL  proved   $(basename "$f")  — no verification summary (compile error?)"; failed=1; continue
  fi
  case $c in
    MALFORMED*)
      echo "FAIL  proved   $(basename "$f")  — unparseable verification summary: ${c#MALFORMED }"; failed=1; continue ;;
  esac
  if [ "$superior" -eq 1 ]; then
    echo "PASS  proved   $(basename "$f")  — SUPERIOR: $proved proved, 0 runtime-checked (all checks eliminated)"
  else
    echo "FAIL  proved   $(basename "$f")  — NOT superior: $proved proved / $fl failed / $unk unknown / $tmo timed / $rtc runtime-checked / $nst skipped-or-conditional / rc=$rc"
    failed=1
  fi
done

for f in "${MUTANT_FIXTURES[@]}"; do
  c="$(counts_of "$f")"
  if [ -z "$c" ]; then
    echo "FAIL  mutant   $(basename "$f")  — no verification summary (compile error?)"; failed=1; continue
  fi
  case $c in
    MALFORMED*)
      echo "FAIL  mutant   $(basename "$f")  — unparseable verification summary: ${c#MALFORMED }"; failed=1; continue ;;
  esac
  read -r proved fl unk tmo rtc nst rc <<<"$c"
  # Sound iff the unsafe access was NOT statically discharged: something must
  # remain failed/unknown/timed-out/runtime-checked (the runtime check is
  # retained). A skipped or conditionally-discharged row says nothing about the
  # check, so it never makes a mutant sound on its own.
  # (`rc` is not consulted here: fail-closed strict mode makes an undischarged
  # mutant a build error, but the retained-check COUNTS are the judgment.)
  if [ "$fl" -gt 0 ] || [ "$unk" -gt 0 ] || [ "$tmo" -gt 0 ] || [ "$rtc" -gt 0 ]; then
    echo "PASS  mutant   $(basename "$f")  — sound: not fully discharged ($fl failed / $unk unknown / $tmo timed / $rtc runtime-checked)"
  else
    echo "FAIL  mutant   $(basename "$f")  — VACUOUS PROOF: unsafe access statically eliminated ($proved proved, $nst skipped-or-conditional, 0 retained)"
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
