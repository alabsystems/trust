#!/usr/bin/env bash
# Survey a cargo crate through Trust's verifier and emit deterministic
# per-obligation JSON, bounded so no single hard obligation can hang the run.
#
# Backs `targo trust survey`. Toolchain-generic: operates on the current cargo
# workspace (cwd) and any package in it. The Rust subcommand binds $TARGO to the
# canonical Cargo frontend beside the selected Trust compiler.
#
# WHY each guard exists (a verifier must never hang on one obligation):
#   - Per-function and per-obligation bounds are rustc tracked options. Targo
#       supplies the compiler defaults plus `trust.toml`'s public timeout policy.
#   - AY executable selection comes from Targo's public solver configuration and
#       is translated to a tracked compiler option by `targo trust check`.
#   - perl alarm backstop        process-level wall clock; kills the whole compile
#       if an uncovered engine path still spins. macOS has no `timeout(1)`.
#
# Usage: trust_survey.sh <crate> [out-dir] [--contracts]
#   crate        cargo package name to survey (required)
#   out-dir      where to drop the JSON + summary (default: target/trust/survey)
#   --contracts  label this as the contracts replay (kept for workflow compatibility;
#                every verifier run already activates cfg(trust_verify))
set -uo pipefail

CRATE=""
OUT_DIR=""
CONTRACTS=0
positional=0
while [ $# -gt 0 ]; do
  case "$1" in
    --contracts) CONTRACTS=1 ;;
    --skip|--skip=*)
      echo "--skip has been removed: an evidence survey must not silently omit named functions" >&2
      exit 2
      ;;
    -*) echo "unknown flag: $1" >&2; exit 2 ;;
    *) if [ "$positional" = 0 ]; then CRATE="$1"; positional=1; else OUT_DIR="$1"; fi ;;
  esac
  shift
done

[ -n "$CRATE" ] || { echo "usage: targo trust survey <crate> [out-dir] [--contracts]" >&2; exit 2; }

# The Rust subcommand passes $TARGO (the selected canonical Targo frontend);
# fall back to `targo` on PATH only for standalone script invocation.
TARGO="${TARGO:-targo}"

# Survey the current cargo workspace. Exported so the perl alarm backstop's
# `chdir $ENV{WS}` (below) can read it.
export WS="${TRUST_SURVEY_WORKSPACE:-$PWD}"
[ -f "$WS/Cargo.toml" ] || { echo "FATAL: no Cargo.toml at $WS (run from a cargo workspace or set TRUST_SURVEY_WORKSPACE)" >&2; exit 2; }

OUT_DIR="${OUT_DIR:-$WS/target/trust/survey}"
mkdir -p "$OUT_DIR"
STAMP="$(date '+%Y%m%d-%H%M%S')"
JSON="$OUT_DIR/${CRATE}-${STAMP}.json"
LOG="$OUT_DIR/${CRATE}-${STAMP}.log"

RUN_TIMEOUT_S="${SURVEY_RUN_TIMEOUT_S:-2700}"
if [ -n "${TRUST_VERIFY_FN_BUDGET_MS+x}" ]; then
  echo "TRUST_VERIFY_FN_BUDGET_MS has been removed from this workflow; compiler budgets must come from tracked Targo policy" >&2
  exit 2
fi
if [ -n "${TRUST_TIMEOUT_MS+x}" ]; then
  echo "TRUST_TIMEOUT_MS has been removed; set timeout_ms in trust.toml so Targo can track it" >&2
  exit 2
fi
if [ -n "${SURVEY_NO_AY_TIMEOUT+x}" ]; then
  echo "SURVEY_NO_AY_TIMEOUT has been removed; solver bounds and AY selection are tracked by Targo" >&2
  exit 2
fi

# Do not forward any retired compiler controls. `targo trust check` owns the
# tracked survey, timeout, scope, and AY options for every Cargo unit.
unset TRUST_VERIFY_FN_BUDGET_MS TRUST_VERIFY_POLICY TRUST_VERIFY_PRIMARY_ONLY
unset TRUST_TIMEOUT_MS AY_DIRECT_SOLVE_TIMEOUT_MS TRUST_VERIFY_SURVEY TRUST_SKIP_FUNCTIONS

echo "targo        : $TARGO"                                | tee    "$LOG"
echo "workspace    : $WS"                                    | tee -a "$LOG"
echo "crate        : $CRATE"                                 | tee -a "$LOG"
echo "contracts replay: $CONTRACTS"                          | tee -a "$LOG"
echo "bounds       : compiler/AY tracked by Targo; run=${RUN_TIMEOUT_S}s" | tee -a "$LOG"
echo "json         : $JSON"                                  | tee -a "$LOG"

# Verification runs DURING compilation, so a cached crate makes trustc skip
# re-verifying and targo emits a degraded probe. Clean just this package to
# force a recompile + re-verify (generic; no crate-layout assumptions).
"$TARGO" clean -p "$CRATE" --manifest-path "$WS/Cargo.toml" >/dev/null 2>&1 || true

# perl alarm = process-level backstop (no timeout(1) on macOS). Run from the
# workspace root so cargo resolves the manifest.
perl -e 'chdir $ENV{WS} or die "chdir $ENV{WS}: $!"; alarm shift; exec @ARGV' "$RUN_TIMEOUT_S" \
  "$TARGO" trust check -p "$CRATE" --format json --survey >"$JSON" 2>>"$LOG"
RC=$?

echo "exit         : $RC"                                    | tee -a "$LOG"
if [ "$RC" = 142 ] || [ "$RC" = 14 ]; then
  echo "!! WHOLE-RUN TIMEOUT after ${RUN_TIMEOUT_S}s — an uncovered engine path still hangs." | tee -a "$LOG"
fi

echo "--- outcome histogram ---" | tee -a "$LOG"
grep -oE '"status"[: ]*"[a-zA-Z_]+"' "$JSON" 2>/dev/null | sort | uniq -c | sort -rn | tee -a "$LOG"
echo "json         : $JSON  ($(wc -c < "$JSON" 2>/dev/null) bytes)" | tee -a "$LOG"
exit "$RC"
