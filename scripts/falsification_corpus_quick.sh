#!/bin/bash
# falsification_corpus_quick.sh — the falsification corpus against ANY trustc, advisory.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS. `scripts/trust_falsification_gate.sh` is the release gate. It pins the
# compiler to exactly `build/<host>/stage2/bin/trustc`, which is deliberate: a gate
# verdict must name its authority. The cost is that nobody runs it while iterating on
# stage 1. Measured 2026-09-28: `tests/trust-falsification/mutant/repr_i8_neg_tag_index.rs`
# was refuted in the 2026-09-12 corpus run and PROVED, with a Clean-kernel certificate,
# on the 2026-09-19 stage 2. No gate saw it for nine days; a by-hand stage-1 run found it
# (fixed in `c5007cc8498`, docs/KNOWN_HAZARDS.md).
#
# WHAT IT DOES. Every fixture under `tests/trust-falsification/{proved,mutant}` is built
# with the given trustc under `-Ztrust-policy=certify`, the gate's policy:
#   * a mutant that exits 0 is a SURVIVOR, a potential false proof. The script exits 1;
#   * a mutant must exit 1 with a Trust refutation or incompleteness verdict.
#     Compiler errors and abnormal exits are tool failures even if they also print
#     verifier text. They are listed, and the script exits 1;
#   * a proved fixture that fails is listed. That is a completeness gap, so it does not
#     change the exit code.
#
# This is a MEASUREMENT, not the gate. It claims nothing about release authority; run
# the gate on stage 2 for that.
#
# USAGE: scripts/falsification_corpus_quick.sh [TRUSTC] [OUT_DIR]
#   TRUSTC   default build/host/stage1/bin/trustc
#   OUT_DIR  default build/tmp/falsification-quick (logs and results.tsv)
set -u
REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
# Trust: share the release owner's diagnostic classifier, including certify's
# instance-hypothesis refusal. An incomplete verdict is only an advisory refusal
# here; the release owner still requires an explicit refutation for a mutant.
# Sourcing defines helpers only; its guarded main does not run or select authority.
source "$REPO_ROOT/scripts/trust_falsification_gate.sh"
TRUSTC=${1:-$REPO_ROOT/build/host/stage1/bin/trustc}
OUT=${2:-$REPO_ROOT/build/tmp/falsification-quick}
[ -x "$TRUSTC" ] || { echo "REFUSE: no trustc at $TRUSTC"; exit 2; }
mkdir -p "$OUT/out"
: > "$OUT/results.tsv"
for kind in proved mutant; do
  for f in "$REPO_ROOT"/tests/trust-falsification/$kind/*.rs; do
    name=$(basename "$f" .rs)
    log="$OUT/$kind-$name.log"
    timeout 300 "$TRUSTC" -Ztrust-verify=on -Ztrust-policy=certify --crate-type=lib \
      --edition 2021 --emit=metadata --out-dir "$OUT/out" "$f" > "$log" 2>&1 < /dev/null
    rc=$?
    case $(classify_verdict "$rc" "$log") in
      refuted|incomplete) v=trust ;;
      *) v=other ;;
    esac
    printf '%s\t%s\t%s\t%s\n' "$kind" "$name" "$rc" "$v" >> "$OUT/results.tsv"
  done
done
survivors=$(awk -F'\t' '$1=="mutant" && $3=="0"' "$OUT/results.tsv")
tool_failures=$(awk -F'\t' '$1=="mutant" && $3!="0" && $4!="trust"' "$OUT/results.tsv")
proved_failing=$(awk -F'\t' '$1=="proved" && $3!="0"' "$OUT/results.tsv")
printf 'trustc: %s\n' "$TRUSTC"
printf 'mutants: %s, survivors: %s, tool failures: %s\n' \
  "$(awk -F'\t' '$1=="mutant"' "$OUT/results.tsv" | wc -l | tr -d ' ')" \
  "$(printf '%s' "$survivors" | grep -c . || true)" \
  "$(printf '%s' "$tool_failures" | grep -c . || true)"
printf 'proved fixtures: %s, not verifying: %s\n' \
  "$(awk -F'\t' '$1=="proved"' "$OUT/results.tsv" | wc -l | tr -d ' ')" \
  "$(printf '%s' "$proved_failing" | grep -c . || true)"
[ -n "$survivors" ] && printf 'SURVIVOR  %s\n' $(printf '%s\n' "$survivors" | cut -f2)
[ -n "$tool_failures" ] && printf 'TOOL-FAILURE  %s\n' $(printf '%s\n' "$tool_failures" | cut -f2)
[ -n "$proved_failing" ] && printf 'not-verifying  %s\n' $(printf '%s\n' "$proved_failing" | cut -f2)
if [ -n "$survivors" ] || [ -n "$tool_failures" ]; then exit 1; fi
exit 0
