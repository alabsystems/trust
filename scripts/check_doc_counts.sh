#!/usr/bin/env bash
# check_doc_counts.sh — Doc-truth gate (gap G26).
#
# Cross-checks human-readable count claims in docs/reports against the in-repo
# source of truth, so optimistic drift fails CI instead of relying on manual scrubs.
#
# Invariants checked:
#   (1) The number of .lean files in proofs/trust-soundness/ matches the "N/N"
#       verified-count claim in proofs/trust-soundness/README.md.
#   (2) No doc presents the INFLATED wasm headline ("82 ... proven unsat"): the
#       honest genuine-obligation count is 54 (28 of the original 82 were
#       degenerate X==X self-equalities). Source of truth:
#       first-party/trust-cg/crates/trust-cg-verify/src/wasm_lowering_proofs.rs.
#
# Exit 0 iff all invariants hold.
set -euo pipefail
cd "$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)"

fail=0

# (1) Lean proof-file count vs README claim.
actual_lean="$(find proofs/trust-soundness -maxdepth 1 -name '*.lean' | wc -l | tr -d ' ')"
readme="proofs/trust-soundness/README.md"
if [ -f "$readme" ]; then
  # Accept the count if the README mentions it as "<actual>/<actual>" or "<actual> files".
  if ! grep -Eq "(\b${actual_lean}/${actual_lean}\b|\b${actual_lean} (proof )?files\b)" "$readme"; then
    echo "FAIL (G26): proofs/trust-soundness has ${actual_lean} .lean files, but README.md does not state that count (stale 31/31 or 30?)."
    grep -nE "verified:?\s*[0-9]+/[0-9]+|[0-9]+ (proof )?files|[0-9]+ declarations" "$readme" | head -5 || true
    fail=1
  else
    echo "ok  lean proof files: ${actual_lean} (README consistent)"
  fi
fi

# (2) No inflated wasm "82 ... proven" headline in the superproject's own docs/.
# (trust-cg's canonical wasm doc lives in the submodule and is that repo's concern.)
hits="$(grep -rInE '82 (ay obligations|per-op refinement obligations) (proven|proved)' \
        docs 2>/dev/null || true)"
if [ -n "$hits" ]; then
  echo "FAIL (G26): inflated wasm proof count (82) presented as proven; honest count is 54:"
  echo "$hits" | sed 's/^/  /'
  fail=1
else
  echo "ok  wasm headline: no inflated '82 ... proven' claim"
fi

[ "$fail" -eq 0 ] && echo && echo "DOC COUNTS OK" || { echo; echo "DOC-TRUTH GATE FAILED"; exit 1; }
