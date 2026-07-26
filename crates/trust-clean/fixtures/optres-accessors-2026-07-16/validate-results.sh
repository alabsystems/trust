#!/bin/sh
# Reproduce the observational six-row baseline with the current grader.
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO=${REPO:-$(git -C "$HERE" rev-parse --show-toplevel)}
FF_GATE=${FF_GATE:-"$REPO/crates/target/release/ff-gate-diagnose-2026-07-10"}

[ -x "$FF_GATE" ] || { echo "missing executable: $FF_GATE" >&2; exit 1; }
command -v cmp >/dev/null 2>&1 || { echo "missing cmp" >&2; exit 1; }

TMP=$(mktemp -d "$HERE/.validate-results.tmp.XXXXXX")
cleanup() {
  status=$?
  trap - 0 HUP INT TERM
  rm -rf "$TMP"
  exit "$status"
}
trap cleanup 0
trap 'exit 1' HUP INT TERM

"$FF_GATE" "$HERE/dumps" >"$TMP/results.tsv"
[ "$(find "$HERE/dumps" -type f -name '*.json' | wc -l | tr -d ' ')" -eq 6 ] || {
  echo "expected exactly six JSON dumps" >&2
  exit 1
}
[ "$(wc -l <"$TMP/results.tsv" | tr -d ' ')" -eq 7 ] || {
  echo "expected one header plus six analyzer rows" >&2
  exit 1
}
cmp -s "$TMP/results.tsv" "$HERE/results-baseline.tsv" || {
  echo "current grader output differs from results-baseline.tsv" >&2
  exit 1
}
echo "validated 6/6 current grader rows"
