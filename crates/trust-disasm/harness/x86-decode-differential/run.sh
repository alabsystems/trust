#!/usr/bin/env bash
# The x86-64 decode differential — gate runner.
#
#   ./run.sh            # corpus + sweep + the non-vacuity battery  (~20 s)
#   ./run.sh --random   # + a 20k random-byte tier
#   ./run.sh --accept   # re-record baseline.json from this run
#
# FAILS when: a mismatch family appears that the baseline does not record, a
# recorded family GROWS, or any mutation goes uncaught. The growth check exists
# because the sibling native-semantic harness recorded family NAMES only, and a
# regression inside an already-open family passed its gate silently.
set -uo pipefail
cd "$(dirname "$0")"

BIN=./target/release/x86-decode-differential
ACCEPT=0
RANDOM_TIER=0
for a in "$@"; do
  case "$a" in
    --accept) ACCEPT=1 ;;
    --random) RANDOM_TIER=1 ;;
    *) echo "unknown argument $a" >&2; exit 2 ;;
  esac
done

command -v clang >/dev/null   || { echo "clang is required (assembles candidates)" >&2; exit 2; }
command -v objdump >/dev/null || { echo "objdump is required (the oracle)" >&2; exit 2; }

echo "building..."
targo --unverified build --release >/dev/null 2>&1 \
  || cargo build --release >/dev/null 2>&1 \
  || { echo "build failed" >&2; exit 2; }

fail=0
for tier in corpus sweep; do
  echo "== tier: $tier"
  "$BIN" --mode "$tier" || fail=1
done
if [ "$RANDOM_TIER" = 1 ]; then
  echo "== tier: random"
  # The random tier has recorded known-open families; it is reported, and its
  # growth is adjudicated against baseline.json by eye until the families are
  # closed. It does not gate on its own exit code.
  "$BIN" --mode random --limit 20000 || true
fi

echo "== non-vacuity battery"
for m in $("$BIN" --list-mutations); do
  printf '   %-14s ' "$m"
  if "$BIN" --mode sweep --mutate "$m" | grep -q 'mutation caught'; then
    echo "caught"
  else
    echo "NOT CAUGHT — the differential has stopped comparing something"
    fail=1
  fi
done

if [ "$ACCEPT" = 1 ]; then
  echo "re-record baseline.json by hand from the tier output (see the note in that file)"
fi
[ "$fail" = 0 ] && echo "OK" || echo "FAILED"
exit "$fail"
