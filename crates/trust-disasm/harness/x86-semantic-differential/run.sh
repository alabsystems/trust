#!/usr/bin/env bash
# The x86-64 SEMANTIC differential — gate runner. Oracle: Rosetta 2.
#
#   ./run.sh              corpus + sweep + the non-vacuity battery
#   ./run.sh --random     + a 20k random tier (adjudicated known-open)
#
# FAILS when: corpus or sweep mismatches at all, or any mutation goes uncaught.
# The random tier carries a recorded known-open set (see baseline.json) and is
# reported, not gated on its own exit — its residual is the `0f 1e` reserved
# encoding (three oracles disagree) and corner-address memory faults.
#
# REQUIRES ROSETTA 2. On an Apple-silicon host: `softwareupdate --install-rosetta
# --agree-to-license`. Without it the x86_64 executor will not start.
set -uo pipefail
cd "$(dirname "$0")"

BIN=./target/release/x86-semantic-differential
RANDOM_TIER=0
for a in "$@"; do case "$a" in
  --random) RANDOM_TIER=1 ;;
  *) echo "unknown argument $a" >&2; exit 2 ;;
esac; done

command -v clang >/dev/null || { echo "clang required" >&2; exit 2; }
if ! arch -x86_64 /usr/bin/true 2>/dev/null; then
  # /usr/bin/true is arm64-only on this host; probe the real executor instead.
  :
fi

echo "building the executor + driver..."
clang -arch x86_64 -O2 -o natsem86 natsem86.c || { echo "executor build failed" >&2; exit 2; }
STAGE2="$(git rev-parse --show-toplevel 2>/dev/null)/build/host/stage2/bin/targo"
if command -v targo >/dev/null 2>&1; then
  targo --unverified build --release >/dev/null 2>&1 || { echo "driver build failed" >&2; exit 2; }
elif [ -x "$STAGE2" ]; then
  "$STAGE2" --unverified build --release >/dev/null 2>&1 || { echo "driver build failed" >&2; exit 2; }
else
  echo "no targo on PATH and no stage2 targo; build the driver first" >&2; exit 2
fi

# One real execution proves Rosetta is available.
if ! ./natsem86 --slotpc >/dev/null 2>&1; then
  echo "natsem86 will not run — is Rosetta 2 installed? (softwareupdate --install-rosetta)" >&2
  exit 2
fi

fail=0
for tier in corpus sweep; do
  echo "== tier: $tier"
  "$BIN" --mode "$tier" || fail=1
done
if [ "$RANDOM_TIER" = 1 ]; then
  echo "== tier: random (known-open adjudicated; see baseline.json)"
  "$BIN" --mode random --limit 20000 || true
fi

echo "== non-vacuity battery"
for m in $("$BIN" --list-mutations); do
  printf '   %-20s ' "$m"
  if "$BIN" --mode sweep --mutate "$m" | grep -q 'mutation caught'; then echo caught
  else echo "NOT CAUGHT"; fail=1; fi
done

[ "$fail" = 0 ] && echo OK || echo FAILED
exit "$fail"
