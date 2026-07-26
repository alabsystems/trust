#!/usr/bin/env bash
# check_pin_coherence.sh — Gate-zero integrity check for the proven-assembly bootstrap (gap G3).
#
# Asserts, for every git submodule, that:
#   (1) the commit recorded in the superproject tree (`git ls-tree HEAD <path>`)
#       is RESOLVABLE in the submodule's local object store, and
#   (2) the submodule working tree is checked out AT that recorded pin
#       (no `+` / `-` / `U` drift).
#
# Rationale: until the on-disk code matches the recorded pins AND every pin is
# fetchable, no claim about "what the bootstrap builds/proves" is verifiable, and
# the build is unreproducible by construction. This is the hard prerequisite for
# everything downstream (see reports/proven-asm-bootstrap-completion-plan-*.md, WS-0.1).
#
# Exit 0 iff every submodule is coherent and every pin resolves; non-zero otherwise.
set -euo pipefail

cd "$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)"

fail=0
problems=()

# Enumerate submodule paths from .gitmodules (robust to working-tree state).
while IFS= read -r path; do
  [ -z "$path" ] && continue

  recorded="$(git ls-tree HEAD "$path" 2>/dev/null | awk '{print $3}')"
  if [ -z "$recorded" ]; then
    problems+=("MISSING-GITLINK  $path  (no gitlink recorded at HEAD)")
    fail=1
    continue
  fi

  if [ ! -e "$path/.git" ]; then
    problems+=("NOT-CHECKED-OUT  $path  pin=$recorded  (run the canonical recreator with --require-seed --no-build; it targets only missing indexed gitlinks)")
    fail=1
    continue
  fi

  # (1) recorded pin must resolve in the submodule object store
  if ! git -C "$path" cat-file -e "${recorded}^{commit}" 2>/dev/null; then
    problems+=("PIN-UNFETCHABLE  $path  pin=$recorded  (recorded commit absent from local object store; push it or re-pin)")
    fail=1
    continue
  fi

  # (2) on-disk HEAD must equal the recorded pin
  ondisk="$(git -C "$path" rev-parse HEAD 2>/dev/null || echo '')"
  if [ "$ondisk" != "$recorded" ]; then
    problems+=("PIN-DRIFT        $path  recorded=$recorded  ondisk=$ondisk")
    fail=1
    continue
  fi

  echo "ok  $path  @ $recorded"
done < <(git config --file .gitmodules --get-regexp 'submodule\..*\.path' | awk '{print $2}')

if [ "$fail" -ne 0 ]; then
  echo
  echo "PIN COHERENCE FAILED (gap G3):"
  for p in "${problems[@]}"; do echo "  - $p"; done
  echo
  echo "Resolve each before relying on any 'proven' claim. See WS-0.1 in the completion plan."
  exit 1
fi

echo
echo "PIN COHERENCE OK: every submodule is at its recorded pin and every pin resolves."
