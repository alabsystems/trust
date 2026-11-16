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

# Enumerate from the committed blob. A dirty/deleted worktree .gitmodules must
# not be able to hide gitlinks, and process-substitution status must not turn a
# parser failure (or an empty inventory) into a vacuous green run.
module_rows=""
if ! module_rows="$(git config --blob HEAD:.gitmodules --get-regexp 'submodule\..*\.path' 2>/dev/null)"; then
  problems+=("GITMODULES-INVALID  .gitmodules  (cannot parse the committed submodule inventory at HEAD)")
  fail=1
elif [ -z "$module_rows" ]; then
  problems+=("GITMODULES-EMPTY    .gitmodules  (the committed submodule inventory may not be empty)")
  fail=1
fi

# A gitlink omitted from .gitmodules is still a submodule-shaped build input.
# Compare both committed inventories so an undeclared extra cannot evade every
# per-path check below.
declared_paths="$(printf '%s\n' "$module_rows" | sed -n 's/^[^ ]* //p' | LC_ALL=C sort)"
if ! tree_gitlinks="$(git ls-tree -r HEAD 2>/dev/null | awk '$1 == "160000" && $2 == "commit" { sub(/^[^\t]*\t/, ""); print }' | LC_ALL=C sort)"; then
  problems+=("GITLINK-INVENTORY-FAILED  .gitmodules  (cannot enumerate committed gitlinks at HEAD)")
  fail=1
elif [ "$tree_gitlinks" != "$declared_paths" ]; then
  problems+=("GITLINK-INVENTORY  .gitmodules  (declared submodules and committed 160000 gitlinks differ)")
  fail=1
fi

while IFS= read -r module_row; do
  [ -z "$module_row" ] && continue
  module_key="${module_row%% *}"
  path="${module_row#* }"
  if [ "$module_key" = "$module_row" ] || [ -z "$path" ]; then
    problems+=("GITMODULES-INVALID  .gitmodules  (malformed committed inventory row)")
    fail=1
    continue
  fi

  tree_row="$(git ls-tree HEAD -- "$path" 2>/dev/null || true)"
  metadata="${tree_row%%$'\t'*}"
  listed_path="${tree_row#*$'\t'}"
  read -r mode object_type recorded extra <<<"$metadata"
  if [ "$mode" != "160000" ] || [ "$object_type" != "commit" ] || \
     [[ ! "$recorded" =~ ^[0-9a-f]{40}$ ]] || [ -n "${extra:-}" ] || \
     [ "$listed_path" != "$path" ]; then
    problems+=("MISSING-GITLINK  $path  (no exact 160000 commit gitlink recorded at HEAD)")
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

  # Matching HEAD is not sufficient: tracked edits or untracked files change
  # the code a local build consumes without changing the superproject gitlink.
  # Include nested-submodule state and fail closed if Git cannot classify it.
  # Only success and empty/nonempty are consumed: normal still reports every
  # untracked tree as dirty without enumerating each descendant in the output.
  if ! dirty="$(git -C "$path" status --porcelain=v1 --untracked-files=normal --ignore-submodules=none 2>/dev/null)"; then
    problems+=("PIN-STATUS-FAILED  $path  pin=$recorded  (could not audit working-tree content)")
    fail=1
    continue
  fi
  if [ -n "$dirty" ]; then
    problems+=("PIN-DIRTY        $path  pin=$recorded  (working-tree content differs from the committed pin)")
    fail=1
    continue
  fi

  # `git status` does not report an uninitialized nested submodule as dirty.
  # Audit the recursive submodule state explicitly; every row must have Git's
  # single-space "initialized at the recorded commit" prefix and a full SHA.
  if ! nested_rows="$(git -C "$path" submodule status --recursive 2>/dev/null)"; then
    problems+=("PIN-NESTED-STATUS-FAILED  $path  pin=$recorded  (could not audit nested submodules)")
    fail=1
    continue
  fi
  nested_bad=0
  while IFS= read -r nested_row; do
    [ -z "$nested_row" ] && continue
    if [[ ! "$nested_row" =~ ^\ [0-9a-f]{40}\  ]]; then
      nested_bad=1
      break
    fi
  done <<<"$nested_rows"
  if [ "$nested_bad" -ne 0 ]; then
    problems+=("PIN-NESTED-DRIFT  $path  pin=$recorded  (nested submodule is uninitialized, conflicted, or off its recorded commit)")
    fail=1
    continue
  fi

  echo "ok  $path  @ $recorded"
done <<<"$module_rows"

if [ "$fail" -ne 0 ]; then
  echo
  echo "PIN COHERENCE FAILED (gap G3):"
  for p in "${problems[@]}"; do echo "  - $p"; done
  echo
  echo "Resolve each before relying on any 'proven' claim. See WS-0.1 in the completion plan."
  if [ -f scripts/submodule_sync.sh ]; then
    echo
    echo "PIN-DRIFT rows above are one word each; they do not say which direction."
    echo "For the BEHIND / AHEAD / DIVERGENT classification, the commit counts, and"
    echo "the exact restore command for the subset that is provably lossless:"
    echo
    echo "    scripts/submodule_sync.sh"
    echo
    echo "Do not blanket-run 'git submodule update': a worktree that is AHEAD of its"
    echo "pin holds commits the pin does not, and a blanket update moves off them."
    echo "submodule_sync.sh will restore an AHEAD/DIVERGENT module only when it has"
    echo "proved that EVERY commit the pin lacks is held by a durable ref, and it"
    echo "prints which ref holds which commit when it does."
  fi
  exit 1
fi

echo
echo "PIN COHERENCE OK: every submodule is at its recorded pin and every pin resolves."
