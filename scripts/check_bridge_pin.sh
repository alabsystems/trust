#!/usr/bin/env bash
# check_bridge_pin.sh — enforce the BRIDGE RULE invariant automatically.
#
# The Lean↔Clean bridge is verified against VENDORED .olean artifacts. Both
# halves of that replay are pinned submodules: trust-ir SUPPLIES the Lean
# semantics the artifacts were built from, and clean SUPPLIES the olean reader
# that decodes them plus the kernel that admits the decoded declarations. A pin
# bump on either side without restaging the manifest changes what the bridge
# replays while the recorded provenance says otherwise — the PinDrift
# fail-closed then reds the bridge gate at push time. This has been repaired by
# hand ~10x in a single session; this script makes it one command.
#
#   default (--check): exit 0 iff, for BOTH first-party/trust-ir and
#     first-party/clean, the STAGE-0 INDEX gitlink EQUALS the corresponding
#     exactly-one commit field in the INDEX copy of
#     crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml AND the
#     initialized, clean checkout is at that same commit.
#     Unmerged/missing/malformed/dirty state fails closed. Cheap; no toolchain.
#
#   --fix: initialize/synchronize the checkouts to the indexed pins, then, when
#     the manifest itself drifts, run `regen-trustir-oleans.sh --write` (needs a
#     Lean toolchain via elan or $LEAN_TOOLCHAIN_BIN). Leaves regenerated files
#     staged-ready (does NOT commit).
#
# Run --check in CI/pre-push; run --fix after any trust-ir or clean pin bump.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml"

# Each row: <gitlink path>|<manifest provenance key>. Both sides of the replay
# are load-bearing, so both are invariants — the reader is not "just tooling".
PINNED_SIDES=(
  "first-party/trust-ir|trustir_commit"
  "first-party/clean|clean_commit"
)

case "${1:---check}" in
  --check) MODE="check" ;;
  --fix) MODE="fix" ;;
  *) echo "usage: scripts/check_bridge_pin.sh [--check|--fix]" >&2; exit 2 ;;
esac
if [[ "$#" -gt 1 ]]; then
  echo "usage: scripts/check_bridge_pin.sh [--check|--fix]" >&2
  exit 2
fi

index_pin() {
  local gitlink="$1"
  if [[ -n "$(git -C "$ROOT" ls-files --unmerged -- "$gitlink")" ]]; then
    echo "BRIDGE PIN INVALID: $gitlink has unmerged index stages" >&2
    return 1
  fi
  local rows count mode object stage path
  rows="$(git -C "$ROOT" ls-files --stage -- "$gitlink")"
  count="$(printf '%s\n' "$rows" | awk 'NF { n += 1 } END { print n + 0 }')"
  if [[ "$count" != 1 ]]; then
    echo "BRIDGE PIN INVALID: expected exactly one stage-0 gitlink for $gitlink; found $count" >&2
    return 1
  fi
  IFS=$' \t' read -r mode object stage path <<< "$rows"
  if [[ "$mode" != 160000 || "$stage" != 0 || "$path" != "$gitlink" \
      || ! "$object" =~ ^[0-9a-f]{40}$ ]]; then
    echo "BRIDGE PIN INVALID: malformed index entry for $gitlink" >&2
    return 1
  fi
  printf '%s\n' "$object"
}

manifest_commit_from_text() {
  local text="$1" key="$2" count value
  count="$(printf '%s\n' "$text" \
    | awk -v key="$key" '$0 ~ "^[[:space:]]*" key "[[:space:]]*=" { n += 1 } END { print n + 0 }')"
  if [[ "$count" != 1 ]]; then
    echo "BRIDGE PIN INVALID: expected exactly one $key in $MANIFEST; found $count" >&2
    return 1
  fi
  value="$(printf '%s\n' "$text" | sed -n \
    "s/^[[:space:]]*$key[[:space:]]*=[[:space:]]*\"\([0-9a-f][0-9a-f]*\)\"[[:space:]]*\$/\1/p")"
  if [[ ! "$value" =~ ^[0-9a-f]{40}$ ]]; then
    echo "BRIDGE PIN INVALID: $key in $MANIFEST is not one lowercase 40-hex commit" >&2
    return 1
  fi
  printf '%s\n' "$value"
}

index_manifest_text() {
  if ! git -C "$ROOT" show ":$MANIFEST" 2>/dev/null; then
    echo "BRIDGE PIN INVALID: $MANIFEST is missing or unmerged in the index" >&2
    return 1
  fi
}

worktree_manifest_text() {
  if [[ ! -f "$ROOT/$MANIFEST" ]]; then
    echo "BRIDGE PIN INVALID: regenerated worktree manifest $MANIFEST is missing" >&2
    return 1
  fi
  cat "$ROOT/$MANIFEST"
}

checkout_commit() {
  local gitlink="$1" value dirty
  # `git -C empty/submodule/path rev-parse` otherwise walks upward and can
  # accidentally report the superproject HEAD as the checkout commit.
  if [[ ! -e "$ROOT/$gitlink/.git" ]]; then
    echo "BRIDGE PIN INVALID: $gitlink is not an initialized git checkout" >&2
    return 2
  fi
  if ! value="$(git -C "$ROOT/$gitlink" rev-parse --verify HEAD 2>/dev/null)"; then
    echo "BRIDGE PIN INVALID: initialized checkout for $gitlink has no valid HEAD" >&2
    return 1
  fi
  if [[ ! "$value" =~ ^[0-9a-f]{40}$ ]]; then
    echo "BRIDGE PIN INVALID: checkout HEAD for $gitlink is not a 40-hex commit" >&2
    return 1
  fi
  if ! dirty="$(git -C "$ROOT/$gitlink" status --porcelain=v1 --untracked-files=all 2>/dev/null)"; then
    echo "BRIDGE PIN INVALID: cannot inspect checkout state for $gitlink" >&2
    return 1
  fi
  if [[ -n "$dirty" ]]; then
    echo "BRIDGE PIN INVALID: $gitlink checkout has tracked or untracked changes" >&2
    echo "  (bridge replay requires the exact clean bytes of the pinned commit)" >&2
    return 1
  fi
  printf '%s\n' "$value"
}

INDEX_MANIFEST="$(index_manifest_text)"

DRIFTED=0
declare -a PINS MANS
for side in "${PINNED_SIDES[@]}"; do
  gitlink="${side%%|*}"
  key="${side##*|}"

  pin="$(index_pin "$gitlink")"
  man="$(manifest_commit_from_text "$INDEX_MANIFEST" "$key")"
  if checkout="$(checkout_commit "$gitlink")"; then
    :
  else
    checkout_status="$?"
    # `--fix` is allowed to initialize a missing checkout. Every other failure,
    # especially a dirty initialized checkout, remains fail-closed so no local
    # bytes are overwritten or mistaken for the pinned source.
    if [[ "$MODE" == "fix" && "$checkout_status" == 2 ]]; then
      checkout="uninitialized"
    else
      exit "$checkout_status"
    fi
  fi

  PINS+=("$pin")
  MANS+=("$man")

  if [[ "$pin" != "$man" ]]; then
    echo "BRIDGE PIN DRIFT: indexed $gitlink pin=$pin  !=  indexed manifest $key=$man"
    echo "  (stage the exact gitlink and its regenerated manifest together)"
    DRIFTED=1
  fi
  if [[ "$checkout" != "$man" ]]; then
    echo "BRIDGE CHECKOUT DRIFT: $gitlink checkout=$checkout  !=  indexed manifest $key=$man"
    echo "  (the bridge replays against checkout bytes, so this cannot be ignored)"
    DRIFTED=1
  fi
done

if [[ "$DRIFTED" == 0 ]]; then
  echo "BRIDGE PIN OK: committed pins == manifest == clean checkouts"
  for index in "${!PINNED_SIDES[@]}"; do
    echo "  ${PINNED_SIDES[$index]%%|*} @ ${PINS[$index]}"
  done
  exit 0
fi

if [[ "$MODE" != "fix" ]]; then
  echo "  run: scripts/check_bridge_pin.sh --fix"
  exit 1
fi

echo "  --fix: checking out the indexed pins…"
NEEDS_REGEN=0
for index in "${!PINNED_SIDES[@]}"; do
  gitlink="${PINNED_SIDES[$index]%%|*}"
  git -C "$ROOT" submodule update --init --checkout -- "$gitlink"
  on_disk="$(checkout_commit "$gitlink")"
  if [[ "$on_disk" != "${PINS[$index]}" ]]; then
    echo "BRIDGE PIN INVALID: submodule update selected $on_disk instead of indexed ${PINS[$index]} for $gitlink" >&2
    exit 1
  fi
  if [[ "${PINS[$index]}" != "${MANS[$index]}" ]]; then
    NEEDS_REGEN=1
  fi
done

if [[ "$NEEDS_REGEN" == 0 ]]; then
  echo "BRIDGE PIN FIXED: checkouts synchronized to the indexed pins and manifest"
  exit 0
fi

echo "  --fix: regenerating oleans for the indexed pins…"
"$ROOT/scripts/regen-trustir-oleans.sh" --write

WORKTREE_MANIFEST="$(worktree_manifest_text)"
STILL_DRIFTED=0
for index in "${!PINNED_SIDES[@]}"; do
  gitlink="${PINNED_SIDES[$index]%%|*}"
  key="${PINNED_SIDES[$index]##*|}"
  man2="$(manifest_commit_from_text "$WORKTREE_MANIFEST" "$key")"
  if [[ "${PINS[$index]}" != "$man2" ]]; then
    echo "BRIDGE PIN STILL DRIFTED after regen: indexed $gitlink pin=${PINS[$index]} worktree manifest $key=$man2 — investigate" >&2
    STILL_DRIFTED=1
  fi
done
if [[ "$STILL_DRIFTED" != 0 ]]; then
  exit 1
fi

echo "BRIDGE PIN FIXED: worktree manifest regenerated"
echo "  stage $MANIFEST and all regenerated .olean files, then run --check"
exit 0
