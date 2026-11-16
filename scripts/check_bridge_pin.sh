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
#     initialized, clean checkout is at that same commit, AND every olean the
#     index manifest lists is staged with exactly its recorded sha256, AND every
#     platform table names the trust-ir revision its bytes were built from, one
#     of them being the manifest's trustir_commit. A platform built from another
#     revision is DISCLOSED (its consumer refuses it: `PlatformStale`), not
#     passed off as current. Unmerged/missing/malformed/dirty state fails
#     closed. Legacy checks are toolchain-free. A source_reuse record additionally
#     invokes the shared minimal Rust input verifier (no Clean proof-stack build).
#
#     Why digests (2026-09-24): a commit string alone let a regeneration on one
#     platform carry another platform's bytes forward under the new commit —
#     Linux oleans built from trust-ir 00180257 sat under trustir_commit
#     29744d5f and this gate said OK.
#
#   --fix: initialize/synchronize the checkouts to the indexed pins, then, when
#     the manifest itself drifts, run `regen-trustir-oleans.sh --write` (needs a
#     Lean toolchain via elan or $LEAN_TOOLCHAIN_BIN). Leaves regenerated files
#     staged-ready (does NOT commit). In a linked worktree, both checkouts must
#     already be clean and at their indexed pins; no submodule configuration is
#     changed there.
#
# Run --check in CI/pre-push; run --fix after any trust-ir or clean pin bump.
#
# WHICH TREE IS JUDGED (2026-09-28). A push publishes the pushed commits'
# trees, not the index or the submodule checkouts. With TRUST_PUSHED_REFS set
# and non-blank (the pre-push hooks export git's
# `<local_ref> <local_sha> <remote_ref> <remote_sha>` lines), `--check` judges
# every non-deletion pushed sha's own tree and nothing else: its two gitlinks,
# its MANIFEST.toml blob, and each listed olean hashed from the tree's blob; each
# pin must be a commit in that submodule's object store (the checkout's, or the
# module store under the git dir when this worktree never initialized it). An
# unreadable pin is a refusal, never a pass. Deletions have no tree and judge
# nothing (a deletion-only push prints `SKIPPED:`); a malformed line exits 2.
# The submodule checkouts are local hygiene, not a property of the push, so
# their state is a `BRIDGE CHECKOUT WARN` line there, never a refusal. Until
# then the lane judged the index whatever was pushed: a non-HEAD ref with a
# wrong manifest or a corrupted olean passed, and so did HEAD with its repair
# only staged, while an untracked file in first-party/clean or a staged WIP
# gitlink refused a clean push (docs/issues/2026-09-28-push-lanes-judge-the-
# checkout-not-the-push.md, case B). With the variable unset or blank the
# standing reading above is unchanged; `--fix` always ignores it.
#
# FINDING KEYS (2026-11-09; docs/DECISION_QUEUE.md BRIDGE-PIN-FINDING-KEYS-
# 2026-11-09 and BRIDGE-PIN-FINDINGS-1). A refused push reading prints one
# `FINDING: <key>` line per tree-local cause, and `FINDINGS: complete` only
# when every judged tree ran every check to its end and every cause was keyed,
# so scripts/hooks/pre-push and `land_gate.py push-rows` grade a red the
# destination already carries INHERITED (the hook's INHERITED-RED) and FAIL a
# push that adds or changes one. A key names the identities that define its
# cause and nothing about the push (no pushed sha, no ref, no label):
#   PIN-DRIFT <gitlink> <pin> <manifest key> <manifest commit>
#   MISSING-GITLINK <gitlink>          NON-GITLINK <gitlink> <mode:type:oid>
#   DIGEST-MISSING <path> <recorded>   DIGEST-MODE <path> <mode:type:oid> <recorded>
#   DIGEST-MISMATCH <path> <actual sha256> <recorded sha256>
#   PLATFORM-NO-CURRENT <trustir_commit> <platform:built_from>...
# Unkeyed, so the marker is withheld and the red stays FAIL: a pushed sha,
# manifest, olean blob or pin this clone cannot read (a property of the local
# stores, not of the tree), a missing, non-regular, malformed or duplicated
# manifest field, a platform with no provenance, a [source_reuse] tree that is
# refused or red, and any key token outside [A-Za-z0-9_./:+=-]. A disclosed
# PLATFORM STALE line is not a refusal. The standing reading prints no keys:
# it reads the index and the checkouts, which no replay against a destination
# revision reproduces, and the hook never inherits a working-tree reader.
set -euo pipefail
# A hook or caller's repository/index must not override any named checkout.
# Keep the same isolation for standing checks, repairs and pushed-tree checks.
unset $(git rev-parse --local-env-vars)
# say() prefixes LABEL; only the push reading sets it, never the environment.
LABEL=""

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="crates/trust-clean/fixtures/trustir-oleans/MANIFEST.toml"
MANIFEST_DIR="${MANIFEST%/MANIFEST.toml}"

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

# Reuse is judged by the same Rust implementation as the runtime gate. It
# compares actual anchor/source objects; selected fields alone grant nothing.
source_reuse_selection() {
  local text="$1" subject="$2" result marker extra tool
  REUSE_PRESENT=0 REUSE_IR="" REUSE_CLEAN=""
  if ! printf '%s\n' "$text" | grep -q '^\[source_reuse\]$'; then return 0; fi
  tool="${TARGO:-targo}"
  # The checkout's own admission script: it is not on PATH (a bare `build-slot`
  # failed every push profile that did not put scripts/ there, 2026-11-06).
  if ! result="$("$ROOT/scripts/build-slot" -- "$tool" --unverified run --offline --locked --quiet \
      --manifest-path "$ROOT/Cargo.toml" -p trust-bridge-closure --no-default-features --bin bridge_source_reuse \
      -- --verify-source-reuse "$ROOT" "$subject")"; then
    say "BRIDGE SOURCE REUSE REFUSED: complete anchored input equality was not established"
    return 1
  fi
  read -r marker REUSE_IR REUSE_CLEAN REUSE_ANCHOR extra <<< "$result"
  if [[ "$marker" != SOURCE_REUSE || -n "${extra:-}" || ! "$REUSE_IR" =~ ^[0-9a-f]{40}$ \
      || ! "$REUSE_CLEAN" =~ ^[0-9a-f]{40}$ || ! "$REUSE_ANCHOR" =~ ^[0-9a-f]{40}$ ]]; then
    say "BRIDGE SOURCE REUSE REFUSED: malformed validator result"
    return 1
  fi
  REUSE_PRESENT=1
  say "BRIDGE SOURCE REUSE: selected $REUSE_IR / $REUSE_CLEAN; original artifact anchor $REUSE_ANCHOR retained"
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
  local gitlink="$1" value dirty top expected
  # `git -C empty/submodule/path rev-parse` otherwise walks upward and can
  # accidentally report the superproject HEAD as the checkout commit.
  if [[ ! -e "$ROOT/$gitlink/.git" ]]; then
    echo "BRIDGE PIN INVALID: $gitlink is not an initialized git checkout" >&2
    return 2
  fi
  if ! top="$(git -C "$ROOT/$gitlink" rev-parse --show-toplevel 2>/dev/null)" \
      || ! top="$(cd "$top" && pwd -P)" \
      || ! expected="$(cd "$ROOT/$gitlink" && pwd -P)" \
      || [[ "$top" != "$expected" ]]; then
    echo "BRIDGE PIN INVALID: $gitlink Git worktree is not bound to its source directory" >&2
    return 1
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

sha256_stdin() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{ print $1 }'
  else
    shasum -a 256 | awk '{ print $1 }'
  fi
}

# One verdict line. LABEL (the pushed ref(s) being judged) prefixes it in the
# push reading; the standing reading has no label and prints the line as is.
say() {
  if [[ -n "${LABEL:-}" ]]; then
    echo "[$LABEL] $*"
  else
    echo "$*"
  fi
}

# The manifest as rows: `F<TAB><path under MANIFEST_DIR><TAB><sha256>` per
# listed olean, then `P<TAB><platform><TAB><built_from_trustir_commit>` per
# platform table. One parser for both readings.
manifest_rows() {
  awk '
  function unq(v) {
    sub(/^[[:space:]]+/, "", v); sub(/[[:space:]]+$/, "", v)
    sub(/^"/, "", v); sub(/"$/, "", v); return v
  }
  /^[[:space:]]*#/ || /^[[:space:]]*$/ { next }
  /^\[files\]$/ { sect = "shared"; next }
  /^\[platforms\."[^"]+"\]$/ {
    t = $0; sub(/^\[platforms\."/, "", t); sub(/"\]$/, "", t)
    sect = "pmeta"; plat = t; built[plat] = ""; order[++n] = plat; next }
  /^\[platforms\."[^"]+"\.files\]$/ {
    t = $0; sub(/^\[platforms\."/, "", t); sub(/"\.files\]$/, "", t)
    sect = "pfiles"; plat = t; next }
  /^\[/ { sect = ""; next }
  {
    split($0, kv, "=")
    key = unq(kv[1]); val = unq(kv[2])
    if (sect == "shared") printf "F\t%s\t%s\n", key, val
    else if (sect == "pfiles") printf "F\tplatform/%s/%s\t%s\n", plat, key, val
    else if (sect == "pmeta" && key == "built_from_trustir_commit") built[plat] = val
  }
  END { for (i = 1; i <= n; i++) printf "P\t%s\t%s\n", order[i], built[order[i]] }
'
}

# `<mode> <type> <object>` of exactly <path> in committed <tree>, or nothing
# when the tree has no entry there. Literal pathspec, and the listed path must
# equal <path> byte for byte, so a manifest key cannot glob or climb.
tree_entry() {
  local tree="$1" path="$2" listing
  listing="$(GIT_LITERAL_PATHSPECS=1 git -C "$ROOT" -c core.quotePath=false \
    ls-tree --full-tree "$tree" -- "$path")" || return 1
  WANT="$path" awk -F'\t' '$2 == ENVIRON["WANT"] { print $1 }' <<< "$listing"
}

# Every olean the manifest text $1 lists must be present at its path with
# exactly the recorded sha256, and every platform table must say what it was
# built from; $2 is the manifest's trustir_commit. Without $3 each olean is the
# INDEX entry (the standing reading); with $3 it is that committed tree's blob.
# With $4=worktree, check generated files on disk instead of indexed entries.
# Accumulates DIGEST_BAD, FILES_CHECKED, MATCHING_PLATFORM and PLATFORM_COUNT.
# In the push reading ($tree non-empty), also records tree-local FINDING keys or
# marks BP_UNKEYED=1 (CONSTELLATION-ALL-FINDINGS / INHERITED-RED).
BP_UNKEYED=0
BP_FINDINGS=()
BP_SAFE_TOKEN='^[A-Za-z0-9_./:+=-]+$'
bp_finding() {
  local tok
  for tok in "$@"; do
    if [[ -z "$tok" || ! "$tok" =~ $BP_SAFE_TOKEN ]]; then
      BP_UNKEYED=1
      return 0
    fi
  done
  BP_FINDINGS+=("$*")
}

digest_rows() {
  local text="$1" trustir_man="$2" tree="${3:-}" kind a b entry oid actual mode type listing=""
  local source="${4:-index}" file parent base
  # Every platform's `<name>:<built_from_trustir_commit>`, in manifest order:
  # the identities a PLATFORM-NO-CURRENT key names (BRIDGE-PIN-FINDINGS-1).
  local -a platform_ids=()
  if [[ -n "$tree" ]]; then
    # One listing of the olean directory; each manifest key must equal a listed
    # path byte for byte, so a key cannot glob or climb out of the directory.
    if ! listing="$(git -C "$ROOT" -c core.quotePath=false \
        ls-tree -r --full-tree "$tree" -- "$MANIFEST_DIR")"; then
      say "BRIDGE DIGEST UNREADABLE: cannot list $MANIFEST_DIR in the pushed tree"
      DIGEST_BAD=1
      BP_UNKEYED=1
      return 0
    fi
  fi
  while IFS=$'\t' read -r kind a b; do
    case "$kind" in
      F)
        FILES_CHECKED=$((FILES_CHECKED + 1))
        if [[ "$source" == worktree ]]; then
          file="$ROOT/$MANIFEST_DIR/$a"
          if [[ ! -f "$file" || -L "$file" ]] \
              || ! parent="$(cd "$(dirname "$file")" && pwd -P)" \
              || ! base="$(cd "$ROOT/$MANIFEST_DIR" && pwd -P)" \
              || [[ "$parent/" != "$base/"* ]]; then
            say "BRIDGE DIGEST MISSING: $MANIFEST_DIR/$a is not a contained regular generated file"
            DIGEST_BAD=1
            continue
          fi
          if ! actual="$(sha256_stdin < "$file")"; then
            say "BRIDGE DIGEST UNREADABLE: $MANIFEST_DIR/$a generated bytes are unreadable"
            DIGEST_BAD=1
          elif [[ "$actual" != "$b" ]]; then
            say "BRIDGE DIGEST MISMATCH: $MANIFEST_DIR/$a generated sha256=$actual  !=  manifest $b"
            DIGEST_BAD=1
          fi
          continue
        fi
        if [[ -z "$tree" ]]; then
          entry="$(git -C "$ROOT" ls-files --stage -- "$MANIFEST_DIR/$a")"
          if [[ -z "$entry" ]]; then
            say "BRIDGE DIGEST MISSING: $MANIFEST_DIR/$a is listed in the manifest but not staged"
            DIGEST_BAD=1
            continue
          fi
          oid="$(awk '{ print $2 }' <<< "$entry")"
          actual="$(git -C "$ROOT" cat-file blob "$oid" | sha256_stdin)"
          if [[ "$actual" != "$b" ]]; then
            say "BRIDGE DIGEST MISMATCH: $MANIFEST_DIR/$a staged sha256=$actual  !=  manifest $b"
            DIGEST_BAD=1
          fi
          continue
        fi
        entry="$(WANT="$MANIFEST_DIR/$a" awk -F'\t' '$2 == ENVIRON["WANT"] { print $1 }' <<< "$listing")"
        if [[ -z "$entry" ]]; then
          say "BRIDGE DIGEST MISSING: $MANIFEST_DIR/$a is listed in the manifest but absent from the pushed tree"
          DIGEST_BAD=1
          bp_finding DIGEST-MISSING "$MANIFEST_DIR/$a" "$b"
          continue
        fi
        read -r mode type oid <<< "$entry"
        if [[ "$type" != blob || ( "$mode" != 100644 && "$mode" != 100755 ) ]]; then
          say "BRIDGE DIGEST MISSING: $MANIFEST_DIR/$a is not a regular file in the pushed tree (mode $mode)"
          DIGEST_BAD=1
          bp_finding DIGEST-MODE "$MANIFEST_DIR/$a" "$mode:$type:$oid" "$b"
          continue
        fi
        if ! actual="$(git -C "$ROOT" cat-file blob "$oid" | sha256_stdin)"; then
          say "BRIDGE DIGEST UNREADABLE: blob $oid of $MANIFEST_DIR/$a is not readable here"
          DIGEST_BAD=1
          BP_UNKEYED=1
          continue
        fi
        if [[ "$actual" != "$b" ]]; then
          say "BRIDGE DIGEST MISMATCH: $MANIFEST_DIR/$a pushed sha256=$actual  !=  manifest $b"
          DIGEST_BAD=1
          bp_finding DIGEST-MISMATCH "$MANIFEST_DIR/$a" "$actual" "$b"
        fi
        ;;
      P)
        PLATFORM_COUNT=$((PLATFORM_COUNT + 1))
        platform_ids+=("$a:$b")
        if [[ ! "$b" =~ ^[0-9a-f]{40}$ ]]; then
          say "BRIDGE PLATFORM PROVENANCE MISSING: platform $a names no built_from_trustir_commit (got '${b}')"
          DIGEST_BAD=1
          [[ -z "$tree" ]] || BP_UNKEYED=1
        elif [[ "$b" == "$trustir_man" ]]; then
          MATCHING_PLATFORM=1
        else
          say "BRIDGE PLATFORM STALE (disclosed): $a bytes were built from trust-ir $b, not trustir_commit $trustir_man;"
          say "  replay on $a refuses them (PlatformStale). Rebuild there: scripts/regen-trustir-oleans.sh --write"
        fi
        ;;
    esac
  done < <(printf '%s\n' "$text" | manifest_rows)
  if [[ "$PLATFORM_COUNT" -gt 0 && "$MATCHING_PLATFORM" == 0 ]]; then
    say "BRIDGE PLATFORM PROVENANCE: no platform's bytes were built from trustir_commit $trustir_man"
    say "  (the manifest would name a revision no vendored byte came from)"
    DIGEST_BAD=1
    # The cause is the manifest's trustir_commit AND what each platform says
    # it was built from: a push that rewrites any platform's provenance moves
    # the key, so it cannot ride in under the destination's red.
    [[ -z "$tree" ]] || bp_finding PLATFORM-NO-CURRENT "$trustir_man" "${platform_ids[@]}"
  fi
}

# ---------------------------------------------------------------------------
# The push reading (TRUST_PUSHED_REFS set and non-blank, `--check` only).
# ---------------------------------------------------------------------------

HEX_SHA='^([0-9a-f]{40}|[0-9a-f]{64})$'

# The git dirs that may hold submodule <gitlink>'s objects: its checkout's own,
# then the module store under this worktree's git dir and under the common git
# dir (a linked worktree that never ran `submodule update` has only the
# latter). The module name comes from the judged tree's .gitmodules, falling
# back to the path, which is git's default name.
submodule_stores() {
  local gitlink="$1" tree="$2" name="" key value top base
  if [[ -e "$ROOT/$gitlink/.git" ]] \
      && top="$(git -C "$ROOT/$gitlink" rev-parse --show-toplevel 2>/dev/null)" \
      && [[ "$(cd "$top" && pwd -P)" == "$(cd "$ROOT/$gitlink" && pwd -P)" ]]; then
    git -C "$ROOT/$gitlink" rev-parse --absolute-git-dir 2>/dev/null || true
  fi
  while read -r key value; do
    if [[ "$value" == "$gitlink" ]]; then
      name="${key#submodule.}"
      name="${name%.path}"
      break
    fi
  done < <(git -C "$ROOT" config --blob "$tree:.gitmodules" \
      --get-regexp '^submodule\..*\.path$' 2>/dev/null || true)
  # Git itself refuses a module name that climbs; so does this lookup.
  case "/$name/" in
    */../*) name="" ;;
  esac
  [[ -n "$name" ]] || name="$gitlink"
  for base in "$(git -C "$ROOT" rev-parse --absolute-git-dir)" \
      "$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir)"; do
    if [[ -d "$base/modules/$name" ]]; then
      printf '%s\n' "$base/modules/$name"
    fi
  done
}

# Whether <pin> is a commit in some local store of submodule <gitlink>.
pin_readable() {
  local gitlink="$1" pin="$2" tree="$3" store
  while IFS= read -r store; do
    [[ -n "$store" ]] || continue
    # The object itself must be a commit: no `^{commit}` peeling, so a gitlink
    # naming an annotated tag is refused (a checkout of it lands on the
    # tagged commit, which is not the pin the manifest names).
    if [[ "$(git --no-replace-objects --git-dir="$store" --bare --work-tree="$store" cat-file -t "$pin" 2>/dev/null)" == commit ]]; then
      return 0
    fi
  done < <(submodule_stores "$gitlink" "$tree")
  return 1
}

# Judge one committed tree. Sets TREE_BAD (0/1) and appends each side's pin to
# TREE_PIN_<index> (for the checkout hygiene notes); prints its verdict lines.
judge_tree() {
  local tree="$1" entry mode type oid text index side gitlink key pin man trustir_man=""
  local -a pins
  LABEL="$2"
  TREE_BAD=0
  if ! entry="$(tree_entry "$tree" "$MANIFEST")"; then
    say "BRIDGE PIN INVALID: cannot list $MANIFEST in the pushed tree"
    TREE_BAD=1
    BP_UNKEYED=1
    return 0
  fi
  if [[ -z "$entry" ]]; then
    say "BRIDGE PIN INVALID: $MANIFEST is missing from the pushed tree"
    TREE_BAD=1
    BP_UNKEYED=1
    return 0
  fi
  read -r mode type oid <<< "$entry"
  if [[ "$type" != blob || ( "$mode" != 100644 && "$mode" != 100755 ) ]]; then
    say "BRIDGE PIN INVALID: $MANIFEST is not a regular file in the pushed tree (mode $mode)"
    TREE_BAD=1
    BP_UNKEYED=1
    return 0
  fi
  if ! text="$(git -C "$ROOT" cat-file blob "$oid")"; then
    say "BRIDGE PIN INVALID: blob $oid of $MANIFEST is not readable here"
    TREE_BAD=1
    BP_UNKEYED=1
    return 0
  fi
  if ! source_reuse_selection "$text" "${3:-$tree}"; then
    TREE_BAD=1
    BP_UNKEYED=1
    return 0
  fi
  pins=()
  for index in "${!PINNED_SIDES[@]}"; do
    side="${PINNED_SIDES[$index]}"
    gitlink="${side%%|*}"
    key="${side##*|}"
    pin=""
    man=""
    if ! entry="$(tree_entry "$tree" "$gitlink")"; then
      say "BRIDGE PIN INVALID: cannot list $gitlink in the pushed tree"
      TREE_BAD=1
      BP_UNKEYED=1
    elif [[ -z "$entry" ]]; then
      say "BRIDGE PIN INVALID: the pushed tree has no gitlink at $gitlink"
      TREE_BAD=1
      bp_finding MISSING-GITLINK "$gitlink"
    else
      read -r mode type oid <<< "$entry"
      if [[ "$mode" != 160000 || "$type" != commit || ! "$oid" =~ ^[0-9a-f]{40}$ ]]; then
        say "BRIDGE PIN INVALID: $gitlink in the pushed tree is not a gitlink (mode $mode, $type)"
        TREE_BAD=1
        bp_finding NON-GITLINK "$gitlink" "$mode:$type:$oid"
      else
        pin="$oid"
      fi
    fi
    if ! man="$(manifest_commit_from_text "$text" "$key" 2>&1)"; then
      say "$man (pushed tree)"
      man=""
      TREE_BAD=1
      BP_UNKEYED=1
    fi
    if [[ "$index" == 0 ]]; then
      trustir_man="$man"
    fi
    if [[ "$REUSE_PRESENT" == 1 ]]; then
      if [[ "$index" == 0 ]]; then man="$REUSE_IR"; else man="$REUSE_CLEAN"; fi
    fi
    pins+=("$pin")
    if [[ -n "$pin" && -n "$man" && "$pin" != "$man" ]]; then
      say "BRIDGE PIN DRIFT: pushed $gitlink pin=$pin  !=  pushed manifest $key=$man"
      say "  (commit the exact gitlink and its regenerated manifest together)"
      TREE_BAD=1
      bp_finding PIN-DRIFT "$gitlink" "$pin" "$key" "$man"
    fi
    if [[ -n "$pin" ]] && ! pin_readable "$gitlink" "$pin" "$tree"; then
      say "BRIDGE PIN UNREADABLE: pushed $gitlink pin=$pin is not a commit in any local store of that submodule"
      say "  (fetch it into $gitlink; a pin this gate cannot read is not a pass)"
      TREE_BAD=1
      BP_UNKEYED=1
    fi
    if [[ -n "$pin" ]]; then
      eval "TREE_PIN_$index+=(\"\$pin\")"
    fi
  done
  if [[ "$REUSE_PRESENT" == 1 && "$TREE_BAD" != 0 ]]; then
    BP_UNKEYED=1
  fi
  if [[ -z "$trustir_man" ]]; then
    BP_UNKEYED=1
    return 0
  fi
  DIGEST_BAD=0
  FILES_CHECKED=0
  MATCHING_PLATFORM=0
  PLATFORM_COUNT=0
  digest_rows "$text" "$trustir_man" "$tree"
  if [[ "$DIGEST_BAD" != 0 ]]; then
    say "  the vendored bytes do not match their manifest; regenerate with scripts/regen-trustir-oleans.sh --write"
    TREE_BAD=1
  fi
  if [[ "$TREE_BAD" == 0 ]]; then
    say "BRIDGE PIN OK: pushed pins == pushed manifest; $FILES_CHECKED olean digest(s) match in the pushed tree"
    for index in "${!PINNED_SIDES[@]}"; do
      say "  ${PINNED_SIDES[$index]%%|*} @ ${pins[$index]}"
    done
  fi
  return 0
}

judge_pushed() {
  local line lref lsha rref rsha extra tree subject subject_tree i found deletions=0 names="" bad=0
  local index gitlink state pin seen identity
  local -a trees labels unresolved subjects identities
  BP_UNKEYED=0
  BP_FINDINGS=()
  trees=()
  labels=()
  unresolved=()
  subjects=() identities=()
  while IFS= read -r line || [[ -n "$line" ]]; do
    [[ "$line" =~ [^[:space:]] ]] || continue
    lref="" lsha="" rref="" rsha="" extra=""
    read -r lref lsha rref rsha extra <<< "$line"
    if [[ -n "$extra" || -z "$rsha" || ! "$lsha" =~ $HEX_SHA || ! "$rsha" =~ $HEX_SHA ]]; then
      echo "BRIDGE PIN INVALID: malformed TRUST_PUSHED_REFS line '$line';" >&2
      echo "  expected \`<local_ref> <local_sha> <remote_ref> <remote_sha>\`" >&2
      exit 2
    fi
    if [[ "$lsha" =~ ^0+$ ]]; then
      deletions=$((deletions + 1))
      continue
    fi
    if ! tree="$(git --no-replace-objects -C "$ROOT" rev-parse --verify --quiet "$lsha^{tree}" 2>/dev/null)"; then
      unresolved+=("[$lref ${lsha:0:12}] BRIDGE PIN INVALID: pushed object $lsha does not name a tree here; a push this gate cannot read is not a pass")
      names="$names${names:+, }$lref ${lsha:0:12}"
      continue
    fi
    names="$names${names:+, }$lref ${lsha:0:12}"
    # Reuse also judges the anchor's ancestry. Distinct commit subjects with
    # an equal tree therefore remain distinct; legacy trees still deduplicate.
    identity="$tree"
    subject="$lsha"
    if git --no-replace-objects -C "$ROOT" show "$tree:$MANIFEST" 2>/dev/null | grep -q '^\[source_reuse\]$'; then
      # An annotated ROOT release tag names a commit whose ancestry is the
      # reuse subject. Preserve its raw pushed OID in labels. Gitlinks below
      # remain strict raw commit objects and are never tag-peeled.
      if ! subject="$(git --no-replace-objects -C "$ROOT" rev-parse --verify --quiet "$lsha^{commit}" 2>/dev/null)" \
          || ! subject_tree="$(git --no-replace-objects -C "$ROOT" rev-parse --verify --quiet "$subject^{tree}" 2>/dev/null)" \
          || [[ "$subject_tree" != "$tree" ]]; then
        unresolved+=("[$lref ${lsha:0:12}] BRIDGE PIN INVALID: reuse requires the exact pushed commit and tree")
        continue
      fi
      identity="$subject"
    fi
    found=""
    for ((i = 0; i < ${#trees[@]}; i++)); do
      if [[ "${identities[$i]}" == "$identity" ]]; then
        labels[$i]="${labels[$i]}, $lref ${lsha:0:12}"
        found=1
        break
      fi
    done
    if [[ -z "$found" ]]; then
      trees+=("$tree")
      labels+=("$lref ${lsha:0:12}")
      subjects+=("$subject") identities+=("$identity")
    fi
  done <<< "$TRUST_PUSHED_REFS"

  if [[ -z "$names" ]]; then
    echo "SUBJECT: the pushed trees (TRUST_PUSHED_REFS: $deletions deletion(s), nothing else)"
    echo "SKIPPED: deletion(s) only, no tree pushed — nothing to judge"
    exit 0
  fi
  if [[ "$(git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null)" != "$(cd "$ROOT" && pwd -P)" ]]; then
    echo "BRIDGE PIN INVALID: TRUST_PUSHED_REFS is set but $ROOT is not the top of a git worktree" >&2
    exit 2
  fi
  if [[ "$deletions" -gt 0 ]]; then
    names="$names; $deletions deletion(s) not judged"
  fi
  echo "SUBJECT: the pushed trees (TRUST_PUSHED_REFS: $names), not the index or the submodule checkouts"
  for ((i = 0; i < ${#unresolved[@]}; i++)); do
    echo "${unresolved[$i]}"
    bad=1
    BP_UNKEYED=1
  done
  TREE_PIN_0=()
  TREE_PIN_1=()
  for ((i = 0; i < ${#trees[@]}; i++)); do
    judge_tree "${trees[$i]}" "${labels[$i]}" "${subjects[$i]}"
    if [[ "$TREE_BAD" != 0 ]]; then
      bad=1
    fi
  done
  LABEL=""

  # Local hygiene: what a bridge replay in THIS checkout would read. Not a
  # property of the push, so it never decides the verdict.
  for index in "${!PINNED_SIDES[@]}"; do
    gitlink="${PINNED_SIDES[$index]%%|*}"
    if ! state="$(checkout_commit "$gitlink" 2>&1)"; then
      echo "BRIDGE CHECKOUT WARN (local hygiene, not judged for this push): ${state#BRIDGE PIN INVALID: }"
      continue
    fi
    seen=" "
    eval "set -- \${TREE_PIN_$index[@]+\"\${TREE_PIN_$index[@]}\"}"
    for pin in "$@"; do
      if [[ "$pin" != "$state" && "$seen" != *" $pin "* ]]; then
        seen="$seen$pin "
        echo "BRIDGE CHECKOUT WARN (local hygiene, not judged for this push): $gitlink checkout=$state  !=  pushed pin=$pin"
        echo "  (a bridge replay in this checkout would not replay the pushed bytes)"
      fi
    done
  done

  if [[ "$bad" != 0 ]]; then
    if [[ "${#BP_FINDINGS[@]}" -gt 0 ]]; then
      printf '%s\n' "${BP_FINDINGS[@]}" | LC_ALL=C sort -u | sed 's/^/FINDING: /'
    fi
    if [[ "$BP_UNKEYED" == 0 && "${#BP_FINDINGS[@]}" -gt 0 ]]; then
      echo "FINDINGS: complete"
    fi
    echo "  repair in a checkout of the refused tree: scripts/check_bridge_pin.sh --fix, then commit and push that"
    exit 1
  fi
  exit 0
}

if [[ "$MODE" == "check" && "${TRUST_PUSHED_REFS:-}" =~ [^[:space:]] ]]; then
  judge_pushed
fi

INDEX_MANIFEST="$(index_manifest_text)"
source_reuse_selection "$INDEX_MANIFEST" INDEX || exit 1
ORIGINAL_TRUSTIR_MAN="$(manifest_commit_from_text "$INDEX_MANIFEST" trustir_commit)"

DRIFTED=0
declare -a PINS MANS CHECKOUTS
for side in "${PINNED_SIDES[@]}"; do
  gitlink="${side%%|*}"
  key="${side##*|}"

  pin="$(index_pin "$gitlink")"
  man="$(manifest_commit_from_text "$INDEX_MANIFEST" "$key")"
  if [[ "$REUSE_PRESENT" == 1 ]]; then
    if [[ "$key" == trustir_commit ]]; then man="$REUSE_IR"; else man="$REUSE_CLEAN"; fi
  fi
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
  CHECKOUTS+=("$checkout")

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

# Every olean the INDEX manifest lists must be staged at its path with exactly
# the recorded sha256, and every platform table must say what it was built from.
TRUSTIR_MAN="$ORIGINAL_TRUSTIR_MAN"
DIGEST_BAD=0
FILES_CHECKED=0
MATCHING_PLATFORM=0
PLATFORM_COUNT=0
digest_rows "$INDEX_MANIFEST" "$TRUSTIR_MAN"
FORCE_REGEN=0
if [[ "$DIGEST_BAD" != 0 ]]; then
  echo "  the vendored bytes do not match their manifest; regenerate with scripts/regen-trustir-oleans.sh --write"
  if [[ "$MODE" != "fix" ]]; then
    exit 1
  fi
  FORCE_REGEN=1
  DRIFTED=1
fi

if [[ "$DRIFTED" == 0 ]]; then
  echo "BRIDGE PIN OK: committed pins == manifest == clean checkouts; $FILES_CHECKED staged olean digest(s) match"
  for index in "${!PINNED_SIDES[@]}"; do
    echo "  ${PINNED_SIDES[$index]%%|*} @ ${PINS[$index]}"
  done
  exit 0
fi

if [[ "$MODE" != "fix" ]]; then
  echo "  run: scripts/check_bridge_pin.sh --fix"
  exit 1
fi

# `submodule update` below writes `core.worktree` into the SHARED module
# gitdir (`.git/modules/first-party/<n>/config`). From a LINKED worktree it
# writes a path relative to THAT worktree, so the primary checkout and every
# other linked worktree are left pointing at a directory that does not resolve
# from where their config lives: `git status` in the primary repo then fails
# outright. Measured 2026-09-09 -- one `--fix` run from a linked worktree broke
# `~/trust` and would equally have broken two sibling worktrees. There is no
# per-worktree submodule config to write instead. A linked worktree can still
# regenerate from already initialized, clean, correctly pinned checkouts without
# running `submodule update` or changing any Git configuration.
GIT_DIR_PATH="$(cd "$(git -C "$ROOT" rev-parse --absolute-git-dir)" && pwd -P)"
GIT_COMMON_PATH="$(cd "$(git -C "$ROOT" rev-parse --path-format=absolute --git-common-dir)" && pwd -P)"
LINKED_WORKTREE=0
if [[ "$GIT_DIR_PATH" != "$GIT_COMMON_PATH" ]]; then
  LINKED_WORKTREE=1
  for index in "${!PINNED_SIDES[@]}"; do
    if [[ "${CHECKOUTS[$index]}" != "${PINS[$index]}" ]]; then
      gitlink="${PINNED_SIDES[$index]%%|*}"
      echo "BRIDGE PIN: --fix refuses checkout repair from a linked worktree: $gitlink" >&2
      echo "  checkout=${CHECKOUTS[$index]} indexed pin=${PINS[$index]}" >&2
      echo "  submodule update could rewrite shared module configuration." >&2
      echo "  Provide initialized, clean checkouts at the indexed pins before retrying." >&2
      exit 2
    fi
  done
fi

if [[ "$LINKED_WORKTREE" == 1 ]]; then
  echo "  --fix: using clean indexed checkouts without changing shared module configuration…"
else
  echo "  --fix: checking out the indexed pins…"
fi
NEEDS_REGEN=0
for index in "${!PINNED_SIDES[@]}"; do
  gitlink="${PINNED_SIDES[$index]%%|*}"
  if [[ "$LINKED_WORKTREE" == 0 ]]; then
    git -C "$ROOT" submodule update --init --checkout -- "$gitlink"
  fi
  on_disk="$(checkout_commit "$gitlink")"
  if [[ "$on_disk" != "${PINS[$index]}" ]]; then
    echo "BRIDGE PIN INVALID: checkout is $on_disk instead of indexed ${PINS[$index]} for $gitlink" >&2
    exit 1
  fi
  if [[ "${PINS[$index]}" != "${MANS[$index]}" ]]; then
    NEEDS_REGEN=1
  fi
done

if [[ "$NEEDS_REGEN" == 0 && "$FORCE_REGEN" == 0 ]]; then
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
  # Endpoint check only: source/index drift still present after generation
  # refuses. The worktree owner must keep inputs stable throughout the build;
  # sampling cannot detect a transient change that was subsequently restored.
  pin2="$(index_pin "$gitlink")"
  checkout2="$(checkout_commit "$gitlink")"
  if [[ "$pin2" != "${PINS[$index]}" || "$checkout2" != "${PINS[$index]}" ]]; then
    echo "BRIDGE PIN STILL DRIFTED after regen: $gitlink source or index changed — investigate" >&2
    STILL_DRIFTED=1
  fi
  man2="$(manifest_commit_from_text "$WORKTREE_MANIFEST" "$key")"
  if [[ "${PINS[$index]}" != "$man2" ]]; then
    echo "BRIDGE PIN STILL DRIFTED after regen: indexed $gitlink pin=${PINS[$index]} worktree manifest $key=$man2 — investigate" >&2
    STILL_DRIFTED=1
  fi
done
if [[ "$STILL_DRIFTED" != 0 ]]; then
  exit 1
fi

DIGEST_BAD=0
FILES_CHECKED=0
MATCHING_PLATFORM=0
PLATFORM_COUNT=0
digest_rows "$WORKTREE_MANIFEST" "${PINS[0]}" "" worktree
if [[ "$DIGEST_BAD" != 0 ]]; then
  exit 1
fi

echo "BRIDGE PIN FIXED: worktree manifest regenerated"
echo "  stage $MANIFEST and all regenerated .olean files, then run --check"
exit 0
