#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
CHECKER="$REPO_ROOT/scripts/check_pin_coherence.sh"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

git_init() {
  git init -q "$1"
  git -C "$1" config user.name test
  git -C "$1" config user.email test@example.invalid
}

fail() {
  printf 'check_pin_coherence_test: %s\n' "$*" >&2
  exit 1
}

leaf="$TMP/leaf"
child="$TMP/child"
root="$TMP/root"
git_init "$leaf"
printf 'leaf\n' >"$leaf/payload.txt"
git -C "$leaf" add payload.txt
git -C "$leaf" commit -qm initial

git_init "$child"
printf 'committed\n' >"$child/payload.txt"
git -C "$child" add payload.txt
git -C "$child" commit -qm initial
git -C "$child" -c protocol.file.allow=always submodule add -q "$leaf" nested/leaf
git -C "$child" add .gitmodules nested/leaf
git -C "$child" commit -qm 'nested leaf'

git_init "$root"
git -C "$root" config advice.addEmbeddedRepo false
mkdir -p "$root/scripts" "$root/first-party"
cp "$CHECKER" "$root/scripts/check_pin_coherence.sh"
chmod +x "$root/scripts/check_pin_coherence.sh"
git -C "$root" -c protocol.file.allow=always submodule add -q "$child" first-party/example
git -C "$root" add .gitmodules first-party/example scripts/check_pin_coherence.sh
git -C "$root" commit -qm fixture
git -C "$root" -c protocol.file.allow=always submodule update -q --init --recursive

if ! positive=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  printf '%s\n' "$positive" >&2
  fail 'a clean exact gitlink was rejected'
fi
case "$positive" in
  *'PIN COHERENCE OK'*) ;;
  *) fail 'positive control did not reach the green verdict' ;;
esac

# Inventory authority is HEAD:.gitmodules, never a dirty worktree copy.
mv "$root/.gitmodules" "$root/.gitmodules.saved"
: >"$root/.gitmodules"
if ! dirty_inventory=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  printf '%s\n' "$dirty_inventory" >&2
  fail 'a dirty empty worktree .gitmodules hid the committed inventory'
fi
mv "$root/.gitmodules.saved" "$root/.gitmodules"

git -C "$root/first-party/example" submodule deinit -q -f -- nested/leaf
if nested=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  fail 'an uninitialized nested submodule was accepted'
fi
case "$nested" in
  *'PIN-NESTED-DRIFT  first-party/example'*) ;;
  *)
    printf '%s\n' "$nested" >&2
    fail 'uninitialized nested submodule did not produce PIN-NESTED-DRIFT'
    ;;
esac
git -C "$root" -c protocol.file.allow=always submodule update -q --init --recursive

printf 'dirty\n' >>"$root/first-party/example/payload.txt"
if tracked=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  fail 'tracked submodule content drift was accepted'
fi
case "$tracked" in
  *'PIN-DIRTY        first-party/example'*) ;;
  *)
    printf '%s\n' "$tracked" >&2
    fail 'tracked drift did not produce PIN-DIRTY'
    ;;
esac
git -C "$root/first-party/example" restore payload.txt

printf 'untracked\n' >"$root/first-party/example/untracked.txt"
if untracked=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  fail 'untracked submodule content drift was accepted'
fi
case "$untracked" in
  *'PIN-DIRTY        first-party/example'*) ;;
  *)
    printf '%s\n' "$untracked" >&2
    fail 'untracked drift did not produce PIN-DIRTY'
    ;;
esac
rm "$root/first-party/example/untracked.txt"

if ! final=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  printf '%s\n' "$final" >&2
  fail 'cleaning the content drift did not restore coherence'
fi

git -C "$root" rm -q --cached first-party/example
git -C "$root" commit -qm 'remove gitlink only'
if missing_gitlink=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  fail 'a committed inventory entry without a gitlink was accepted'
fi
case "$missing_gitlink" in
  *'MISSING-GITLINK  first-party/example'*) ;;
  *)
    printf '%s\n' "$missing_gitlink" >&2
    fail 'missing gitlink did not produce MISSING-GITLINK'
    ;;
esac

restored_pin=$(git -C "$root/first-party/example" rev-parse HEAD)
git -C "$root" update-index --add --cacheinfo "160000,$restored_pin,first-party/example"
git -C "$root" commit -qm 'restore gitlink'

hidden_pin=$(git -C "$leaf" rev-parse HEAD)
git -C "$root" update-index --add --cacheinfo "160000,$hidden_pin,first-party/hidden"
git -C "$root" commit -qm 'undeclared hidden gitlink'
if hidden=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  fail 'an undeclared committed gitlink was accepted'
fi
case "$hidden" in
  *'GITLINK-INVENTORY  .gitmodules'*) ;;
  *)
    printf '%s\n' "$hidden" >&2
    fail 'undeclared gitlink did not produce GITLINK-INVENTORY'
    ;;
esac
git -C "$root" rm -q --cached first-party/hidden
git -C "$root" commit -qm 'remove hidden gitlink'

: >"$root/.gitmodules"
git -C "$root" add .gitmodules
git -C "$root" commit -qm 'empty committed inventory'
if empty_inventory=$(cd "$root" && bash scripts/check_pin_coherence.sh 2>&1); then
  fail 'an empty committed inventory produced a vacuous pass'
fi
case "$empty_inventory" in
  *'GITMODULES-INVALID  .gitmodules'*|*'GITMODULES-EMPTY    .gitmodules'*) ;;
  *)
    printf '%s\n' "$empty_inventory" >&2
    fail 'empty committed inventory did not fail closed'
    ;;
esac

printf 'check_pin_coherence_test: PASS\n'
