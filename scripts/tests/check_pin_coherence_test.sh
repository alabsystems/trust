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
printf 'ignored/\n*.ignored\npartial/*\n!partial/visible/\npartial/visible/*\n!partial/visible/keep.txt\n' >"$child/.gitignore"
ln -s payload.txt "$child/tracked-link"
git -C "$child" add payload.txt .gitignore tracked-link
git -C "$child" commit -qm initial
git -C "$child" -c protocol.file.allow=always submodule add -q "$leaf" nested/leaf
git -C "$child" add .gitmodules nested/leaf
git -C "$child" commit -qm 'nested leaf'

git_init "$root"
git -C "$root" config advice.addEmbeddedRepo false
mkdir -p "$root/scripts" "$root/first-party"
cp "$CHECKER" "$root/scripts/check_pin_coherence.sh"
# Exercise complete old/new gates, not only a mocked status classifier. Their
# only difference is Git's path-display granularity; both retain all pin checks.
sed 's/--untracked-files=normal/--untracked-files=all/g' "$CHECKER" >"$root/scripts/status-all.sh"
sed 's/--untracked-files=all/--untracked-files=normal/g' "$CHECKER" >"$root/scripts/status-normal.sh"
chmod +x "$root/scripts/check_pin_coherence.sh"
git -C "$root" -c protocol.file.allow=always submodule add -q "$child" first-party/example
git -C "$root" add .gitmodules first-party/example scripts/check_pin_coherence.sh
git -C "$root" commit -qm fixture
git -C "$root" -c protocol.file.allow=always submodule update -q --init --recursive

parity_checks=0
parity() {
  local expected="$1" marker="$2" label="$3" all normal all_status normal_status
  if all=$(cd "$root" && bash scripts/status-all.sh 2>&1); then all_status=0; else all_status=$?; fi
  if normal=$(cd "$root" && bash scripts/status-normal.sh 2>&1); then normal_status=0; else normal_status=$?; fi
  if [ "$all_status" -ne "$normal_status" ] || [ "$normal_status" -ne "$expected" ]; then
    printf 'all=%s\n%s\nnormal=%s\n%s\n' "$all_status" "$all" "$normal_status" "$normal" >&2
    fail "status-mode predicate mismatch: $label"
  fi
  case "$all" in *"$marker"*) ;; *) fail "old gate missed $marker: $label" ;; esac
  case "$normal" in *"$marker"*) ;; *) fail "new gate missed $marker: $label" ;; esac
  parity_checks=$((parity_checks + 1))
}

checked="$root/first-party/example"
nested_leaf="$checked/nested/leaf"
parity 0 'PIN COHERENCE OK' 'clean exact pins'

mkdir -p "$checked/empty/deep" "$checked/ignored/deep"
printf 'ignored\n' >"$checked/ignored/deep/data"
printf 'ignored\n' >"$checked/only.ignored"
parity 0 'PIN COHERENCE OK' 'empty directories and ignored-only descendants'
rm -rf "$checked/empty" "$checked/ignored" "$checked/only.ignored"

mkdir -p "$checked/untracked/deep"
printf 'one\n' >"$checked/untracked/deep/one"
printf 'two\n' >"$checked/untracked/deep/two"
parity 1 'PIN-DIRTY' 'nested untracked files'
# Explicit command-line mode must still override a local display preference.
git -C "$checked" config status.showUntrackedFiles no
parity 1 'PIN-DIRTY' 'nested untracked files despite configured hidden display'
git -C "$checked" config --unset status.showUntrackedFiles
rm -rf "$checked/untracked"

mkdir -p "$checked/partial/visible"
printf 'ignored\n' >"$checked/partial/hidden"
printf 'unignored\n' >"$checked/partial/visible/keep.txt"
parity 1 'PIN-DIRTY' 'one unignored descendant in an otherwise ignored tree'
rm -rf "$checked/partial"

ln -s payload.txt "$checked/untracked-link"
parity 1 'PIN-DIRTY' 'untracked symlink'
rm "$checked/untracked-link"
ln -s missing-target "$checked/dangling-link"
parity 1 'PIN-DIRTY' 'dangling untracked symlink'
rm "$checked/dangling-link"
rm "$checked/tracked-link"
ln -s missing-target "$checked/tracked-link"
parity 1 'PIN-DIRTY' 'tracked symlink replacement'
git -C "$checked" restore tracked-link

printf 'changed\n' >>"$checked/payload.txt"
parity 1 'PIN-DIRTY' 'tracked modification'
git -C "$checked" restore payload.txt
rm "$checked/payload.txt"
parity 1 'PIN-DIRTY' 'tracked deletion'
git -C "$checked" restore payload.txt
printf 'staged\n' >"$checked/staged.txt"
git -C "$checked" add staged.txt
parity 1 'PIN-DIRTY' 'staged addition'
git -C "$checked" reset -q -- staged.txt
rm "$checked/staged.txt"

printf 'nested changed\n' >>"$nested_leaf/payload.txt"
parity 1 'PIN-DIRTY' 'nested tracked modification'
git -C "$checked" config submodule.nested/leaf.ignore all
parity 1 'PIN-DIRTY' 'explicit nested audit overrides ignore configuration'
git -C "$checked" config --unset submodule.nested/leaf.ignore
git -C "$nested_leaf" restore payload.txt
mkdir -p "$nested_leaf/untracked/deep"
printf 'nested untracked\n' >"$nested_leaf/untracked/deep/file"
parity 1 'PIN-DIRTY' 'nested submodule untracked files'
rm -rf "$nested_leaf/untracked"

nested_pin=$(git -C "$nested_leaf" rev-parse HEAD)
git -C "$nested_leaf" -c user.name=test -c user.email=test@example.invalid commit -qm 'off-pin nested commit' --allow-empty
parity 1 'PIN-DIRTY' 'nested off-pin commit'
git -C "$nested_leaf" checkout -q "$nested_pin"

# Corrupt only this fixture's index: real Git still resolves HEAD/the pin but
# status fails. Require the specific failure branch, not an incidental earlier
# inventory refusal from a fake Git command.
index=$(git -C "$checked" rev-parse --git-path index)
cp "$index" "$TMP/index.saved"
printf 'invalid index\n' >"$index"
git -C "$checked" cat-file -e "HEAD^{commit}"
git -C "$checked" rev-parse HEAD >/dev/null
parity 1 'PIN-STATUS-FAILED' 'actual Git status failure'
cp "$TMP/index.saved" "$index"
parity 0 'PIN COHERENCE OK' 'restored index and all content'

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
parity 1 'PIN-NESTED-DRIFT' 'uninitialized nested submodule'
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

printf 'check_pin_coherence_test: PASS (%s real-Git all/normal parity controls)\n' "$parity_checks"
