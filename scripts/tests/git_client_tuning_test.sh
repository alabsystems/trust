#!/usr/bin/env bash
# Tests of the git client tuning both hook installers apply
# (scripts/hooks/_git_client_tuning.sh, which reads what to set from the
# declaration scripts/git-clone.gitconfig; docs/DECISION_QUEUE.md
# GIT-CLIENT-TUNING-1, Continuum EW-13).
#
# Every case runs real git against throwaway repositories, with an isolated HOME
# and global config. A `git` shim first on PATH records each run of git's
# untracked-cache mtime self-test (`update-index --test-untracked-cache`) and
# answers it as SHIM_MTIME says: `ok`, `fail`, or `real` (git's own test, about
# 6 s of sleeps; the first case runs it). With SHIM_NO_SCOPE=1 it refuses
# `--show-scope` the way a git older than 2.26 does, and with SHIM_OLD_INDEX=1
# `--show-index-version` the way one older than 2.43 does. Every other git command is
# the real one. The last cases run the completion gate's, G2's checker's and
# recreate_bootstrap.py's own repository-configuration checks against a tuned
# repository and each core.fsmonitor spelling, and trust-cg's host-boundary
# allowlist (when first-party/trust-cg is populated) against the submodule keys,
# so the premises of the ruling are tested here, not recalled. When
# TRUST_GIT_TUNING_OLD_GITS names gits older than 2.40, a final case runs each
# against a tuned index's null trailer. It checks which of `ls-files`, `status`
# and `fsck` each git accepts, and that a rewrite by that git restores a
# checksum.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
for f in scripts/install-git-hooks.sh scripts/install-pin-hook.sh scripts/hooks/_git_client_tuning.sh \
  scripts/git-clone.gitconfig scripts/hooks/pre-push scripts/hooks/_ssh_keepalive.sh scripts/hooks/_ssh_probe.pl scripts/hooks-pin/pre-push \
  scripts/two_language_completion_gate.py scripts/completion_gates/check_g2_lean_input.py \
  scripts/recreate_bootstrap.py; do
  [ -f "$REPO_ROOT/$f" ] || { echo "git client tuning tests: no $REPO_ROOT/$f" >&2; exit 2; }
done

unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_SSH GIT_SSH_COMMAND
unset GIT_CONFIG GIT_CONFIG_COUNT GIT_CONFIG_PARAMETERS GIT_CONFIG_SYSTEM GIT_INDEX_VERSION
TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "${TMP:?}"' EXIT
export HOME="$TMP/home"
mkdir -p "$HOME" "$TMP/bin"
export GIT_CONFIG_GLOBAL="$TMP/global.gitconfig" GIT_CONFIG_NOSYSTEM=1
: >"$GIT_CONFIG_GLOBAL"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
REAL_GIT="$(command -v git)" || { echo "git client tuning tests: no git" >&2; exit 2; }
export REAL_GIT SHIM_LOG="$TMP/selftest.log" SHIM_MTIME=ok SHIM_NO_SCOPE=0 SHIM_OLD_INDEX=0
: >"$SHIM_LOG"
cat >"$TMP/bin/git" <<'EOF'
#!/usr/bin/env bash
for arg in "$@"; do
  if [ "$arg" = --show-scope ] && [ "$SHIM_NO_SCOPE" = 1 ]; then
    echo "error: unknown option \`show-scope'" >&2
    exit 129
  fi
  if [ "$arg" = --show-index-version ] && [ "$SHIM_OLD_INDEX" = 1 ]; then
    echo "error: unknown option \`show-index-version'" >&2
    exit 129
  fi
  if [ "$arg" = --test-untracked-cache ]; then
    printf 'selftest %s\n' "$PWD" >>"$SHIM_LOG"
    case "$SHIM_MTIME" in
      ok) exit 0 ;;
      fail) exit 1 ;;
    esac
  fi
done
exec "$REAL_GIT" "$@"
EOF
chmod +x "$TMP/bin/git"
export PATH="$TMP/bin:$PATH"

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }
show() { printf '%s\n' "$OUT" | sed 's/^/        /' | tail -25; }
saw() { if grep -qE -- "$2" <<<"$OUT"; then pass "$1"; else fail "$1: output lacks /$2/"; show; fi; }
not_saw() { if grep -qE -- "$2" <<<"$OUT"; then fail "$1: output has /$2/"; show; else pass "$1"; fi; }
is() { if [ "$2" = "$3" ]; then pass "$1"; else fail "$1: got '$2', want '$3'"; fi; }

local_all() { git -C "$1" config --local --get-all "$2" 2>/dev/null; }
index_file() { git -C "$1" rev-parse --path-format=absolute --git-path index; }
# The format from the index header ("DIRC", then a big-endian version), read
# without git: `git update-index --show-index-version` locks and may rewrite it.
index_format() {
  od -An -tu1 -N8 "$(index_file "$1")" 2>/dev/null | awk '{ for (i = 1; i <= NF; i++) b[n++] = $i }
    END { if (n == 8 && b[0] == 68 && b[1] == 73 && b[2] == 82 && b[3] == 67) print b[4] * 16777216 + b[5] * 65536 + b[6] * 256 + b[7] }'
}
index_sum() { cksum <"$(index_file "$1")"; }
# feature.manyFiles implies index.skipHash only from git 2.40.
GIT_MM="$(git version | sed -n 's/^git version \([0-9][0-9]*\)\.\([0-9][0-9]*\).*/\1 \2/p')"
# shellcheck disable=SC2086 # "MAJOR MINOR", split into $1 and $2 on purpose
skiphash_git() { set -- $GIT_MM; [ "${1:-0}" -gt 2 ] || { [ "${1:-0}" -eq 2 ] && [ "${2:-0}" -ge 40 ]; }; }
selftests() { wc -l <"$SHIM_LOG" | tr -d ' '; }
# A trailing hash of twenty zero bytes is index.skipHash's.
null_trailer() {
  if [ "$(tail -c 20 "$(index_file "$1")" | od -An -v -tx1 | tr -d ' \n')" = "0000000000000000000000000000000000000000" ]; then
    printf yes
  else
    printf no
  fi
}
has_untracked_cache() { if LC_ALL=C grep -q UNTR "$(index_file "$1")"; then printf yes; else printf no; fi; }

# The template: the real installers and hook directories, committed.
T="$TMP/template"
mkdir -p "$T/scripts/hooks" "$T/scripts/hooks-pin"
cp "$REPO_ROOT/scripts/install-git-hooks.sh" "$REPO_ROOT/scripts/install-pin-hook.sh" \
  "$REPO_ROOT/scripts/git-clone.gitconfig" "$T/scripts/"
cp "$REPO_ROOT/scripts/hooks/pre-push" "$REPO_ROOT/scripts/hooks/_ssh_keepalive.sh" \
  "$REPO_ROOT/scripts/hooks/_ssh_probe.pl" "$REPO_ROOT/scripts/hooks/_git_client_tuning.sh" "$T/scripts/hooks/"
cp "$REPO_ROOT/scripts/hooks-pin/pre-push" "$T/scripts/hooks-pin/"
printf 'fixture\n' >"$T/README.md"
git -C "$T" init -q -b main
git -C "$T" add -A && git -C "$T" commit -qm template

# A second template that carries a submodule which carries one of its own.
git init -q -b main "$TMP/nested-src"
printf 'nested\n' >"$TMP/nested-src/n.txt"
git -C "$TMP/nested-src" add -A && git -C "$TMP/nested-src" commit -qm nested
git init -q -b main "$TMP/sub-src"
printf 'sub\n' >"$TMP/sub-src/s.txt"
git -C "$TMP/sub-src" -c protocol.file.allow=always submodule add -q "$TMP/nested-src" nested
git -C "$TMP/sub-src" add -A && git -C "$TMP/sub-src" commit -qm sub
T2="$TMP/template-sub"
git clone -q "$T" "$T2"
git -C "$T2" -c protocol.file.allow=always submodule add -q "$TMP/sub-src" first-party/sub
git -C "$T2" -c protocol.file.allow=always submodule update -q --init --recursive
git -C "$T2" add -A && git -C "$T2" commit -qm "with a submodule"

# new_repo NAME [TEMPLATE]: W, a fresh clone with its submodules populated.
new_repo() {
  echo "-- $1"
  W="$TMP/$1"
  git -c protocol.file.allow=always clone -q --recurse-submodules "${2:-$T}" "$W"
}
install_full() { OUT="$(cd "$W" && bash scripts/install-git-hooks.sh "$@" 2>&1)"; RC=$?; }
install_pin() { OUT="$(cd "$W" && bash scripts/install-pin-hook.sh "$@" 2>&1)"; RC=$?; }

echo "== the full installer on a fresh clone"
new_repo fresh
start_format="$(index_format "$W")"
SHIM_MTIME=real install_full
is "install exits 0" "$RC" 0
is "  ... runs git's own mtime self-test once" "$(selftests)" 1
is "  ... sets core.untrackedCache = true in the clone's config, once" "$(local_all "$W" core.untrackedCache)" true
is "  ... sets feature.manyFiles = true in the clone's config, once" "$(local_all "$W" feature.manyFiles)" true
is "  ... moves the index to format 4" "$(index_format "$W")" 4
saw "  ... and says so" "index format $start_format -> 4"
is "  ... never writes core.fsmonitor" "$(git -C "$W" config --get core.fsmonitor)" ""
not_saw "  ... and names no fsmonitor" 'NOTE core.fsmonitor'
is "  ... leaves a clean checkout clean" "$(git -C "$W" status --porcelain)" ""
if skiphash_git; then
  is "  ... the next index write has no checksum (index.skipHash)" "$(null_trailer "$W")" yes
else
  echo "  skip the index.skipHash trailer: $(git version) predates 2.40"
fi
is "  ... and carries the untracked cache" "$(has_untracked_cache "$W")" yes
printf 'x\n' >"$W/new.txt"
is "  ... while status still names an untracked file" "$(git -C "$W" status --porcelain)" "?? new.txt"
mkdir -p "$W/deep/er" && printf 'y\n' >"$W/deep/er/f.txt" && rm "$W/new.txt"
is "  ... and one in a new nested directory" "$(git -C "$W" status --porcelain)" "?? deep/"
rm -rf "$W/deep"
printf 'edit\n' >>"$W/README.md"
is "  ... and a tracked edit" "$(git -C "$W" status --porcelain)" " M README.md"
git -C "$W" checkout -q -- README.md

echo "== a second install"
install_full
is "exits 0" "$RC" 0
is "  ... runs the self-test again, since the cache is in effect" "$(selftests)" 2
is "  ... leaves exactly one core.untrackedCache" "$(local_all "$W" core.untrackedCache)" true
is "  ... and one feature.manyFiles" "$(local_all "$W" feature.manyFiles)" true
saw "  ... saying they are already set" 'core.untrackedCache already true'

echo "== --status, then --uninstall"
install_full --status
is "--status exits 0" "$RC" 0
saw "  ... reports the tuning" 'git tuning: superproject: core.untrackedCache=true \(local\) feature.manyFiles=true \(local\), index format 4'
not_saw "  ... and calls nothing untuned" 'untuned'
install_full --uninstall
is "--uninstall exits 0" "$RC" 0
is "  ... removes core.hooksPath" "$(local_all "$W" core.hooksPath)" ""
is "  ... and leaves the tuning, which is not a hook" "$(local_all "$W" feature.manyFiles)" true

echo "== a worktree added after install"
git -C "$W" worktree add -q "$TMP/linked" -b linked
is "reads the clone's feature.manyFiles" "$(git -C "$TMP/linked" config --show-scope --get feature.manyFiles)" "$(printf 'local\ttrue')"
is "  ... starts its index at format 4 with no install" "$(index_format "$TMP/linked")" 4
OUT="$(cd "$TMP/linked" && bash scripts/install-git-hooks.sh --status 2>&1)"
saw "  ... and --status there says so" 'git tuning: superproject: core.untrackedCache=true \(local\) feature.manyFiles=true \(local\), index format 4'

echo "== --status on an untuned clone writes nothing"
new_repo untouched
before_config="$(git -C "$W" config --local --list)"
before_sum="$(index_sum "$W")"
before_tests="$(selftests)"
install_full --status
is "the config is unchanged" "$(git -C "$W" config --local --list)" "$before_config"
is "  ... the index is unchanged" "$(index_sum "$W")" "$before_sum"
is "  ... no self-test ran" "$(selftests)" "$before_tests"
saw "  ... it reports the unset keys" 'core.untrackedCache=<unset> feature.manyFiles=<unset>'
saw "  ... and the fix" 'installing again tunes it where git.s mtime self-test passes'

echo "== a value chosen in another scope is kept"
printf '[core]\n\tuntrackedCache = false\n' >"$GIT_CONFIG_GLOBAL"
new_repo global-choice
install_full
is "install exits 0" "$RC" 0
is "  ... writes no local core.untrackedCache over the global false" "$(local_all "$W" core.untrackedCache)" ""
is "  ... so git still reads false" "$(git -C "$W" config --type=bool --get core.untrackedCache)" false
saw "  ... and says it is kept" 'core.untrackedCache=false is set in global config; it is kept'
is "  ... while feature.manyFiles is still set" "$(local_all "$W" feature.manyFiles)" true
: >"$GIT_CONFIG_GLOBAL"
new_repo local-choice
git -C "$W" config feature.manyFiles false
start_format="$(index_format "$W")"
install_full
is "a local feature.manyFiles=false is kept" "$(local_all "$W" feature.manyFiles)" false
saw "  ... and reported" 'feature.manyFiles=false is set in local config; it is kept'
is "  ... and its index keeps its format" "$(index_format "$W")" "$start_format"
new_repo index-version
git -C "$W" config index.version 3
install_full
saw "an explicit index.version=3 is kept" 'index.version=3 is set; its index is not converted'
is "  ... and the index is not moved to 4" "$([ "$(index_format "$W")" = 4 ] && printf moved || printf kept)" kept

echo "== git's mtime self-test failing"
new_repo mtime-fail "$T2"
start_format="$(index_format "$W")"
SHIM_MTIME=fail install_full
is "install still exits 0" "$RC" 0
is "  ... naming the failed self-test for each of the three repositories" "$(grep -c 'self-test FAILED' <<<"$OUT")" 3
is "  ... writing no core.untrackedCache" "$(local_all "$W" core.untrackedCache)" ""
is "  ... and no feature.manyFiles" "$(local_all "$W" feature.manyFiles)" ""
is "  ... nor a submodule's core.untrackedCache" "$(local_all "$W/first-party/sub" core.untrackedCache)" ""
is "  ... leaving the index format" "$(index_format "$W")" "$start_format"
install_full --status
not_saw "  ... and --status does not promise that installing again tunes it everywhere" 'installing again tunes it$'
saw "  ... only where the self-test passes" 'installing again tunes it where git.s mtime self-test passes'
new_repo mtime-fail-tuned
install_full
SHIM_MTIME=fail install_full
is "a failing self-test where the cache is already on still exits 0" "$RC" 0
saw "  ... and warns that status there can miss an untracked file" 'WARNING the untracked cache is in effect here'
is "  ... changing no key" "$(local_all "$W" core.untrackedCache)" true

echo "== an index another process holds"
new_repo locked
start_format="$(index_format "$W")"
: >"$(index_file "$W").lock"
install_full
is "install still exits 0" "$RC" 0
is "  ... still writes the keys" "$(local_all "$W" feature.manyFiles)" true
is "  ... does not convert the held index" "$(index_format "$W")" "$start_format"
saw "  ... and says installing again converts it" 'not converted \(another process may'
rm -f "$(index_file "$W").lock"
before_sum="$(index_sum "$W")"
install_full --status
is "  ... --status on that tuned, unconverted index changes no byte of it" "$(index_sum "$W")" "$before_sum"
saw "  ... and reports its format" "index format $start_format"
install_full
is "  ... which installing again does" "$(index_format "$W")" 4

echo "== populated submodules, nested"
new_repo with-sub "$T2"
before_tests="$(selftests)"
sub_format="$(index_format "$W/first-party/sub")"
install_full
is "install exits 0" "$RC" 0
for sub in first-party/sub first-party/sub/nested; do
  is "  ... $sub gets core.untrackedCache in its own config" "$(local_all "$W/$sub" core.untrackedCache)" true
  is "  ... $sub gets no feature.manyFiles, which trust-cg's host boundary refuses" "$(local_all "$W/$sub" feature.manyFiles)" ""
  is "  ... $sub's index keeps its format" "$(index_format "$W/$sub")" "$sub_format"
done
is "  ... while the superproject's index is format 4" "$(index_format "$W")" 4
is "  ... one self-test covers the one filesystem" "$(selftests)" "$((before_tests + 1))"
is "  ... the superproject stays clean" "$(git -C "$W" status --porcelain)" ""
printf 'edit\n' >>"$W/first-party/sub/nested/n.txt"
is "  ... and still names an edit two submodules down" "$(git -C "$W" status --porcelain)" " M first-party/sub"
git -C "$W/first-party/sub/nested" checkout -q -- n.txt
install_full --status
saw "  ... --status names each submodule" 'git tuning: first-party/sub/nested: core.untrackedCache=true \(local\), index format'
not_saw "  ... and calls none untuned" 'untuned'

echo "== a gitlink git cannot resolve"
new_repo broken-gitlink
git init -q -b main "$W/embedded"
git -C "$W/embedded" commit -q --allow-empty -m embedded
git -C "$W" add embedded 2>/dev/null
git -C "$W" commit -qm "an embedded repository, with no .gitmodules entry"
install_full
is "install exits 0" "$RC" 0
saw "  ... and says it cannot list every submodule" 'cannot list every submodule \(.*embedded'
is "  ... while the superproject is still tuned" "$(local_all "$W" feature.manyFiles)" true
install_full --status
saw "  ... --status says so too" 'cannot list every submodule \(.*embedded'

echo "== a git that cannot report config scopes"
printf '[core]\n\tuntrackedCache = false\n' >"$GIT_CONFIG_GLOBAL"
new_repo no-scope
SHIM_NO_SCOPE=1 install_full
is "install exits 0" "$RC" 0
saw "  ... and says why" 'this git \(git version .*\) cannot say which$'
saw "  ... and that it tunes nothing" 'nothing is tuned with it$'
is "  ... writing no core.untrackedCache over the global false" "$(local_all "$W" core.untrackedCache)" ""
is "  ... nor feature.manyFiles" "$(local_all "$W" feature.manyFiles)" ""
SHIM_NO_SCOPE=1 install_full --status
saw "  ... --status says the same" 'cannot say which'
: >"$GIT_CONFIG_GLOBAL"

echo "== a git without update-index --show-index-version (before 2.43)"
new_repo old-index-git
start_format="$(index_format "$W")"
SHIM_OLD_INDEX=1 install_full
is "install exits 0" "$RC" 0
is "  ... still moves the index to format 4" "$(index_format "$W")" 4
saw "  ... and says so" "index format $start_format -> 4"
SHIM_OLD_INDEX=1 install_full --status
saw "  ... --status still reads the format" 'git tuning: superproject: .*, index format 4$'

echo "== the pin installer tunes too"
new_repo pin
install_pin
is "install exits 0" "$RC" 0
is "  ... sets feature.manyFiles" "$(local_all "$W" feature.manyFiles)" true
is "  ... and core.untrackedCache" "$(local_all "$W" core.untrackedCache)" true
is "  ... and moves the index to format 4" "$(index_format "$W")" 4
install_pin --status
is "  ... --status exits 0 while the pin hooks are installed" "$RC" 0
saw "  ... and reports the tuning" 'git tuning: superproject: core.untrackedCache=true \(local\) feature.manyFiles=true \(local\), index format 4'
install_pin --uninstall
install_pin --status
is "  ... and exits 1 once they are not" "$RC" 1
saw "  ... still reporting the tuning" 'git tuning: superproject: core.untrackedCache=true \(local\)'

echo "== the declaration is what is set"
# T3 declares other keys: core.untrackedCache and fetch.writeCommitGraph (a
# boolean that touches neither the index nor the cache) for the superproject,
# fetch.writeCommitGraph alone for submodules, and no index format.
T3="$TMP/template-declared"
git -c protocol.file.allow=always clone -q --recurse-submodules "$T2" "$T3"
printf '[tuning]\n\tsuperproject = core.untrackedCache\n\tsuperproject = fetch.writeCommitGraph\n\tsubmodule = fetch.writeCommitGraph\n' \
  >"$T3/scripts/git-clone.gitconfig"
git -C "$T3" commit -qam "another declaration"
new_repo declared "$T3"
start_format="$(index_format "$W")"
install_full
is "install exits 0" "$RC" 0
is "  ... sets the declared core.untrackedCache" "$(local_all "$W" core.untrackedCache)" true
is "  ... and the declared fetch.writeCommitGraph" "$(local_all "$W" fetch.writeCommitGraph)" true
is "  ... and no feature.manyFiles, which it no longer declares" "$(local_all "$W" feature.manyFiles)" ""
is "  ... so the index keeps its format" "$(index_format "$W")" "$start_format"
for sub in first-party/sub first-party/sub/nested; do
  is "  ... $sub gets the declared submodule key" "$(local_all "$W/$sub" fetch.writeCommitGraph)" true
  is "  ... and not core.untrackedCache, which is no longer declared for it" "$(local_all "$W/$sub" core.untrackedCache)" ""
done
install_full --status
saw "  ... --status reports the declared keys" 'git tuning: superproject: core.untrackedCache=true \(local\) fetch.writeCommitGraph=true \(local\), index format'
saw "  ... for each submodule too" 'git tuning: first-party/sub: fetch.writeCommitGraph=true \(local\), index format'
new_repo declared-mtime-fail "$T3"
SHIM_MTIME=fail install_full
is "a failed self-test still exits 0" "$RC" 0
is "  ... writes no core.untrackedCache" "$(local_all "$W" core.untrackedCache)" ""
is "  ... while a declared key that does not turn the cache on is still written" "$(local_all "$W" fetch.writeCommitGraph)" true
is "  ... in the submodules too, where no cache key is declared and no self-test failure is named" \
  "$(local_all "$W/first-party/sub" fetch.writeCommitGraph) $(grep -c 'self-test FAILED' <<<"$OUT")" "true 1"

echo "== a declaration's refused entries"
# T4 declares, for the superproject, the installers' own keys, a key it also
# declares never set and a malformed name beside one good key, an index format
# of 2, and an entry outside [tuning]. (git writes a format-3 index as 2 when no
# entry needs 3's extended flags, so 2 is the format a test can tell from 4.)
T4="$TMP/template-refused"
git clone -q "$T" "$T4"
printf '[tuning]\n\tsuperproject = core.hooksPath\n\tsuperproject = core.sshCommand\n\tsuperproject = core.fsmonitor\n\tsuperproject = notakey\n\tsuperproject = feature.manyFiles\n\tindexVersion = 2\n\tnever = core.fsmonitor\n[other]\n\tthing = 1\n' \
  >"$T4/scripts/git-clone.gitconfig"
git -C "$T4" commit -qam "a declaration with refused entries"
new_repo refused "$T4"
git -C "$W" update-index --index-version 4
install_pin
is "the pin installer exits 0" "$RC" 0
saw "  ... refusing core.hooksPath" 'tuning.superproject=core.hooksPath is the installers. own, not'
is "  ... which keeps the installer's own value" "$(local_all "$W" core.hooksPath)" scripts/hooks-pin
saw "  ... refusing core.sshCommand" 'tuning.superproject=core.sshCommand is the installers. own, not'
is "  ... which stays unset" "$(local_all "$W" core.sshCommand)" ""
saw "  ... refusing a key also declared never set" 'tuning.superproject=core.fsmonitor is also declared never set; not set'
is "  ... which stays unset" "$(local_all "$W" core.fsmonitor)" ""
saw "  ... refusing a malformed name" 'tuning.superproject=notakey is not a section.name key; not set'
saw "  ... naming an entry outside [tuning]" 'other.thing is not a tuning entry; ignored'
is "  ... while the good key is set" "$(local_all "$W" feature.manyFiles)" true
is "  ... and the index moves from 4 to the declared format 2" "$(index_format "$W")" 2
saw "  ... saying so" 'index format 4 -> 2'
new_repo bad-index "$T"
printf '[tuning]\n\tsuperproject = feature.manyFiles\n\tindexVersion = 7\n' >"$W/scripts/git-clone.gitconfig"
start_format="$(index_format "$W")"
install_full
is "an index format that is not 2, 3 or 4 still exits 0" "$RC" 0
saw "  ... is named" 'tuning.indexVersion=7 is not 2, 3 or 4;'
is "  ... the key is set" "$(local_all "$W" feature.manyFiles)" true
is "  ... and the index keeps its format" "$(index_format "$W")" "$start_format"

echo "== no declaration"
T5="$TMP/template-undeclared"
git clone -q "$T" "$T5"
git -C "$T5" rm -q scripts/git-clone.gitconfig
git -C "$T5" commit -qm "no declaration"
new_repo undeclared "$T5"
before_tests="$(selftests)"
before_sum="$(index_sum "$W")"
install_full
is "install exits 0" "$RC" 0
saw "  ... saying there is nothing to tune" 'no scripts/git-clone.gitconfig in this checkout, which declares the'
is "  ... setting no core.untrackedCache" "$(local_all "$W" core.untrackedCache)" ""
is "  ... nor feature.manyFiles" "$(local_all "$W" feature.manyFiles)" ""
is "  ... running no self-test" "$(selftests)" "$before_tests"
is "  ... leaving the index untouched" "$(index_sum "$W")" "$before_sum"
is "  ... while the hooks are installed" "$(local_all "$W" core.hooksPath)" scripts/hooks
install_full --status
saw "  ... --status says so too" 'no scripts/git-clone.gitconfig in this checkout'
printf '[tuning\n' >"$W/scripts/git-clone.gitconfig"
install_full
is "an unreadable declaration still exits 0" "$RC" 0
saw "  ... and is named" 'cannot read scripts/git-clone.gitconfig \(git config exited'
is "  ... setting nothing" "$(local_all "$W" feature.manyFiles)" ""

echo "== core.fsmonitor is named, never written"
# From here on every git the installers and the library run reads
# core.fsmonitor=false from the command scope, so no daemon starts. The library
# judges only local and worktree records, and the gates drop every GIT_*
# variable, so neither sees this one.
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=core.fsmonitor GIT_CONFIG_VALUE_0=false
new_repo fsmonitor
git -C "$W" config core.fsmonitor true
install_full
is "install leaves a local core.fsmonitor alone" "$(local_all "$W" core.fsmonitor)" true
saw "  ... and names it" 'NOTE core.fsmonitor true is set in local config'
git -C "$W" config --unset core.fsmonitor
printf '[core]\n\tfsmonitor\n' >>"$(git -C "$W" rev-parse --path-format=absolute --git-common-dir)/config"
install_full --status
saw "a key with no value, which git reads as true, is named" 'NOTE core.fsmonitor \(no value, which git reads as true\)'
git -C "$W" config --unset core.fsmonitor
git -C "$W" config core.fsmonitor Off
install_full --status
saw "Off, which git reads as false, is named for recreate_bootstrap.py" 'NOTE core.fsmonitor Off is set in local config; git reads'
git -C "$W" config core.fsmonitor FALSE
install_full --status
not_saw "FALSE is not named" 'NOTE core.fsmonitor'
git -C "$W" config core.fsmonitor ""
install_full --status
not_saw "an empty value is not named" 'NOTE core.fsmonitor'

echo "== the gates' own configuration checks"
R="$TMP/gate"
git init -q -b main "$R"
mkdir -p "$R/scripts"
cp "$REPO_ROOT/scripts/git-clone.gitconfig" "$R/scripts/"
git -C "$R" add -A && git -C "$R" commit -qm gate
OUT="$(
  # shellcheck source=../hooks/_git_client_tuning.sh
  . "$REPO_ROOT/scripts/hooks/_git_client_tuning.sh" && trust_git_tuning_apply "$R" 2>&1
)"
is "the library alone tunes a repository" "$(local_all "$R" feature.manyFiles)" true
verdicts() {
  python3 -I -B - "$REPO_ROOT" "$R" <<'EOF' 2>&1
import importlib.util
import sys
from pathlib import Path

root, repo = Path(sys.argv[1]), Path(sys.argv[2])


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


gate = load("tuning_test_completion_gate", root / "scripts/two_language_completion_gate.py")
g2 = load("tuning_test_g2", root / "scripts/completion_gates/check_g2_lean_input.py")
recreate = load("tuning_test_recreate_bootstrap", root / "scripts/recreate_bootstrap.py")
refusals = []
gate._CheckoutInspection.refuse_program_config(repo, refusals.append)
print("completion-gate=" + ("refused" if refusals else "accepted"))
context = g2.Context(repo, Path("/dev/null"), "", Path("/dev/null"), "", "", "")
try:
    context.refuse_repository_overrides(repo, "the repository")
    print("g2=accepted")
except g2.Refusal as error:
    print("g2=refused" if "starts a program" in str(error) else f"g2=error {error}")
try:
    recreate._reject_local_git_execution_authority(repo)
    print("recreate-bootstrap=accepted")
except RuntimeError as error:
    print("recreate-bootstrap=refused" if "hidden execution" in str(error) else f"recreate-bootstrap=error {error}")
EOF
}
# gate_case LABEL WANT_GATE WANT_G2 WANT_RECREATE WANT_NOTE: the three
# verdicts on R as configured, and whether the library names its fsmonitor.
gate_case() {
  OUT="$(verdicts)"
  saw "$1: the completion gate $2" "^completion-gate=$2\$"
  saw "  ... G2's checker $3" "^g2=$3\$"
  saw "  ... recreate_bootstrap.py $4" "^recreate-bootstrap=$4\$"
  OUT="$(. "$REPO_ROOT/scripts/hooks/_git_client_tuning.sh" && trust_git_tuning_status "$R" 2>&1)"
  if [ "$5" = named ]; then
    saw "  ... and the library names it" 'NOTE core.fsmonitor'
  else
    not_saw "  ... and the library names nothing" 'NOTE core.fsmonitor'
  fi
}
gate_case "tuned, no core.fsmonitor" accepted accepted accepted silent
git -C "$R" config core.fsmonitor true
gate_case "core.fsmonitor=true" refused refused refused named
git -C "$R" config core.fsmonitor Off
gate_case "core.fsmonitor=Off" accepted accepted refused named
git -C "$R" config core.fsmonitor 0
gate_case "core.fsmonitor=0" accepted accepted refused named
git -C "$R" config core.fsmonitor false
gate_case "core.fsmonitor=false" accepted accepted accepted silent
git -C "$R" config --unset core.fsmonitor
# The declaration's tuning.never says the three gates refuse each key it names.
for key in $(git config --file "$REPO_ROOT/scripts/git-clone.gitconfig" --get-all tuning.never); do
  git -C "$R" config "$key" true
  gate_case "declared never set, $key=true" refused refused refused named
  git -C "$R" config --unset "$key"
done

unset GIT_CONFIG_COUNT GIT_CONFIG_KEY_0 GIT_CONFIG_VALUE_0

echo "== trust-cg's host boundary and the submodule keys"
HB="$REPO_ROOT/first-party/trust-cg/scripts/host_boundary.py"
if [ -f "$HB" ]; then
  OUT="$(
    python3 -I -B - "$HB" "$(git config --file "$REPO_ROOT/scripts/git-clone.gitconfig" --get-all tuning.submodule | tr '\n' ' ')" <<'EOF' 2>&1
import importlib.util
import sys

spec = importlib.util.spec_from_file_location("tuning_test_host_boundary", sys.argv[1])
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
for key in sys.argv[2].split():
    print(f"declared {key.lower()}=" + ("allowed" if module.local_key_allowed(key.lower()) else "refused"))
print("feature.manyfiles=" + ("allowed" if module.local_key_allowed("feature.manyfiles") else "refused"))
EOF
  )"
  saw "it allows core.untrackedCache, the key the declaration gives every submodule" '^declared core.untrackedcache=allowed$'
  not_saw "  ... and every key the declaration gives a submodule" '^declared .*=refused$'
  saw "  ... while refusing feature.manyFiles, which is why submodules do not get it" '^feature.manyfiles=refused$'
else
  echo "  skip: first-party/trust-cg is not populated, so its host boundary cannot be read"
fi

echo "== an older git and the tuned index"
# git-config(1), index.skipHash: a git before 2.13 refuses the index, and one
# before 2.40 reports it corrupt in `git fsck`. GIT-CLIENT-TUNING-1 states what
# 2.12.5, 2.25.5 and 2.39.5 do with a tuned index. Name gits older than 2.40
# (paths, space-separated) in TRUST_GIT_TUNING_OLD_GITS to check that statement
# against them. Every step first confirms the trailer is still null, since any
# write by an older git puts a real checksum back.
# version_before "MAJOR MINOR" MAJ MIN: MAJOR.MINOR is older than MAJ.MIN.
version_before() {
  local major="${1% *}" minor="${1#* }"
  [ "$major" -lt "$2" ] || { [ "$major" -eq "$2" ] && [ "$minor" -lt "$3" ]; }
}
if [ -z "${TRUST_GIT_TUNING_OLD_GITS:-}" ]; then
  echo "  skip: TRUST_GIT_TUNING_OLD_GITS names no git older than 2.40"
elif ! skiphash_git; then
  echo "  skip: $(git version) predates 2.40, so it writes no skipHash index"
else
  n=0
  for OLD in $TRUST_GIT_TUNING_OLD_GITS; do
    n=$((n + 1))
    OLD_MM="$("$OLD" version 2>/dev/null | sed -n 's/^git version \([0-9][0-9]*\)\.\([0-9][0-9]*\).*/\1 \2/p')"
    if [ -z "$OLD_MM" ]; then
      fail "$OLD answers no git version"
      continue
    fi
    V="git ${OLD_MM/ /.}"
    if ! version_before "$OLD_MM" 2 40; then
      fail "$OLD is $V, not older than 2.40"
      continue
    fi
    new_repo "old-git-$n"
    SHIM_MTIME=ok install_full
    is "  ... the installer tunes the clone" "$RC" 0
    is "  ... and its index has a null trailer" "$(null_trailer "$W")" yes
    if version_before "$OLD_MM" 2 13; then
      OUT="$("$OLD" -C "$W" ls-files 2>&1)"
      is "  $V refuses ls-files" "$?" 128
      saw "  ... naming the index corrupt" 'index file corrupt'
      is "  ... with the trailer still null" "$(null_trailer "$W")" yes
      OUT="$("$OLD" -C "$W" status --porcelain 2>&1)"
      is "  $V refuses status" "$?" 128
      saw "  ... naming the index corrupt" 'index file corrupt'
      is "  ... with the trailer still null" "$(null_trailer "$W")" yes
      OUT="$("$OLD" -C "$W" fsck 2>&1)"
      is "  $V fsck exits 128" "$?" 128
      saw "  ... naming the index corrupt" 'index file corrupt'
      continue
    fi
    OUT="$("$OLD" -C "$W" ls-files 2>&1)"
    is "  $V reads it with ls-files" "$?" 0
    saw "  ... listing the tracked files" '^README\.md$'
    is "  ... with the trailer still null" "$(null_trailer "$W")" yes
    if ! version_before "$OLD_MM" 2 15; then
      OUT="$("$OLD" --no-optional-locks -C "$W" status --porcelain 2>&1)"
      is "  $V reads it with status --no-optional-locks" "$?" 0
      is "  ... and finds the checkout clean" "$OUT" ""
      is "  ... with the trailer still null" "$(null_trailer "$W")" yes
    fi
    OUT="$("$OLD" -C "$W" fsck 2>&1)"
    is "  $V fsck exits 128 on it" "$?" 128
    saw "  ... naming the index corrupt" 'index file corrupt'
    touch "$W/README.md"
    "$OLD" -C "$W" update-index -q --refresh >/dev/null 2>&1
    is "  ... an index $V rewrites carries a real checksum" "$(null_trailer "$W")" no
    OUT="$("$OLD" -C "$W" fsck 2>&1)"
    is "  ... which its fsck accepts" "$?" 0
    OUT="$(git -C "$W" status --porcelain 2>&1)"
    is "  ... and $(git version | cut -d' ' -f3) reads as clean" "$OUT" ""
  done
fi

echo
if [ "$FAILED" -ne 0 ]; then
  echo "git client tuning tests: FAILED"
  exit 1
fi
echo "git client tuning tests: all passed"
