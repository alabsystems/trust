#!/usr/bin/env bash
# Tests of the ssh keepalive the push path needs (docs/DECISION_QUEUE.md
# PUSH-PATH-SSH-KEEPALIVE): scripts/install-git-hooks.sh sets it and reports
# it, and scripts/hooks/pre-push refuses before any lane when it is off.
#
# Every case runs with an isolated HOME and global config and a stub `ssh`
# first on PATH. `ssh -G` prints a serveraliveinterval taken from its `-o`
# options (else STUB_SSH_DEFAULT, 0 like OpenSSH's own default) and records
# the destination and port it was asked about; any other call is a transport:
# it runs the git command it was handed against bare repositories under
# $TMP/remote-root, so a real `git push` over "ssh" lands or is refused here.
# Real ssh is never run.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
for f in scripts/install-git-hooks.sh scripts/git-clone.gitconfig scripts/hooks/_git_client_tuning.sh scripts/hooks/pre-push scripts/hooks/_ssh_keepalive.sh scripts/hooks/_ssh_probe.pl; do
  [ -f "$REPO_ROOT/$f" ] || { echo "ssh keepalive tests: no $REPO_ROOT/$f" >&2; exit 2; }
done

unset TRUST_PUSHED_REFS TRUST_PUSH_REMOTE GIT_SSH GIT_SSH_COMMAND GIT_SSH_VARIANT
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE
TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "${TMP:?}"' EXIT
export HOME="$TMP/home"
mkdir -p "$HOME"
export GIT_CONFIG_GLOBAL="$TMP/global.gitconfig" GIT_CONFIG_NOSYSTEM=1
# The installer also tunes the git client as scripts/git-clone.gitconfig
# declares (scripts/hooks/_git_client_tuning.sh), and keeps a value already
# chosen in any scope. Choosing both keys here keeps
# these cases about ssh: no 6 s mtime self-test per fixture, no index rewrite.
# scripts/tests/git_client_tuning_test.sh is the tuning's own suite.
printf '[core]\n\tuntrackedCache = false\n[feature]\n\tmanyFiles = false\n' >"$GIT_CONFIG_GLOBAL"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid
export GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid
export TRUST_PRE_PUSH_SHADOW=0 TRUST_PRE_PUSH_FAST_JOBS=1
export STUB_LOG="$TMP/ssh.log" STUB_REMOTE_ROOT="$TMP/remote-root"
mkdir -p "$TMP/bin" "$STUB_REMOTE_ROOT"

cat >"$TMP/bin/ssh" <<'EOF'
#!/usr/bin/env bash
interval="${STUB_SSH_DEFAULT:-0}" probe=0 port="" args=()
while [ $# -gt 0 ]; do
  case "$1" in
    -G) probe=1 ;;
    -o) shift; case "$1" in ServerAliveInterval=*) interval="${1#*=}" ;; esac ;;
    -oServerAliveInterval=*) interval="${1#-oServerAliveInterval=}" ;;
    -o*) ;;
    -p) shift; port="$1" ;;
    -*) ;;
    *) args+=("$1") ;;
  esac
  shift
done
if [ "$probe" = 1 ]; then
  printf 'probe %s port=%s\n' "${args[0]:-}" "$port" >>"$STUB_LOG"
  [ -z "${STUB_SSH_FAIL:-}" ] || exit 255
  printf 'user git\nhostname %s\nserveraliveinterval %s\nserveralivecountmax 3\n' "${args[0]#*@}" "$interval"
  exit 0
fi
printf 'connect %s\n' "${args[*]}" >>"$STUB_LOG"
cd "$STUB_REMOTE_ROOT" && exec sh -c "${args[*]:1}"
EOF
chmod +x "$TMP/bin/ssh"
export PATH="$TMP/bin:$PATH"

FAILED=0
pass() { echo "  ok   $1"; }
fail() { echo "  FAIL $1"; FAILED=1; }
show() { printf '%s\n' "$OUT" | sed 's/^/        /' | tail -25; }
saw() { if grep -qE -- "$2" <<<"$OUT"; then pass "$1"; else fail "$1: output lacks /$2/"; show; fi; }
not_saw() { if grep -qE -- "$2" <<<"$OUT"; then fail "$1: output has /$2/"; show; else pass "$1"; fi; }
is() { if [ "$2" = "$3" ]; then pass "$1"; else fail "$1: got '$2', want '$3'"; fi; }
KEEP="ssh -o ServerAliveInterval=30 -o ServerAliveCountMax=10"

# A repository carrying the real installer and hooks, a stand-in harness and
# reader derivation. The harness lists a fast lane and a scoped lane that each
# record that they ran; FIXTURE_NO_SCOPED drops the scoped row.
T="$TMP/template"
mkdir -p "$T/scripts/hooks" "$T/tests/trust-comprehensive"
cp "$REPO_ROOT/scripts/install-git-hooks.sh" "$REPO_ROOT/scripts/git-clone.gitconfig" "$T/scripts/"
cp "$REPO_ROOT/scripts/hooks/_git_client_tuning.sh" "$T/scripts/hooks/"
cp "$REPO_ROOT/scripts/hooks/pre-push" "$REPO_ROOT/scripts/hooks/_ssh_keepalive.sh" "$REPO_ROOT/scripts/hooks/_ssh_probe.pl" "$T/scripts/hooks/"
printf '# quarantine ledger (fixture)\n' >"$T/tests/trust-comprehensive/divergences.toml"
printf 'import sys\n' >"$T/scripts/check_gate_lane_coverage.py"
cat >"$T/tests/run_trust_comprehensive_harness.sh" <<EOF
#!/usr/bin/env bash
[ "\${1:-}" = "--list" ] || exit 0
printf '%s\t%s\t%s\t%s\t%s\n' fast.ok fixture true 2026-10-24 'echo fast >>"$TMP/lanes.ran"'
[ -n "\${FIXTURE_NO_SCOPED:-}" ] || printf '%s\t%s\t%s\t%s\t%s\n' scoped.ok fixture true 2026-10-24 'echo scoped >>"$TMP/lanes.ran"'
EOF
git -C "$T" init -q -b main
git -C "$T" add -A && git -C "$T" commit -qm template

# new_repo <name> [origin url]: W a fresh copy, origin pointing at that URL.
new_repo() {
  echo "-- $1"
  W="$TMP/$1"
  cp -R "$T" "$W"
  [ -z "${2:-}" ] || git -C "$W" remote add origin "$2"
  : >"$STUB_LOG"
  rm -f "$TMP/lanes.ran"
}
installer() { OUT="$(cd "$W" && bash scripts/install-git-hooks.sh "$@" 2>&1)"; RC=$?; }
local_ssh() { git -C "$W" config --local --get-all core.sshCommand 2>/dev/null; }
lanes_ran() { cat "$TMP/lanes.ran" 2>/dev/null | tr '\n' ' '; }

echo "== the installer"
new_repo fresh git@github.invalid:owner/trust.git
installer
is "install exits 0" "$RC" 0
is "  ... keeps the non-executable Perl helper's tracked mode" "$([ -x "$W/scripts/hooks/_ssh_probe.pl" ] && printf yes || printf no)" no
is "  ... leaves a clean tracked checkout clean" "$(git -C "$W" status --porcelain)" ""
is "  ... sets core.hooksPath" "$(git -C "$W" config --local --get core.hooksPath)" scripts/hooks
is "  ... sets this clone's core.sshCommand" "$(local_ssh)" "$KEEP"
saw "  ... and reports the keepalive git now uses" 'ssh keepalive: on 30 \(core.sshCommand\)'
not_saw "  ... reading the tuning the checkout declares" 'nothing is tuned'
installer
is "a second install exits 0" "$RC" 0
is "  ... and leaves exactly one value" "$(local_ssh | wc -l | tr -d ' ')" 1
saw "  ... saying it was already set" 'already set by this script'
not_saw "  ... and does not call its own scripts/hooks/pre-push a foreign hook" 'foreign hook'
printf '#!/bin/sh\nexit 0\n' >"$(git -C "$W" rev-parse --path-format=absolute --git-common-dir)/hooks/pre-push"
installer
saw "  ... while a hook someone wrote in .git/hooks is still named" 'foreign hook remains at .*/\.git/hooks/pre-push'
rm -f "$(git -C "$W" rev-parse --path-format=absolute --git-common-dir)/hooks/pre-push"
installer --status
is "--status exits 0 when hooks and keepalive are in place" "$RC" 0
saw "  ... naming the keepalive" 'ssh keepalive: on 30 \(core.sshCommand\) for origin \(git@github.invalid:owner/trust.git\)'
is "  ... every ssh -G was about origin's destination, no port" \
  "$(grep '^probe ' "$STUB_LOG" | sort -u)" "probe git@github.invalid port="
installer --uninstall
is "--uninstall exits 0" "$RC" 0
is "  ... removes core.hooksPath" "$(git -C "$W" config --local --get core.hooksPath)" ""
is "  ... removes the core.sshCommand it set" "$(local_ssh)" ""
installer --status
is "--status after uninstall exits 1" "$RC" 1
saw "  ... the keepalive is reported OFF" 'ssh keepalive: OFF, off \(default ssh\)'
saw "  ... naming the installer as the fix" 'run: bash scripts/install-git-hooks.sh'

new_repo tracked-modes git@github.invalid:owner/trust.git
printf '# data, not a hook\n' >"$W/scripts/hooks/support data.txt"
printf '#!/bin/sh\nexit 0\n' >"$W/scripts/hooks/executable helper"
chmod 644 "$W/scripts/hooks/support data.txt"
chmod 755 "$W/scripts/hooks/executable helper"
git -C "$W" add -A && git -C "$W" commit -qm tracked-modes || exit 2
chmod 644 "$W/scripts/hooks/pre-push" "$W/scripts/hooks/executable helper"
installer
is "install repairs a tracked hook's missing executable bit" "$([ -x "$W/scripts/hooks/pre-push" ] && printf yes || printf no)" yes
is "  ... repairs a tracked executable whose name contains spaces" "$([ -x "$W/scripts/hooks/executable helper" ] && printf yes || printf no)" yes
is "  ... preserves tracked non-executable data with spaces" "$([ -x "$W/scripts/hooks/support data.txt" ] && printf yes || printf no)" no
is "  ... restores the tracked modes without dirtying helpers" "$(git -C "$W" status --porcelain)" ""
installer
is "  ... and repeating installation leaves the checkout clean" "$(git -C "$W" status --porcelain)" ""

new_repo foreign-local git@github.invalid:owner/trust.git
git -C "$W" config --local core.sshCommand "ssh -i /k"
installer
is "an install beside a clone's own core.sshCommand exits 0" "$RC" 0
is "  ... keeps it" "$(local_ssh)" "ssh -i /k"
saw "  ... saying so" "own core.sshCommand \(ssh -i /k\) is kept"
saw "  ... and reports it as keepalive OFF" 'ssh keepalive: OFF'
saw "  ... with the fix for one's own command" 'add -o ServerAliveInterval=30 to it'
installer --uninstall
is "  ... and --uninstall leaves it" "$(local_ssh)" "ssh -i /k"

new_repo global-keepalive git@github.invalid:owner/trust.git
git config --global core.sshCommand "ssh -o ServerAliveInterval=60"
installer
is "an install under a global core.sshCommand sets no local one" "$(local_ssh)" ""
saw "  ... saying where it is" 'set in your global config; it is kept'
saw "  ... and reports its keepalive" 'on 60 \(core.sshCommand\)'
git config --global core.sshCommand "ssh"
installer --status
is "--status with a global ssh command lacking keepalive exits 1" "$RC" 1
saw "  ... with the fix for one's own command" 'add -o ServerAliveInterval=30 to it'
git config --global --unset core.sshCommand

new_repo git-ssh git@github.invalid:owner/trust.git
OUT="$(cd "$W" && GIT_SSH="$TMP/bin/ssh" bash scripts/install-git-hooks.sh 2>&1)"
is "an install with GIT_SSH set sets no core.sshCommand (it would override GIT_SSH)" "$(local_ssh)" ""
saw "  ... saying so" 'GIT_SSH .* is set; core.sshCommand would override it'

new_repo git-ssh-command git@github.invalid:owner/trust.git
OUT="$(cd "$W" && GIT_SSH_COMMAND="ssh -o ServerAliveInterval=5" bash scripts/install-git-hooks.sh 2>&1)"
is "an install with GIT_SSH_COMMAND set still sets core.sshCommand (for pushes without it)" "$(local_ssh)" "$KEEP"
saw "  ... and reports the variable's keepalive, which git prefers" 'on 5 \(GIT_SSH_COMMAND\)'

new_repo https-origin https://example.invalid/owner/trust.git
installer --status
saw "--status for an https origin says there is nothing to check" 'is not an ssh URL; nothing to check'

echo "== the hook, run directly"
new_repo hook git@github.invalid:owner/trust.git
git -C "$W" config core.hooksPath scripts/hooks
SHA="$(git -C "$W" rev-parse HEAD)"
Z=0000000000000000000000000000000000000000
hook() {  # hook <url> [env assignments...]: the hook alone, for one ref update
  local url="$1"; shift
  rm -f "$TMP/lanes.ran"
  OUT="$(cd "$W" && printf 'refs/heads/main %s refs/heads/main %s\n' "$SHA" "$Z" | env "$@" bash scripts/hooks/pre-push origin "$url" 2>&1)"
  RC=$?
}
hook git@github.invalid:owner/trust.git
is "default ssh to an ssh destination: refused, exit 2" "$RC" 2
saw "  ... naming the cause" 'PRE-PUSH: NO SSH KEEPALIVE'
saw "  ... and the fix" 'bash scripts/install-git-hooks.sh'
is "  ... before any lane ran" "$(lanes_ran)" ""
hook ssh://git@github.invalid:2222/owner/trust.git
is "an ssh:// destination with a port: refused" "$RC" 2
is "  ... ssh -G was given that port" "$(grep -c 'port=2222$' "$STUB_LOG")" 1
hook git@github.invalid:owner/trust.git GIT_SSH_COMMAND="ssh -o ServerAliveInterval=15"
is "GIT_SSH_COMMAND with a keepalive: judged" "$RC" 0
saw "  ... reporting it" 'ssh keepalive: on 15 \(GIT_SSH_COMMAND\)'
is "  ... every lane ran" "$(lanes_ran)" "fast scoped "
hook git@github.invalid:owner/trust.git STUB_SSH_DEFAULT=45
is "a keepalive from ssh's own config: judged" "$RC" 0
saw "  ... reporting it" 'ssh keepalive: on 45 \(default ssh\)'
hook git@github.invalid:owner/trust.git STUB_SSH_FAIL=1
is "an ssh whose -G cannot be read: judged on" "$RC" 0
saw "  ... saying so" 'ssh keepalive unknown \(default ssh\)'
hook "$TMP/remote-root/none.git"
is "a path destination is not ssh: judged" "$RC" 0
not_saw "  ... no keepalive line" 'keepalive'
hook git@github.invalid:owner/trust.git FIXTURE_NO_SCOPED=1
is "a profile with no scoped lane: not refused" "$RC" 0
not_saw "  ... and not checked" 'keepalive'
OUT="$(cd "$W" && printf '' | bash scripts/hooks/pre-push origin git@github.invalid:owner/trust.git 2>&1)"
is "the standing reading (no refs on stdin): not refused" "$?" 0
git -C "$W" config core.sshCommand "$KEEP"
hook git@github.invalid:owner/trust.git
is "core.sshCommand as the installer writes it: judged" "$RC" 0
saw "  ... reporting it" 'ssh keepalive: on 30 \(core.sshCommand\)'

echo "== a real git push over (stub) ssh"
git init -q --bare "$STUB_REMOTE_ROOT/owner/trust.git"
new_repo push git@github.invalid:owner/trust.git
git -C "$W" config core.hooksPath scripts/hooks
OUT="$(git -C "$W" push origin HEAD:main 2>&1)"
is "a plain push with default ssh is refused" "$?" 1
saw "  ... by the keepalive check" 'PRE-PUSH: NO SSH KEEPALIVE'
is "  ... and the remote has no main" "$(git -C "$STUB_REMOTE_ROOT/owner/trust.git" rev-parse -q --verify refs/heads/main)" ""
installer
OUT="$(git -C "$W" push origin HEAD:main 2>&1)"
is "after the installer, the same plain push lands" "$?" 0
is "  ... the remote's main is the pushed commit" "$(git -C "$STUB_REMOTE_ROOT/owner/trust.git" rev-parse -q --verify refs/heads/main)" "$(git -C "$W" rev-parse HEAD)"
saw "  ... through the keepalive the installer set" 'ssh keepalive: on 30 \(core.sshCommand\)'

# The hook already requires Python3; these real process controls use no SSH.
python3 "$REPO_ROOT/scripts/tests/ssh_keepalive_process_test.py" || FAILED=1

echo
if [ "$FAILED" -eq 0 ]; then
  echo "ssh keepalive tests: all passed"
  exit 0
fi
echo "ssh keepalive tests: FAILED"
exit 1
