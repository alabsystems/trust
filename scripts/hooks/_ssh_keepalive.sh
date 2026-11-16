#!/usr/bin/env bash
# Does git's ssh connection to a push destination keep itself alive? Sourced by
# scripts/hooks/pre-push (which refuses early when it does not) and by
# scripts/install-git-hooks.sh (which sets a keepalive and reports it).
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY (2026-10-24, docs/DECISION_QUEUE.md PUSH-PATH-SSH-KEEPALIVE). git opens the
# push's connection BEFORE it runs pre-push and holds it idle for the whole
# hook, and GitHub closes an idle ssh connection. Measured 2026-10-24 with an
# idle `git-receive-pack` (no pack sent, nothing pushed): default ssh
# (`serveraliveinterval 0`) was cut, "Connection to github.com closed by remote
# host", after 362 s; with ServerAliveInterval=30 it was still open at 532 s,
# when it was closed by hand. The fast tier alone takes about 4.4 minutes and
# the scoped lanes 15-35, so with default ssh a hook that passes still loses
# the push at its end. No hook code can repair a connection git opened before
# the hook ran; the fix is the ssh command git runs, which only configuration
# names. So the installer sets one (TRUST_SSH_KEEPALIVE_COMMAND) and the hook
# reads, before any lane, what this file reads.
#
# WHAT GIT RUNS (connect.c): GIT_SSH_COMMAND, else core.sshCommand (both
# through the shell, as `sh -c '<command> "$@"' <command> <args>`), else the
# program GIT_SSH, else `ssh`. trust_ssh_keepalive runs that same command with
# `-G`, which prints the configuration ssh would use for the destination
# (command-line `-o` options and ~/.ssh/config, Match blocks included) and
# connects to nothing.
#
# Functions (no output on stderr, no side effects):
#   trust_ssh_target URL     "<[user@]host>\t<port or empty>" for an ssh URL
#                            (scp-like `[user@]host:path` or ssh://), status 0;
#                            status 1 for any other URL (a path, file://,
#                            https://, git://).
#   trust_ssh_command        "<how>\t<shell 1|0>\t<command>": what git runs.
#   trust_ssh_keepalive URL  one line, and its status:
#                              0 "on <seconds> (<how>)"
#                              1 "off (<how>)"
#                              2 "unknown (<how>): <why>"  (ssh -G unreadable)
#                              3 "not ssh"
#
# TRUST_SSH_KEEPALIVE_COMMAND is the value the installer writes; the hook names
# it in its refusal. 30 s x 10 tolerates five minutes of a silent network
# before ssh itself gives up, well beyond a laptop's Wi-Fi handover.

TRUST_SSH_KEEPALIVE_COMMAND="ssh -o ServerAliveInterval=30 -o ServerAliveCountMax=10"
TRUST_SSH_PROBE_HELPER="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/_ssh_probe.pl"

trust_ssh_target() {
  local url="${1:-}" hostpart port=""
  case "$url" in
    ssh://*|git+ssh://*|ssh+git://*)
      hostpart="${url#*://}"
      hostpart="${hostpart%%/*}"
      ;;
    *://*|"") return 1 ;;
    \[*\]:*)
      # git's bracketed scp-like form, `[user@host:port]:path`.
      hostpart="${url#\[}"
      hostpart="${hostpart%%\]*}"
      ;;
    *:*)
      # scp-like when a colon comes before any slash (git's rule), and not a
      # one-letter drive prefix.
      hostpart="${url%%:*}"
      case "$hostpart" in */*|?|"") return 1 ;; esac
      printf '%s\t\n' "$hostpart"
      return 0
      ;;
    *) return 1 ;;
  esac
  # ssh:// and the bracketed form: [user@]host[:port], host possibly [v6].
  case "$hostpart" in
    *\]:*) port="${hostpart##*\]:}"; hostpart="${hostpart%:*}" ;;
    *\]*) ;;
    *:*) port="${hostpart##*:}"; hostpart="${hostpart%:*}" ;;
  esac
  case "$port" in *[!0-9]*) return 1 ;; esac
  hostpart="${hostpart/\[/}"
  hostpart="${hostpart/\]/}"
  [ -n "$hostpart" ] || return 1
  printf '%s\t%s\n' "$hostpart" "$port"
}

trust_ssh_command() {
  local configured
  if [ -n "${GIT_SSH_COMMAND:-}" ]; then
    printf 'GIT_SSH_COMMAND\t1\t%s\n' "$GIT_SSH_COMMAND"
  elif configured="$(git config --get core.sshCommand 2>/dev/null)" && [ -n "$configured" ]; then
    printf 'core.sshCommand\t1\t%s\n' "$configured"
  elif [ -n "${GIT_SSH:-}" ]; then
    printf 'GIT_SSH\t0\t%s\n' "$GIT_SSH"
  else
    printf 'default ssh\t0\tssh\n'
  fi
}

trust_ssh_keepalive() {
  local target dest port how shell command out interval
  local args=()
  target="$(trust_ssh_target "${1:-}")" || { echo "not ssh"; return 3; }
  IFS=$'\t' read -r dest port <<<"$target"
  IFS=$'\t' read -r how shell command <<<"$(trust_ssh_command)"
  args=(-G)
  [ -z "$port" ] || args+=(-p "$port")
  args+=("$dest")
  # Ten seconds to capture, then bounded TERM/KILL/reap/group closure. A
  # Match exec or wrapper can retain stdout after its leader exits; alarm on
  # that leader alone cannot bound command substitution. The helper owns its
  # new session and retains the leader PID until its last group signal.
  if [ "$shell" = 1 ]; then
    out="$(perl "$TRUST_SSH_PROBE_HELPER" -- sh -c "$command \"\$@\"" "$command" "${args[@]}" 2>/dev/null)"
  else
    out="$(perl "$TRUST_SSH_PROBE_HELPER" -- "$command" "${args[@]}" 2>/dev/null)"
  fi || {
    echo "unknown ($how): \`$command -G\` failed, so its keepalive cannot be read"
    return 2
  }
  interval="$(awk '$1 == "serveraliveinterval" { print $2; exit }' <<<"$out")"
  case "$interval" in
    ""|*[!0-9]*)
      echo "unknown ($how): \`$command -G\` printed no serveraliveinterval"
      return 2
      ;;
    0)
      echo "off ($how)"
      return 1
      ;;
  esac
  echo "on $interval ($how)"
  return 0
}
