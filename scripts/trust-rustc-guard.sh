#!/usr/bin/env bash
# Copyright 2026 The Trust Authors
# SPDX-License-Identifier: Apache-2.0 OR MIT
#
# trust-rustc-guard.sh — a graceful RUSTC_WRAPPER that nudges humans away from
# raw `cargo` and toward the Trust frontends in the Trust repos.
#
# WHY: raw `cargo build` / `cargo build-dev` is a footgun here. On a source
# cache-hit cargo skips rustc entirely, so trustc never re-runs and you get a
# STALE codegen binary (the "Trust Gap 4" symptom); and raw cargo compiles with
# NONE of the Trust verifier flags, so the binary looks built but carries no
# obligations. `targo trust` force-cleans the selected package before proof,
# pins RUSTC to stage2 trustc, injects explicit verifier flags, and audits the
# JSON transport. Use `targo` for Cargo-compatible work and `targo trust` for
# verification evidence.
#
# DESIGN (deliberately NON-kludgey):
#   * It is a RUSTC_WRAPPER, so it sees EVERY rustc spawn regardless of cache
#     state or which crate has a build.rs (a per-crate build.rs misses the exact
#     cache-hit case that bites here; the workspace root has no [package] so it
#     can't carry one at all).
#   * It NEVER blocks by default — it prints ONE notice per build and execs the
#     real rustc, so it cannot break `x.py` bootstrap or any legitimate flow.
#     Opt into hard-fail with TRUST_STRICT_CARGO=1.
#   * It stays SILENT under targo (compiler descendants carry the internal
#     TRUST_TARGO_FRONTEND=1 lineage marker) and for cargo's metadata/version
#     probes, so there is zero noise on the supported path.
set -euo pipefail

# cargo passes the real rustc as $1, then its args.
REAL_RUSTC="$1"; shift

# --- pass straight through on every legitimate path (no message) --------------
# TRUST_TARGO_VERIFY is a separate internal marker used only when an external
# verifier driver also injects a fresh proof-session nonce and tracked Trust
# policy; neither marker is a compiler-side verification switch. x.py/bootstrap
# may disable the guard.
if [ "${TRUST_TARGO_FRONTEND:-}" = "1" ] || \
   [ "${TRUST_TARGO_VERIFY:-}" = "1" ] || \
   [ "${TRUST_RUSTC_GUARD:-}" = "off" ]; then
	exec "$REAL_RUSTC" "$@"
fi
# Version/print probes carry no crate and must never be disturbed (cargo uses
# them for metadata; blocking or even printing here can corrupt that output).
case " $* " in
	*" -vV "* | *" --version "* | *" --print"*)
		exec "$REAL_RUSTC" "$@" ;;
esac

# --- raw cargo: warn once per build, then proceed (or hard-fail if strict) -----
# One notice per cargo invocation. Keep markers below a private per-user root,
# and opportunistically remove only markers whose recorded parent is dead or
# whose PID has been reused with a different process start time. This bounds
# marker accumulation without deleting the live marker shared by concurrent
# rustc siblings. Atomic mkdir elects exactly one notice writer.
_parent_started="$(ps -o lstart= -p "$PPID" 2>/dev/null || true)"
_parent_started="${_parent_started//[![:alnum:]]/_}"
_guard_uid="$(id -u 2>/dev/null || printf 'unknown')"
_guard_uid="${_guard_uid//[![:alnum:]]/_}"
_marker_root="${TMPDIR:-/tmp}/trust-rustc-guard-${_guard_uid:-unknown}"
_marker_root_ready=0
if (umask 077 && mkdir "$_marker_root") 2>/dev/null; then
	_marker_root_ready=1
elif [ -d "$_marker_root" ] && [ ! -L "$_marker_root" ] && \
     [ -O "$_marker_root" ] && chmod 700 "$_marker_root" 2>/dev/null; then
	# Refuse attacker-owned directories and symlinks below a shared /tmp.
	# `-O` is a bash ownership test (this script's interpreter is bash).
	_marker_root_ready=1
fi
if [ "$_marker_root_ready" = 1 ]; then
	for _candidate in "$_marker_root"/cargo.*; do
		[ -d "$_candidate" ] || continue
		_candidate_name="${_candidate##*/}"
		_candidate_identity="${_candidate_name#cargo.}"
		_candidate_pid="${_candidate_identity%%.*}"
		_candidate_started="${_candidate_identity#*.}"
		case "$_candidate_pid" in
			'' | *[!0-9]*) continue ;;
		esac
		_candidate_stale=0
		if ! kill -0 "$_candidate_pid" 2>/dev/null; then
			_candidate_stale=1
		elif [ "$_candidate_started" != "unknown" ]; then
			_live_started="$(ps -o lstart= -p "$_candidate_pid" 2>/dev/null || true)"
			_live_started="${_live_started//[![:alnum:]]/_}"
			if [ -n "$_live_started" ] && [ "$_live_started" != "$_candidate_started" ]; then
				_candidate_stale=1
			fi
		fi
		if [ "$_candidate_stale" = 1 ]; then
			# Guard markers are empty directories. rmdir is deliberately used
			# instead of rm -rf so pruning can never follow or erase attacker-
			# controlled content beneath a shared temporary directory.
			rmdir "$_candidate" 2>/dev/null || true
		fi
	done
fi

_marker="$_marker_root/cargo.${PPID}.${_parent_started:-unknown}"
_print_notice=0
if [ "$_marker_root_ready" = 1 ]; then
	if mkdir "$_marker" 2>/dev/null; then
		_print_notice=1
	fi
else
	# If the private marker root cannot be secured, retain the warning instead
	# of silently suppressing it through an unsafe shared path.
	_print_notice=1
fi

if [ "$_print_notice" = 1 ]; then
	cat >&2 <<'EOF'

  ┌─ Trust ───────────────────────────────────────────────────────────────┐
  │ You are building with raw `cargo`. Use the Trust frontends instead.    │
  │                                                                        │
  │ Raw cargo can serve a STALE trustc binary (cache-hit ⇒ trustc never    │
  │ re-runs) and compiles with NO verifier flags. `targo trust` cleans     │
  │ the package, pins stage2 trustc, injects verifier flags, and audits    │
  │ the JSON transport — so proof results are real and reproducible.       │
  │                                                                        │
  │   targo --unverified build -p <crate> # explicit compatibility build │
  │   targo trust check                   # verifier, fail-closed          │
  │   targo trust kani --crate <c> --proof <p>                            │
  │                                                                        │
  │ Proceeding anyway (this is only a warning). Set TRUST_STRICT_CARGO=1   │
  │ to make raw cargo a hard error; see scripts/trust-rustc-guard.sh.      │
  └────────────────────────────────────────────────────────────────────────┘

EOF
fi

# Strict mode applies to every rustc child, not only the child that won the
# one-notice marker race. Otherwise later/concurrent siblings could compile
# after the first wrapper failed, contradicting the requested hard guard.
if [ "${TRUST_STRICT_CARGO:-}" = "1" ]; then
	echo "  trust-rustc-guard: TRUST_STRICT_CARGO=1 — refusing raw cargo." >&2
	exit 1
fi

exec "$REAL_RUSTC" "$@"
