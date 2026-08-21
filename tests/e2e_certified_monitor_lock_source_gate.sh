#!/usr/bin/env bash
# Executable regression for the certified-monitor Cargo source boundary.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
GATE="$ROOT/scripts/check_lockfile_no_git_sources.sh"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/trust-lock-source-gate.XXXXXX")"
trap 'rm -rf -- "$TMP"' EXIT

valid_lock="$TMP/valid.lock"
git_lock="$TMP/git.lock"
unsupported_lock="$TMP/unsupported.lock"
malformed_lock="$TMP/malformed.lock"
quoted_key_lock="$TMP/quoted-key.lock"

# The current constellation may intentionally be between pin epochs, so seed a
# minimal canonical lock rather than weakening the positive case around it.
printf '%s\n' \
    'version = 4' \
    '' \
    '[[package]]' \
    'name = "local-package"' \
    'version = "0.0.0"' \
    '' \
    '[[package]]' \
    'name = "registry-package"' \
    'version = "1.0.0"' \
    'source = "registry+https://github.com/rust-lang/crates.io-index"' \
    'checksum = "0000000000000000000000000000000000000000000000000000000000000000"' \
    '# source = "git+https://example.invalid/comment-only.git"' \
    > "$valid_lock"
"$GATE" "$valid_lock"

cp "$valid_lock" "$git_lock"
printf '%s\n' \
    '' \
    '[[package]]' \
    'name = "escaped-git-package"' \
    'version = "1.0.0"' \
    'source = "git+https://github.com/example/escaped.git?rev=0123456789abcdef#0123456789abcdef"' \
    >> "$git_lock"
if "$GATE" "$git_lock" >"$TMP/git.stdout" 2>"$TMP/git.stderr"; then
    echo "error: Git-sourced package row passed the certified-monitor source gate" >&2
    exit 1
fi
grep -F 'contains 1 Git-sourced package(s)' "$TMP/git.stderr" >/dev/null

cp "$valid_lock" "$unsupported_lock"
printf '%s\n' \
    '' \
    '[[package]]' \
    'name = "unsupported-package"' \
    'version = "1.0.0"' \
    'source = "sparse+https://example.invalid/index"' \
    >> "$unsupported_lock"
if "$GATE" "$unsupported_lock" >"$TMP/unsupported.stdout" 2>"$TMP/unsupported.stderr"; then
    echo "error: unsupported package source passed the certified-monitor source gate" >&2
    exit 1
fi
grep -F 'unsupported non-registry package source row(s)' "$TMP/unsupported.stderr" >/dev/null

cp "$valid_lock" "$malformed_lock"
printf '%s\n' \
    '' \
    '[[package]]' \
    'name = "malformed-package"' \
    'version = "1.0.0"' \
    ' source = "git+https://example.invalid/non-canonical.git"' \
    >> "$malformed_lock"
if "$GATE" "$malformed_lock" >"$TMP/malformed.stdout" 2>"$TMP/malformed.stderr"; then
    echo "error: non-canonical package source passed the certified-monitor source gate" >&2
    exit 1
fi
grep -F 'malformed/non-canonical package source row(s)' "$TMP/malformed.stderr" >/dev/null

cp "$valid_lock" "$quoted_key_lock"
printf '%s\n' \
    '' \
    '[[package]]' \
    'name = "quoted-source-key-package"' \
    'version = "1.0.0"' \
    '"source" = "git+https://example.invalid/quoted-key.git"' \
    >> "$quoted_key_lock"
if "$GATE" "$quoted_key_lock" >"$TMP/quoted.stdout" 2>"$TMP/quoted.stderr"; then
    echo "error: quoted non-canonical source key passed the certified-monitor source gate" >&2
    exit 1
fi
grep -F 'malformed/non-canonical package source row(s)' "$TMP/quoted.stderr" >/dev/null

ln -s "$valid_lock" "$TMP/symlink.lock"
if "$GATE" "$TMP/symlink.lock" >"$TMP/symlink.stdout" 2>"$TMP/symlink.stderr"; then
    echo "error: symlinked Cargo lockfile passed the certified-monitor source gate" >&2
    exit 1
fi
grep -F 'not one exact regular file' "$TMP/symlink.stderr" >/dev/null

echo "certified-monitor lock source gate e2e: PASS"
