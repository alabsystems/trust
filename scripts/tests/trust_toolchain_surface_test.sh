#!/bin/sh

set -eu

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
. "$ROOT/scripts/lib/trust_toolchain_surface.sh"

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/trust-toolchain-surface-test.XXXXXX")"
trap 'rm -rf "$TMP_ROOT"' EXIT HUP INT TERM

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

write_executable() {
    path="$1"
    text="$2"
    printf '%s\n' "$text" >"$path"
    chmod +x "$path"
}

bin="$TMP_ROOT/selected/bin"
ambient="$TMP_ROOT/ambient/bin"
mkdir -p "$bin" "$ambient"
write_executable "$bin/trustc" 'canonical compiler fixture'
cp "$bin/trustc" "$bin/rustc"
chmod +x "$bin/rustc"

trust_toolchain_alias_pair_valid "$bin" trustc rustc \
    || fail "same-bin byte-identical alias pair was rejected"

rm "$bin/rustc"
ln -s trustc "$bin/rustc"
trust_toolchain_alias_pair_valid "$bin" trustc rustc \
    || fail "same-bin symlink to the canonical artifact was rejected"

rm "$bin/rustc"
cp "$bin/trustc" "$ambient/rustc"
chmod +x "$ambient/rustc"
ln -s "$ambient/rustc" "$bin/rustc"
if trust_toolchain_alias_pair_valid "$bin" trustc rustc; then
    fail "outward alias symlink passed despite byte-identical ambient target"
fi
error="$(trust_toolchain_alias_pair_error "$bin" trustc rustc)"
case "$error" in
    *'rustc resolves outside selected bin directory:'*) ;;
    *) fail "outward alias error was not explicit: $error" ;;
esac

rm "$bin/rustc"
write_executable "$bin/rustc" 'different compiler fixture'
if trust_toolchain_alias_pair_valid "$bin" trustc rustc; then
    fail "same-bin mismatched compatibility binary passed"
fi

rm "$bin/trustc" "$bin/rustc"
write_executable "$ambient/trustc" 'canonical compiler fixture'
ln -s "$ambient/trustc" "$bin/trustc"
ln -s trustc "$bin/rustc"
if trust_toolchain_alias_pair_valid "$bin" trustc rustc; then
    fail "outward canonical tool symlink passed through its local alias"
fi

rm "$bin/trustc" "$bin/rustc"
write_executable "$bin/trustc" 'canonical compiler fixture'
cp "$bin/trustc" "$bin/rustc"
chmod +x "$bin/rustc"
trust_toolchain_forbidden_entries_absent "$bin" \
    || fail "canonical surface was classified as forbidden"

write_executable "$bin/rust-lldb" 'retired debugger fixture'
if trust_toolchain_forbidden_entries_absent "$bin"; then
    fail "retired debugger spelling escaped forbidden-surface validation"
fi
rm "$bin/rust-lldb"

mkdir -p "$TMP_ROOT/selected/libexec"
ln -s "$TMP_ROOT/missing-helper" \
    "$TMP_ROOT/selected/libexec/rust-analyzer-proc-macro-srv"
if trust_toolchain_forbidden_entries_absent "$bin"; then
    fail "dangling forbidden libexec alias escaped validation"
fi

echo "Trust toolchain surface tests: ok"
