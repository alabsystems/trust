#!/bin/sh

set -eu

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
SOURCE_SCRIPT="$ROOT/scripts/rustup-link-trust.sh"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/rustup-link-trust-test.XXXXXX")"
cleanup() {
    chmod -R u+w "$TMP_ROOT" 2>/dev/null || true
    rm -rf "$TMP_ROOT"
}
trap cleanup EXIT HUP INT TERM

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

new_stage1_fixture() {
    name="$1"
    fixture="$TMP_ROOT/$name"
    mkdir -p \
        "$fixture/scripts/lib" \
        "$fixture/build/host/stage1/bin" \
        "$fixture/fake-bin"
    cp "$SOURCE_SCRIPT" "$fixture/scripts/rustup-link-trust.sh"
    cp "$ROOT/scripts/lib/trust_toolchain_surface.sh" "$fixture/scripts/lib/"
    chmod +x "$fixture/scripts/rustup-link-trust.sh"

    cat >"$fixture/build/host/stage1/bin/trustc" <<'SH'
#!/bin/sh
echo 'trustc fixture (trustc)'
SH
    chmod +x "$fixture/build/host/stage1/bin/trustc"

    cat >"$fixture/fake-bin/rustup" <<'SH'
#!/bin/sh
printf '%s\n' "$*" >"${RUSTUP_CALL_LOG:?}"
SH
    chmod +x "$fixture/fake-bin/rustup"
    printf '%s\n' "$fixture"
}

new_external_stage2_fixture() {
    name="$1"
    fixture="$TMP_ROOT/$name"
    sysroot="$fixture/external/trust"
    mkdir -p \
        "$fixture/scripts/lib" \
        "$fixture/fake-bin" \
        "$sysroot/bin" \
        "$sysroot/libexec" \
        "$sysroot/lib/rustlib/fixture/lib" \
        "$sysroot/lib/rustlib/src/rust/library" \
        "$sysroot/lib/rustlib/rustc-src/rust"
    cp "$SOURCE_SCRIPT" "$fixture/scripts/rustup-link-trust.sh"
    cp "$ROOT/scripts/lib/trust_toolchain_surface.sh" "$fixture/scripts/lib/"
    chmod +x "$fixture/scripts/rustup-link-trust.sh"

    cat >"$sysroot/bin/tool-dispatch" <<'SH'
#!/bin/sh
tool="${0##*/}"
root="$(cd "$(dirname "$0")/.." && pwd -P)"
case "$tool:$*" in
    trustc:*'--print sysroot'*) printf '%s\n' "$root" ;;
    rustc:*'--print sysroot'*) printf '%s\n' "$root" ;;
    trustc:*'--print target-libdir'*) printf '%s\n' "$root/lib/rustlib/fixture/lib" ;;
    rustc:*'--print target-libdir'*) printf '%s\n' "$root/lib/rustlib/fixture/lib" ;;
    trustc:*|rustc:*) echo 'rustc fixture (trustc)' ;;
    targo:*|cargo:*) echo 'targo 1.99.0-fixture' ;;
    trustdoc:*) echo 'rustdoc fixture (trustdoc)' ;;
    *) echo "$tool fixture" ;;
esac
SH
    chmod +x "$sysroot/bin/tool-dispatch"
    for tool in \
        trustc rustc targo cargo targo-trust trustd trustdoc trustfmt targo-fmt \
        tippy targo-tippy tippy-driver trust-analyzer
    do
        ln -s tool-dispatch "$sysroot/bin/$tool"
    done
    : >"$sysroot/lib/rustlib/fixture/lib/libstd-fixture.rlib"
    cat >"$sysroot/libexec/trust-analyzer-proc-macro-srv" <<'SH'
#!/bin/sh
echo 'trust analyzer proc macro fixture'
SH
    chmod +x "$sysroot/libexec/trust-analyzer-proc-macro-srv"

    cat >"$fixture/fake-bin/rustup" <<'SH'
#!/bin/sh
printf '%s\n' "$*" >"${RUSTUP_CALL_LOG:?}"
SH
    chmod +x "$fixture/fake-bin/rustup"
    printf '%s\n' "$fixture"
}

run_link() {
    fixture="$1"
    shift
    PATH="$fixture/fake-bin:$PATH" \
        RUSTUP_CALL_LOG="$fixture/rustup-call.log" \
        "$fixture/scripts/rustup-link-trust.sh" "$@"
}

# Validation-only mode must not mutate a missing compatibility surface.
fixture="$(new_stage1_fixture no-repair)"
if run_link "$fixture" stage1 >"$fixture/stdout" 2>"$fixture/stderr"; then
    fail "stage1 without rustc unexpectedly passed without --repair-aliases"
fi
grep -q 'missing required stage1 tool: .*bin/rustc' "$fixture/stderr" \
    || fail "missing rustc failure was not explicit"
[ ! -e "$fixture/build/host/stage1/bin/rustc" ] \
    || fail "validation-only mode created rustc"
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after failed validation"

# Opt-in repair creates only rustc and proves it is the canonical artifact.
fixture="$(new_stage1_fixture repair)"
run_link "$fixture" --repair-aliases stage1 >"$fixture/stdout" 2>"$fixture/stderr"
[ -L "$fixture/build/host/stage1/bin/rustc" ] || fail "repair did not create rustc symlink"
[ "$(readlink "$fixture/build/host/stage1/bin/rustc")" = trustc ] \
    || fail "rustc repair does not target canonical trustc"
cmp -s "$fixture/build/host/stage1/bin/trustc" "$fixture/build/host/stage1/bin/rustc" \
    || fail "repaired rustc is not the canonical artifact"
grep -q '^toolchain link trust-stage1 .*/build/host/stage1$' "$fixture/rustup-call.log" \
    || fail "validated fixture was not linked through rustup"

# Repair must not overwrite a mismatched pre-existing compatibility binary.
fixture="$(new_stage1_fixture mismatch)"
cat >"$fixture/build/host/stage1/bin/rustc" <<'SH'
#!/bin/sh
echo 'unrelated rustc fixture'
SH
chmod +x "$fixture/build/host/stage1/bin/rustc"
if run_link "$fixture" --repair-aliases stage1 >"$fixture/stdout" 2>"$fixture/stderr"; then
    fail "mismatched rustc unexpectedly passed same-artifact validation"
fi
grep -q 'trustc and rustc are not byte-identical same-surface artifacts' "$fixture/stderr" \
    || fail "same-artifact failure was not explicit"
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after artifact mismatch"

# Byte identity is insufficient: the alias target must resolve inside the selected bin.
fixture="$(new_stage1_fixture outward-alias)"
mkdir -p "$fixture/ambient/bin"
cp "$fixture/build/host/stage1/bin/trustc" "$fixture/ambient/bin/rustc"
chmod +x "$fixture/ambient/bin/rustc"
ln -s "$fixture/ambient/bin/rustc" "$fixture/build/host/stage1/bin/rustc"
if run_link "$fixture" stage1 >"$fixture/stdout" 2>"$fixture/stderr"; then
    fail "byte-identical outward rustc symlink unexpectedly passed same-sysroot validation"
fi
grep -q 'rustc resolves outside selected bin directory' "$fixture/stderr" \
    || fail "outward alias failure was not explicit"
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after outward alias rejection"

# Secondary Rust spellings remain forbidden and are never manufactured by repair.
fixture="$(new_stage1_fixture repair-does-not-grow-secondary-aliases)"
cp "$fixture/build/host/stage1/bin/trustc" "$fixture/build/host/stage1/bin/trust-gdb"
chmod +x "$fixture/build/host/stage1/bin/trust-gdb"
run_link "$fixture" --repair-aliases stage1 >"$fixture/stdout" 2>"$fixture/stderr"
[ ! -e "$fixture/build/host/stage1/bin/rust-gdb" ] \
    || fail "repair created forbidden rust-gdb from trust-gdb"

fixture="$(new_stage1_fixture forbidden-secondary)"
cp "$fixture/build/host/stage1/bin/trustc" "$fixture/build/host/stage1/bin/rust-lldb"
chmod +x "$fixture/build/host/stage1/bin/rust-lldb"
if run_link "$fixture" --repair-aliases stage1 >"$fixture/stdout" 2>"$fixture/stderr"; then
    fail "stage1 with forbidden rust-lldb unexpectedly linked"
fi
grep -q 'forbidden stock or retired public entrypoint is present: .*bin/rust-lldb' "$fixture/stderr" \
    || fail "forbidden debugger spelling failure was not explicit"
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran with forbidden secondary alias"

# Direct Trust tools are not rustup proxies and must never be taught +toolchain syntax.
if grep -Eq '(trustc|targo) \+[^[:space:]]+' "$SOURCE_SCRIPT"; then
    fail "rustup link guidance teaches unsupported direct Trust-tool +toolchain syntax"
fi
grep -q 'rustup run trust-stage1 trustc --version' "$TMP_ROOT/repair/stdout" \
    || fail "post-link guidance does not use rustup run for canonical trustc"

# An explicit external sysroot is validated without any attempt to repair it.
fixture="$(new_external_stage2_fixture external-read-only)"
external_sysroot="$fixture/external/trust"
chmod -R a-w "$external_sysroot"
run_link "$fixture" --name trust-external --sysroot "$external_sysroot" \
    >"$fixture/stdout" 2>"$fixture/stderr"
grep -q '^toolchain link trust-external .*/external/trust$' "$fixture/rustup-call.log" \
    || fail "external sysroot was not linked through its canonical path"
grep -q 'alias repair: forbidden for external --sysroot' "$fixture/stderr" \
    || fail "external validation did not state the immutable no-repair policy"

# Repair requests and stage selectors are both incompatible with --sysroot.
rm -f "$fixture/rustup-call.log"
if run_link "$fixture" --repair-aliases --sysroot "$external_sysroot" \
    >"$fixture/repair-stdout" 2>"$fixture/repair-stderr"; then
    fail "external sysroot unexpectedly accepted --repair-aliases"
fi
grep -q 'alias repair is forbidden with --sysroot' "$fixture/repair-stderr" \
    || fail "external repair rejection was not explicit"
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after external repair rejection"

if run_link "$fixture" stage2 --sysroot "$external_sysroot" \
    >"$fixture/stage-stdout" 2>"$fixture/stage-stderr"; then
    fail "external sysroot unexpectedly accepted a stage selector"
fi
grep -q -- '--sysroot is mutually exclusive with stage1/stage2' "$fixture/stage-stderr" \
    || fail "external stage-selection rejection was not explicit"
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after stage/sysroot rejection"

echo "rustup-link-trust tests: ok"
