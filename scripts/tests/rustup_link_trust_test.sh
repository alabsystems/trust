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
    targo-fmt:*) echo 'trustfmt 1.9.0-fixture' ;;
    targo-tippy:*|tippy-driver:*) echo 'tippy 0.1.0-fixture' ;;
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

# The Trust brand parenthetical carries a VERSION on every ordinary build.
# rustc_driver_impl emits " ({display_binary} {trust_version})" when
# CFG_TRUST_VERSION is set and " ({display_binary})" only when it is not
# (compiler/rustc_driver_impl/src/lib.rs:2382-2389), so a check written against
# the literal "(trustc)" refused every real toolchain built since that version
# was threaded through -- measured 2026-08-22 on a stage1 sysroot that passes
# tools/verify-toolchain.sh in full. Both shapes must link.
fixture="$(new_external_stage2_fixture external-versioned-brand)"
external_sysroot="$fixture/external/trust"
sed -e 's/(trustc)/(trustc 0.1.0)/' -e 's/(trustdoc)/(trustdoc 0.1.0)/' \
    "$external_sysroot/bin/tool-dispatch" >"$fixture/tool-dispatch.versioned"
cat "$fixture/tool-dispatch.versioned" >"$external_sysroot/bin/tool-dispatch"
if ! run_link "$fixture" --name trust-versioned --sysroot "$external_sysroot" \
    >"$fixture/stdout" 2>"$fixture/stderr"; then
    sed 's/^/    /' "$fixture/stderr" >&2
    fail "versioned Trust brand '(trustc 0.1.0)' was refused"
fi
grep -q '^toolchain link trust-versioned .*/external/trust$' "$fixture/rustup-call.log" \
    || fail "versioned Trust brand '(trustc 0.1.0)' was not accepted for linking"

# An unbranded rustc is still refused: the brand is what distinguishes a Trust
# compiler from a stock one wearing the same banner.
fixture="$(new_external_stage2_fixture external-unbranded)"
external_sysroot="$fixture/external/trust"
sed -e 's/ (trustc)//' "$external_sysroot/bin/tool-dispatch" \
    >"$fixture/tool-dispatch.unbranded"
cat "$fixture/tool-dispatch.unbranded" >"$external_sysroot/bin/tool-dispatch"
if run_link "$fixture" --name trust-unbranded --sysroot "$external_sysroot" \
    >"$fixture/stdout" 2>"$fixture/stderr"; then
    fail "an unbranded rustc was linked as a Trust toolchain"
fi
grep -q "trustc --version does not carry the Trust brand" "$fixture/stderr" \
    || fail "unbranded rejection was not explicit"
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after an unbranded rejection"

# Every Trust tool with a stock ancestor is held to its own name, not just the
# compiler: a stock rustfmt, clippy or rust-analyzer installed under the Trust
# name (a stale tools-directory artifact restored by bootstrap, a hand copy)
# runs and answers --version, so only the banner tells them apart. Each case
# swaps ONE tool for a stand-in that prints the stock program's real banner
# (measured from rustup's stable 1.98.0, 2026-09-30).
for case in \
    'trustfmt:rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)' \
    'targo-fmt:rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)' \
    'tippy:clippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'targo-tippy:clippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'tippy-driver:clippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'trust-analyzer:rust-analyzer 1.98.0 (88d9e12a 2026-08-18)' \
    'targo:cargo 1.98.0 (797e8a9bc 2026-08-05)' \
    'trustdoc:rustdoc 1.98.0 (88d9e12ae 2026-08-18)'
do
    tool="${case%%:*}"
    banner="${case#*:}"
    fixture="$(new_external_stage2_fixture "external-stock-$tool")"
    external_sysroot="$fixture/external/trust"
    rm "$external_sysroot/bin/$tool"
    printf '#!/bin/sh\necho %s\n' "'$banner'" >"$external_sysroot/bin/$tool"
    chmod +x "$external_sysroot/bin/$tool"
    # `cargo` is held byte-identical to `targo`; keep that pairing intact so
    # the identity check is what refuses. (This fixture carries no `rustdoc`.)
    if [ "$tool" = targo ]; then
        rm "$external_sysroot/bin/cargo"
        cp "$external_sysroot/bin/targo" "$external_sysroot/bin/cargo"
    fi
    if run_link "$fixture" --name "trust-stock-$tool" --sysroot "$external_sysroot" \
        >"$fixture/stdout" 2>"$fixture/stderr"; then
        fail "a stock program under the Trust name $tool was linked as a Trust toolchain"
    fi
    grep -qF "/bin/$tool: a stock program under a Trust name" "$fixture/stderr" \
        || { sed 's/^/    /' "$fixture/stderr" >&2; fail "stock $tool was refused for the wrong reason"; }
    [ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after stock $tool was refused"
done

# Identity is read from standard output alone. A genuine targo prints Cargo's
# configuration warnings on stderr BEFORE its banner (an unused key in a
# .cargo/config.toml in the working directory or a parent; a CARGO_HOME holding
# both `config` and `config.toml`); read merged, that warning was the first line
# and the real Targo was refused as a stock program.
fixture="$(new_external_stage2_fixture external-targo-stderr-warning)"
external_sysroot="$fixture/external/trust"
sed -e "s|^    targo:\*\|cargo:\*) echo 'targo 1.99.0-fixture' ;;|    targo:*\|cargo:*) echo 'warning: unused config key \`unstable.foo\` in \`/fixture/.cargo/config.toml\`' >\&2; echo 'targo 1.99.0-fixture' ;;|" \
    "$external_sysroot/bin/tool-dispatch" >"$fixture/tool-dispatch.warning"
grep -q 'warning: unused config key' "$fixture/tool-dispatch.warning" \
    || fail "stderr-warning fixture was not constructed"
cat "$fixture/tool-dispatch.warning" >"$external_sysroot/bin/tool-dispatch"
if ! run_link "$fixture" --name trust-targo-warning --sysroot "$external_sysroot" \
    >"$fixture/stdout" 2>"$fixture/stderr"; then
    sed 's/^/    /' "$fixture/stderr" >&2
    fail "a targo that warns on stderr before its banner was refused"
fi
grep -q '^toolchain link trust-targo-warning .*/external/trust$' "$fixture/rustup-call.log" \
    || fail "a targo that warns on stderr before its banner was not linked"

# ...and stderr cannot vouch for a stock stdout banner.
fixture="$(new_external_stage2_fixture external-stderr-vouch)"
external_sysroot="$fixture/external/trust"
rm "$external_sysroot/bin/trustfmt"
cat >"$external_sysroot/bin/trustfmt" <<'SH'
#!/bin/sh
echo 'trustfmt 1.9.0-fixture' >&2
echo 'rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)'
SH
chmod +x "$external_sysroot/bin/trustfmt"
if run_link "$fixture" --name trust-stderr-vouch --sysroot "$external_sysroot" \
    >"$fixture/stdout" 2>"$fixture/stderr"; then
    fail "a Trust banner on stderr vouched for a stock stdout banner"
fi
grep -qF 'trustfmt --version does not identify the Trust build' "$fixture/stderr" \
    || { sed 's/^/    /' "$fixture/stderr" >&2; fail "stderr-vouched trustfmt was refused for the wrong reason"; }
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after a stderr-vouched trustfmt"

# The same holds at stage1, which used to check no banner at all.
fixture="$(new_stage1_fixture stage1-stock-trustc)"
cat >"$fixture/build/host/stage1/bin/trustc" <<'SH'
#!/bin/sh
echo 'rustc 1.98.0 (88d9e12ae 2026-08-18)'
SH
chmod +x "$fixture/build/host/stage1/bin/trustc"
if run_link "$fixture" --repair-aliases stage1 >"$fixture/stdout" 2>"$fixture/stderr"; then
    fail "a stock rustc under the name trustc was linked as trust-stage1"
fi
grep -q "trustc --version does not carry the Trust brand" "$fixture/stderr" \
    || fail "stage1 stock trustc was refused for the wrong reason"
[ ! -e "$fixture/rustup-call.log" ] || fail "rustup ran after a stage1 stock trustc"

# Closing guidance follows the SYSROOT, not the internal stage forcing.
# --sysroot sets STAGE=stage2 as a VALIDATION LEVEL (the full same-surface
# contract), which is not a claim about provenance -- but it used to drive the
# daily-driver advice, so `install-trust-toolchain.sh --stage 1`, which links
# build/<triple>/stage1 through --sysroot, produced two contradictory
# instructions in one run: "rustup default trust" from here, and "stage1 is a
# DEVELOPER artifact, rustup default should not point at it" from the installer.
fixture="$(new_external_stage2_fixture external-stage1-path)"
mv "$fixture/external/trust" "$fixture/external/stage1"
run_link "$fixture" --name trust-stage1-path --sysroot "$fixture/external/stage1" \
    >"$fixture/stdout" 2>"$fixture/stderr"
grep -q 'stage1 is developer-only' "$fixture/stdout" \
    || fail "a stage1-named external sysroot did not get the developer-only guidance"
grep -q 'rustup default' "$fixture/stdout" \
    && fail "a stage1-named external sysroot was recommended as the default toolchain"

# A stage2-named external sysroot is the case where the default advice is right.
fixture="$(new_external_stage2_fixture external-stage2-path)"
mv "$fixture/external/trust" "$fixture/external/stage2"
run_link "$fixture" --name trust-stage2-path --sysroot "$fixture/external/stage2" \
    >"$fixture/stdout" 2>"$fixture/stderr"
grep -q 'rustup default trust-stage2-path' "$fixture/stdout" \
    || fail "a stage2-named external sysroot lost its make-default guidance"

# And when the path names no stage, say what cannot be known instead of guessing.
grep -q 'cannot tell a complete stage2' "$TMP_ROOT/external-read-only/stdout" \
    || fail "an unstaged external sysroot did not state what this script cannot know"
grep -q 'rustup default' "$TMP_ROOT/external-read-only/stdout" \
    && fail "an unstaged external sysroot was recommended as the default toolchain"

echo "rustup-link-trust tests: ok"
