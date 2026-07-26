#!/usr/bin/env bash
# Focused adversarial tests for the off-stock-Rust preflight and exec auditor.
set -euo pipefail

REPO_ROOT=$(cd -P "${BASH_SOURCE[0]%/*}/../.." && pwd -P)
SCRIPT="$REPO_ROOT/scripts/prove_rust_free_build.sh"
HELPER="$REPO_ROOT/scripts/off_stock_rust_audit.py"
PYTHON=$(type -P python3)
ENV_BIN=$(type -P env)
TRUE_BIN=$(type -P true)
BASH_BIN=$(type -P bash)
TMP=$(mktemp -d "${TMPDIR:-/tmp}/off-stock-test.XXXXXX")
trap 'rm -rf "$TMP"' EXIT HUP INT TERM

PASS_COUNT=0
LAST_OUTPUT=
LAST_STATUS=0

pass() {
    PASS_COUNT=$((PASS_COUNT + 1))
    printf 'ok %d - %s\n' "$PASS_COUNT" "$1"
}

fail() {
    printf 'not ok - %s\n' "$1" >&2
    printf '%s\n' "$LAST_OUTPUT" >&2
    exit 1
}

expect_status() {
    local expected=$1
    local label=$2
    if [ "$LAST_STATUS" -ne "$expected" ]; then
        fail "$label (expected status $expected, got $LAST_STATUS)"
    fi
}

expect_contains() {
    local needle=$1
    local label=$2
    case "$LAST_OUTPUT" in
        *"$needle"*) ;;
        *) fail "$label (missing: $needle)" ;;
    esac
}

expect_not_contains() {
    local needle=$1
    local label=$2
    case "$LAST_OUTPUT" in
        *"$needle"*) fail "$label (unexpected: $needle)" ;;
        *) ;;
    esac
}

run_command() {
    set +e
    LAST_OUTPUT=$("$@" 2>&1)
    LAST_STATUS=$?
    set -e
}

make_fixture() {
    local root=$1
    rm -rf "$root"
    mkdir -p "$root/scripts" "$root/src" "$root/bootstrap/trust-stage0/dist/2026-07-11"
    cp "$SCRIPT" "$root/scripts/prove_rust_free_build.sh"
    cp "$HELPER" "$root/scripts/off_stock_rust_audit.py"
    chmod +x "$root/scripts/prove_rust_free_build.sh"
    "$PYTHON" -I -S - "$root" <<'PY'
import hashlib
import os
import sys
from pathlib import Path

root = Path(sys.argv[1])
dist = root / "bootstrap/trust-stage0/dist/2026-07-11"
payloads = {
    "trustc-1.99.0-trust-test-host.tar.xz": b"trustc seed\n",
    "targo-1.99.0-trust-test-host.tar.xz": b"targo seed\n",
    "trust-std-1.99.0-trust-test-host.tar.xz": b"std seed\n",
}
pins = []
for name, content in payloads.items():
    (dist / name).write_bytes(content)
    pins.append((name, hashlib.sha256(content).hexdigest()))
manifest = b"manifest = 'fixture'\n"
(dist / "channel-rust-trust.toml").write_bytes(manifest)
(root / "src/version").write_text("1.99.0\n")
stage0 = [
    "dist_server=file://{trust-root}/bootstrap/trust-stage0",
    "compiler_date=2026-07-11",
    "compiler_version=1.99.0-trust",
    "compiler_channel_manifest_hash=" + hashlib.sha256(manifest).hexdigest(),
]
stage0 += [f"dist/2026-07-11/{name}={digest}" for name, digest in pins]
(root / "src/stage0").write_text("\n".join(stage0) + "\n")
(root / "x.py").write_text(
    "from pathlib import Path\nPath(__file__).with_name('BUILD_RAN').write_text('bad')\n"
)
PY
}

FIXTURE="$TMP/repo"
SAFE_BIN="$TMP/safe-bin"
mkdir -p "$SAFE_BIN"
ln -s "$PYTHON" "$SAFE_BIN/python3"
ln -s "$(type -P bash)" "$SAFE_BIN/bash"

invoke_fixture() {
    run_command "$ENV_BIN" -i HOME="$TMP/home" PATH="$SAFE_BIN" \
        "$FIXTURE/scripts/prove_rust_free_build.sh" "$@"
}

make_fixture "$FIXTURE"
invoke_fixture
expect_status 0 "valid static preflight"
expect_contains "PREFLIGHT OK" "valid static preflight"
expect_contains "No build was run and no execution claim is made" "static claim boundary"
expect_not_contains "off-stock-Rust invariant holds" "old false proof text removed"
pass "default mode is explicitly static-only"

invoke_fixture --unknown
expect_status 2 "unknown argument"
expect_contains "unknown argument" "unknown argument diagnostic"
pass "unknown arguments fail with usage status"

invoke_fixture --build extra
expect_status 2 "extra argument"
expect_contains "exactly --build" "extra argument diagnostic"
pass "extra arguments cannot be silently ignored"

run_command "$ENV_BIN" -i HOME="$TMP/home" PATH="$SAFE_BIN" \
    RUSTC_WRAPPER="$TMP/stock-wrapper" \
    "$FIXTURE/scripts/prove_rust_free_build.sh"
expect_status 1 "inherited wrapper"
expect_contains "RUSTC_WRAPPER" "inherited wrapper diagnostic"
pass "inherited compiler wrappers fail preflight"

run_command "$ENV_BIN" -i HOME="$TMP/home" PATH="$SAFE_BIN" \
    RUST_BOOTSTRAP_CONFIG="$TMP/alternate.toml" \
    "$FIXTURE/scripts/prove_rust_free_build.sh"
expect_status 1 "alternate bootstrap config injection"
expect_contains "RUST_BOOTSTRAP_CONFIG" "alternate bootstrap config diagnostic"
pass "environment-selected bootstrap configs fail preflight"

OUTSIDE="$TMP/outside"
mkdir -p "$OUTSIDE"
cp "$TRUE_BIN" "$OUTSIDE/rustc"
chmod +x "$OUTSIDE/rustc"
printf '[build]\nrustc = "%s"\n' "$OUTSIDE/rustc" > "$FIXTURE/config.toml"
invoke_fixture
expect_status 1 "config.toml stock compiler"
expect_contains "config.toml: build.rustc is outside" "config.toml diagnostic"
pass "config.toml compiler selection is authenticated"

rm "$FIXTURE/config.toml"
printf '[build]\ncargo = "%s"\n' "$OUTSIDE/rustc" > "$FIXTURE/bootstrap.toml"
invoke_fixture
expect_status 1 "bootstrap.toml stock compiler"
expect_contains "bootstrap.toml: build.cargo" "bootstrap.toml diagnostic"
pass "bootstrap.toml compiler selection is authenticated"

rm "$FIXTURE/bootstrap.toml"
printf 'include = ["included.toml"]\n' > "$FIXTURE/bootstrap.toml"
printf '[build]\nrustc = "%s"\n' "$OUTSIDE/rustc" > "$FIXTURE/included.toml"
invoke_fixture
expect_status 1 "included bootstrap config stock compiler"
expect_contains "included.toml: build.rustc is outside" "included bootstrap config diagnostic"
pass "recursive bootstrap configuration includes are authenticated"
rm "$FIXTURE/bootstrap.toml" "$FIXTURE/included.toml"

mkdir -p "$FIXTURE/.cargo"
printf 'include = ["compiler.toml"]\n' > "$FIXTURE/.cargo/config.toml"
printf '[build]\nrustc = "%s"\n' "$OUTSIDE/rustc" > "$FIXTURE/.cargo/compiler.toml"
invoke_fixture
expect_status 1 "included Cargo config stock compiler"
expect_contains "compiler.toml: build.rustc is outside" "included Cargo config diagnostic"
pass "stable recursive Cargo configuration includes are authenticated"
rm -rf "$FIXTURE/.cargo"

mkdir -p "$FIXTURE/.cargo/tools" "$FIXTURE/tools"
cp "$TRUE_BIN" "$FIXTURE/tools/trustc"
chmod +x "$FIXTURE/tools/trustc"
ln -s "$OUTSIDE/rustc" "$FIXTURE/.cargo/tools/trustc"
printf '[build]\nrustc = "tools/trustc"\n' > "$FIXTURE/.cargo/config.toml"
invoke_fixture
expect_status 1 "Cargo config-relative compiler identity"
expect_contains "is outside the authenticated checkout" "Cargo config-relative path diagnostic"
pass "Cargo tool paths resolve relative to the defining config, not the checkout root"
rm -rf "$FIXTURE/.cargo" "$FIXTURE/tools"

mkdir -p "$TMP/.cargo"
printf '[build]\nrustc = "%s"\n' "$OUTSIDE/rustc" > "$TMP/.cargo/config.toml"
invoke_fixture
expect_status 1 "ancestor Cargo configuration"
expect_contains "Cargo would discover configuration outside" "ancestor Cargo config diagnostic"
pass "Cargo configurations discovered above the checkout fail closed"
rm -rf "$TMP/.cargo"

UNSAFE_BIN="$TMP/unsafe-bin"
mkdir -p "$UNSAFE_BIN"
cp "$TRUE_BIN" "$UNSAFE_BIN/rustc"
chmod +x "$UNSAFE_BIN/rustc"
run_command "$ENV_BIN" -i HOME="$TMP/home" PATH="$SAFE_BIN:$UNSAFE_BIN" \
    "$FIXTURE/scripts/prove_rust_free_build.sh"
expect_status 1 "arbitrary PATH rustc"
expect_contains "stock-Rust command name is reachable on PATH" "arbitrary PATH diagnostic"
pass "all PATH components are checked, not only command -v's winner"

rm "$UNSAFE_BIN/rustc"
mkdir -p "$TMP/home/.rustup/toolchains/nightly/bin"
cp "$TRUE_BIN" "$TMP/home/.rustup/toolchains/nightly/bin/renamed"
chmod +x "$TMP/home/.rustup/toolchains/nightly/bin/renamed"
ln -s "$TMP/home/.rustup/toolchains/nightly/bin/renamed" "$UNSAFE_BIN/trustc"
run_command "$ENV_BIN" -i HOME="$TMP/home" PATH="$SAFE_BIN:$UNSAFE_BIN" \
    "$FIXTURE/scripts/prove_rust_free_build.sh"
expect_status 1 "PATH symlink into rustup"
expect_contains "resolves into rustup/genesis-stage0" "PATH symlink diagnostic"
pass "PATH entries are classified by canonical identity"

rm "$UNSAFE_BIN/trustc"
ln -s "$TMP/home/.rustup/toolchains/nightly/bin/renamed" "$FIXTURE/seed-trustc"
printf '[build]\nrustc = "./seed-trustc"\n' > "$FIXTURE/config.toml"
invoke_fixture
expect_status 1 "config symlink into rustup"
expect_contains "resolves through rustup/genesis-stage0" "config symlink diagnostic"
pass "configuration symlinks cannot disguise stock compilers"

rm "$FIXTURE/config.toml"
sed 's#file://{trust-root}/bootstrap/trust-stage0#https://example.invalid/stock#' \
    "$FIXTURE/src/stage0" > "$FIXTURE/src/stage0.changed"
mv "$FIXTURE/src/stage0.changed" "$FIXTURE/src/stage0"
invoke_fixture
expect_status 1 "foreign seed server"
expect_contains "dist_server is not the authenticated repository-local" "foreign seed server diagnostic"
pass "stage0 cannot redirect the audited build to an unauthenticated compiler server"
sed 's#https://example.invalid/stock#file://{trust-root}/bootstrap/trust-stage0#' \
    "$FIXTURE/src/stage0" > "$FIXTURE/src/stage0.changed"
mv "$FIXTURE/src/stage0.changed" "$FIXTURE/src/stage0"

cp "$FIXTURE/src/stage0" "$TMP/stage0-outside"
rm "$FIXTURE/src/stage0"
ln -s "$TMP/stage0-outside" "$FIXTURE/src/stage0"
invoke_fixture
expect_status 1 "symlinked seed metadata"
expect_contains "seed metadata is not a regular repository-owned file" "symlinked seed diagnostic"
pass "seed metadata cannot escape the authenticated checkout through a symlink"
rm "$FIXTURE/src/stage0"
cp "$TMP/stage0-outside" "$FIXTURE/src/stage0"

invoke_fixture --build
expect_status 1 "unsupported or unavailable exec tracer"
expect_contains "requires" "exec tracer diagnostic"
if [ -e "$FIXTURE/BUILD_RAN" ]; then
    fail "unsupported --build executed the build anyway"
fi
expect_not_contains "fresh stage2 build satisfied" "unsupported build claim boundary"
pass "--build fails closed when no supported exec tracer is available"

# Exercise the complete Linux branch with deterministic fake audit utilities.
# The fake tracer still writes through the real bounded collector and the real
# parser; it only substitutes for unavailable strace on non-Linux test hosts.
FAKE_AUDIT_BIN="$TMP/fake-audit-bin"
FOREIGN_CWD="$TMP/foreign-cwd"
mkdir -p "$FAKE_AUDIT_BIN" "$FOREIGN_CWD"
ln -s "$BASH_BIN" "$FAKE_AUDIT_BIN/bash"
ln -s "$ENV_BIN" "$FAKE_AUDIT_BIN/env"
printf '[build]\nrustc = "%s"\n' "$OUTSIDE/rustc" > "$FOREIGN_CWD/bootstrap.toml"
"$PYTHON" -I -S - "$FIXTURE" "$FAKE_AUDIT_BIN" "$PYTHON" "$BASH_BIN" <<'PY'
import os
import sys
from pathlib import Path

root, bindir, real_python, bash = map(Path, sys.argv[1:])
(root / "x.py").write_text(
    """from pathlib import Path
import sys

root = Path(__file__).parent
(root / 'BUILD_RAN').write_text('yes')
(root / 'BUILD_CWD').write_text(str(Path.cwd()))
args = sys.argv[1:]
build = Path(args[args.index('--build-dir') + 1])
for relative in (
    'host/stage1/bin/trustc',
    'host/stage1/bin/targo',
    'host/stage2/bin/trustc',
):
    output = build / relative
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('#!/bin/sh\\nexit 0\\n')
    output.chmod(0o755)
"""
)

python_wrapper = bindir / "python3"
python_wrapper.write_text(
    f"""#!{bash}
if [ "$#" -ge 4 ] && [ "$1" = -I ] && [ "$2" = -S ] && [ "$3" = -c ] && \\
   [ "$4" = 'import platform; print(platform.system())' ]; then
    printf 'Linux\\n'
    exit 0
fi
exec {real_python} "$@"
"""
)

timeout = bindir / "timeout"
timeout.write_text(
    f"""#!{bash}
while [ "$#" -gt 0 ]; do
    case "$1" in
        --signal=*|--kill-after=*|12h) shift ;;
        *) break ;;
    esac
done
exec "$@"
"""
)

strace = bindir / "strace"
strace.write_text(
    f"""#!{bash}
if [ "${{1:-}}" = --help ]; then
    printf 'usage: strace --kill-on-exit\\n'
    exit 0
fi
pipe=
while [ "$#" -gt 0 ]; do
    case "$1" in
        --kill-on-exit|-f|-yy) shift ;;
        -s|-e) shift 2 ;;
        -o) pipe=$2; shift 2 ;;
        *) break ;;
    esac
done
build=
previous=
for argument in "$@"; do
    if [ "$previous" = --build-dir ]; then
        build=$argument
        break
    fi
    previous=$argument
done
"$@"
status=$?
if [ -n "$pipe" ] && [ -n "$build" ]; then
    printf '[pid 1] execve("%s", ["trustc"], 0x0) = 0\\n' \\
        "$build/host/stage1/bin/trustc" > "$pipe"
    printf '[pid 1] execve("%s", ["targo"], 0x0) = 0\\n' \\
        "$build/host/stage1/bin/targo" >> "$pipe"
fi
exit "$status"
"""
)

for executable in (python_wrapper, timeout, strace):
    executable.chmod(0o755)
PY

run_command "$ENV_BIN" -i HOME="$TMP/home" PATH="$FAKE_AUDIT_BIN" \
    "$BASH_BIN" -c 'cd "$1" && "$2" --build' bash \
    "$FOREIGN_CWD" "$FIXTURE/scripts/prove_rust_free_build.sh"
expect_status 0 "complete fake Linux exec audit"
expect_contains "PASS: fresh stage2 build satisfied" "complete fake Linux audit claim"
BUILD_CWD=$(<"$FIXTURE/BUILD_CWD")
FIXTURE_REAL=$(cd -P "$FIXTURE" && pwd -P)
if [ "$BUILD_CWD" != "$FIXTURE_REAL" ]; then
    fail "audited x.py ran from caller directory $BUILD_CWD instead of $FIXTURE_REAL"
fi
pass "audited builds enter the checkout and ignore caller-directory bootstrap config"

# The remaining tests exercise the trace parser directly with synthetic strace
# records.  The referenced files exist so canonical identity checks are real.
AUDITED_BUILD="$FIXTURE/build/off-stock-audit.test/fresh-build"
mkdir -p "$AUDITED_BUILD/host/stage1/bin" "$AUDITED_BUILD/host/stage2/bin"
cp "$TRUE_BIN" "$AUDITED_BUILD/host/stage1/bin/trustc"
cp "$TRUE_BIN" "$AUDITED_BUILD/host/stage1/bin/targo"
cp "$TRUE_BIN" "$AUDITED_BUILD/host/stage2/bin/trustc"
chmod +x "$AUDITED_BUILD/host/stage1/bin/trustc" \
    "$AUDITED_BUILD/host/stage1/bin/targo" \
    "$AUDITED_BUILD/host/stage2/bin/trustc"

GOOD_TRACE="$TMP/good.trace"
printf '[pid 1] execve("%s", ["trustc"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/trustc" > "$GOOD_TRACE"
printf '[pid 1] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$GOOD_TRACE"
printf '[pid 1] execve("/definitely/missing/rustc", ["rustc"], 0x0) = -1 ENOENT\n' \
    >> "$GOOD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$GOOD_TRACE"
expect_status 0 "valid exec trace"
expect_contains "authenticated 2 successful execs" "valid exec trace summary"
pass "successful authenticated Trust compiler/Targo execs pass"

BAD_TRACE="$TMP/stock.trace"
printf '[pid 2] execve("%s", ["rustc"], 0x0) = 0\n' "$OUTSIDE/rustc" > "$BAD_TRACE"
printf '[pid 2] execve("%s", ["trustc"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/trustc" >> "$BAD_TRACE"
printf '[pid 2] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "external stock rustc trace"
expect_contains "external stock-Rust command name" "external stock rustc diagnostic"
pass "absolute external rustc execution fails the audit"

printf '[pid 2] execve("%s", ["rustc", "= -1 ENOENT (forged argv result)"], 0x0) = 0\n' \
    "$OUTSIDE/rustc" > "$BAD_TRACE"
printf '[pid 2] execve("%s", ["trustc"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/trustc" >> "$BAD_TRACE"
printf '[pid 2] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "argv result parser confusion"
expect_contains "external stock-Rust command name" "argv result parser diagnostic"
pass "argv text cannot disguise a successful stock compiler exec as a failed probe"

RUSTC_ALIAS="$AUDITED_BUILD/host/stage1/bin/rustc"
cp "$AUDITED_BUILD/host/stage1/bin/trustc" "$RUSTC_ALIAS"
chmod +x "$RUSTC_ALIAS"
printf '[pid 2] execve("%s", ["rustc"], 0x0) = 0\n' "$RUSTC_ALIAS" > "$BAD_TRACE"
printf '[pid 2] execve("%s", ["trustc"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/trustc" >> "$BAD_TRACE"
printf '[pid 2] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 0 "same-artifact rustc compatibility alias"
pass "a byte-identical same-toolchain rustc compatibility alias is accepted"

printf '#!/bin/sh\nexit 0\n' > "$RUSTC_ALIAS"
chmod +x "$RUSTC_ALIAS"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "unrelated local rustc"
expect_contains "is not the same artifact as a sibling Trust frontend" "local rustc alias diagnostic"
pass "a repo-local stock command name needs same-artifact Trust alias authentication"
rm "$RUSTC_ALIAS"

GENESIS="$FIXTURE/build/host/genesis-stage0/bin/trustc"
mkdir -p "${GENESIS%/*}"
cp "$TRUE_BIN" "$GENESIS"
chmod +x "$GENESIS"
printf '[pid 3] execve("%s", ["trustc"], 0x0) = 0\n' "$GENESIS" > "$BAD_TRACE"
printf '[pid 3] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "genesis trace"
expect_contains "executed rustup/genesis-stage0 path" "genesis trace diagnostic"
pass "absolute genesis-stage0 execution fails even inside build/"

SYMLINK_TRUSTC="$AUDITED_BUILD/host/stage1/bin/trustc"
rm "$SYMLINK_TRUSTC"
ln -s "$TMP/home/.rustup/toolchains/nightly/bin/renamed" "$SYMLINK_TRUSTC"
printf '[pid 4] execve("%s", ["trustc"], 0x0) = 0\n' "$SYMLINK_TRUSTC" > "$BAD_TRACE"
printf '[pid 4] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "trace symlink identity"
expect_contains "executed rustup/genesis-stage0 path" "trace symlink diagnostic"
pass "exec audit checks canonical targets, not symlink spelling"

cp "$TRUE_BIN" "$SYMLINK_TRUSTC.tmp"
rm "$SYMLINK_TRUSTC"
mv "$SYMLINK_TRUSTC.tmp" "$SYMLINK_TRUSTC"
chmod +x "$SYMLINK_TRUSTC"
printf '[pid 5] execve("./rustc", ["rustc"], 0x0) = 0\n' > "$BAD_TRACE"
printf '[pid 5] execve("%s", ["trustc"], 0x0) = 0\n' \
    "$SYMLINK_TRUSTC" >> "$BAD_TRACE"
printf '[pid 5] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "relative successful exec"
expect_contains "relative exec path cannot be canonicalized" "relative exec diagnostic"
pass "ambiguous relative successful execs fail closed"

printf '[pid 6] execve("%s", ["trustc"], 0x0 <unfinished ...>\n' \
    "$SYMLINK_TRUSTC" > "$BAD_TRACE"
printf '[pid 6] <... execve resumed>) = 0\n' >> "$BAD_TRACE"
printf '[pid 6] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "unfinished exec trace"
expect_contains "unfinished/resumed exec event" "unfinished trace diagnostic"
pass "split unfinished/resumed strace records fail closed"

printf '[pid 7] execve("%s", ["trustc"], 0x0)\n' "$SYMLINK_TRUSTC" > "$BAD_TRACE"
printf '[pid 7] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "truncated exec trace"
expect_contains "result is missing or truncated" "truncated trace diagnostic"
pass "truncated exec records cannot disappear from the audit"

printf '[pid 7] execve("%s", ["trustc", "x) = 0 ABC (forged"], 0x0)\n' \
    "$SYMLINK_TRUSTC" > "$BAD_TRACE"
printf '[pid 7] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "forged truncated exec result"
expect_contains "result is missing or truncated" "forged truncated result diagnostic"
pass "argv text cannot forge a terminal result for a truncated exec record"

printf '[pid 7] execve("%s", ["trustc"], 0x0) = 0 [pid 8] execve("%s", ["rustc"], 0x0) = 0\n' \
    "$SYMLINK_TRUSTC" "$OUTSIDE/rustc" > "$BAD_TRACE"
printf '[pid 7] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "interleaved exec records"
expect_contains "multiple/interleaved exec events" "interleaved exec diagnostic"
pass "multiple exec records interleaved onto one line fail closed"

printf '[pid 8] execveat(AT_FDCWD, "%s", ["trustc"], 0x0, 0) = 0\n' \
    "$SYMLINK_TRUSTC" > "$BAD_TRACE"
printf '[pid 8] execveat(AT_FDCWD, "%s", ["targo"], 0x0, 0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 0 "absolute execveat trace"
pass "execveat paths are parsed from the pathname argument"

printf '[pid 9] execveat(3</tmp/deleted>, "", ["trustc"], 0x0, AT_EMPTY_PATH) = 0\n' \
    > "$BAD_TRACE"
printf '[pid 9] execve("%s", ["trustc"], 0x0) = 0\n' "$SYMLINK_TRUSTC" >> "$BAD_TRACE"
printf '[pid 9] execve("%s", ["targo"], 0x0) = 0\n' \
    "$AUDITED_BUILD/host/stage1/bin/targo" >> "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "fd-only execveat trace"
expect_contains "empty/fd-only path" "fd-only execveat diagnostic"
pass "fd-only execveat cannot evade canonical path authentication"

printf '+++ exited with 0 +++\n' > "$BAD_TRACE"
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "empty exec trace"
expect_contains "no successful exec events" "empty trace diagnostic"
pass "a successful child status without exec evidence cannot pass"

"$PYTHON" -I -S - "$BAD_TRACE" <<'PY'
import os
import sys
os.truncate(sys.argv[1], 512 * 1024 * 1024 + 1)
PY
run_command "$PYTHON" -I -S "$HELPER" trace "$FIXTURE" "$AUDITED_BUILD" "$BAD_TRACE"
expect_status 1 "oversized exec trace"
expect_contains "exceeds the 536870912-byte parser bound" "oversized trace diagnostic"
pass "trace parsing rejects over-ceiling evidence before allocating it"

run_command "$PYTHON" -I -S "$HELPER" stage2-output "$FIXTURE" "$AUDITED_BUILD"
expect_status 0 "unique fresh stage2 output"
expect_contains "fresh stage2 compiler output" "fresh stage2 output diagnostic"
pass "exactly one canonical fresh stage2 output is required"

mv "$AUDITED_BUILD/host/stage2/bin/trustc" "$AUDITED_BUILD/host/stage2/bin/trustc.real"
ln -s trustc.real "$AUDITED_BUILD/host/stage2/bin/trustc"
run_command "$PYTHON" -I -S "$HELPER" stage2-output "$FIXTURE" "$AUDITED_BUILD"
expect_status 1 "symlinked stage2 output"
expect_contains "expected exactly one" "symlinked stage2 output diagnostic"
pass "fresh stage2 output must be a direct regular executable, not a symlink"
rm "$AUDITED_BUILD/host/stage2/bin/trustc"
mv "$AUDITED_BUILD/host/stage2/bin/trustc.real" "$AUDITED_BUILD/host/stage2/bin/trustc"

cp "$TRUE_BIN" "$AUDITED_BUILD/other/stage2/bin/trustc" 2>/dev/null || {
    mkdir -p "$AUDITED_BUILD/other/stage2/bin"
    cp "$TRUE_BIN" "$AUDITED_BUILD/other/stage2/bin/trustc"
}
chmod +x "$AUDITED_BUILD/other/stage2/bin/trustc"
run_command "$PYTHON" -I -S "$HELPER" stage2-output "$FIXTURE" "$AUDITED_BUILD"
expect_status 1 "ambiguous stage2 outputs"
expect_contains "expected exactly one" "ambiguous stage2 output diagnostic"
pass "ambiguous stage2 output discovery fails closed"

COLLECT_PARENT="$TMP/collector"
mkdir -p "$COLLECT_PARENT"
COLLECT_DIR=$("$PYTHON" -I -S "$HELPER" make-audit-dir "$COLLECT_PARENT")
IDENTITY_BEFORE=$("$PYTHON" -I -S "$HELPER" file-identity "$COLLECT_DIR/exec.trace")
run_command bash -c '
    python=$1 helper=$2 pipe=$3 output=$4
    "$python" -I -S "$helper" collect-trace "$pipe" "$output" 5 &
    collector=$!
    printf 1234567890 > "$pipe"
    wait "$collector"
' bash "$PYTHON" "$HELPER" "$COLLECT_DIR/exec.trace.pipe" "$COLLECT_DIR/exec.trace"
expect_status 1 "bounded trace overflow"
expect_contains "exceeded" "bounded trace overflow diagnostic"
TRACE_SIZE=$("$PYTHON" -I -S -c 'import os,sys; print(os.path.getsize(sys.argv[1]))' \
    "$COLLECT_DIR/exec.trace")
if [ "$TRACE_SIZE" -ne 5 ]; then
    fail "bounded trace collector wrote $TRACE_SIZE bytes instead of 5"
fi
IDENTITY_AFTER=$("$PYTHON" -I -S "$HELPER" file-identity "$COLLECT_DIR/exec.trace")
if [ "$IDENTITY_BEFORE" != "$IDENTITY_AFTER" ]; then
    fail "bounded trace collector replaced its pre-created evidence inode"
fi
pass "trace collection is byte-bounded and preserves the exclusive evidence inode"

PRIVATE_DIR=$("$PYTHON" -I -S "$HELPER" make-audit-dir "$COLLECT_PARENT")
chmod 0644 "$PRIVATE_DIR/exec.trace"
run_command "$PYTHON" -I -S "$HELPER" collect-trace \
    "$PRIVATE_DIR/exec.trace.pipe" "$PRIVATE_DIR/exec.trace" 5
expect_status 1 "non-private trace output"
expect_contains "owner-private" "non-private trace output diagnostic"
pass "trace collection rejects evidence files writable outside the owner policy"

UNSAFE_COLLECT_PARENT="$TMP/unsafe-collector-parent"
mkdir -p "$UNSAFE_COLLECT_PARENT"
chmod 0777 "$UNSAFE_COLLECT_PARENT"
run_command "$PYTHON" -I -S "$HELPER" make-audit-dir "$UNSAFE_COLLECT_PARENT"
expect_status 1 "writable audit parent"
expect_contains "owner-controlled" "writable audit parent diagnostic"
pass "audit directories cannot be planted or replaced through a writable parent"

printf '1..%d\n' "$PASS_COUNT"
