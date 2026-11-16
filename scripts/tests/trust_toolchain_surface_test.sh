#!/bin/sh

set -eu

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
. "$ROOT/scripts/lib/trust_toolchain_surface.sh"

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/trust-toolchain-surface-test.XXXXXX")"
trap 'rm -rf "$TMP_ROOT"' EXIT HUP INT TERM
# The path contract resolves symlinks, and macOS's default TMPDIR lies under
# /var, a link to /private/var: build the fixtures under the physical path so a
# resolved path can be compared with the path the fixture was written to.
TMP_ROOT="$(cd "$TMP_ROOT" && pwd -P)"

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

# Real Python startup must not run caller-controlled sitecustomize code while
# resolving a path for a toolchain contract. It must also ignore PYTHONPATH
# when selecting the standard-library pathlib implementation.
startup="$TMP_ROOT/python-startup"
mkdir -p "$startup"
cat >"$startup/sitecustomize.py" <<'PY'
import os
with open(os.environ['TRUST_SURFACE_STARTUP_MARKER'], 'w') as marker:
    marker.write('sitecustomize executed')
print('startup contaminated the path contract')
PY
cat >"$startup/pathlib.py" <<'PY'
raise RuntimeError('ambient pathlib shadow reached the path contract')
PY
(
    export PYTHONPATH="$startup"
    export TRUST_SURFACE_STARTUP_MARKER="$TMP_ROOT/python-startup-ran"
    resolved="$(trust_toolchain_resolve_path "$bin")" \
        || fail "isolated path resolution rejected a real selected bin"
    [ "$resolved" = "$bin" ] || fail "Python startup changed the resolved tool path"
    [ ! -e "$TRUST_SURFACE_STARTUP_MARKER" ] || fail "Python sitecustomize ran in the tool contract"
    trust_toolchain_alias_pair_valid "$bin" trustc rustc \
        || fail "Python startup affected same-bin alias validation"
)

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

# Drive the public output contract with a complete synthetic root. Its Targo
# must implement the explicit lane selector itself, even if a renamed Cargo
# can delegate a successful doctor command to the real sibling targo-trust.
complete="$TMP_ROOT/complete"
mkdir -p "$complete/bin" "$complete/libexec"
for tool in trustc rustc ay ty clean cargo targo targo-trust trustd trustdoc rustdoc \
    trustfmt targo-fmt tippy targo-tippy tippy-driver trust-analyzer; do
    write_executable "$complete/bin/$tool" '#!/bin/sh
printf "synthetic tool fixture\n"'
done
# The Trust tools with a stock ancestor answer --version with their Trust name,
# as the real ones do (trust_toolchain_identity_error).
write_executable "$complete/bin/trustc" '#!/bin/sh
printf "rustc 0.0.0-fixture (0000000 2026-09-30) (trustc 0.0.0)\n"'
cp "$complete/bin/trustc" "$complete/bin/rustc"
write_executable "$complete/bin/trustdoc" '#!/bin/sh
printf "rustc 0.0.0-fixture (0000000 2026-09-30) (trustdoc 0.0.0)\n"'
cp "$complete/bin/trustdoc" "$complete/bin/rustdoc"
for tool in trustfmt targo-fmt; do
    write_executable "$complete/bin/$tool" '#!/bin/sh
printf "trustfmt 0.0.0-fixture\n"'
done
for tool in tippy targo-tippy tippy-driver; do
    write_executable "$complete/bin/$tool" '#!/bin/sh
printf "tippy 0.0.0-fixture\n"'
done
write_executable "$complete/bin/trust-analyzer" '#!/bin/sh
printf "trust-analyzer 0.0.0-fixture\n"'
write_executable "$complete/libexec/trust-analyzer-proc-macro-srv" '#!/bin/sh
exit 0'
write_executable "$complete/bin/targo" '#!/bin/sh
if [ "${1:-}" = --resource-capabilities ]; then
    printf "%s\n" "{\"version\":3,\"cpu_workers\":false,\"supports_invocation\":false}"
    exit 0
fi
if [ "$*" = "--unverified --version" ] || [ "$*" = "--version" ]; then
    printf "targo 0.0.0-fixture\n"
    exit 0
fi
exit 2'
cp "$complete/bin/targo" "$complete/bin/cargo"
sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 \
    --resource-receipt="$TMP_ROOT/positive-resource.json" >"$TMP_ROOT/positive.log" 2>&1 \
    || { cat "$TMP_ROOT/positive.log" >&2; fail "real Targo lane fixture was rejected"; }
python3 -I -S -B - "$TMP_ROOT/positive-resource.json" <<'PY'
import json, sys
record = json.load(open(sys.argv[1]))
assert record['passed'] is True and record['opening_cohort'] == record['closing_cohort']
assert len(record['observations']) == 2
assert all(row['supported_boundary'] == 'fixed' for row in record['observations'])
PY

write_executable "$complete/bin/targo-trust" '#!/bin/sh
if [ "$*" = "doctor --format json" ]; then
    printf "{\"ready\":true}\n"
else
    printf "synthetic verification driver\n"
fi'
# A genuine but stale native frontend passes the existing lane and delegated
# doctor while advertising only the retired platform/command-shape protocol.
write_executable "$complete/bin/targo" '#!/bin/sh
case "$1" in
    --resource-capabilities) printf "%s\n" "{\"version\":2,\"cpu_workers\":true,\"supports_invocation\":true}" ;;
    trust) shift; exec "$(dirname "$0")/targo-trust" "$@" ;;
    *) printf "targo 0.0.0-fixture\n" ;;
esac'
cp "$complete/bin/targo" "$complete/bin/cargo"
[ "$("$complete/bin/targo" trust doctor --format json)" = '{"ready":true}' ] \
    || fail "stale native fixture did not reproduce passing doctor delegation"
for waiver in '' '--allow-missing=targo'; do
    if sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 ${waiver:+"$waiver"} \
        >"$TMP_ROOT/stale-targo.log" 2>&1; then
        fail "stale native Targo passed through lane/version and delegated doctor"
    fi
    grep -q 'invalid capability response' "$TMP_ROOT/stale-targo.log" \
        || { cat "$TMP_ROOT/stale-targo.log" >&2; fail "stale native Targo failed for the wrong reason"; }
done
write_executable "$complete/bin/targo" '#!/bin/sh
case "$1" in
    --version|-V|--help) printf "cargo 0.0.0-fixture\n"; exit 0 ;;
    trust) shift; exec "$(dirname "$0")/targo-trust" "$@" ;;
    *) printf "unexpected argument: %s\n" "$1" >&2; exit 2 ;;
esac'
cp "$complete/bin/targo" "$complete/bin/cargo"
[ "$("$complete/bin/targo" trust doctor --format json)" = '{"ready":true}' ] \
    || fail "stock Cargo fixture did not reproduce successful doctor delegation"
for waiver in '' '--allow-missing=targo'; do
    if sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 ${waiver:+"$waiver"} \
        >"$TMP_ROOT/stock-cargo.log" 2>&1; then
        fail "renamed Cargo passed the Targo gate through generic probes or doctor delegation"
    fi
    grep -q 'Targo lane probe --unverified --version' "$TMP_ROOT/stock-cargo.log" \
        || { cat "$TMP_ROOT/stock-cargo.log" >&2; fail "renamed Cargo was refused for the wrong reason"; }
done

write_executable "$complete/bin/targo" '#!/bin/sh
case "$*" in
    "--unverified --version") exit 0 ;;
    --version|-V|--help) printf "targo 0.0.0-fixture\n"; exit 0 ;;
    *) exit 2 ;;
esac'
cp "$complete/bin/targo" "$complete/bin/cargo"
if sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 >"$TMP_ROOT/silent.log" 2>&1; then
    fail "silent zero-exit Targo probe passed without a version response"
fi
grep -q 'Targo lane probe --unverified --version' "$TMP_ROOT/silent.log" \
    || fail "silent Targo was refused for the wrong reason"

# A stock program under a Trust name runs and answers every probe, so the
# contract must refuse it by identity, and --allow-missing (which waives
# ABSENCE) must not rescue it. Restore the real Targo fixture first.
write_executable "$complete/bin/targo" '#!/bin/sh
if [ "${1:-}" = --resource-capabilities ]; then
    printf "%s\n" "{\"version\":3,\"cpu_workers\":false,\"supports_invocation\":false}"
    exit 0
fi
if [ "$*" = "--unverified --version" ] || [ "$*" = "--version" ]; then
    printf "targo 0.0.0-fixture\n"
    exit 0
fi
exit 2'
cp "$complete/bin/targo" "$complete/bin/cargo"
sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 >"$TMP_ROOT/branded.log" 2>&1 \
    || { cat "$TMP_ROOT/branded.log" >&2; fail "branded Trust fixture was rejected"; }
for case in \
    'trustfmt:rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)' \
    'targo-fmt:rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)' \
    'tippy:clippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'targo-tippy:clippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'tippy-driver:clippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'trust-analyzer:rust-analyzer 1.98.0 (88d9e12a 2026-08-18)' \
    'trustdoc:rustdoc 1.98.0 (88d9e12ae 2026-08-18)' \
    'trustc:rustc 1.98.0 (88d9e12ae 2026-08-18)' \
    'targo:cargo 1.98.0 (797e8a9bc 2026-08-05)'
do
    tool="${case%%:*}"
    banner="${case#*:}"
    cp "$complete/bin/$tool" "$TMP_ROOT/saved-$tool"
    write_executable "$complete/bin/$tool" "#!/bin/sh
printf '%s\\n' '$banner'"
    # Keep each compatibility alias byte-identical to its canonical tool, so
    # the identity probe, not the alias check, is what refuses.
    case "$tool" in
        trustc) cp "$complete/bin/trustc" "$complete/bin/rustc" ;;
        trustdoc) cp "$complete/bin/trustdoc" "$complete/bin/rustdoc" ;;
        targo) cp "$complete/bin/targo" "$complete/bin/cargo" ;;
    esac
    for waiver in '' "--allow-missing=$tool" "--allow-missing-backend=$tool"; do
        if sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 ${waiver:+"$waiver"} \
            >"$TMP_ROOT/stock-$tool.log" 2>&1; then
            cat "$TMP_ROOT/stock-$tool.log" >&2
            fail "stock program under the Trust name $tool passed the output contract ${waiver:-unwaived}"
        fi
        grep -q "^IDENTITY: $tool (tier [12]) is not the Trust build of $tool\$" "$TMP_ROOT/stock-$tool.log" \
            || { cat "$TMP_ROOT/stock-$tool.log" >&2; fail "stock $tool was refused for the wrong reason"; }
    done
    cp "$TMP_ROOT/saved-$tool" "$complete/bin/$tool"
    case "$tool" in
        trustc) cp "$complete/bin/trustc" "$complete/bin/rustc" ;;
        trustdoc) cp "$complete/bin/trustdoc" "$complete/bin/rustdoc" ;;
        targo) cp "$complete/bin/targo" "$complete/bin/cargo" ;;
    esac
done
sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 >"$TMP_ROOT/restored.log" 2>&1 \
    || { cat "$TMP_ROOT/restored.log" >&2; fail "restored branded fixture was rejected"; }

# Identity is read from standard output alone. Cargo prints configuration
# warnings on stderr BEFORE its banner (an unused key in a .cargo/config.toml in
# the working directory or a parent; a CARGO_HOME holding both `config` and
# `config.toml`), so a genuine Targo whose stderr leads with one must pass. The
# same holds for every branded probe, not only Targo's lane probe.
cp "$complete/bin/targo" "$TMP_ROOT/saved-targo"
cp "$complete/bin/trustfmt" "$TMP_ROOT/saved-trustfmt"
cat >"$complete/bin/targo" <<'SH'
#!/bin/sh
printf 'warning: unused config key `unstable.foo` in `/fixture/.cargo/config.toml`\n' >&2
if [ "${1:-}" = --resource-capabilities ]; then
    printf "%s\n" "{\"version\":3,\"cpu_workers\":false,\"supports_invocation\":false}"
    exit 0
fi
if [ "$*" = "--unverified --version" ] || [ "$*" = "--version" ]; then
    printf 'targo 0.0.0-fixture\n'
    exit 0
fi
exit 2
SH
cp "$complete/bin/targo" "$complete/bin/cargo"
cat >"$complete/bin/trustfmt" <<'SH'
#!/bin/sh
printf 'warning: fixture diagnostic before the banner\n' >&2
printf 'trustfmt 0.0.0-fixture\n'
SH
sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 >"$TMP_ROOT/stderr-warning.log" 2>&1 \
    || { cat "$TMP_ROOT/stderr-warning.log" >&2; fail "a Trust tool that warns on stderr before its banner was refused"; }
grep -q '^  OK        targo  *--unverified --version -> targo 0.0.0-fixture$' "$TMP_ROOT/stderr-warning.log" \
    || { cat "$TMP_ROOT/stderr-warning.log" >&2; fail "targo was not identified from its stdout banner"; }
cp "$TMP_ROOT/saved-targo" "$complete/bin/targo"
cp "$complete/bin/targo" "$complete/bin/cargo"

# And stderr cannot vouch for a stock program: a Trust banner written to stderr
# ahead of a stock stdout banner is refused. (Merged with 2>&1, the stderr line
# came first and passed.)
cat >"$complete/bin/trustfmt" <<'SH'
#!/bin/sh
printf 'trustfmt 0.0.0-fixture\n' >&2
printf 'rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)\n'
SH
if sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 >"$TMP_ROOT/stderr-vouch.log" 2>&1; then
    cat "$TMP_ROOT/stderr-vouch.log" >&2
    fail "a Trust banner on stderr vouched for a stock stdout banner"
fi
grep -q '^IDENTITY: trustfmt (tier 2) is not the Trust build of trustfmt$' "$TMP_ROOT/stderr-vouch.log" \
    || { cat "$TMP_ROOT/stderr-vouch.log" >&2; fail "stderr-vouched trustfmt was refused for the wrong reason"; }
cp "$TMP_ROOT/saved-trustfmt" "$complete/bin/trustfmt"

# The documented limit (docs/trust-naming.md, "What The Banner Check Does Not
# Establish"). The banner is self-reported, so a wrapper that runs a stock
# program and rewrites its first line passes. The local genesis stage0 adapter
# makes exactly this rewrite (scripts/create_local_genesis_stage0.py,
# wrapper_script's rewrite_version: `1s/^rustfmt /trustfmt /`). This pins the
# limit both ways. A change that closes it fails here and must update that
# section. A change that widens it fails the refusals below, which are the
# reason neither gate accepts a whole genesis root.
mkdir -p "$TMP_ROOT/stock"
cat >"$TMP_ROOT/stock/rustfmt" <<'SH'
#!/bin/sh
printf 'rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)\n'
SH
chmod +x "$TMP_ROOT/stock/rustfmt"
cat >"$complete/bin/trustfmt" <<SH
#!/bin/sh
case "\$*" in
    --version|-V) "$TMP_ROOT/stock/rustfmt" "\$@" | sed -e '1s/^rustfmt /trustfmt /' ;;
    *) exec "$TMP_ROOT/stock/rustfmt" "\$@" ;;
esac
SH
[ "$("$complete/bin/trustfmt" --help)" = 'rustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)' ] \
    || fail "banner-rewriting wrapper fixture does not run the stock program"
sh "$ROOT/tools/verify-toolchain.sh" "$complete" --probe-timeout=1 >"$TMP_ROOT/rewrite-wrapper.log" 2>&1 \
    || { cat "$TMP_ROOT/rewrite-wrapper.log" >&2; fail "the documented banner-rewriting-wrapper limit changed: update docs/trust-naming.md"; }
grep -q '^  OK        trustfmt  *--version -> trustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)$' "$TMP_ROOT/rewrite-wrapper.log" \
    || { cat "$TMP_ROOT/rewrite-wrapper.log" >&2; fail "the banner-rewriting wrapper passed for an unexpected reason"; }
cp "$TMP_ROOT/saved-trustfmt" "$complete/bin/trustfmt"
for rewritten in \
    'trustfmt:trustfmt 1.9.0-stable (88d9e12ae1 2026-08-18)' \
    'tippy:tippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'targo-tippy:tippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'tippy-driver:tippy 0.1.98 (88d9e12ae1 2026-08-18)' \
    'trust-analyzer:trust-analyzer 1.98.0 (88d9e12a 2026-08-18)' \
    'targo:targo 1.98.0 (797e8a9bc 2026-08-05)'
do
    trust_toolchain_identity_valid "${rewritten%%:*}" "${rewritten#*:}" \
        || fail "the documented limit changed for ${rewritten%%:*}: update docs/trust-naming.md"
done
for rewritten in \
    'trustc:trustc 1.98.0 (88d9e12ae 2026-08-18)' \
    'trustdoc:trustdoc 1.98.0 (88d9e12ae 2026-08-18)' \
    'targo-fmt:targo-fmt 1.9.0-stable (88d9e12ae1 2026-08-18)'
do
    if trust_toolchain_identity_valid "${rewritten%%:*}" "${rewritten#*:}"; then
        fail "a genesis-style rewrite passed as ${rewritten%%:*}: ${rewritten#*:}"
    fi
done

# The identity rule itself: only the first line counts, the rustc-derived
# parenthetical has exactly two shapes, and a name with no brand is an error,
# never a pass.
trust_toolchain_identity_valid trustc 'rustc 1.99.0-dev (7d5533b2b 2026-09-23) (trustc 0.1.0)' \
    || fail "versioned trustc brand was refused"
trust_toolchain_identity_valid trustc 'rustc 1.99.0-dev (52e0a7031 2026-07-20) (trustc)' \
    || fail "bare trustc brand was refused"
if trust_toolchain_identity_valid trustc 'rustc 1.98.0 (88d9e12ae 2026-08-18)
(trustc 0.1.0)'; then
    fail "a brand on a later line vouched for a stock first line"
fi
if trust_toolchain_identity_valid trustc 'rustc 1.98.0 (88d9e12ae 2026-08-18) (trustcx)'; then
    fail "a lookalike parenthetical passed as the trustc brand"
fi
trust_toolchain_identity_valid tippy-driver 'tippy 0.1.98 (7d5533b2bb 2026-09-23)' \
    || fail "tippy-driver brand was refused"
if trust_toolchain_identity_valid trustfmt 'trustfmtx 1.0'; then
    fail "a lookalike leading token passed as the trustfmt brand"
fi
if trust_toolchain_identity_valid ay 'ay 1.0.0'; then
    fail "a tool with no Trust brand passed the identity check"
fi
for tool in $TRUST_TOOLCHAIN_FORBIDDEN_PUBLIC_BINS; do
    case " $TRUST_TOOLCHAIN_BRANDED_PUBLIC_BINS " in
        *" $tool "*) fail "forbidden stock name $tool is listed as a branded Trust tool" ;;
    esac
done

echo "Trust toolchain surface tests: ok"
