#!/bin/sh
# Self-test for scripts/install-trust-toolchain.sh.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# WHAT CAN AND CANNOT BE TESTED HERE. The installer's expensive step is a 15-36
# minute `x.py build`, so this suite never reaches it: everything below runs in
# --dry-run (which mutates nothing) or stops at a refusal before any build. The
# BUILT half — that the generated config produces a sysroot which passes
# tools/verify-toolchain.sh, that the sysroot links, that the gates run through
# it — is proved against a real toolchain by tools/verify-toolchain.sh and
# scripts/prove-trust-frontend-gate.sh, which is where that evidence belongs.
#
# What this pins down is the part that is cheap to get wrong and expensive to
# discover: the CONFIG. `[build] tools = [...]` is an allowlist
# (tool.rs:900 l2_backend_enabled, absent = ALL, present = ONLY THESE) and
# `extended = true` is what puts trustfmt/tippy in the sysroot at all, so a
# generator that drifts on either one produces a green build with no formatter,
# no linter, or no verification backends.

set -eu

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
SOURCE_SCRIPT="$ROOT/scripts/install-trust-toolchain.sh"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/install-trust-toolchain-test.XXXXXX")"
# Physical path: the installer resolves its build dir with `pwd -P`, and on
# macOS $TMPDIR lives under a /var -> /private/var symlink, so a logical path
# here would never match the paths the script prints.
TMP_ROOT="$(cd "$TMP_ROOT" && pwd -P)"
cleanup() {
    chmod -R u+w "$TMP_ROOT" 2>/dev/null || true
    rm -rf "$TMP_ROOT"
}
trap cleanup EXIT HUP INT TERM

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

# A hermetic host: no brew, no rustup home, no Homebrew LLVM, and a stage0 rustc
# that answers -vV with a fixed host triple. Every path the installer prints is
# then a function of the fixture alone.
new_host() {
    name="$1"
    host="$TMP_ROOT/$name"
    mkdir -p "$host/fake-bin" "$host/home/.cargo/bin" "$host/stage0/bin" "$host/checkout"

    cat >"$host/stage0/bin/rustc" <<'SH'
#!/bin/sh
case "${1:-}" in
    -vV) printf 'rustc 1.95.0 (fixture)\nhost: test-host\n' ;;
    *)   printf 'rustc 1.95.0 (fixture)\n' ;;
esac
SH
    chmod +x "$host/stage0/bin/rustc"

    cat >"$host/fake-bin/llvm-config" <<'SH'
#!/bin/sh
echo '21.1.0'
SH
    chmod +x "$host/fake-bin/llvm-config"

    cat >"$host/home/.cargo/bin/rustup" <<'SH'
#!/bin/sh
printf '%s\n' "$*" >>"${RUSTUP_CALL_LOG:-/dev/null}"
case "$1" in
    "toolchain") [ "${2:-}" = list ] && echo "trust" ;;
esac
exit 0
SH
    chmod +x "$host/home/.cargo/bin/rustup"

    # A checkout shaped like the real one: x.py plus the two contract scripts the
    # installer delegates to.
    : >"$host/checkout/x.py"
    mkdir -p "$host/checkout/tools" "$host/checkout/scripts"
    printf '#!/bin/sh\nexit 0\n' >"$host/checkout/tools/verify-toolchain.sh"
    printf '#!/bin/sh\nexit 0\n' >"$host/checkout/scripts/rustup-link-trust.sh"
    chmod +x "$host/checkout/tools/verify-toolchain.sh" "$host/checkout/scripts/rustup-link-trust.sh"

    printf '%s\n' "$host"
}

# PATH deliberately omits the rustup shim dir: that is this machine's real
# default (measured 2026-08-22 — `command -v rustc` is /opt/homebrew/bin/rustc
# and $HOME/.cargo/bin is nowhere on PATH), and it is the condition the
# installer has to detect and say out loud.
run_install() {
    host="$1"
    shift
    env -i \
        HOME="$host/home" \
        PATH="$host/fake-bin:/usr/bin:/bin:/usr/sbin:/sbin" \
        TMPDIR="$TMP_ROOT" \
        TRUST_STAGE0_RUSTC="$host/stage0/bin/rustc" \
        TRUST_LLVM_CONFIG="$host/fake-bin/llvm-config" \
        RUSTUP_CALL_LOG="$host/rustup-call.log" \
        sh "$SOURCE_SCRIPT" "$@"
}

# --- usage surface ----------------------------------------------------------
sh "$SOURCE_SCRIPT" --help >"$TMP_ROOT/help.out" 2>&1 \
    || fail "--help exited non-zero"
grep -q -- '--build-dir DIR' "$TMP_ROOT/help.out" || fail "--help does not document --build-dir"
grep -q -- '--dry-run' "$TMP_ROOT/help.out" || fail "--help does not document --dry-run"

if sh "$SOURCE_SCRIPT" --not-an-option >"$TMP_ROOT/bad.out" 2>&1; then
    fail "an unknown argument was accepted"
fi

host="$(new_host stage-validation)"
if run_install "$host" --stage 3 --build-dir "$host/checkout" --dry-run \
    >"$TMP_ROOT/stage3.out" 2>&1; then
    fail "--stage 3 was accepted"
fi
grep -q 'stage must be 1 or 2' "$TMP_ROOT/stage3.out" || fail "--stage 3 rejection was not explicit"

# --- dry-run plans the whole thing and touches nothing -----------------------
host="$(new_host dry-run)"
run_install "$host" --build-dir "$host/checkout" --dry-run \
    >"$TMP_ROOT/dry.out" 2>"$TMP_ROOT/dry.err" \
    || fail "dry run exited non-zero: $(cat "$TMP_ROOT/dry.err")"

[ ! -e "$host/checkout/bootstrap.toml" ] || fail "dry run wrote bootstrap.toml"
[ ! -e "$host/checkout/build" ] || fail "dry run created a build directory"
[ ! -e "$host/rustup-call.log" ] || fail "dry run invoked rustup"

for needle in \
    'would run: git -C .* submodule update --init --recursive' \
    'would run: .*x.py build --stage 1' \
    'would run: sh .*verify-toolchain.sh' \
    'would run: sh .*rustup-link-trust.sh --name trust --sysroot' \
    'would run: sh .*prove-trust-frontend-gate.sh'
do
    grep -Eq "$needle" "$TMP_ROOT/dry.out" || fail "dry-run plan is missing a step: $needle"
done

# ORDERING IS THE GUARD (see the submodule fixtures at the bottom of this file):
# the classification must be planned BEFORE the update, because the update is
# what destroys the state being classified.
awk '/classification, BEFORE any mutation/ { c = NR }
     /would run: git -C .* submodule update --init --recursive/ { u = NR }
     END { exit !(c > 0 && u > 0 && c < u) }' "$TMP_ROOT/dry.out" \
    || fail "the plan does not classify submodule drift before mutating the worktrees"

# The contract scripts come from THIS repo, never from the build tree. The
# fixture checkout carries decoy copies of both, and picking them up would mean
# the decision to link is made by whatever commit the build tree happens to sit
# at — measured 2026-08-22, a tree 14 commits behind main rejected a sysroot its
# own bootstrap produced, because it held 76d408e1cd (emit `rustdoc`) without
# f12893ca49 (admit `rustdoc` as an alias).
grep -q "would run: sh $ROOT/tools/verify-toolchain.sh" "$TMP_ROOT/dry.out" \
    || fail "verify step does not use this repo's verify-toolchain.sh"
grep -q "would run: sh $ROOT/scripts/rustup-link-trust.sh" "$TMP_ROOT/dry.out" \
    || fail "link step does not use this repo's rustup-link-trust.sh"
grep -q "$host/checkout/tools/verify-toolchain.sh" "$TMP_ROOT/dry.out" \
    && fail "verify step took its contract from the build tree"
grep -q "$host/checkout/scripts/rustup-link-trust.sh" "$TMP_ROOT/dry.out" \
    && fail "link step took its contract from the build tree"

# The sysroot is addressed by explicit triple, never by the build/host symlink,
# because the tree being linked need not be the repo the script ran from.
grep -q "$host/checkout/build/test-host/stage1" "$TMP_ROOT/dry.out" \
    || fail "sysroot path was not derived from the detected host triple"

# --- the PATH condition that makes a linked toolchain invisible --------------
grep -q 'is NOT on PATH' "$TMP_ROOT/dry.err" \
    || fail "installer did not warn that \$HOME/.cargo/bin is off PATH"

# ...and the step 8 proof must not launder that same condition. It used to
# prepend $HOME/.cargo/bin itself, print one stderr NOTE, and go on to print
# PROOF COMPLETE — a proof about a shell it had just built, on a machine where
# every pinned repository would still refuse. A NOTE under a green result is
# read by nobody, so this is now a failure.
# A separate variable: $host still names the dry-run fixture whose generated
# config is asserted below.
proof_host="$(new_host proof-refuses-path-repair)"
if env -i HOME="$proof_host/home" PATH="/usr/bin:/bin:/usr/sbin:/sbin" TMPDIR="$TMP_ROOT" \
    sh "$ROOT/scripts/prove-trust-frontend-gate.sh" >"$TMP_ROOT/proofpath.out" 2>&1; then
    fail "the frontend-gate proof passed on a PATH that cannot find rustup at all"
fi
grep -q 'PROOF FAILED' "$TMP_ROOT/proofpath.out" \
    || fail "the proof did not fail loudly when its own PATH could not find rustup"
grep -q 'PROOF COMPLETE' "$TMP_ROOT/proofpath.out" \
    && fail "the proof reported completion after repairing the very PATH under test"
grep -q 'export PATH=' "$TMP_ROOT/proofpath.out" \
    || fail "the proof's PATH refusal does not carry the fix"

# ...nor may step 1 read a FAILING pin reader as "no shim on PATH". A rustup
# `rustc` shim whose link is stale prints nothing on stdout, exactly like aterm's
# reroute stub; for a while the proof took any empty `rustc --print sysroot` as
# "no shim" and printed PROOF COMPLETE — channel resolves, when the pin had not
# resolved at all. Only the reroute stub, identified positively, may be skipped.
# A hermetic Trust frontend: `trustc` and `rustup run trust` agree on a sysroot.
pin_fx="$TMP_ROOT/pin-reader"
mkdir -p "$pin_fx/sysroot/bin" "$pin_fx/sysroot/lib" "$pin_fx/rustup-bin" \
    "$pin_fx/stale-shim" "$pin_fx/reroute" "$pin_fx/home"
cat >"$pin_fx/sysroot/bin/trustc" <<SH
#!/bin/sh
[ "\$1" = --print ] && [ "\$2" = sysroot ] && { printf '%s\\n' "$pin_fx/sysroot"; exit 0; }
exit 1
SH
printf 'fixture driver' >"$pin_fx/sysroot/lib/librustc_driver-fixture.dylib"
cat >"$pin_fx/rustup-bin/rustup" <<'SH'
#!/bin/sh
case "$1" in
    toolchain) printf 'trust\n' ;;
    run) shift 2; exec "$@" ;;
    *) exit 1 ;;
esac
SH
cat >"$pin_fx/stale-shim/rustc" <<'SH'
#!/bin/sh
echo "error: 'rustc' is not installed for the custom toolchain 'trust'." >&2
exit 1
SH
printf 'reroute dir\n' >"$pin_fx/reroute/.atpkg-reroute-dir"
cat >"$pin_fx/reroute/rustc" <<'SH'
#!/bin/sh
# atpkg reroute stub v1
echo "aterm: upstream 'rustc' is not on PATH; on Trust the tool is 'trustc'" >&2
exit 127
SH
chmod +x "$pin_fx/sysroot/bin/trustc" "$pin_fx/rustup-bin/rustup" \
    "$pin_fx/stale-shim/rustc" "$pin_fx/reroute/rustc"
pin_path_tail="$pin_fx/sysroot/bin:$pin_fx/rustup-bin:/usr/bin:/bin:/usr/sbin:/sbin"
run_pin_proof() {
    env -i HOME="$pin_fx/home" PATH="$1" TMPDIR="$TMP_ROOT" \
        sh "$ROOT/scripts/prove-trust-frontend-gate.sh" >"$2" 2>&1
}

# (a) the stale shim FIRST on PATH: the reviewer's measured mutant.
if run_pin_proof "$pin_fx/stale-shim:$pin_path_tail" "$TMP_ROOT/pin-stale.out"; then
    fail "the frontend-gate proof passed with a rustc shim that cannot resolve the pin"
fi
grep -q 'PROOF FAILED: .*stale-shim/rustc --print sysroot' "$TMP_ROOT/pin-stale.out" \
    || fail "a failing pin reader was not the named cause of the proof's failure"
grep -q 'PROOF COMPLETE' "$TMP_ROOT/pin-stale.out" \
    && fail "the proof reported completion over a pin reader that resolves nothing"

# (b) the stub first, the stale shim behind it: the stub execs that shim in
# passthrough mode, so the shim is still the reader, and it still fails.
if run_pin_proof "$pin_fx/reroute:$pin_fx/stale-shim:$pin_path_tail" "$TMP_ROOT/pin-behind.out"; then
    fail "the proof passed with a failing rustc shim behind the reroute stub"
fi
grep -q 'PROOF FAILED: .*stale-shim/rustc --print sysroot' "$TMP_ROOT/pin-behind.out" \
    || fail "a failing pin reader behind the reroute stub was not named"

# (c) positive control: only the reroute stub. Step 1 passes and says the pin
# was not read; the proof then stops at the fixture's missing targo (step 2).
if run_pin_proof "$pin_fx/reroute:$pin_path_tail" "$TMP_ROOT/pin-stub.out"; then
    fail "the proof passed on a fixture sysroot with no targo"
fi
grep -q "PROVED   no pin reader on PATH: the only \`rustc\` on PATH is aterm's reroute stub" \
    "$TMP_ROOT/pin-stub.out" || fail "the proof did not identify the reroute stub positively"
grep -q 'targo is missing' "$TMP_ROOT/pin-stub.out" \
    || fail "with only the reroute stub, the proof did not get past step 1"

# --- the generated config ---------------------------------------------------
# Extracted from the dry-run's "would write" block, which is the same text the
# non-dry run writes (one emit_bootstrap_toml, two consumers).
sed -n 's/^  | //p' "$TMP_ROOT/dry.out" >"$TMP_ROOT/generated.toml"
[ -s "$TMP_ROOT/generated.toml" ] || fail "dry run printed no bootstrap.toml content"

grep -Eq '^extended = true$' "$TMP_ROOT/generated.toml" \
    || fail "generated bootstrap.toml does not set extended = true"
if grep -Eq '^[[:space:]]*tools[[:space:]]*=' "$TMP_ROOT/generated.toml"; then
    fail "generated bootstrap.toml declares a [build] tools allowlist — that is the
  configuration that silently drops the verification backends"
fi

# The [build] key set, in order, as the working toolchain tree carries it. A
# golden list rather than spot checks: an added or dropped key here changes what
# the build produces, and the difference does not surface until something is
# missing from the sysroot.
awk '/^\[build\]/{inblock=1;next} /^\[/{inblock=0} /^#/{next} inblock && /=/{sub(/[ \t]*=.*/,"");print}' \
    "$TMP_ROOT/generated.toml" >"$TMP_ROOT/build-keys"
cat >"$TMP_ROOT/build-keys.golden" <<'KEYS'
rustc
cargo
rustfmt
rustdoc
docs
submodules
extended
KEYS
if ! cmp -s "$TMP_ROOT/build-keys" "$TMP_ROOT/build-keys.golden"; then
    echo "generated [build] keys:" >&2
    cat "$TMP_ROOT/build-keys" >&2
    fail "generated [build] section drifted from the settings the working toolchain tree has"
fi

grep -q "^rustc   = \"$host/stage0/bin/rustc\"$" "$TMP_ROOT/generated.toml" \
    || fail "generated config does not point stage0 at the detected host rustc"
grep -q '^docs = false$' "$TMP_ROOT/generated.toml" || fail "docs = false missing"
grep -q '^submodules = false$' "$TMP_ROOT/generated.toml" || fail "submodules = false missing"
grep -q '^download-ci-llvm = false$' "$TMP_ROOT/generated.toml" || fail "download-ci-llvm = false missing"
grep -q '^\[target.test-host\]$' "$TMP_ROOT/generated.toml" \
    || fail "generated config has no [target.<host-triple>] section"
grep -q "^llvm-config = \"$host/fake-bin/llvm-config\"$" "$TMP_ROOT/generated.toml" \
    || fail "generated config does not point at the detected llvm-config"
grep -q '^channel = "trust"$' "$TMP_ROOT/generated.toml" || fail "[rust] channel = \"trust\" missing"

# --- an existing config is validated, never rewritten -----------------------
host="$(new_host reuse-good-config)"
cat >"$host/checkout/bootstrap.toml" <<'TOML'
# hand-written, deliberately different from what the generator emits
[build]
extended = true
TOML
cp "$host/checkout/bootstrap.toml" "$TMP_ROOT/reuse-before.toml"
run_install "$host" --build-dir "$host/checkout" --dry-run \
    >"$TMP_ROOT/reuse.out" 2>&1 || fail "dry run over a valid existing config failed"
cmp -s "$host/checkout/bootstrap.toml" "$TMP_ROOT/reuse-before.toml" \
    || fail "an existing bootstrap.toml was rewritten"
grep -q 'reusing existing' "$TMP_ROOT/reuse.out" || fail "reuse of an existing config was not stated"

# --- the allowlist trap is refused, before any build ------------------------
host="$(new_host tools-allowlist)"
cat >"$host/checkout/bootstrap.toml" <<'TOML'
[build]
extended = true
tools = ["trustfmt", "tippy"]
TOML
if run_install "$host" --build-dir "$host/checkout" --dry-run \
    >"$TMP_ROOT/tools.out" 2>&1; then
    fail "a bootstrap.toml with a [build] tools allowlist was accepted"
fi
grep -q 'ALLOWLIST' "$TMP_ROOT/tools.out" \
    || fail "the tools-list refusal does not explain the allowlist semantics"
grep -q 'would run: .*x.py build' "$TMP_ROOT/tools.out" \
    && fail "the installer planned a build despite refusing the configuration"

# --- a config that cannot produce the tier-2 surface is refused -------------
host="$(new_host no-extended)"
cat >"$host/checkout/bootstrap.toml" <<'TOML'
[build]
docs = false
TOML
if run_install "$host" --build-dir "$host/checkout" --dry-run \
    >"$TMP_ROOT/noext.out" 2>&1; then
    fail "a bootstrap.toml without extended = true was accepted"
fi
grep -q 'extended = true' "$TMP_ROOT/noext.out" \
    || fail "the missing-extended refusal does not name the setting to add"
grep -q 'trustfmt' "$TMP_ROOT/noext.out" \
    || fail "the missing-extended refusal does not name what would be absent"

# --- --link-only skips the two expensive steps ------------------------------
host="$(new_host link-only)"
run_install "$host" --build-dir "$host/checkout" --link-only --dry-run \
    >"$TMP_ROOT/linkonly.out" 2>&1 || fail "--link-only dry run failed"
grep -q 'submodules — skipped' "$TMP_ROOT/linkonly.out" || fail "--link-only still plans submodules"
grep -q 'x.py build — skipped' "$TMP_ROOT/linkonly.out" || fail "--link-only still plans a build"
grep -q 'would run: sh .*rustup-link-trust.sh' "$TMP_ROOT/linkonly.out" \
    || fail "--link-only skipped the link it exists to perform"
[ ! -e "$host/checkout/bootstrap.toml" ] \
    || fail "--link-only wrote a config for a tree that is already built"

# --- --skip-proof is the only way to lose the proof step --------------------
host="$(new_host skip-proof)"
run_install "$host" --build-dir "$host/checkout" --skip-proof --dry-run \
    >"$TMP_ROOT/skipproof.out" 2>&1 || fail "--skip-proof dry run failed"
grep -q 'proof — skipped' "$TMP_ROOT/skipproof.out" || fail "--skip-proof did not skip the proof"

# --- re-running plans the same thing (idempotence of the PLAN) --------------
host="$(new_host idempotent)"
run_install "$host" --build-dir "$host/checkout" --dry-run >"$TMP_ROOT/first.out" 2>&1 \
    || fail "first dry run failed"
run_install "$host" --build-dir "$host/checkout" --dry-run >"$TMP_ROOT/second.out" 2>&1 \
    || fail "second dry run failed"
cmp -s "$TMP_ROOT/first.out" "$TMP_ROOT/second.out" \
    || fail "two identical dry runs produced different plans"

# --- a build dir that is not a checkout is refused, not created into ---------
host="$(new_host not-a-checkout)"
mkdir -p "$host/empty"
if run_install "$host" --build-dir "$host/empty" --dry-run >"$TMP_ROOT/empty.out" 2>&1; then
    fail "a directory with no x.py was accepted as a build tree"
fi
grep -q 'not a Trust checkout' "$TMP_ROOT/empty.out" || fail "non-checkout refusal was not explicit"

# --- the submodule guard: classify BEFORE mutating --------------------------
# REGRESSION (2026-08-23). Step 4 used to run
#
#     git -C "$BUILD_DIR" submodule update --init --recursive
#
# FIRST and scripts/submodule_sync.sh second. The blanket recursive update
# checks every drifted worktree back onto its pin, so the classifier that
# followed it always saw a synced tree and returned 0: the guard could not fire
# for the case its own refusal message describes, and the "restoring would
# destroy commits" it warned about had already been done by the line above it.
# Measured on the fixture below with the old ordering: `submodule sync: OK — all
# 1 submodule worktrees are at the pins`, exit 0, and the unlanded commit on no
# ref afterwards. These two cases pin the ordering AND its two outcomes.
#
# Both run the installer for real (not --dry-run): the classification only runs
# outside dry-run, and the refusal is what stops the run before x.py. The
# fixture's x.py is empty, so the BEHIND case is stopped a step later by the
# sysroot check instead, which is asserted rather than ignored.
GITF="git -c protocol.file.allow=always -c advice.detachedHead=false"
GITF="$GITF -c user.name=install-test -c user.email=install-test@example.invalid"
GITF="$GITF -c commit.gpgsign=false -c init.defaultBranch=main"

# A superproject fixture: the hermetic host above, plus a real first-party/
# submodule whose worktree can be placed in any state. Real git objects, not a
# simulation — the bug was in what git does to them.
new_submodule_host() {
    host="$(new_host "$1")"
    donor="$host/donor"
    mkdir -p "$donor"
    $GITF init -q "$donor"
    n=1
    while [ "$n" -le 3 ]; do
        echo "line $n" >>"$donor/f.txt"
        $GITF -C "$donor" add f.txt
        $GITF -C "$donor" commit -qm "c$n"
        n=$((n + 1))
    done
    $GITF init -q "$host/checkout"
    $GITF -C "$host/checkout" add -A
    $GITF -C "$host/checkout" commit -qm root
    mkdir -p "$host/checkout/first-party"
    $GITF -C "$host/checkout" submodule -q add "$donor" first-party/sub
    $GITF -C "$host/checkout" commit -qm "pin first-party/sub" >/dev/null
    # The installer's own git calls carry no -c flags; local file:// submodule
    # transport is refused by default since git 2.38 (CVE-2022-39253).
    $GITF -C "$host/checkout" config protocol.file.allow always
    printf '%s\n' "$host"
}

host="$(new_submodule_host guard-ahead)"
sub="$host/checkout/first-party/sub"
pin="$($GITF -C "$sub" rev-parse HEAD)"
# A commit that lives in the worktree and on NO ref: the only shape that proves
# the refusal is real, because it is the only one a checkout actually loses.
# DETACHED first — committing on a branch would advance refs/heads/main, which
# is a durable ref, which makes the module ANCHORED and therefore lossless to
# restore. That is a different (correct) verdict, and it is not this test.
$GITF -C "$sub" checkout -q --detach HEAD
echo "unlanded work" >"$sub/local.txt"
$GITF -C "$sub" add local.txt
$GITF -C "$sub" commit -qm "unlanded work"
ahead="$($GITF -C "$sub" rev-parse HEAD)"
[ "$ahead" != "$pin" ] || fail "fixture did not move the submodule worktree off its pin"

if run_install "$host" --build-dir "$host/checkout" \
    >"$TMP_ROOT/guard.out" 2>"$TMP_ROOT/guard.err"; then
    fail "the installer proceeded past a submodule worktree holding unlanded commits"
fi
grep -q 'AHEAD of or DIVERGENT' "$TMP_ROOT/guard.err" \
    || fail "the submodule refusal does not name the state it refused"
# The teeth: the refusal came BEFORE the update, so the unlanded commit is still
# checked out. Under the old ordering this assertion is the one that fails —
# HEAD would be the pin, having been moved by the very command the message says
# it refused to run.
[ "$($GITF -C "$sub" rev-parse HEAD)" = "$ahead" ] \
    || fail "the installer moved the submodule worktree onto its pin while refusing to proceed"
grep -q 'x.py build' "$TMP_ROOT/guard.out" \
    && fail "the installer reached the build step after refusing the submodule state"

# BEHIND is lossless to restore, so the guard must NOT fire: a guard that
# refuses a merely stale (or fresh) tree is a guard people delete.
host="$(new_submodule_host guard-behind)"
sub="$host/checkout/first-party/sub"
pin="$($GITF -C "$sub" rev-parse HEAD)"
$GITF -C "$sub" checkout -q --detach "$pin~1"
[ "$($GITF -C "$sub" rev-parse HEAD)" != "$pin" ] || fail "fixture did not put the worktree behind its pin"

run_install "$host" --build-dir "$host/checkout" \
    >"$TMP_ROOT/behind.out" 2>"$TMP_ROOT/behind.err" || true
grep -q 'AHEAD of or DIVERGENT' "$TMP_ROOT/behind.err" \
    && fail "the guard refused a BEHIND worktree, which is provably lossless to restore"
[ "$($GITF -C "$sub" rev-parse HEAD)" = "$pin" ] \
    || fail "the update did not run after the classifier cleared the tree"
grep -q 'step 5/8' "$TMP_ROOT/behind.out" \
    || fail "the installer did not reach the build step on a lossless-to-restore tree"
# It stops one step later, on the fixture's absent sysroot — named here so a
# future change that stops it EARLIER cannot masquerade as this pass.
grep -q 'no sysroot at' "$TMP_ROOT/behind.err" \
    || fail "the BEHIND run stopped somewhere other than the sysroot check"

# A LINKED build tree is populated by the classifier's --restore, never by the
# blanket update. A build tree made by `git worktree add` (what this installer
# makes when --build-dir does not exist) shares each submodule's repository with
# the first checkout, and `git submodule update` there rewrites core.worktree in
# that shared config even when it moves nothing. Measured with this fixture and
# the old step (Apple Git 2.54.0): `worktree = ../../../../first-party/sub`
# became `../../../../../../../second/first-party/sub`, which resolves from
# neither tree's side of that config, and the first checkout's
# `git -C first-party/sub rev-parse HEAD` failed.
# The teeth are the byte comparison of that config and the absent update line.
host="$(new_submodule_host guard-linked)"
sub="$host/checkout/first-party/sub"
pin="$($GITF -C "$sub" rev-parse HEAD)"
$GITF -C "$host/checkout" worktree add -q --detach "$host/second" HEAD
$GITF -C "$sub" worktree add -q --detach "$host/second/first-party/sub" "$pin~1"
store_config="$host/checkout/.git/modules/first-party/sub/config"
cp "$store_config" "$TMP_ROOT/linked-store-config.before"
[ -f "$($GITF -C "$host/second/first-party/sub" rev-parse --absolute-git-dir)/commondir" ] \
    || fail "fixture did not make the second tree's submodule a linked worktree"

run_install "$host" --build-dir "$host/second" --dry-run \
    >"$TMP_ROOT/linked-dry.out" 2>&1 || fail "dry run of a linked build tree failed"
grep -Eq 'would run: bash .*submodule_sync.sh --root .*/second --restore' "$TMP_ROOT/linked-dry.out" \
    || fail "the dry run of a linked build tree does not plan the classifier's --restore"
grep -q 'submodule update --init --recursive' "$TMP_ROOT/linked-dry.out" \
    && fail "the dry run of a linked build tree plans the blanket submodule update"

run_install "$host" --build-dir "$host/second" \
    >"$TMP_ROOT/linked.out" 2>"$TMP_ROOT/linked.err" || true
[ "$($GITF -C "$host/second/first-party/sub" rev-parse HEAD)" = "$pin" ] \
    || fail "the linked build tree's submodule was not moved to its pin"
cmp -s "$store_config" "$TMP_ROOT/linked-store-config.before" \
    || fail "populating a linked build tree rewrote the first checkout's submodule config"
[ "$($GITF -C "$sub" rev-parse HEAD)" = "$pin" ] \
    || fail "populating a linked build tree broke or moved the first checkout's submodule"
grep -Eq '^  \+ bash .*submodule_sync.sh --root .*/second --restore$' "$TMP_ROOT/linked.out" \
    || fail "a linked build tree was not populated through the classifier's --restore"
grep -Eq '^  \+ git -C .* submodule update --init --recursive' "$TMP_ROOT/linked.out" \
    && fail "the blanket submodule update ran in a linked build tree"
grep -q 'no sysroot at' "$TMP_ROOT/linked.err" \
    || fail "the linked run stopped somewhere other than the sysroot check"

# The installer's own case: a build tree `git worktree add` has just made, with
# its submodule never checked out. --restore makes that checkout a linked
# worktree of the first checkout's store (its git directory has a `commondir`),
# and the build tree gets no store of its own.
host="$(new_submodule_host guard-linked-absent)"
sub="$host/checkout/first-party/sub"
pin="$($GITF -C "$sub" rev-parse HEAD)"
$GITF -C "$host/checkout" worktree add -q --detach "$host/second" HEAD
store_config="$host/checkout/.git/modules/first-party/sub/config"
cp "$store_config" "$TMP_ROOT/absent-store-config.before"
[ ! -e "$host/second/first-party/sub/.git" ] \
    || fail "fixture: the new build tree's submodule is already checked out"

run_install "$host" --build-dir "$host/second" \
    >"$TMP_ROOT/absent.out" 2>"$TMP_ROOT/absent.err" || true
[ "$($GITF -C "$host/second/first-party/sub" rev-parse HEAD)" = "$pin" ] \
    || fail "the new build tree's submodule was not checked out at its pin"
[ -f "$($GITF -C "$host/second/first-party/sub" rev-parse --absolute-git-dir)/commondir" ] \
    || fail "the new build tree's submodule is not a linked worktree of the first checkout's store"
[ ! -e "$host/checkout/.git/worktrees/second/modules" ] \
    || fail "the new build tree was given a submodule store of its own"
cmp -s "$store_config" "$TMP_ROOT/absent-store-config.before" \
    || fail "populating a new build tree rewrote the first checkout's submodule config"
[ "$($GITF -C "$sub" rev-parse HEAD)" = "$pin" ] \
    || fail "populating a new build tree broke or moved the first checkout's submodule"
grep -Eq '^  \+ bash .*submodule_sync.sh --root .*/second --restore$' "$TMP_ROOT/absent.out" \
    || fail "a new build tree was not populated through the classifier's --restore"
grep -Eq '^  \+ git -C .* submodule update --init --recursive' "$TMP_ROOT/absent.out" \
    && fail "the blanket submodule update ran in a new linked build tree"
grep -q 'no sysroot at' "$TMP_ROOT/absent.err" \
    || fail "the new-build-tree run stopped somewhere other than the sysroot check"

# The same tree on a host where the classifier cannot run (here a `bash` that
# exits 3, its environment-error code). Only --restore makes the shared shape,
# so nothing is linked there, and the blanket update is what it always was: a
# clone for this tree alone. The tree is populated, not left without sources.
host="$(new_submodule_host guard-linked-noclassifier)"
sub="$host/checkout/first-party/sub"
pin="$($GITF -C "$sub" rev-parse HEAD)"
printf '#!/bin/sh\nexit 3\n' >"$host/fake-bin/bash"
chmod +x "$host/fake-bin/bash"
$GITF -C "$host/checkout" worktree add -q --detach "$host/second" HEAD
store_config="$host/checkout/.git/modules/first-party/sub/config"
cp "$store_config" "$TMP_ROOT/noclassifier-store-config.before"

# git does not hand the superproject's protocol.file.allow to the clone a
# submodule update starts, so this one run allows the fixture's local donor in
# the environment, which that clone does read.
env -i \
    HOME="$host/home" \
    PATH="$host/fake-bin:/usr/bin:/bin:/usr/sbin:/sbin" \
    TMPDIR="$TMP_ROOT" \
    TRUST_STAGE0_RUSTC="$host/stage0/bin/rustc" \
    TRUST_LLVM_CONFIG="$host/fake-bin/llvm-config" \
    RUSTUP_CALL_LOG="$host/rustup-call.log" \
    GIT_ALLOW_PROTOCOL=file \
    sh "$SOURCE_SCRIPT" --build-dir "$host/second" \
    >"$TMP_ROOT/noclassifier.out" 2>"$TMP_ROOT/noclassifier.err" || true
grep -q 'the submodule classifier could not run (exit 3)' "$TMP_ROOT/noclassifier.err" \
    || fail "fixture: the classifier ran, so the no-classifier branch was not taken"
[ "$($GITF -C "$host/second/first-party/sub" rev-parse HEAD)" = "$pin" ] \
    || fail "a linked build tree was left without its submodule when the classifier could not run"
[ -d "$host/checkout/.git/worktrees/second/modules/first-party/sub/objects" ] \
    || fail "the no-classifier fallback did not clone a store for the build tree alone"
cmp -s "$store_config" "$TMP_ROOT/noclassifier-store-config.before" \
    || fail "the no-classifier fallback rewrote the first checkout's submodule config"
[ "$($GITF -C "$sub" rev-parse HEAD)" = "$pin" ] \
    || fail "the no-classifier fallback broke or moved the first checkout's submodule"
grep -Eq '^  \+ git -C .*/second submodule update --init --recursive' "$TMP_ROOT/noclassifier.out" \
    || fail "the no-classifier fallback did not run the update in a tree with nothing linked"

# ...and never where a checkout IS linked: the update would rewrite the first
# checkout's config. With nothing absent the tree is left as it is.
host="$(new_submodule_host guard-linked-noclassifier-linked)"
sub="$host/checkout/first-party/sub"
pin="$($GITF -C "$sub" rev-parse HEAD)"
printf '#!/bin/sh\nexit 3\n' >"$host/fake-bin/bash"
chmod +x "$host/fake-bin/bash"
$GITF -C "$host/checkout" worktree add -q --detach "$host/second" HEAD
$GITF -C "$sub" worktree add -q --detach "$host/second/first-party/sub" "$pin"
store_config="$host/checkout/.git/modules/first-party/sub/config"
cp "$store_config" "$TMP_ROOT/noclassifier-linked-store-config.before"

run_install "$host" --build-dir "$host/second" \
    >"$TMP_ROOT/noclassifier-linked.out" 2>"$TMP_ROOT/noclassifier-linked.err" || true
grep -q 'the submodule classifier could not run (exit 3)' "$TMP_ROOT/noclassifier-linked.err" \
    || fail "fixture: the classifier ran, so the no-classifier branch was not taken"
grep -Eq '^  \+ git -C .* submodule update --init --recursive' "$TMP_ROOT/noclassifier-linked.out" \
    && fail "the blanket submodule update ran over a linked submodule checkout"
cmp -s "$store_config" "$TMP_ROOT/noclassifier-linked-store-config.before" \
    || fail "a linked submodule checkout's shared config was rewritten when the classifier could not run"
[ "$($GITF -C "$sub" rev-parse HEAD)" = "$pin" ] \
    || fail "the first checkout's submodule broke when the classifier could not run"

echo "install-trust-toolchain tests: ok"
