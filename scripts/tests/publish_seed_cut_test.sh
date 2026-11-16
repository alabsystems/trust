#!/usr/bin/env bash
# scripts/publish_seed_cut.sh — the cut's archives' release and re-pin push happen only for
# a pack sealed from the mint, with the archives its re-pin pins, and fail closed when the
# cut's own inputs are not what they must be. It asks no candidate gate (D27, amended
# 2026-10-17): a stub `targo` on PATH records any call, and none may come. Synthetic tools
# in temporary roots: that stub, a stub `agh` that records its argv, and a local bare remote
# the re-pin branch is pushed to. No credential, network or build.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/publish-seed-cut-test.XXXXXX")"
WORK="$(cd "$WORK" && pwd -P)"
trap 'rm -rf "$WORK"' EXIT
checks=0
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }
ok() { checks=$((checks + 1)); printf 'ok %s\n' "$1"; }
GITC=(-c core.hooksPath=/dev/null -c commit.gpgsign=false -c user.name=fixture -c user.email=fixture@example.invalid)

# The trust checkout: this script, one commit, and the re-pin on its branch.
T="$WORK/trust"
mkdir -p "$T/scripts" "$T/src" "$T/bootstrap/trust-stage0"
cp "$REPO/scripts/publish_seed_cut.sh" "$T/scripts/"
echo base >"$T/README"
git -C "$T" init -q -b main
git -C "$T" add -A && git -C "$T" "${GITC[@]}" commit -qm base
C="$(git -C "$T" rev-parse HEAD)"
BRANCH="seed/repin-${C:0:12}"
TAG="trust-stage0-2026-10-03"
MINT="$T/build/pack-mint-1.99.0-aarch64-apple-darwin-${C:0:12}"
DIST="$MINT/repin/bootstrap/trust-stage0/dist/2026-10-03"
mkdir -p "$DIST"
printf 'trustc archive\n' >"$DIST/trustc-1.99.0-trust-aarch64-apple-darwin.tar.xz"
printf 'std archive\n' >"$DIST/trust-std-1.99.0-trust-aarch64-apple-darwin.tar.xz"
sha() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1"; else shasum -a 256 "$1"; fi | awk '{ print $1 }'; }
stage0() {
	printf 'compiler_date=2026-10-03\ncompiler_version=1.99.0-trust\n'
	for archive in "$DIST"/*.tar.xz; do
		printf 'dist/2026-10-03/%s=%s\n' "${archive##*/}" "$(sha "$archive")"
	done
}
ledger() { # ledger <tag> -> the re-pin's seed ledger
	printf 'scope = "internal"\nchecksums = [\n'
	for archive in "$DIST"/*.tar.xz; do
		printf '  "sha256:%s",\n' "$(sha "$archive")"
	done
	cat <<EOF
]

[release]
repo = "fixture/trust"
tag = "$1"
title = "Trust stage0 seed 2026-10-03 (1.99.0-trust, aarch64-apple-darwin)"
date = "2026-10-03"
EOF
}
git -C "$T" checkout -q -b "$BRANCH"
ledger "$TAG" >"$T/bootstrap/trust-stage0/seed-ledger.toml"
stage0 >"$T/src/stage0"
git -C "$T" add -A bootstrap src && git -C "$T" "${GITC[@]}" commit -qm "re-pin"
REPIN="$(git -C "$T" rev-parse HEAD)"
BASE_REPIN="$REPIN"
cp "$T/src/stage0" "$WORK/stage0.keep"
cp "$T/bootstrap/trust-stage0/seed-ledger.toml" "$WORK/ledger.keep"
git -C "$T" checkout -q main
git init -q --bare "$WORK/origin.git"
git -C "$T" remote add origin "$WORK/origin.git"
printf 'pinned_seed_commit=629729f69eefb1cfe6ed766c6c01ee38aa7b0484\nrepin_commit=%s\nrepin_branch=%s\nrepin_release_tag=%s\n' \
	"$REPIN" "$BRANCH" "$TAG" >"$MINT/trust-seed-mint"

# The staged pack: a toolchain carrying the mint's receipt.
PACK="$WORK/toolchains/stage-trust-${C:0:8}-wp"
mkdir -p "$PACK/bin"
printf '#!/bin/sh\necho "commit-hash: %s"\n' "$C" >"$PACK/bin/trustc" && chmod +x "$PACK/bin/trustc"
cp "$MINT/trust-seed-mint" "$PACK/SEED-MINT"

# aterm: only named, in the printed pack step; the script reads nothing there.
A="$WORK/aterm"
# targo: the script runs none (no candidate gate); a call is recorded and fails.
mkdir -p "$WORK/targo-bin"
cat >"$WORK/targo-bin/targo" <<STUB
#!/usr/bin/env bash
printf '%s\n' "\$*" >>"$WORK/targo.argv"
echo "stub targo: publish_seed_cut.sh must not run targo (\$*)" >&2
exit 2
STUB
chmod +x "$WORK/targo-bin/targo"
# agh: records the routed release act, with separate dry-run and upload refusals.
mkdir -p "$WORK/bin"
cat >"$WORK/bin/agh" <<STUB
#!/usr/bin/env bash
printf '%s\n' "\$*" >>"$WORK/agh.argv"
[[ \$1 == release && \$2 == ensure ]] || exit 2
case " \$* " in
  *" --dry-run "*) [[ ! -e "$WORK/agh-dry-fails" ]] ;;
  *) [[ ! -e "$WORK/agh-fails" ]] ;;
esac
STUB
# A stale gh call is an error even on machines where gh happens to be installed.
printf '#!/bin/sh\nexit 99\n' >"$WORK/bin/gh"
chmod +x "$WORK/bin/agh" "$WORK/bin/gh"
# The Git transport must never inherit the ambient GitHub token.
cat >"$WORK/origin.git/hooks/pre-receive" <<'STUB'
#!/bin/sh
[ -z "${GITHUB_TOKEN+x}" ] || exit 23
cat >/dev/null
STUB
chmod +x "$WORK/origin.git/hooks/pre-receive"
export PATH="$WORK/targo-bin:$WORK/bin:$PATH"
unset ATERM_ROOT

run() { # run [args…] -> $out, $rc (the script under test, from the trust checkout)
	set +e
	out="$(cd "$T" && bash scripts/publish_seed_cut.sh "$@" 2>&1)"
	rc=$?
	set -e
}
pushed() { git -C "$WORK/origin.git" rev-parse --verify -q "refs/heads/$BRANCH" || true; }
reset() { rm -f "$WORK/agh.argv" "$WORK/targo.argv" "$WORK/agh-fails" "$WORK/agh-dry-fails"; }
asked() { [[ -s "$WORK/targo.argv" ]]; }
untouched() { # nothing released, nothing pushed
	[[ ! -s "$WORK/agh.argv" && -z "$(pushed)" ]]
}
rewrite_repin() { # bind edited stage0 and ledger files to a new fixture re-pin
	git -C "$T" checkout -q "$BRANCH"
	cp "$1" "$T/src/stage0"
	cp "$2" "$T/bootstrap/trust-stage0/seed-ledger.toml"
	git -C "$T" add src/stage0 bootstrap/trust-stage0/seed-ledger.toml
	git -C "$T" "${GITC[@]}" commit -qm "fixture metadata change"
	REPIN="$(git -C "$T" rev-parse HEAD)"
	git -C "$T" checkout -q main
	sed "s/^repin_commit=.*/repin_commit=$REPIN/" "$WORK/seed-mint.keep" >"$MINT/trust-seed-mint"
	cp "$MINT/trust-seed-mint" "$PACK/SEED-MINT"
}
restore_repin() {
	git -C "$T" branch -q -f "$BRANCH" "$BASE_REPIN"
	REPIN="$BASE_REPIN"
	cp "$WORK/seed-mint.keep" "$PACK/SEED-MINT"
	cp "$WORK/seed-mint.keep" "$MINT/trust-seed-mint"
}
refused_inventory() { # invoke publication and verify all external acts stay untouched
	run --pack "$PACK" --mint "$MINT" --aterm "$A" --publish
	[[ $rc == 2 ]] && grep -q "$1" <<<"$out" && untouched && ! asked \
		|| fail "$2 (exit $rc): $out"
	ok "$2"
}

# 1. NO CANDIDATE GATE (D27, amended 2026-10-17): no aterm checkout is read, no targo is
# run, and the retired gate's options are refused as unknown.
reset
run --pack "$PACK" --mint "$MINT" --aterm "$WORK/no-aterm"
[[ $rc == 0 ]] && grep -q "in $WORK/no-aterm: targo --unverified run -q -p atpkg-publish -- --host agh publish-group rustc --seal $PACK" <<<"$out" && untouched && ! asked \
	|| fail "a dry run needs no aterm checkout and runs no targo (exit $rc): $out $(cat "$WORK/targo.argv" 2>/dev/null)"
ok "no candidate gate: an absent aterm checkout is only named, and no targo runs"
(cd "$T" && HOME="$WORK/no-home" bash scripts/publish_seed_cut.sh --pack "$PACK" --mint "$MINT" >"$WORK/o" 2>&1) || fail "a dry run with no --aterm must pass: $(cat "$WORK/o")"
grep -q "in $WORK/no-home/aterm: targo" "$WORK/o" && untouched && ! asked || fail "the default aterm named is ~/aterm: $(cat "$WORK/o")"
ok "the aterm checkout named by default is ~/aterm"
for retired in "--base-build 9192" "--receipts $WORK"; do
	# shellcheck disable=SC2086
	run --pack "$PACK" --mint "$MINT" --aterm "$A" $retired --publish
	[[ $rc == 2 ]] && grep -q "unknown argument ${retired%% *}" <<<"$out" && untouched && ! asked || fail "the gate's ${retired%% *} must be refused as unknown (exit $rc): $out"
done
ok "the retired gate options --base-build and --receipts are refused, nothing published"

# 2. THE PACK MUST BE THE MINT'S, its re-pin here, its archives the ledger's.
reset
cp "$PACK/SEED-MINT" "$WORK/seed-mint.keep"
echo "extra=1" >>"$PACK/SEED-MINT"
run --pack "$PACK" --mint "$MINT" --aterm "$A" --publish
cp "$WORK/seed-mint.keep" "$PACK/SEED-MINT"
[[ $rc == 2 ]] && grep -q "the pack's SEED-MINT is not $MINT/trust-seed-mint" <<<"$out" && untouched || fail "a pack not sealed from this mint must refuse (exit $rc): $out"
ok "a pack whose SEED-MINT is not the mint's receipt: refused"
git -C "$T" branch -q -f "$BRANCH" "$C"
run --pack "$PACK" --mint "$MINT" --aterm "$A" --publish
git -C "$T" branch -q -f "$BRANCH" "$REPIN"
[[ $rc == 2 ]] && grep -q "branch $BRANCH is $C here, not the re-pin" <<<"$out" && untouched || fail "a re-pin branch at another commit must refuse (exit $rc): $out"
ok "a re-pin branch that is not the receipt's commit: refused"
printf 'not pinned\n' >"$DIST/rogue.tar.xz"
run --pack "$PACK" --mint "$MINT" --aterm "$A" --publish
rm -f "$DIST/rogue.tar.xz"
[[ $rc == 2 ]] && grep -q "rogue.tar.xz" <<<"$out" && untouched || fail "an archive the ledger does not pin must refuse (exit $rc): $out"
ok "an archive the re-pin's ledger does not pin: refused"
TRUSTC_ARCHIVE="$DIST/trustc-1.99.0-trust-aarch64-apple-darwin.tar.xz"
STD_ARCHIVE="$DIST/trust-std-1.99.0-trust-aarch64-apple-darwin.tar.xz"
mv "$STD_ARCHIVE" "$WORK/std.keep"
refused_inventory 'missing=.*trust-std' "a missing pinned archive: refused before publication"
mv "$WORK/std.keep" "$STD_ARCHIVE"
mv "$STD_ARCHIVE" "$DIST/renamed.tar.xz"
refused_inventory 'missing=.*trust-std.*extra=.*renamed.tar.xz' "a renamed archive with pinned bytes: refused before publication"
mv "$DIST/renamed.tar.xz" "$STD_ARCHIVE"
cp "$TRUSTC_ARCHIVE" "$DIST/extra-copy.tar.xz"
refused_inventory 'extra=.*extra-copy.tar.xz' "an extra copy of pinned bytes: refused before publication"
rm "$DIST/extra-copy.tar.xz"
cp "$TRUSTC_ARCHIVE" "$DIST/extra.tar.gz"
refused_inventory 'extra=.*extra.tar.gz' "an extra archive in another compression format: refused before publication"
rm "$DIST/extra.tar.gz"
mv "$STD_ARCHIVE" "$WORK/std.keep"
ln -s "$WORK/std.keep" "$STD_ARCHIVE"
refused_inventory 'not a readable regular file' "a symlinked archive: refused before publication"
rm "$STD_ARCHIVE"
mkfifo "$STD_ARCHIVE"
refused_inventory 'not a regular file' "a nonregular archive: refused without blocking"
rm "$STD_ARCHIVE"
cp "$TRUSTC_ARCHIVE" "$STD_ARCHIVE"
refused_inventory 'differs from its re-pin src/stage0 pin' "pinned bytes under the wrong component name: refused before publication"
mv "$WORK/std.keep" "$STD_ARCHIVE"
mv "$DIST" "$DIST.actual"
ln -s "$DIST.actual" "$DIST"
refused_inventory 'archive directory is not a regular directory' "a symlinked archive directory: refused before publication"
rm "$DIST"
mv "$DIST.actual" "$DIST"
# The committed src/stage0 is the authority, rather than a mutable copy under the mint.
mkdir -p "$MINT/repin/src"
printf 'this mutable stage0 is ignored\n' >"$MINT/repin/src/stage0"
run --pack "$PACK" --mint "$MINT" --aterm "$A"
[[ $rc == 0 ]] && untouched || fail "only the re-pin commit supplies src/stage0 (exit $rc): $out"
ok "src/stage0 is read from the re-pin commit"
sed '/trust-std-/d' "$WORK/stage0.keep" >"$WORK/stage0.edited"
rewrite_repin "$WORK/stage0.edited" "$WORK/ledger.keep"
refused_inventory 'checksums do not match its src/stage0 archive pins' "a ledger inconsistent with src/stage0: refused before publication"
restore_repin
sed 's@dist/2026-10-03/trust-std-@dist/2026-10-03/../trust-std-@' "$WORK/stage0.keep" >"$WORK/stage0.edited"
rewrite_repin "$WORK/stage0.edited" "$WORK/ledger.keep"
refused_inventory 'noncanonical archive pin' "a traversal archive pin: refused before publication"
restore_repin
sed 's/compiler_date=2026-10-03/compiler_date=2026-10-04/' "$WORK/stage0.keep" >"$WORK/stage0.edited"
rewrite_repin "$WORK/stage0.edited" "$WORK/ledger.keep"
refused_inventory 'compiler_date differs from the seed ledger date' "a release date inconsistent with src/stage0: refused before publication"
restore_repin
sed 's/^repin_release_tag=.*/repin_release_tag=trust-stage0-other/' "$WORK/seed-mint.keep" >"$PACK/SEED-MINT"
cp "$PACK/SEED-MINT" "$MINT/trust-seed-mint"
run --pack "$PACK" --mint "$MINT" --aterm "$A" --publish
cp "$WORK/seed-mint.keep" "$PACK/SEED-MINT"; cp "$WORK/seed-mint.keep" "$MINT/trust-seed-mint"
[[ $rc == 2 ]] && grep -q "the re-pin seed ledger releases $TAG, the SEED-MINT receipt trust-stage0-other" <<<"$out" && untouched || fail "a release tag the ledger does not name must refuse (exit $rc): $out"
ok "a release tag the re-pin's ledger does not name: refused"

# Multi-host releases must publish the entire cohort and agree with each host table.
FOREIGN_ARCHIVE="$DIST/trustc-1.99.0-trust-x86_64-unknown-linux-gnu.tar.xz"
SOURCE_ARCHIVE="$DIST/trust-src-1.99.0-trust.tar.xz"
printf 'foreign trustc archive\n' >"$FOREIGN_ARCHIVE"
printf 'shared source archive\n' >"$SOURCE_ARCHIVE"
stage0 >"$WORK/stage0.edited"
ledger "$TAG" >"$WORK/ledger.hosts"
for host in aarch64-apple-darwin x86_64-unknown-linux-gnu; do
	printf '\n[release.hosts."%s"]\nhost = "%s"\n\n[release.hosts."%s".payloads]\n' "$host" "$host" "$host" >>"$WORK/ledger.hosts"
	for archive in "$DIST"/*-"$host".tar.xz "$SOURCE_ARCHIVE"; do
		printf '"dist/2026-10-03/%s" = "%s"\n' "${archive##*/}" "$(sha "$archive")" >>"$WORK/ledger.hosts"
	done
done
rewrite_repin "$WORK/stage0.edited" "$WORK/ledger.hosts"
run --pack "$PACK" --mint "$MINT" --aterm "$A"
[[ $rc == 0 ]] && grep -q "$FOREIGN_ARCHIVE" <<<"$out" && untouched || fail "a complete multi-host cohort passes (exit $rc): $out"
ok "the complete multi-host archive cohort passes"
mv "$FOREIGN_ARCHIVE" "$WORK/foreign.keep"
refused_inventory 'missing=.*x86_64-unknown-linux-gnu' "a missing second-host archive: refused before publication"
mv "$WORK/foreign.keep" "$FOREIGN_ARCHIVE"
sed '/^"dist\/.*x86_64-unknown-linux-gnu.tar.xz"/d' "$WORK/ledger.hosts" >"$WORK/ledger.edited"
rewrite_repin "$WORK/stage0.edited" "$WORK/ledger.edited"
refused_inventory 'host payloads differ from src/stage0: x86_64-unknown-linux-gnu' "a host table missing its pinned archive: refused before publication"
restore_repin
rm "$FOREIGN_ARCHIVE" "$SOURCE_ARCHIVE"
! asked || fail "no input refusal runs targo: $(cat "$WORK/targo.argv")"
ok "no input refusal runs targo"

# 3. CHECKED: a dry run prints the two acts and does neither; --publish does both, in order.
reset
run --pack "$PACK" --mint "$MINT" --aterm "$A"
[[ $rc == 0 ]] && grep -q "DRY RUN — $PACK is sealed from this mint" <<<"$out" && grep -q "1. agh release ensure fixture/trust $TAG --title" <<<"$out" \
	&& grep -q "2. env -u GITHUB_TOKEN git -C $T push origin refs/heads/$BRANCH:refs/heads/$BRANCH" <<<"$out" && untouched && ! asked || fail "a checked dry run prints both acts and does neither (exit $rc): $out"
grep -q "then, once main contains the re-pin, in $A: targo --unverified run -q -p atpkg-publish -- --host agh publish-group rustc --seal $PACK --trust-repo $T --out $PACK.atpkg-group --dry-run, then the same with --stage-upload; run its staging canary, then the same with --publish-staged" <<<"$out" \
	|| fail "the dry run names the pack's publish, aterm's atpkg-publish publish-group rustc: $out"
ok "checked, dry run: both acts printed, neither done, the pack's publish named"
reset; touch "$WORK/agh-dry-fails"
run --pack "$PACK" --mint "$MINT" --aterm "$A" --publish
[[ $rc == 1 && -z "$(pushed)" && $(wc -l <"$WORK/agh.argv") -eq 1 ]] \
	&& grep -q ' --publish --dry-run$' "$WORK/agh.argv" \
	&& grep -q "the release dry run failed; the re-pin is not pushed" <<<"$out" || fail "a refused agh dry run must stop before upload and push (exit $rc): $out"
ok "checked, the release dry run fails: neither upload nor re-pin push runs"
reset; touch "$WORK/agh-fails"
run --pack "$PACK" --mint "$MINT" --aterm "$A" --publish
[[ $rc == 1 && -z "$(pushed)" && $(wc -l <"$WORK/agh.argv") -eq 2 ]] && grep -q "the release did not publish; the re-pin is not pushed" <<<"$out" || fail "a failed release must stop before the push (exit $rc): $out"
ok "checked, the release fails: the re-pin is not pushed"
reset
GITHUB_TOKEN=fixture-must-not-reach-git ATERM_ROOT="$A" run --pack "$PACK" --mint "$MINT" --publish
[[ $rc == 0 ]] && ! asked || fail "a checked --publish must publish, and run no targo (exit $rc): $out"
grep -q "^release ensure fixture/trust $TAG --title Trust stage0 seed 2026-10-03 (1.99.0-trust, aarch64-apple-darwin) --notes .* --file $DIST/trust-std-1.99.0-trust-aarch64-apple-darwin.tar.xz --file $DIST/trustc-1.99.0-trust-aarch64-apple-darwin.tar.xz --publish$" "$WORK/agh.argv" \
	|| fail "the release names the ledger's repo, tag and title and every archive: $(cat "$WORK/agh.argv")"
[[ $(wc -l <"$WORK/agh.argv") -eq 2 ]] && head -n 1 "$WORK/agh.argv" | grep -q ' --publish --dry-run$' \
	|| fail "agh must preflight the same release act before publication"
[[ "$(pushed)" == "$REPIN" ]] || fail "the re-pin branch must reach the remote at the receipt's commit: $(pushed)"
grep -q "next, once main contains the re-pin, in $A: targo --unverified run -q -p atpkg-publish -- --host agh publish-group rustc --seal $PACK --trust-repo $T --out $PACK.atpkg-group --dry-run" <<<"$out" || fail "a publish names the pack's publish next: $out"
ok "checked, --publish (ATERM_ROOT names the checkout): the archives released, then the re-pin pushed"

printf 'publish_seed_cut_test: PASS (%d checks)\n' "$checks"
