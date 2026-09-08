#!/usr/bin/env bash
# Promote a freshly-built stage2 into a sealed, immutable Trust toolchain
# artifact and flip the rustup `trust` channel onto it — atomically.
#
# WHY: linking rustup straight at build/<host>/stage2 points the channel at the
# LIVE build directory. Sessions iterating on the compiler run x.py
# continuously, and x.py empties bin/ and the stdlib for the duration of every
# run — so every repo pinning channel = "trust" fails randomly with E0463 /
# "rustc is not installed". Sealed artifacts + one atomic symlink flip remove
# that whole failure class.
#
#   scripts/promote-toolchain.sh                 # promote <repo>/build/host/stage2 at its own rev
#   scripts/promote-toolchain.sh <stage2-dir>    # promote some other stage2
#
# Environment:
#   TRUST_TOOLCHAIN_HOME   where sealed artifacts live (default: ~/toolchains)
#   RUSTUP_HOME            rustup home whose toolchains/trust link is flipped
#                          (default: ~/.rustup)
#
# Refuses to promote a stage2 that is mid-build or incomplete. Never mutates an
# existing artifact directory — artifacts are immutable once published
# (rewriting one would rewrite shipped provenance).
#
# ALSO SEALS THE MATCHING rustc-private SYSROOT. A sealed stage2 deliberately
# omits the rustc-dev component, so repos that link `rustc_private` and drive
# the compiler's MIR out-of-tree — trust-wp is the one today — cannot build
# against it directly. They go through trust-wp's
# `scripts/trustc-private-wrapper.sh` (first-party/trust-wp in this tree),
# which overlays a PREPARED private sysroot on the compiler's std sysroot and
# looks for it at `$(dirname <compiler sysroot>)/rustc-private-sysroots`. In
# the build tree bootstrap stages those beside stage2; in the sealed root they
# must therefore sit beside `trust-<rev>`. Sealing the pair together —
# fail-closed, using the WRAPPER'S OWN selection rule — is what makes
# "promoted" mean "every repo on this channel can build".
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"

usage() {
	cat <<EOF
Usage: scripts/promote-toolchain.sh [stage2-dir]
       scripts/promote-toolchain.sh --gate-only   [toolchain-dir]
       scripts/promote-toolchain.sh --provenance  [toolchain-dir]

Seal a fully-built stage2 (default: $REPO/build/host/stage2)
into an immutable artifact under \$TRUST_TOOLCHAIN_HOME (default ~/toolchains),
seal its byte-matched rustc-private sysroot beside it, verify the pair, then
atomically flip \${RUSTUP_HOME:-~/.rustup}/toolchains/trust onto the artifact.

Every promotion first establishes PROVENANCE (step 1c) and then runs the UI gate
(step 1d): a named, fast subset of this tree's own \`tests/ui/trust\` files, run
through the CANDIDATE compiler. A toolchain that fails either is never sealed,
and every seal carries a \`PROVENANCE\` file recording which evidence class it
earned -- including UNVERIFIED-PROVENANCE, which is recorded, never hidden.

Options:
  -h, --help     show this help and exit
  --gate-only    run ONLY the pre-promotion UI gate against the named toolchain
                 and exit with its verdict. Mutates nothing, seals nothing and
                 flips nothing, so it is also how you check an ALREADY-SEALED
                 artifact (including the one the channel currently serves).
  --provenance   print the named toolchain's PROVENANCE record and exit. Read
                 only. With no argument, reports what the DEFAULT stage2 would
                 be sealed as, without sealing it -- i.e. a dry run of step 1c.
  --allow-dirty-provenance
                 permit sealing a stage2 whose build record says the tree was
                 DIRTY (or changed mid-build). Refused by default. The waiver
                 and its reason are written into the seal's PROVENANCE.
  --require-provenance
                 turn UNVERIFIED-PROVENANCE into a refusal. Use once every build
                 tree in play has been rebuilt under an x.py that stamps.

Environment:
  TRUST_TOOLCHAIN_HOME   sealed-artifact root (default: ~/toolchains)
  RUSTUP_HOME            rustup home to flip (default: ~/.rustup)
  TRUST_BUILD_PROVENANCE_DIR
                         where to look for the build stamp (default: the build
                         tree containing <stage2-dir>, then \$REPO/build)
  TRUST_REQUIRE_BUILD_PROVENANCE=1   same as --require-provenance
  TRUST_PROVENANCE_WAIVER_REASON     reason recorded with --allow-dirty-provenance
EOF
}

GATE_ONLY=0
PROVENANCE_ONLY=0
ALLOW_DIRTY=0
REQUIRE_PROV="${TRUST_REQUIRE_BUILD_PROVENANCE:-0}"
while [[ $# -gt 0 ]]; do
	case "$1" in
		-h|--help) usage; exit 0 ;;
		--gate-only) GATE_ONLY=1; shift ;;
		--provenance) PROVENANCE_ONLY=1; shift ;;
		--allow-dirty-provenance) ALLOW_DIRTY=1; shift ;;
		--require-provenance) REQUIRE_PROV=1; shift ;;
		-*) printf 'promote: unknown option %s (options are refused, never ignored)\n' "$1" >&2; usage >&2; exit 3 ;;
		*) break ;;
	esac
done

SRC="${1:-$REPO/build/host/stage2}"
ROOT="${TRUST_TOOLCHAIN_HOME:-$HOME/toolchains}"
RUSTUP_LINK="${RUSTUP_HOME:-$HOME/.rustup}/toolchains/trust"

die() { printf '\npromote: %s\n' "$*" >&2; exit 1; }
say() { printf '==> %s\n' "$*"; }

# ---------------------------------------------------------------------------
# THE PRE-PROMOTION UI GATE (step 1b below; runnable alone via --gate-only).
#
# WHY IT EXISTS, as one measured sentence. The seal this gate was written after
# — `trust-1979a7b8` — was the live `trust` channel for 322 commits while
# `tests/ui/trust/r1/flip_caller_covered.rs`, a `//@ build-pass` test checked
# into THIS repo, FAILED on it: `e89b89bb29` (the bundled-member Assert gate
# exempting local members) was on main and not in the artifact. Every repo
# pinning `channel = "trust"` inherited that regression and nothing said so,
# because sealing verified only that the artifact RUNS — hello world compiles,
# `-Ztrust-verify` is a known flag — and never that it still returns the RIGHT
# VERDICTS. "Promoted" has to mean the toolchain still passes the compiler's
# own tests, or the word is doing no work.
#
# EXIT STATUS IS NOT ENOUGH, and this regression is the proof. On that stale
# seal `tool_attr_unknown_refused.rs` "passed" a pure exit-code check: it did
# refuse the file — with a generic `E0433: cannot find module or crate trust`,
# because the `trust` tool was not predefined at all, rather than with the
# targeted refusal the test is checked in to assert. A gate that only reads
# exit codes therefore certifies a compiler that is wrong in exactly the way
# the test was written to catch. Each row below carries a REQUIRED MARKER as
# well as an expected status, and the marker is chosen to witness the
# behaviour rather than merely its sign.
#
# The pass/fail expectation and the compile-flags are read from each test's own
# `//@` headers rather than restated here, so a row cannot drift from what the
# suite asserts.
#
# WHY NOT compiletest: the full UI suite needs a built test harness and minutes
# of wall clock. A gate that costs minutes is a gate that gets skipped, and a
# gate people skip is not a gate. This runs a handful of small files directly
# through the candidate's own `trustc` and costs seconds. It is deliberately
# NOT exhaustive — it is the regression FLOOR, not the suite.
#
# FAIL-CLOSED, WITH NO OFF SWITCH. A missing test file, a header it cannot
# read, or a `trustc` that will not run is a REFUSAL, never a skip.

# A marker is matched against the compiler's own DIAGNOSTIC lines only, never
# against the source rustc echoes back inside a diagnostic. That distinction is
# not pedantic — it was measured. Every one of these UI tests annotates its own
# expectations inline (`//~ ERROR is not a Trust attribute`), and rustc prints
# those annotated source lines as part of the rendered error. A marker matched
# over the raw output therefore matches the TEST'S OWN TEXT and reports `ok`
# for a compiler that never emitted the diagnostic at all: on the stale seal
# `tool_attr_unknown_refused.rs` passed that way while the compiler was really
# emitting `E0433`. A checker that can lie is worse than no checker.
#
# The filter drops rustc's snippet furniture: the `NN | source` gutter (whose
# line number starts at COLUMN 0, so "keep only unindented lines" does not work
# and was tried), the bare `|` continuation, the ` --> file:line:col` locator
# and the ` = note:` footers. Diagnostic headers — `error:`, `warning:`,
# `note:`, and Trust's own column-0 `Trust: ASSUMPTION ...` rows — survive it.
diagnostic_lines() {
	grep -vE '^[[:space:]]*([0-9]+[[:space:]]*)?\|' "$1" | grep -vE '^[[:space:]]*(-->|=[[:space:]])'
}

# Rows are `<test path>|<expected status: pass|fail>|<required marker>`.
# The status column is asserted against the file's own `//@` directives too,
# so a row that disagrees with its test is itself a refusal.
UI_GATE_ROWS=(
	# THE NAMED CASE. This is the exact test that silently regressed. Its
	# marker is `1 proved` and not merely "exit 0": the test's own header
	# warns it "must never pass by minting a reusable KernelCertified verdict
	# from caller metadata alone", so passing while proving NOTHING would be
	# the wrong kind of green.
	"tests/ui/trust/r1/flip_caller_covered.rs|pass|1 proved, 0 failed"

	# 9a243492fa — an unconsumed name in the reserved `trust::` namespace is a
	# TARGETED hard error. Marker guards the wrong-reason hole described above.
	"tests/ui/trust/tool_attr_unknown_refused.rs|fail|is not a Trust attribute"

	# 9a243492fa, the other half — a CLAIMED name must resolve and be consumed.
	# The marker witnesses consumption (a consumer reporting the assumption),
	# not just that resolution stopped erroring.
	"tests/ui/trust/tool_attr_vocabulary_accepted.rs|pass|carries #[trust::assume_total]"

	# d9d9d675e3 — an over-budget event in ADVISORY is a warning plus a counted
	# Unknown, and the build survives.
	"tests/ui/trust/verifier_budget_advisory_verdict.rs|pass|warning: Trust verification exceeded its per-function budget"

	# d9d9d675e3's other side, and the reason both rows are here: the SAME
	# event under STRICT stays a located hard error. One row alone cannot tell
	# "advisory was downgraded" from "the check stopped firing".
	"tests/ui/trust/verifier_budget_termination.rs|fail|error: Trust verification exceeded its per-function budget"

	# The ICE a CLEAN crate hit under the compiler's own default lane: the R177
	# gate read `tcx.def_path_str`, which runs the diagnostics-only
	# `trimmed_def_paths` query, and rustc asserts anything asking for it goes on
	# to emit a diagnostic. A crate with nothing wrong in it had none to give, so
	# `pub fn add(a: u8, b: u8) -> u8 { a.wrapping_add(b) }` exited 101 — passing
	# only under `-Ztrust-verify=off`, the one flag verification exists to make
	# unnecessary. No toolchain should ever be sealed with that again.
	#
	# NEGATED marker, and it has to be: the test asserts the compiler stays
	# SILENT, so there is no output to require. Any diagnostic at all satisfies
	# `must_produce_diag` and hides the ICE — two earlier drafts of this test
	# passed on the broken compiler for exactly that reason. Both halves are
	# checked: a returning ICE trips the pass/exit check, and the signature is
	# forbidden from the diagnostics besides.
	"tests/ui/trust/ice_trimmed_def_paths_clean_crate.rs|pass|!trimmed_def_paths"
)

ui_gate() {
	local tc="$1"
	local work failures=0 row rel expect marker file flags edition emit rc out combined
	work="$(mktemp -d)" || die "UI gate: could not create a scratch directory"

	say "UI gate: ${#UI_GATE_ROWS[@]} named tests through $tc/bin/trustc"
	for row in "${UI_GATE_ROWS[@]}"; do
		rel="${row%%|*}"
		expect="${row#*|}"; expect="${expect%%|*}"
		marker="${row##*|}"
		file="$REPO/$rel"

		[[ -r "$file" ]] || die "UI gate: $rel is missing or unreadable in $REPO.
    The gate names its tests explicitly and cannot silently skip one: a row
    that cannot run is a REFUSAL. Restore the test, or remove the row
    deliberately and say why in the commit that removes it."

		# Expectation is the TEST'S, cross-checked against the row so the two
		# can never quietly disagree.
		local declared=fail
		if grep -qE '^//@ (build-pass|check-pass|run-pass)$' "$file"; then declared=pass; fi
		[[ "$declared" == "$expect" ]] || die "UI gate: $rel declares '$declared' in its own \`//@\` headers but this gate's row says '$expect' — fix the row, do not paper over it"

		flags="$(sed -n 's|^//@ compile-flags: *||p' "$file" | head -1)"
		edition="--edition=2015"
		if grep -q '^//@ edition' "$file"; then
			edition="--edition=$(sed -n 's|^//@ edition: *||p' "$file" | head -1)"
		fi
		emit=""
		if grep -qE '^//@ check-pass$' "$file"; then emit="--emit=metadata"; fi

		out="$work/$(basename "$rel" .rs)"
		mkdir -p "$out"
		combined="$out/output.txt"
		rc=0
		# Word splitting on $flags/$emit is intended — they are compiler
		# arguments read from the test header.
		# shellcheck disable=SC2086
		"$tc/bin/trustc" --sysroot "$tc" $edition $flags $emit \
			--out-dir "$out" "$file" > "$combined" 2>&1 || rc=$?

		local verdict=ok why=""
		if [[ "$expect" == pass && "$rc" -ne 0 ]]; then
			verdict=FAIL
			why="expected it to compile (//@ $(grep -oE 'build-pass|check-pass|run-pass' "$file" | head -1)), got exit $rc: $(grep -m1 '^error' "$combined" | cut -c1-140)"
		elif [[ "$expect" == fail && "$rc" -eq 0 ]]; then
			verdict=FAIL
			why="expected a refusal (the test declares no pass directive), but it compiled cleanly"
		elif [[ "$marker" == '!'* ]] && diagnostic_lines "$combined" | grep -qF "${marker#!}"; then
			# NEGATED marker. Some regressions have no output to assert on —
			# their whole point is that the compiler stays silent — so the only
			# honest assertion is that a known failure signature is ABSENT.
			verdict=FAIL
			why="status was right but a FORBIDDEN marker appeared in a diagnostic line.
          forbidden marker: ${marker#!}
          got:              $(diagnostic_lines "$combined" | grep -m1 -F "${marker#!}" | cut -c1-140)"
		elif [[ "$marker" != '!'* ]] && ! diagnostic_lines "$combined" | grep -qF "$marker"; then
			verdict=FAIL
			why="status was right but the required marker never appeared in a DIAGNOSTIC line — the compiler reached this outcome for a different reason than the test asserts.
          wanted marker: $marker
          got instead:   $(diagnostic_lines "$combined" | grep -m1 -E '^(error|warning)' | cut -c1-140)"
		fi

		if [[ "$verdict" == FAIL ]]; then
			failures=$((failures + 1))
			printf '    FAIL  %s\n          %s\n' "$rel" "$why"
		else
			printf '    ok    %s (%s)\n' "$rel" "$expect"
		fi
	done

	rm -rf "$work"
	if [[ "$failures" -gt 0 ]]; then
		return 1
	fi
	say "UI gate: ${#UI_GATE_ROWS[@]}/${#UI_GATE_ROWS[@]} passed"
	return 0
}

# ---------------------------------------------------------------------------
# PROVENANCE (step 1c below; runnable alone via --provenance).
#
# WHY IT EXISTS. A seal used to derive its ENTIRE identity from one string:
# `"$SRC/bin/trustc" --version`, i.e. the compiler's own `CFG_VERSION`. That
# value is `git rev-parse HEAD` at build time and nothing else -- bootstrap's
# `GitInfo::new` never asks whether the working tree was CLEAN at that commit.
# So the seal's name, the directory it lives in, and every downstream ancestry
# answer describe the HEAD the build started from, never the tree it compiled.
#
# THE MEASUREMENT, 2026-08-31. A blast-radius assessment concluded that "not one
# of the eight sealed toolchains contains fix `945a8fbff5`", by
# `git merge-base --is-ancestor` against each seal's self-reported revision.
# Read at the binary instead, `trust-3ae9948d/lib/librustc_driver-*.dylib`
# CONTAINS that fix's `span_warn` text verbatim -- `git log -S` puts that
# string's first appearance at `945a8fbff5` and nowhere earlier. It was built
# from a working tree that already carried the patch, hours before the patch was
# committed, while `CFG_VERSION` still named the pre-fix commit.
#
# THE RULE THIS ENCODES. **A seal's embedded rev is its HEAD, not the tree it
# was compiled from.** Ancestry BOUNDS what could be in an artifact; it never
# establishes what is. And it fails in the dangerous direction too: a seal whose
# HEAD contains a fix proves nothing if the tree had that fix stashed, reverted,
# or not yet rebuilt.
#
# WHAT PROMOTE CAN AND CANNOT DO. Promotion runs AFTER the build, so it cannot
# retroactively observe the build tree's state. Three sources of evidence, in
# descending order of what they establish:
#
#   (a) THE BUILD STAMP -- the only one that can settle the question, because
#       only the build is present while the build tree is. `x.py` writes
#       `build/trust-build-provenance` at build start and closes it at build
#       end (HEAD, clean/dirty, a digest of the uncommitted diff, the submodule
#       pins, and whether the tree changed mid-build). Promote REQUIRES it to
#       claim a clean provenance and copies it into the seal verbatim.
#   (b) THE ARTIFACT FINGERPRINT -- sha256 of the driver and the binaries that
#       define this toolchain's behaviour. It establishes IDENTITY, not origin:
#       it cannot say what source produced these bytes, but it lets any future
#       lane ask whether two seals are the same build, which is the question
#       the 2026-08-31 investigation had no way to answer.
#   (c) SEAL-TIME CONSISTENCY -- is the tree clean NOW, and does `git rev-parse
#       HEAD` equal the binary's self-reported rev NOW. **This is NECESSARY,
#       NEVER SUFFICIENT, and saying so is the whole point of this block:** a
#       tree that is clean at seal time is exactly as consistent with a clean
#       build as with a dirty build whose diff was since stashed, committed, or
#       reverted. It is recorded as a cross-check, never as a certificate.
#
# A seal that earns none of (a) is stamped UNVERIFIED-PROVENANCE in its own
# PROVENANCE file. It is not given a clean-looking name and left to be read as
# one -- that silence is what made the original error possible.

PROV_CLASS=""       # BUILD-STAMPED-CLEAN | BUILD-STAMPED-DIRTY | UNVERIFIED-PROVENANCE
PROV_REASON=""
PROV_RECORD=""      # path to the build stamp, if one was found and matched
PROV_SEAL_TREE=""   # clean|dirty|unknown   -- the tree AT SEAL TIME
PROV_SEAL_HEAD=""
PROV_HEAD_MATCHES="" # yes|no|unknown       -- seal-time HEAD vs the binary's rev

prov_get() { sed -n "s/^$2=//p" "$1" 2>/dev/null | head -1; }

# Locate the build stamp for a given stage2. A stage2 lives at
# <build-tree>/<host>/stage2, so its build tree is two levels up.
prov_find_record() {
	local src="$1" cand
	for cand in \
		"${TRUST_BUILD_PROVENANCE_DIR:-}/trust-build-provenance" \
		"$(dirname "$(dirname "$src")")/trust-build-provenance" \
		"$REPO/build/trust-build-provenance"
	do
		[[ "$cand" == "/trust-build-provenance" ]] && continue
		[[ -r "$cand" ]] && { printf '%s\n' "$cand"; return 0; }
	done
	return 1
}

# sha256 of one file, or `-` when absent. Portable across shasum/sha256sum.
prov_sha256() {
	[[ -r "$1" ]] || { printf '%s\n' "-"; return 0; }
	if command -v shasum >/dev/null 2>&1; then
		shasum -a 256 "$1" | awk '{print $1}'
	elif command -v sha256sum >/dev/null 2>&1; then
		sha256sum "$1" | awk '{print $1}'
	else
		printf '%s\n' "unavailable"
	fi
}

# (b) IDENTITY of the artifact itself. The driver is where the compiler's
# behaviour lives; the three proof backends decide what a verdict means. Hashing
# all of them costs ~1s (the 428 MB driver dominates at 0.8s, measured).
prov_artifact_fingerprint() {
	local dir="$1" f base
	for f in "$dir"/lib/librustc_driver-*.dylib "$dir"/lib/librustc_driver-*.so; do
		[[ -e "$f" ]] || continue
		printf 'artifact_driver_name=%s\n' "$(basename "$f")"
		printf 'artifact_driver_sha256=%s\n' "$(prov_sha256 "$f")"
		printf 'artifact_driver_bytes=%s\n' "$(wc -c < "$f" | tr -d ' ')"
	done
	for base in trustc ay clean ty targo; do
		[[ -e "$dir/bin/$base" ]] || continue
		printf 'artifact_bin_%s_sha256=%s\n' "$base" "$(prov_sha256 "$dir/bin/$base")"
	done
}

# (c) What promote CAN check at seal time, plus (a) if a build stamp is there.
prov_classify() {
	local src="$1" rec head_rec state changed
	PROV_SEAL_HEAD="$(git -C "$REPO" rev-parse HEAD 2>/dev/null || echo unknown)"
	if git -C "$REPO" rev-parse HEAD >/dev/null 2>&1; then
		if [[ -z "$(git -C "$REPO" status --porcelain -uall 2>/dev/null)" ]]; then
			PROV_SEAL_TREE=clean
		else
			PROV_SEAL_TREE=dirty
		fi
	else
		PROV_SEAL_TREE=unknown
	fi
	if [[ "$PROV_SEAL_HEAD" == "$COMMIT" ]]; then PROV_HEAD_MATCHES=yes
	elif [[ "$PROV_SEAL_HEAD" == unknown ]]; then PROV_HEAD_MATCHES=unknown
	else PROV_HEAD_MATCHES=no; fi

	if ! rec="$(prov_find_record "$src")"; then
		PROV_CLASS=UNVERIFIED-PROVENANCE
		PROV_REASON="no build stamp found -- this stage2 was built by an x.py that does not record one, or its build/ was cleaned"
		return 0
	fi
	head_rec="$(prov_get "$rec" head)"
	if [[ "$head_rec" != "$COMMIT" ]]; then
		PROV_CLASS=UNVERIFIED-PROVENANCE
		PROV_REASON="the build stamp at $rec describes a build from ${head_rec:-<unreadable>}, but this stage2 reports $COMMIT -- the record does not describe this artifact"
		return 0
	fi
	PROV_RECORD="$rec"
	state="$(prov_get "$rec" tree_state)"
	changed="$(prov_get "$rec" tree_changed_during_build)"
	if [[ "$state" == clean && "$changed" != "YES" ]]; then
		PROV_CLASS=BUILD-STAMPED-CLEAN
		PROV_REASON="the build tree was clean at $COMMIT when the build started, and unchanged when it finished"
	else
		PROV_CLASS=BUILD-STAMPED-DIRTY
		if [[ "$changed" == "YES" ]]; then
			PROV_REASON="the build tree CHANGED while the build was running (start/end fingerprints differ), so no single commit describes what was compiled"
		else
			PROV_REASON="the build tree was DIRTY at $COMMIT: $(prov_get "$rec" dirty_tracked) tracked + $(prov_get "$rec" dirty_untracked) untracked change(s), diff sha256 $(prov_get "$rec" diff_sha256)"
		fi
	fi
}

prov_report() {
	say "provenance: $PROV_CLASS"
	printf '    %s\n' "$PROV_REASON"
	printf '    seal-time cross-check: tree=%s HEAD=%s head-matches-binary=%s\n' \
		"$PROV_SEAL_TREE" "${PROV_SEAL_HEAD:0:9}" "$PROV_HEAD_MATCHES"
	if [[ "$PROV_CLASS" == UNVERIFIED-PROVENANCE ]]; then
		printf '    NOTE: seal-time checks are NECESSARY, NEVER SUFFICIENT. A clean tree\n'
		printf '          now is equally consistent with a clean build and with a dirty\n'
		printf '          build whose diff was since stashed, committed or reverted.\n'
	fi
}

[[ -d "$SRC/bin" ]] || die "no such stage2: $SRC"

# `--gate-only` mutates nothing, so it deliberately runs before (and without)
# the mid-build guard below: it is the read-only way to ask whether an
# already-sealed artifact — including the one the channel serves right now —
# still passes this tree's tests.
if [[ "$GATE_ONLY" -eq 1 ]]; then
	[[ -x "$SRC/bin/trustc" ]] || die "no trustc in $SRC/bin — nothing to gate"
	if ui_gate "$SRC"; then
		say "gate-only: PASS — $SRC would clear the pre-promotion UI gate"
		exit 0
	fi
	die "gate-only: REFUSED — $SRC fails this tree's named UI tests (see rows above)"
fi

# `--provenance` is read-only too. On an ALREADY-SEALED artifact it prints the
# PROVENANCE the seal carries; on a build tree's stage2 it prints the class that
# stage2 WOULD be sealed as. Both without sealing, flipping or mutating anything.
if [[ "$PROVENANCE_ONLY" -eq 1 ]]; then
	if [[ -r "$SRC/PROVENANCE" ]]; then
		cat "$SRC/PROVENANCE"
		exit 0
	fi
	[[ -x "$SRC/bin/trustc" ]] || die "no trustc in $SRC/bin and no PROVENANCE file — nothing to report"
	COMMIT="$("$SRC/bin/trustc" -vV 2>/dev/null | sed -n 's/^commit-hash: //p' | head -1)"
	[[ -n "$COMMIT" ]] || die "this trustc reports no commit-hash at all"
	say "no PROVENANCE file in $SRC — reporting what it would be sealed as"
	prov_classify "$SRC"
	prov_report
	printf '\n'
	prov_artifact_fingerprint "$SRC"
	exit 0
fi

# 1. Refuse to snapshot a half-swapped tree. An x.py run in flight leaves bin/
#    and the stdlib empty or partial; snapshotting that ships a toolchain that
#    cannot compile (or cannot verify).
if pgrep -f '[x]\.py|[b]ootstrap build' >/dev/null 2>&1; then
	die "an x.py/bootstrap build is running — wait for it to finish (a mid-build stage2 is incomplete by definition)"
fi
#    `rustdoc` is in this list and it is not cosmetic. rustup dispatches
#    doctests by exec'ing `bin/rustdoc` BY THAT NAME; the Trust artifact's own
#    copy is `trustdoc`, and the two are byte-identical in every build
#    measured. An artifact shipped without `rustdoc` breaks `cargo test` in
#    ANY repo pinning channel = "trust" that has a single doctest — the same
#    class of gap as the rustc-private sysroot above, and the same rule
#    applies: "promoted" has to mean every repo on this channel can BUILD AND
#    TEST, not just compile.
for tool in trustc rustc cargo targo targo-trust trustfmt trustdoc rustdoc ay clean ty; do
	[[ -x "$SRC/bin/$tool" ]] || die "stage2 is incomplete: bin/$tool missing (all three proof backends — ay, clean, ty — must be present or the toolchain cannot verify)"
done
STD_COUNT="$(find "$SRC/lib/rustlib" -name 'libstd-*.rlib' 2>/dev/null | wc -l | tr -d ' ')"
[[ "$STD_COUNT" -gt 0 ]] || die "stage2 has no stdlib rlibs — the uplift did not finish"

# 1b. IDENTITY, read before anything is spent on this candidate. This block used
#     to sit AFTER the UI gate; it moved up because the gate runs THIS TREE's
#     tests against the candidate, and a candidate whose rev is not this tree's
#     is being graded with the wrong tests. Establish who the artifact claims to
#     be first, then decide whether that claim is worth anything (1c), then test
#     it (1d).
REV="$("$SRC/bin/trustc" --version 2>/dev/null | sed -n 's/.*(\([0-9a-f]\{9\}\) .*/\1/p')"
[[ -n "$REV" ]] || die "could not read the rev out of trustc --version"
SHORT="${REV:0:8}"
DEST="$ROOT/trust-$SHORT"

[[ -e "$DEST" ]] && die "artifact $DEST already exists — artifacts are IMMUTABLE (a published one is shipped provenance). Remove it deliberately if it was never published."

COMMIT="$("$SRC/bin/trustc" -vV 2>/dev/null | sed -n 's/^commit-hash: //p' | head -1)"
[[ -n "$COMMIT" ]] || die "stage2's trustc does not report a commit-hash, so no private sysroot can be matched to it"

#     A rev this repository has never heard of makes the seal's whole name
#     meaningless — `trust-<rev>` would point at nothing, and every ancestry
#     question asked of it later would error rather than answer. Unambiguous, so
#     it is a hard refusal with no waiver.
git -C "$REPO" cat-file -e "${COMMIT}^{commit}" 2>/dev/null || die "this stage2 reports commit-hash $COMMIT, which is NOT a commit in $REPO.

    The seal would be named after a revision this repository cannot resolve, so
    nothing could ever check what is in it. Either this stage2 came from a
    different repository, or the commit was never pushed and has since been
    garbage-collected. Fetch the commit, or rebuild here."

# 1c. PROVENANCE. See the long block above for why the rev alone is not an
#     answer. This decides which evidence class the seal earns, and it is
#     recorded either way — an unverifiable seal is stamped as such, never given
#     a clean-looking name and left to be read as one.
prov_classify "$SRC"
prov_report

if [[ "$PROV_CLASS" == BUILD-STAMPED-DIRTY && "$ALLOW_DIRTY" -ne 1 ]]; then
	die "REFUSED: this stage2's own build record says it was NOT built from a clean tree.

    $PROV_REASON

    The artifact will nevertheless stamp itself \`$REV\`, so its name — and every
    \`git merge-base --is-ancestor\` answer derived from that name — would
    describe a tree that is not the one compiled. That is exactly the hole that
    made \`trust-3ae9948d\` report \"fix absent\" while its binary carried the fix.

    Options:
      * Commit or stash the changes and rebuild, so the rev names the tree:
            cd $REPO && python3 x.py build --stage 2 -j 8
      * Promote it anyway, deliberately and on the record:
            TRUST_PROVENANCE_WAIVER_REASON='<why>' \\
              scripts/promote-toolchain.sh --allow-dirty-provenance
        The waiver and its reason are written into the seal's PROVENANCE, and
        the seal is marked BUILD-STAMPED-DIRTY forever.
      * Inspect the record first, without sealing anything:
            scripts/promote-toolchain.sh --provenance"
fi

if [[ "$PROV_CLASS" == UNVERIFIED-PROVENANCE && "$REQUIRE_PROV" == 1 ]]; then
	die "REFUSED (--require-provenance): no usable build stamp for this stage2.

    $PROV_REASON

    Rebuild through x.py so the build records what it compiled:
        cd $REPO && python3 x.py build --stage 2 -j 8"
fi

# 1d. Does it still compute the right verdicts? Steps 1 and 6 only ever asked
#     whether the artifact RUNS. This asks whether it is still CORRECT, and it
#     runs here — before the first `cp` — so a failing candidate is refused
#     without an artifact directory ever existing for it. See the block above
#     for why exit codes alone were not enough.
ui_gate "$SRC" || die "stage2 at $SRC FAILS this tree's named UI tests (listed above) — refusing to seal it.

    A promoted toolchain that fails the compiler's own checked-in tests is
    exactly how the stale seal shipped for 322 commits without anyone
    noticing. Fix the compiler, or rebuild:
        cd $REPO && python3 x.py build --stage 2 -j 8
    To inspect any toolchain without promoting anything:
        scripts/promote-toolchain.sh --gate-only <toolchain-dir>"

# 2. Resolve the matching rustc-private sysroot BEFORE mutating anything, so a
#    toolchain whose private half is missing is never half-promoted.
#
#    The selection rule is the wrapper's, reproduced exactly — deliberately, so
#    the two can never disagree about what "matching" means:
#      * `.rustc-commit-hash` equals the compiler's own `commit-hash`. The crate
#        hash alone is NOT an identity: a librustc_driver filename can survive
#        source commits whose metadata versions are mutually incompatible, and
#        mixing them is E0514 at the consumer.
#      * the staged `librustc_driver` is BYTE-IDENTICAL to the one this compiler
#        ships. Bootstrap keys its staging directories by content, so several
#        roots can carry the same commit AND the same driver filename while
#        holding payloads from different builds; only the identical one is safe.
#    Measured: the newest same-commit root can be minutes stale and fail
#    exactly this cmp, which is why the rule is here and not "newest wins".
PRIV_NAME="rustc-private-sysroots"
PRIV_SRC_ROOT="$(dirname "$SRC")/$PRIV_NAME"
PRIV_DEST_ROOT="$ROOT/$PRIV_NAME"

DRIVER=""
for candidate in "$SRC"/lib/librustc_driver-*.dylib "$SRC"/lib/librustc_driver-*.so; do
	[[ -e "$candidate" ]] || continue
	[[ -n "$DRIVER" ]] && die "stage2 ships multiple librustc_driver dynamic libraries under lib/ — cannot tell which one defines the private ABI"
	DRIVER="$candidate"
done
[[ -n "$DRIVER" ]] || die "stage2 ships no librustc_driver dynamic library under lib/ — an rustc_private consumer could never link against it"

DRIVER_FILE="$(basename "$DRIVER")"
#    `COMMIT` was read and validated in step 1b — it is needed before the
#    provenance decision, so it is no longer read here.
TARGET_LIBDIR="$("$SRC/bin/trustc" --print target-libdir 2>/dev/null)"
TRIPLE="$(basename "$(dirname "$TARGET_LIBDIR")")"
[[ -n "$TRIPLE" ]] || die "could not read the host triple out of trustc --print target-libdir"

[[ -d "$PRIV_SRC_ROOT" ]] || die "no $PRIV_NAME beside $SRC — bootstrap has never staged the private crates for this build tree; build an in-tree rustc-private tool (or trust-wp) against this stage2 first"

PRIV_SRC=""
for candidate_root in "$PRIV_SRC_ROOT"/*; do
	[[ -d "$candidate_root" ]] || continue
	[[ -r "$candidate_root/.rustc-commit-hash" ]] || continue
	[[ "$(tr -d '\r\n' < "$candidate_root/.rustc-commit-hash")" == "$COMMIT" ]] || continue
	candidate="$candidate_root/$TRIPLE/$DRIVER_FILE"
	[[ -e "$candidate" ]] || continue
	cmp -s "$candidate" "$DRIVER" || continue
	[[ -n "$PRIV_SRC" ]] && die "multiple byte-identical private sysroots match commit $COMMIT and $DRIVER_FILE under $PRIV_SRC_ROOT — the wrapper refuses this too; remove the duplicates"
	PRIV_SRC="$candidate_root"
done
[[ -n "$PRIV_SRC" ]] || die "no private sysroot under $PRIV_SRC_ROOT matches commit $COMMIT with a byte-identical $DRIVER_FILE.
    Promoting anyway would ship a channel that trust-wp cannot build against —
    which is the exact failure this check exists to prevent. Bootstrap stages a
    matching root as a side effect of building an rustc-private tool against
    THIS stage2, so rebuild one and promote again:
        cd $REPO && python3 x.py build --stage 2 -j 8"
say "private sysroot: $(basename "$PRIV_SRC")"

# 3. Copy (APFS clone where possible — near-free and atomic per-file).
say "sealing $SRC -> $DEST (rev $REV)"
mkdir -p "$ROOT"
cp -ac "$SRC" "$DEST" 2>/dev/null || cp -a "$SRC" "$DEST"

# 3b. A sealed artifact may not point outside itself. `cp -a` preserves symlinks
#     verbatim, so stage2's `lib/rustlib/rustc-src/rust` — which x.py aims at
#     whatever source tree built it — was copied into every seal and then went
#     stale. Measured on the live roots before this fix:
#
#       trust-6500fd4d -> <temporary-worktree>/seal-wt (path normalized)  DANGLING
#       trust-1979a7b8 -> /private/tmp/tcg-p2                             DANGLING
#       trust-ca497bef -> /private/tmp/ice-land                           DANGLING
#       trust-3ae9948d -> <source-checkout> (path normalized)            the MUTABLE dev tree
#
#     Both outcomes defeat sealing. A dangling rustc-src breaks every
#     source-resolving tool; a LIVE one re-attaches the "immutable" artifact to
#     the build tree the seal exists to escape — and trust-6500fd4d is the root
#     the whole constellation resolves through `channel = "trust"`.
#     trust-ir's check_trust_default_authority.py is the one thing that checks
#     this ("sealed sysroot contains a symlinked artifact"), and nothing runs it.
#
#     Drop escaping links rather than materialise them: rustc-src is IDE source
#     navigation, not part of the compiler's own closure, and copying a whole
#     source tree into every seal to satisfy a nicety is the wrong trade.
# Resolve parent traversal and every intermediate link before comparing roots.
# A lexical "$DEST/" prefix also admits "$DEST/../outside" and links reached
# through another escaping directory link. Inspect all links before removing
# any, so deleting an intermediate link cannot hide an escape in a later row.
python3 "$REPO/scripts/prune_seal_symlinks.py" "$DEST" || \
	die "could not verify symlink confinement in the copied toolchain: $DEST"

# 4. Seal the private sysroot beside the toolchain, under its bootstrap name —
#    that name is a content key, so an identical root re-promoted is the same
#    directory and this is idempotent. A DIFFERING one under the same name would
#    be a bootstrap key collision, which is a bug, not something to overwrite.
PRIV_DEST="$PRIV_DEST_ROOT/$(basename "$PRIV_SRC")"
mkdir -p "$PRIV_DEST_ROOT"
if [[ -e "$PRIV_DEST" ]]; then
	cmp -s "$PRIV_DEST/$TRIPLE/$DRIVER_FILE" "$DRIVER" \
		|| die "$PRIV_DEST already exists and its driver differs from this stage2's — refusing to rewrite a sealed private sysroot"
	say "private sysroot already sealed: $PRIV_DEST"
else
	say "sealing $PRIV_SRC -> $PRIV_DEST"
	cp -ac "$PRIV_SRC" "$PRIV_DEST" 2>/dev/null || cp -a "$PRIV_SRC" "$PRIV_DEST"
fi

# 5. cargo-subcommand compat names. rustup dispatches `cargo +trust fmt` by
#    exec'ing `cargo-fmt` from the toolchain bin; the Trust artifact ships only
#    targo-* names, so without these every rustup-shimmed fmt/clippy gate
#    breaks and falls back to stock. HARD links, not symlinks: tippy refuses a
#    symlinked frontend outright ("frontends cannot be symlinks or reparse
#    points"), and a hard link is a plain regular file to that check.
say "adding cargo-subcommand compat names (hard links)"
ln -f "$DEST/bin/targo-fmt"   "$DEST/bin/cargo-fmt"
ln -f "$DEST/bin/targo-tippy" "$DEST/bin/cargo-clippy"

# 5b. `rustdoc` must exist under that exact name or doctests cannot run at all
#     (see the tool list in step 1). The wholesale `cp -a` above carries it when
#     the stage2 has it, and step 1 refuses a stage2 that does not — so this is
#     a belt-and-braces reconstruction for an artifact copied before that check
#     existed. `trustdoc` is byte-identical in every build measured, so a hard
#     link to it is exactly the right bytes rather than an approximation.
if [[ ! -e "$DEST/bin/rustdoc" ]]; then
	say "restoring bin/rustdoc (hard link to the byte-identical trustdoc)"
	ln -f "$DEST/bin/trustdoc" "$DEST/bin/rustdoc"
fi

# 6. Verify the artifact before anything points at it.
say "verifying"
"$DEST/bin/trustc" --version >/dev/null || die "sealed trustc will not run"
HELLO="$(mktemp -d)"; trap 'rm -rf "$HELLO"' EXIT
printf 'fn main(){println!("ok")}\n' > "$HELLO/h.rs"
"$DEST/bin/trustc" --sysroot "$DEST" -Ztrust-verify=off -o "$HELLO/h" "$HELLO/h.rs" >/dev/null 2>&1 \
	|| die "sealed toolchain cannot compile a hello world"
[[ "$("$HELLO/h")" == "ok" ]] || die "hello world did not run"
"$DEST/bin/rustc" -Z help 2>/dev/null | grep -q 'trust-verify' \
	|| die "sealed toolchain has no -Ztrust-verify flag — it cannot verify, so it is not a Trust toolchain"

#    Replay the wrapper's lookup against the SEALED pair, from the sealed
#    compiler's own sysroot. Matching in the build tree (step 2) is not the same
#    question as resolving in the sealed root: an older sealed sysroot could also
#    match and make the choice ambiguous, which the wrapper refuses outright.
#    This is the check that actually earns the word "promoted".
SEALED_DRIVER="$DEST/lib/$DRIVER_FILE"
[[ -e "$SEALED_DRIVER" ]] || die "sealed toolchain lost $DRIVER_FILE in the copy"
RESOLVED=""
for candidate_root in "$PRIV_DEST_ROOT"/*; do
	[[ -d "$candidate_root" ]] || continue
	[[ -r "$candidate_root/.rustc-commit-hash" ]] || continue
	[[ "$(tr -d '\r\n' < "$candidate_root/.rustc-commit-hash")" == "$COMMIT" ]] || continue
	candidate="$candidate_root/$TRIPLE/$DRIVER_FILE"
	[[ -e "$candidate" ]] || continue
	cmp -s "$candidate" "$SEALED_DRIVER" || continue
	[[ -n "$RESOLVED" ]] && die "two sealed private sysroots resolve for commit $COMMIT — the wrapper would refuse this as ambiguous; remove the stale one under $PRIV_DEST_ROOT"
	RESOLVED="$candidate_root"
done
[[ -n "$RESOLVED" ]] || die "the sealed private sysroot does not resolve against the sealed toolchain — an rustc_private consumer would still fail"
say "rustc-private overlay resolves: $(basename "$RESOLVED")"

# 6b. WRITE THE PROVENANCE INTO THE SEAL, before anything points at it. This is
#     the durable half: the classification above is a decision made once, at a
#     moment nobody will be able to reconstruct, and a seal that does not carry
#     it is a seal whose only self-description is a name that may be a lie.
#
#     It is written for a reader who has ONLY this directory — hence the prose.
#     Every seal gets one, including UNVERIFIED-PROVENANCE ones.
say "recording provenance"
{
	printf '# PROVENANCE — what this sealed toolchain actually is\n#\n'
	printf '# A seal is named `trust-<rev>` after the compiler binary'"'"'s OWN\n'
	printf '# self-reported revision (CFG_VERSION), which is `git rev-parse HEAD`\n'
	printf '# at build time and NOTHING ELSE. It does not say whether the working\n'
	printf '# tree was clean at that commit. THIS FILE DOES.\n#\n'
	printf '# READ THIS BEFORE ANSWERING "is fix X in this toolchain?".\n'
	printf '# `git merge-base --is-ancestor <fix> %s` BOUNDS what could be in\n' "$COMMIT"
	printf '# here; it never establishes what is. Measured 2026-08-31:\n'
	printf '# `trust-3ae9948d` reported a rev that is NOT a descendant of fix\n'
	printf '# `945a8fbff5`, while its librustc_driver contained that fix verbatim.\n'
	printf '# See docs/TOOLCHAIN_POSTURE.md 2a for the technique that settles it.\n#\n'
	printf 'provenance_class=%s\n' "$PROV_CLASS"
	printf 'provenance_reason=%s\n' "$PROV_REASON"
	printf 'sealed_at=%s\n' "$(date +%Y-%m-%dT%H:%M:%S%z)"
	printf 'sealed_by=%s\n' "scripts/promote-toolchain.sh"
	printf 'seal_name=%s\n' "trust-$SHORT"
	printf 'reported_rev=%s\n' "$REV"
	printf 'reported_commit=%s\n' "$COMMIT"
	printf 'private_sysroot=%s\n' "$(basename "$RESOLVED")"
	printf '\n# (b) ARTIFACT IDENTITY — establishes SAMENESS, not origin. Two seals\n'
	printf '#     with the same driver sha256 are the same build, whatever they are named.\n'
	prov_artifact_fingerprint "$DEST"
	printf '\n# (c) SEAL-TIME CROSS-CHECK — NECESSARY, NEVER SUFFICIENT. A clean tree\n'
	printf '#     at seal time is equally consistent with a clean build and with a\n'
	printf '#     dirty build whose diff was since stashed, committed or reverted.\n'
	printf 'sealtime_repo_head=%s\n' "$PROV_SEAL_HEAD"
	printf 'sealtime_repo_tree=%s\n' "$PROV_SEAL_TREE"
	printf 'sealtime_head_matches_binary=%s\n' "$PROV_HEAD_MATCHES"
	if [[ "$ALLOW_DIRTY" -eq 1 ]]; then
		printf '\n# WAIVER — a dirty-tree build was promoted deliberately.\n'
		printf 'dirty_provenance_waived=yes\n'
		printf 'dirty_provenance_waiver_reason=%s\n' "${TRUST_PROVENANCE_WAIVER_REASON:-<none given>}"
	fi
	if [[ -n "$PROV_RECORD" ]]; then
		printf '\n# (a) THE BUILD STAMP, copied verbatim from %s.\n' "$PROV_RECORD"
		printf '#     This is the only evidence here that was gathered while the build\n'
		printf '#     tree was still the build tree. Everything above it is inference.\n'
		sed 's/^/build_stamp:/' "$PROV_RECORD"
	else
		printf '\n# (a) THE BUILD STAMP — ABSENT. Nothing observed this artifact'"'"'s build\n'
		printf '#     tree while it was being compiled, so no statement in this file\n'
		printf '#     establishes what source produced these bytes.\n'
		printf 'build_stamp=absent\n'
	fi
} > "$DEST/PROVENANCE"
if [[ -n "$PROV_RECORD" && -r "$PROV_RECORD.status" ]]; then
	cp "$PROV_RECORD.status" "$DEST/PROVENANCE.build-status"
fi

# 7. Flip. `ln -sfn` replaces the symlink via rename(2) — atomic, so no
#    invocation ever observes a missing toolchain.
mkdir -p "$(dirname "$RUSTUP_LINK")"
PREV="$(readlink "$RUSTUP_LINK" 2>/dev/null || echo none)"
ln -sfn "$DEST" "$RUSTUP_LINK"
ln -sfn "$DEST" "$ROOT/trust-current"

say "promoted: rustup channel \`trust\` -> $DEST"
say "previous: $PREV"
say "provenance: $PROV_CLASS (full record: $DEST/PROVENANCE)"
echo
echo "Verify:  rustc +trust --version && cargo +trust fmt --version"
echo "Rollback: ln -sfn $PREV $RUSTUP_LINK"
