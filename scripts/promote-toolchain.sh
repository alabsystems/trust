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
#   TRUST_TOOLCHAIN_SERIAL_COMMAND
#                          REQUIRED by a seal and by --gate-only: a built
#                          `trust-serial-command`, and the run must hold a build
#                          slot (scripts/build-slot). `--help` has the commands.
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
umask 022

# BSD mktemp ignores TMPDIR unless the template names it explicitly. Resolve
# caller-relative scratch once, before any gate changes its working directory.
if [[ -n "${TMPDIR:-}" && "$TMPDIR" != /* ]]; then
    TMPDIR="$(pwd -P)/$TMPDIR"
    export TMPDIR
fi

PROMOTER_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$PROMOTER_ROOT"

usage() {
	cat <<EOF
Usage: scripts/promote-toolchain.sh [stage2-dir]
       scripts/promote-toolchain.sh --gate-only   [toolchain-dir]
       scripts/promote-toolchain.sh --provenance  [toolchain-dir]
       scripts/promote-toolchain.sh --no-flip [--lineage FILE] [stage2-dir]

  --source-root DIR  Read compiler sources, build stamps and existing gates from
                     this checkout; the promoter's own identity remains separate.
  --native-tools RECORD --native-tools-sha256 SHA
                     Add a qualified, source-paired native linker/debug component
                     before the new seal's gates and content fingerprint.
  --frontend-component ABS --frontend-component-sha256 SHA
                     Validate a prepared, source-bound targo-trust component.
                     Replace only the new seal frontend before existing sealed
                     gates; actual installed doctor must qualify it. Provenance
                     mode requires the installed component's exact authority.
  --stage-provenance-receipt ABS --stage-provenance-sha256 SHA
                     Select an accepted external audit of the ORIGINAL stage
                     under --source-root. Carry those exact bytes only into the
                     new seal; preserve the original stage's receipt unchanged.

Seal a fully-built stage2 (default: $REPO/build/host/stage2)
into an immutable artifact under \$TRUST_TOOLCHAIN_HOME (default ~/toolchains),
seal its byte-matched rustc-private sysroot beside it, verify the pair, then
atomically flip \${RUSTUP_HOME:-~/.rustup}/toolchains/trust onto the artifact.

Every promotion first establishes PROVENANCE (step 1c) and then runs the UI gate
(step 1d): a named, fast subset of this tree's own \`tests/ui/trust\` files, run
through the CANDIDATE compiler. A toolchain that fails either is never sealed,
and every seal carries a \`PROVENANCE\` file recording which evidence class it
earned -- including UNVERIFIED-PROVENANCE, which is recorded, never hidden.

It then STARTS every shipped tool that is built on the compiler (the tool-start
gate, step 1f, and again on the sealed copy): tippy through its driver and
through its frontend, trust-miri when shipped, trustdoc and trustfmt, each on a
one-function crate. A \`--version\` that answers is not a start. A toolchain
whose tippy cannot lint is never sealed. The result on the sealed copy is
written into PROVENANCE (\`tool_start_gate=\`, the rows by name).

A stage2 built by scripts/recreate_bootstrap.py carries that build's receipt,
\`tool-provenance.json\` (which stage0 it started from, every tool bound to the
artifact it was copied from). Promotion checks it before anything is copied
(step 1b''): well formed, not rejected by its own writer, and naming THIS
stage2 -- its commit is the compiler's, and every file hash it records is the
file being sealed (executables only: a receipt records no hash under lib/). One
that fails is a refusal. One that passes is named in PROVENANCE
(\`stage_receipt_*\`: sha256, status, lineage mode, trust_from_trust, seed
materialization, the LLVM it carries and the command line, when recorded); a
stage2 without one is sealed as before and says \`stage_receipt=absent\`.

WHICH LLVM a stage2 carries is the receipt's \`llvm_identity\` record. x.py
rebuilds the in-tree LLVM when HEAD:src/llvm-project moves from the tree
recorded beside it, but it keeps an LLVM that cannot say what it was built from
(one built before that record, whose own build header names no commit this
checkout has), and a change to src/bootstrap, src/version, the bootstrap config
or the native tools rebuilds none, so a stage built in a reused build directory
can carry an LLVM built from other sources or with another recipe. By default
the seal records what the receipt says (\`stage_receipt_llvm_identity=stated\`
or \`not-stated\`, or \`stage_receipt_llvm=not-recorded\`) and is cut either
way. \`--require-llvm-identity\` makes anything but \`stated\` a refusal. A
stage2 that links an LLVM through the recreator's \`--llvm-config\`
(\`stage_receipt_llvm=external\`) is never \`stated\`: the build did not
see that LLVM built, and binds the llvm-config executable, not what it points at.
Nor is one whose bootstrap config does not itself say which LLVM x.py links
(\`stage_receipt_llvm=unknown\`). The seal writes the source tree's LLVM ids
beside an in-tree LLVM only.

Options go before the path; a word after it is refused, as an unknown option is.
So is an option the mode does not use: --gate-only takes --source-root and no
other option, and --provenance takes --source-root, --require-llvm-identity and
the paired --frontend-component and --frontend-component-sha256. So are
--lineage given twice and a path that is an empty word.

Options:
  -h, --help     show this help and exit
  --gate-only    run the read-only pre-promotion gates against the named
                 toolchain: UI, tool-start, native rustc-dev link/run and,
                 for a Darwin host, the paired native-tool surface (any
                 other host: reported as not applicable; a Darwin SDK
                 with neither bin/rust-lld nor bin/dsymutil: reported
                 as ABSENT and recorded, not refused). All
                 always run, so a failure never hides another gate; then exit
                 with their verdict. Mutates nothing, seals nothing and flips
                 nothing, so it is also how you check an ALREADY-SEALED
                 artifact (including the one the channel currently serves).
  --provenance   print the named toolchain's PROVENANCE record and exit. Read
                 only. With no argument, reports what the DEFAULT stage2 would
                 be sealed as, without sealing it -- i.e. a dry run of step 1c,
                 with the content identity and the stage-receipt lines it would
                 record (a receipt promotion would refuse is refused here too).
  --allow-dirty-provenance
                 permit sealing a stage2 whose build record says the tree was
                 DIRTY (or changed mid-build). Refused by default. The waiver
                 and its reason are written into the seal's PROVENANCE.
  --require-provenance
                 turn UNVERIFIED-PROVENANCE into a refusal. Use once every build
                 tree in play has been rebuilt under an x.py that stamps.
  --require-llvm-identity
                 refuse a stage2 that does not state which LLVM it carries: one
                 with no stage receipt, one whose receipt holds no LLVM record
                 (written before 2026-10-13), and one whose record says the
                 identity is not stated, which every stage2 built with
                 \`--llvm-config\` does. The flag for a seal; build its stage
                 with \`recreate_bootstrap.py --require-llvm-identity\`.
                 --require-provenance does NOT imply it. With --provenance it
                 is the same question asked without sealing (of a sealed
                 artifact: of the lines its PROVENANCE holds).
  --no-flip      seal, verify and record everything, but leave the rustup
                 \`trust\` link and trust-current where they are. Admission onto
                 the channel is then a separate, deliberate step (it prints the
                 two \`ln -sfn\` commands). Nothing else is skipped.
  --lineage FILE a seed-staircase lineage record (scripts/seed_staircase.py
                 lineage; schema trust-seed-staircase-v1) naming THIS stage2 by
                 the sha256 of its trustc and librustc_driver and its commit.
                 It is checked before anything is copied, sealed into the
                 artifact as STAGE0-LINEAGE, and summarized in PROVENANCE. A
                 record that names a different stage2 is refused.

Environment:
  TRUST_TOOLCHAIN_HOME   sealed-artifact root (default: ~/toolchains)
  RUSTUP_HOME            rustup home to flip (default: ~/.rustup)
  TRUST_BUILD_PROVENANCE_DIR
                         where to look for the build stamp (default: the build
                         tree containing <stage2-dir>, then \$REPO/build)
  TRUST_REQUIRE_BUILD_PROVENANCE=1   same as --require-provenance (0 or unset:
                                     not required; any other value is refused)
  TRUST_PROVENANCE_WAIVER_REASON     reason recorded with --allow-dirty-provenance
  TRUST_TOOLCHAIN_SERIAL_COMMAND
                         REQUIRED by a seal and by --gate-only (--provenance
                         runs no gate and does not read it): the
                         absolute path of a built \`trust-serial-command\`, a
                         regular file, not a symlink. Every gate starts the
                         compiler and the shipped tools through it. Build it
                         with a Trust toolchain:
                           (cd $PROMOTER_ROOT/crates/trust-resource-controller &&
                            CARGO_TARGET_DIR=<dir> targo --unverified build --locked \\
                              --release --features serial-command --bin trust-serial-command)
                         and name <dir>/release/trust-serial-command. It grants no
                         CPU or memory of its own and refuses a caller that holds
                         no build slot, so promotion runs under one:
                           python3 scripts/build-slot --cpus 1 -- bash scripts/promote-toolchain.sh ...
                         Both are asked once, before any gate, by starting a
                         no-op through it; a refusal there names which is missing.
EOF
}

GATE_ONLY=0
PROVENANCE_ONLY=0
ALLOW_DIRTY=0
NO_FLIP=0
REQUIRE_LLVM=0
LINEAGE=""
SOURCE_ROOT=""
NATIVE_TOOLS=""
NATIVE_TOOLS_SHA=""
STAGE_PROVENANCE_RECEIPT=""
STAGE_PROVENANCE_SHA=""
FRONTEND_COMPONENT=""
FRONTEND_COMPONENT_SHA=""
REQUIRE_PROV="${TRUST_REQUIRE_BUILD_PROVENANCE:-0}"
TYPED="" # the options typed, in order: a mode refuses one it does not use (below)
while [[ $# -gt 0 ]]; do
	OPTION="$1"
	case "$1" in
		-h|--help) usage; exit 0 ;;
		--gate-only) GATE_ONLY=1; shift ;;
		--provenance) PROVENANCE_ONLY=1; shift ;;
		--allow-dirty-provenance) ALLOW_DIRTY=1; shift ;;
		--require-provenance) REQUIRE_PROV=1; shift ;;
		--require-llvm-identity) REQUIRE_LLVM=1; shift ;;
		--no-flip) NO_FLIP=1; shift ;;
		--source-root|--native-tools|--native-tools-sha256|--stage-provenance-receipt|--stage-provenance-sha256|--frontend-component|--frontend-component-sha256)
			[[ $# -ge 2 && -n "$2" && "$2" != -* ]] || { printf 'promote: %s needs a value\n' "$1" >&2; exit 3; }
			case "$1" in
				--frontend-component) [[ -z "$FRONTEND_COMPONENT" ]] || { printf 'promote: duplicate --frontend-component\n' >&2; exit 3; }; FRONTEND_COMPONENT="$2" ;;
				--frontend-component-sha256) [[ -z "$FRONTEND_COMPONENT_SHA" ]] || { printf 'promote: duplicate --frontend-component-sha256\n' >&2; exit 3; }; FRONTEND_COMPONENT_SHA="$2" ;;
				--source-root) [[ -z "$SOURCE_ROOT" ]] || { printf 'promote: duplicate --source-root\n' >&2; exit 3; }; SOURCE_ROOT="$2" ;;
				--native-tools) [[ -z "$NATIVE_TOOLS" ]] || { printf 'promote: duplicate --native-tools\n' >&2; exit 3; }; NATIVE_TOOLS="$2" ;;
				--native-tools-sha256) [[ -z "$NATIVE_TOOLS_SHA" ]] || { printf 'promote: duplicate --native-tools-sha256\n' >&2; exit 3; }; NATIVE_TOOLS_SHA="$2" ;;
				--stage-provenance-receipt) [[ -z "$STAGE_PROVENANCE_RECEIPT" ]] || { printf 'promote: duplicate --stage-provenance-receipt\n' >&2; exit 3; }; STAGE_PROVENANCE_RECEIPT="$2" ;;
				--stage-provenance-sha256) [[ -z "$STAGE_PROVENANCE_SHA" ]] || { printf 'promote: duplicate --stage-provenance-sha256\n' >&2; exit 3; }; STAGE_PROVENANCE_SHA="$2" ;;
			esac
			shift 2 ;;
		--lineage)
			[[ $# -ge 2 && -n "$2" ]] || { printf 'promote: --lineage needs a file\n' >&2; exit 3; }
			# An option is not a file: `--lineage --require-llvm-identity <stage2>`
			# would take the flag for the record's name, and --provenance and
			# --gate-only never open that record, so the flag was dropped.
			[[ "$2" != -* ]] || { printf 'promote: --lineage needs a file, not the option %s (options are refused, never ignored)\n' "$2" >&2; usage >&2; exit 3; }
			# One record is checked and sealed. A second --lineage replaced the
			# first, which was then never opened.
			[[ -z "$LINEAGE" ]] || { printf 'promote: --lineage %s after --lineage %s (one record is checked; options are refused, never ignored)\n' "$2" "$LINEAGE" >&2; usage >&2; exit 3; }
			LINEAGE="$2"; shift 2 ;;
		-*) printf 'promote: unknown option %s (options are refused, never ignored)\n' "$1" >&2; usage >&2; exit 3 ;;
		*) break ;;
	esac
	TYPED="$TYPED $OPTION"
done
if [[ -n "$SOURCE_ROOT" ]]; then
	REPO="$(cd "$SOURCE_ROOT" && pwd -P)" || { printf 'promote: --source-root is not an accessible directory\n' >&2; exit 3; }
	[[ -f "$REPO/scripts/lib/stage_receipt_provenance.py" ]] || { printf 'promote: --source-root is not a compiler checkout\n' >&2; exit 3; }
fi
if [[ -n "$NATIVE_TOOLS" || -n "$NATIVE_TOOLS_SHA" ]]; then
	[[ -n "$NATIVE_TOOLS" && "$NATIVE_TOOLS_SHA" =~ ^[0-9a-f]{64}$ ]] || { printf 'promote: native tools require both a record and its exact SHA-256\n' >&2; exit 3; }
fi
if [[ -n "$FRONTEND_COMPONENT" || -n "$FRONTEND_COMPONENT_SHA" ]]; then
	[[ "$FRONTEND_COMPONENT" == /* && "$FRONTEND_COMPONENT_SHA" =~ ^[0-9a-f]{64}$ ]] || { printf 'promote: frontend component requires an absolute record and exact SHA-256\n' >&2; exit 3; }
fi
STAGE_PROVENANCE_ARGS=()
if [[ -n "$STAGE_PROVENANCE_RECEIPT" || -n "$STAGE_PROVENANCE_SHA" ]]; then
	[[ "$STAGE_PROVENANCE_RECEIPT" == /* && "$STAGE_PROVENANCE_SHA" =~ ^[0-9a-f]{64}$ ]] || { printf 'promote: stage provenance requires both an absolute receipt and its exact SHA-256\n' >&2; exit 3; }
	STAGE_PROVENANCE_ARGS=(--stage-provenance-receipt "$STAGE_PROVENANCE_RECEIPT" --stage-provenance-sha256 "$STAGE_PROVENANCE_SHA")
fi
# The path is the last word: every mode takes at most one (the stage2 to seal,
# or the toolchain --gate-only or --provenance is asked about). Until
# 2026-10-13 nothing looked past it, so `--no-flip <stage2>
# --require-llvm-identity` cut a seal WITHOUT the check it names (exit 0), as
# did `--provenance <seal> --require-llvm-identity`, and an unknown option
# there was accepted where before the path it is refused (measured by the third
# reading of the LLVM-identity change). A word after the path is refused here
# as an unknown option is above: same words, same exit.
if [[ $# -gt 1 ]]; then
	printf 'promote: %s after the path %s (options are refused, never ignored; type every option before the path)\n' "$2" "$1" >&2
	usage >&2
	exit 3
fi
# An empty word is not "no path": `promote-toolchain.sh --no-flip "$STAGE"` with
# an empty $STAGE took the checkout's default stage2 for the one to seal (found
# by the review of the follow-up, 2026-10-13).
if [[ $# -eq 1 && -z "$1" ]]; then
	printf 'promote: the path is an empty word (name the toolchain, or give no path for %s; an empty word is refused, never read as no path)\n' "$REPO/build/host/stage2" >&2
	usage >&2
	exit 3
fi
# TRUST_REQUIRE_BUILD_PROVENANCE is the requirement only when it says 1, and
# until 2026-10-14 any other value (`true`, `yes`) turned it off without a word.
case "${TRUST_REQUIRE_BUILD_PROVENANCE:-0}" in
	0|1) ;;
	*)
		printf 'promote: TRUST_REQUIRE_BUILD_PROVENANCE=%s is neither 1 (require) nor 0 (do not require) (a value that is not understood is refused, never read as 0)\n' "$TRUST_REQUIRE_BUILD_PROVENANCE" >&2
		usage >&2
		exit 3
		;;
esac
# A mode refuses an option it does not use. --gate-only starts tools and reads
# no record, so it uses none; --provenance asks one requirement of a record,
# --require-llvm-identity. Until 2026-10-14 the others were dropped without a
# word: `--provenance --require-provenance <stage2>` reported the class
# UNVERIFIED-PROVENANCE and exited 0, `--gate-only --require-llvm-identity`
# passed on the gates alone, and `--provenance --gate-only` ran the gates and
# printed no record (measured on the scripts before this change, 2026-10-14).
# TRUST_REQUIRE_BUILD_PROVENANCE=1, the same requirement as --require-provenance,
# is refused there as that flag is.
if [[ "$GATE_ONLY" -eq 1 || "$PROVENANCE_ONLY" -eq 1 ]]; then
	if [[ "$GATE_ONLY" -eq 1 ]]; then
		MODE=--gate-only USES="" TAKES="it takes no other option"
	else
		MODE=--provenance USES=--require-llvm-identity TAKES="it takes --require-llvm-identity and paired explicit frontend authority"
	fi
	for OPTION in $TYPED; do
		[[ "$OPTION" == --source-root ]] && continue
		if [[ "$PROVENANCE_ONLY" -eq 1 && ( "$OPTION" == --frontend-component || "$OPTION" == --frontend-component-sha256 ) ]]; then continue; fi
		[[ "$OPTION" == "$MODE" || "$OPTION" == "$USES" ]] && continue
		printf 'promote: %s does not use %s (options are refused, never ignored; %s)\n' "$MODE" "$OPTION" "$TAKES" >&2
		usage >&2
		exit 3
	done
	if [[ "${TRUST_REQUIRE_BUILD_PROVENANCE:-0}" == 1 ]]; then
		printf 'promote: %s does not use TRUST_REQUIRE_BUILD_PROVENANCE=1, the requirement of a seal (a requirement is refused, never ignored; %s)\n' "$MODE" "$TAKES" >&2
		usage >&2
		exit 3
	fi
fi

SRC="${1:-$REPO/build/host/stage2}"
if [[ -n "$FRONTEND_COMPONENT" ]]; then
	SRC="$(cd "$SRC" && pwd -P)" || { printf 'promote: cannot resolve frontend component subject\n' >&2; exit 3; }
fi
ROOT="${TRUST_TOOLCHAIN_HOME:-$HOME/toolchains}"
# Absolute, from the caller's directory: the serial executor starts an absolute
# program only, so a relative home was refused at the hello world of step 6,
# after the copy, and the rustup link would have named a path relative to itself.
[[ "$ROOT" == /* ]] || ROOT="$PWD/$ROOT"
RUSTUP_LINK="${RUSTUP_HOME:-$HOME/.rustup}/toolchains/trust"

die() { printf '\npromote: %s\n' "$*" >&2; exit 1; }
say() { printf '==> %s\n' "$*"; }
# scratch [-d]: a scratch file (with -d, a directory) under TMPDIR, relative or
# not, named tmp.* as mktemp names its own. The template is explicit because
# macOS's mktemp ignores a relative TMPDIR and falls back to the user temp
# directory; BSD and GNU mktemp both honor a template.
scratch() {
	local parent="${TMPDIR:-/tmp}"
	mktemp "$@" "${parent%/}/tmp.XXXXXXXXXX"
}

# The caller pins this independently packaged native executor before promotion.
# It owns real GNU transport under the existing outer admission, adds no credits,
# and preserves the direct compiler argv and raw output/status.
serial_executor() {
    local executor="${TRUST_TOOLCHAIN_SERIAL_COMMAND:-}"
    [[ "$executor" == /* && -f "$executor" && ! -L "$executor" && -x "$executor" ]] \
        || die "direct compiler gates require an explicit regular executable TRUST_TOOLCHAIN_SERIAL_COMMAND"
    printf '%s' "$executor"
}

serial_command() {
    local executor
    executor="$(serial_executor)" || return
    "$executor" -- "$@"
}

# serial_precondition: asked ONCE, before the first gate, so a host that cannot
# start a gate's commands gets one refusal that names the cause.
#
# WHY IT EXISTS, as one measured case. Until 2026-11-12 nothing asked. Every
# gate row started the executor itself with its output sent to a scratch file,
# so on a host with no executor, or under a caller holding no build slot, the
# UI gate printed `FAIL <row>` for all eight rows with nothing after the colon,
# deleted the scratch files, and the seal was refused as "FAILS this tree's
# named UI tests ... Fix the compiler" (the GB10, 2026-11-10, on a stage2 that
# passes every row once the two are supplied). The script's own test,
# scripts/tests/promote_toolchain_test.sh, had been stopping at its first case
# for the same reason since the executor arrived in 083f70d694.
#
# It starts a no-op through the executor in the caller's own environment: what
# the executor refuses for a no-op it refuses for the compiler. It adds no
# switch: there is no way to run a gate without the executor.
serial_precondition() {
	local executor="${TRUST_TOOLCHAIN_SERIAL_COMMAND:-}" noop said rc=0
	local how="    Every gate here starts the compiler and the shipped tools through
    \`trust-serial-command\` (crates/trust-resource-controller). That program
    grants no CPU or memory of its own: it starts a command only for a caller
    that already holds a build slot. Build it with a Trust toolchain, name it,
    and run promotion under a slot:
        (cd $PROMOTER_ROOT/crates/trust-resource-controller && CARGO_TARGET_DIR=<dir> \\
            targo --unverified build --locked --release --features serial-command --bin trust-serial-command)
        TRUST_TOOLCHAIN_SERIAL_COMMAND=<dir>/release/trust-serial-command \\
            python3 $PROMOTER_ROOT/scripts/build-slot --cpus 1 -- bash $PROMOTER_ROOT/scripts/promote-toolchain.sh ...
    No gate ran. This says nothing about the toolchain."
	[[ -n "$executor" ]] || die "REFUSED before any gate: TRUST_TOOLCHAIN_SERIAL_COMMAND is not set.

$how"
	[[ "$executor" == /* && -f "$executor" && ! -L "$executor" && -x "$executor" ]] \
		|| die "REFUSED before any gate: TRUST_TOOLCHAIN_SERIAL_COMMAND=$executor is not the absolute path of a regular executable file (a relative path, a directory, a symlink and a file that is not executable are each refused).

$how"
	noop="$(type -P true || true)"
	[[ "$noop" == /* ]] || die "REFUSED before any gate: found no \`true\` on PATH to start through the serial executor"
	said="$("$executor" -- "$noop" 2>&1)" || rc=$?
	[[ "$rc" -eq 0 ]] || die "REFUSED before any gate: the serial executor would not start a no-op (exit $rc).

    ran:  $executor -- $noop
    said: $(printf '%s\n' "${said:-(it printed nothing)}" | sed -n '1,3p' | cut -c1-240 | sed '2,$s/^/          /')

$how"
}

# scratch_precondition: asked ONCE, beside serial_precondition and for the same
# reason. Two UI rows, the rustc-dev probe and the hello world of step 6 each
# build a program in a `scratch -d` directory and run it. Where that directory
# is on a filesystem mounted noexec the compiler writes every one of them and
# none may be executed: the rows printed FAIL, --gate-only read "UI gate
# FAILED ... native rustc-dev gate FAILED" and the seal was refused as "FAILS
# this tree's named UI tests", under rows that said (cannot_run_why) "which
# says nothing about the compiler". Measured 2026-11-12 with TMPDIR on
# /run/lock, on a fixture toolchain that passes every gate anywhere else. It
# asks what the gates ask (`-x`) of a file made where they make theirs. A
# relative TMPDIR is not refused: a program runs from one (rustc_dev_probe
# makes its own scratch path absolute for the executor). cannot_run_why stays
# in the rows: a filesystem can be remounted while a run is under way.
scratch_precondition() {
	local dir said
	dir="$(scratch -d)" || die "REFUSED before any gate: could not create a scratch directory under ${TMPDIR:-/tmp} (what \`mktemp -d\` said is above).
    No gate ran. This says nothing about the toolchain."
	if ! said="$( { printf '#!/bin/sh\n' > "$dir/program" && chmod 700 "$dir/program"; } 2>&1)"; then
		rm -rf "${dir:?}"
		die "REFUSED before any gate: could not write a file in a scratch directory under ${dir%/*} and give it an execute bit: ${said:-(nothing was printed)}
    No gate ran. This says nothing about the toolchain."
	fi
	if [[ ! -x "$dir/program" ]]; then
		rm -rf "${dir:?}"
		die "REFUSED before any gate: a file written under ${dir%/*} with an execute bit may not be executed there (is that a filesystem mounted noexec?).

    The UI gate, the rustc-dev probe and the hello world of the sealed copy
    each build a program in a scratch directory under TMPDIR and run it. Set
    TMPDIR to a directory on a filesystem that allows execution, and run again.
    No gate ran. This says nothing about the toolchain."
	fi
	rm -rf "${dir:?}"
}

# gate_said <output file>: the one line a FAIL row quotes from what its command
# printed. The first line beginning `error` when there is one, otherwise the
# first line that is not blank, otherwise the words "(it printed nothing)".
# Never empty: a row used to quote `grep -m1 '^error'` alone, and a command
# that died without a compiler diagnostic left nothing after the row's colon.
# A line over 240 columns keeps its first 60 and its last 175: a loader's line
# opens with the program's whole path and ends with the reason (133 columns
# from `error while loading` for a missing librustc_driver), so a cut from the
# left at any column loses the reason for a deep enough path. `grep -a`: a NUL
# or a byte that is not UTF-8 makes grep call the file binary and print no line.
gate_said() {
	local line
	line="$(grep -a -m1 '^error' "$1" 2>/dev/null | LC_ALL=C tr -d '\000' || true)"
	[[ -n "$line" ]] || line="$(grep -a -m1 -v '^[[:space:]]*$' "$1" 2>/dev/null | LC_ALL=C tr -d '\000' || true)"
	[[ -n "$line" ]] || line="(it printed nothing)"
	[[ "${#line}" -le 240 ]] || line="${line:0:60} ... ${line:$((${#line} - 175))}"
	printf '%s' "$line"
}

# cannot_run_why <file>: why `-x` is false for a file a compiler exited 0 after
# being asked to write. Three answers that used to be one sentence ("left no
# executable"), which blamed the compiler for a TMPDIR mounted noexec: nothing
# was written; it was written without an execute bit; or its mode has the bit
# and this run still may not execute it, which is the filesystem's rule.
cannot_run_why() {
	if [[ ! -e "$1" ]]; then
		printf 'the compiler exited 0 and wrote no %s' "${1##*/}"
	elif [[ -z "$(find "$1" -maxdepth 0 -type f -perm -100 2>/dev/null)" ]]; then
		printf 'the compiler exited 0 and wrote %s as something that is not a file with an execute bit (%s)' \
			"${1##*/}" "$(ls -ld "$1" 2>/dev/null | awk '{ print $1 }')"
	else
		printf 'the compiler wrote %s with an execute bit and this run still may not execute it, which says nothing about the compiler: is %s on a filesystem mounted noexec? Set TMPDIR to a directory on one that is not, and run again' \
			"${1##*/}" "${1%/*}"
	fi
}

# serial_refusal <exit status> <output file>: did the serial executor refuse to
# start the command, so that the status and the file are the executor's and not
# the command's? Prints the executor's line when so. The executor refuses
# before it starts anything, exits 75 and names itself; a variable that stopped
# naming one is this script's own refusal, exit 1. serial_precondition asks
# once at the start; this is for a refusal that begins after it (the slot is
# released, the file is replaced), so that no row reports an executor's refusal
# as the compiler's verdict or a tool's failure to start. A file that still
# passes the mode tests and can no longer be executed has no words of its own;
# for any other status the no-op is asked again (the last arm).
serial_refusal() {
	local line noop said rc=0
	line="$(grep -a -m1 -v '^[[:space:]]*$' "$2" 2>/dev/null | LC_ALL=C tr -d '\000' || true)"
	case "$1:$line" in
		# A program the OS would not start (no such file, no loader or
		# interpreter, not executable, another architecture) comes back in the
		# same shape: exit 75, "refused: command launch: <OS error>". While the
		# executor still starts a no-op that is the program's failure, and the
		# row is a FAIL that quotes it, not a refusal of this run.
		75:trust-serial-command:\ refused:\ command\ launch:*)
			noop="$(type -P true || true)"
			if [[ "$noop" == /* ]] && "${TRUST_TOOLCHAIN_SERIAL_COMMAND:-}" -- "$noop" >/dev/null 2>&1; then return 1; fi
			printf '%s' "${line:0:240}" ;;
		75:trust-serial-command*|1:promote:\ direct\ compiler\ gates\ require*) printf '%s' "${line:0:240}" ;;
		*)
			# Not the executor's words, and still perhaps the executor's failure:
			# a file that is being rewritten in place, or was left half written,
			# or is another machine's, passes `-f` and `-x` and cannot be
			# executed. The status does not say which (measured 2026-11-12:
			# bash answers 126; env(1), which starts the tool rows, hands a file
			# of the wrong format to sh, which exited 2; half an ELF dies by
			# SIGSEGV, 139), so the no-op is asked again. An executor that
			# starts it (0), or refuses it in its own words (75), is one that
			# ran this command, and the status is the command's.
			noop="$(type -P true || true)"
			[[ "$noop" == /* ]] || return 1
			said="$( { "${TRUST_TOOLCHAIN_SERIAL_COMMAND:-/nonexistent}" -- "$noop"; } 2>&1)" || rc=$?
			[[ "$rc" -ne 0 && "$rc" -ne 75 ]] || return 1
			said="$(printf '%s\n' "$said" | grep -a -m1 -v '^[[:space:]]*$' | LC_ALL=C tr -d '\000' || true)"
			[[ -n "$said" || "$rc" -le 128 ]] || said="(it printed nothing; killed by signal $((rc - 128)))"
			# Head and tail, as gate_said: the shell's line opens with two paths
			# and ends with the reason.
			[[ "${#said}" -le 200 ]] || said="${said:0:40} ... ${said:$((${#said} - 155))}"
			printf 'the serial executor itself can no longer be started (a no-op through it now exits %s): %s' \
				"$rc" "${said:-(it printed nothing)}" ;;
	esac
}

# gate_not_run <gate> <what was not done>: the refusal for a gate with a row
# the executor would not start. Never the gate's own verdict.
gate_not_run() {
	die "$1 did not finish: the serial executor refused to start a command for each row marked NOT RUN above — $2.

    That is a refusal of this run, not a verdict on the toolchain: a row that
    did not run proved nothing either way. Each NOT RUN row above quotes the
    executor's own reason; the file TRUST_TOOLCHAIN_SERIAL_COMMAND names may
    have changed since this run began. Run it again under a slot:
        python3 $PROMOTER_ROOT/scripts/build-slot --cpus 1 -- bash $PROMOTER_ROOT/scripts/promote-toolchain.sh ..."
}

# step_not_run <what was asked> <what was not done> <the executor's line>: the
# same refusal for one command outside a gate (the target-libdir read, the
# hello world and the -Z help of step 6, and the build of the AY-admission
# probe of step 6a). Those used to report an executor's refusal in the words
# kept for a toolchain that failed the question.
step_not_run() {
	die "$1 was NOT RUN: the serial executor refused to start it — $2.

    said: $3

    That is a refusal of this run, not a verdict on the toolchain. Run it
    again under a slot:
        python3 $PROMOTER_ROOT/scripts/build-slot --cpus 1 -- bash $PROMOTER_ROOT/scripts/promote-toolchain.sh ..."
}

# said_block <output file>: up to twelve lines of what a command printed, for a
# refusal that quotes more than one. From its first `error` line when it has
# one (a link failure opens with the linker's whole command line), otherwise
# from its first line that is not blank. A line over 240 columns keeps its
# head and its tail (the reason is at the end of a line that opens with a
# path). Never empty.
said_block() {
	local text clip='function clip(s) { return length(s) > 240 ? substr(s, 1, 60) " ... " substr(s, length(s) - 174) : s }'
	text="$(awk "$clip"' /^error/ { on = 1 } on && n < 12 { print "        | " clip($0); n++ }' "$1" 2>/dev/null | LC_ALL=C tr -d '\000' || true)"
	[[ -n "$text" ]] || text="$(awk "$clip"' NF && n < 12 { print "        | " clip($0); n++ }' "$1" 2>/dev/null | LC_ALL=C tr -d '\000' || true)"
	[[ -n "$text" ]] || text='        | (it printed nothing)'
	printf '%s\n' "$text"
}

# trustc_answer <trustc> <argument> <what is not known without it>: the
# compiler's answer to an identity question (`--version`, `-vV`), or the
# refusal that says what it printed instead. Call it as
#     X="$(trustc_answer ...)" || exit 1
# These reads were `"$trustc" -vV 2>/dev/null | sed ...` in a plain assignment:
# under pipefail and errexit a compiler that could not start ended the script
# on that line with no output at all (exit 127, nothing printed).
trustc_answer() {
	local err out rc=0
	err="$(scratch)" || die "could not create a scratch file for $1 $2"
	out="$("$1" "$2" 2>"$err")" || rc=$?
	if [[ "$rc" -ne 0 ]]; then
		printf '%s\n' "$out" >> "$err"
		out="$(said_block "$err")"
		rm -f "$err"
		die "$1 $2 exited $rc, so $3. It said:
$out"
	fi
	rm -f "$err"
	printf '%s\n' "$out"
}

# rustc_dev_probe <toolchain> <scratch-dir>: can <toolchain>'s own compiler
# link and run a rustc_private consumer from its OWN sysroot, with no overlay?
# Run on the candidate before anything is copied (step 1e) and again on the
# sealed copy (step 6). It returns 1 for a toolchain that cannot, after saying
# which of its two steps failed and quoting that step's output under its own
# name, and 2 when the serial executor refused to start a step: NOT RUN, which
# says nothing about the toolchain. The scratch directory holds the source and
# everything both steps printed; the caller keeps it unless the probe passed.
rustc_dev_probe() (
	local toolchain scratch="$2" rc=0 refused
	# Absolute, as in the two gates below: the serial executor starts an absolute
	# program only, and `--gate-only build/host/stage2` names a relative one.
	toolchain="$(cd "$1" && pwd -P)" \
		|| { printf 'rustc-dev probe: cannot resolve the toolchain directory %s\n' "$1" >&2; return 1; }
	# The scratch directory too: the consumer built in it is started through the
	# executor, and `scratch -d` under a relative TMPDIR names a relative one.
	[[ "$scratch" == /* ]] || scratch="$PWD/$scratch"
	# The probe must use this prefix's libraries, not a caller's loader or
	# linker overlay. Keep the caller's environment unchanged outside this run.
	unset LIBRARY_PATH LD_LIBRARY_PATH LD_PRELOAD LD_AUDIT LD_RUN_PATH \
		DYLD_LIBRARY_PATH DYLD_FALLBACK_LIBRARY_PATH DYLD_INSERT_LIBRARIES \
		DYLD_FRAMEWORK_PATH DYLD_FALLBACK_FRAMEWORK_PATH DYLD_VERSIONED_LIBRARY_PATH \
		DYLD_VERSIONED_FRAMEWORK_PATH DYLD_ROOT_PATH DYLD_IMAGE_SUFFIX
	cat > "$scratch/rustc_dev_probe.rs" <<'RS'
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_public_bridge;
struct ProbeCallbacks;
impl rustc_driver::Callbacks for ProbeCallbacks {}
fn main() -> std::process::ExitCode {
    rustc_driver::catch_with_exit_code(|| {
        let args = ["rustc_dev_probe".to_owned(), "--version".to_owned()];
        rustc_driver::run_compiler(&args, &mut ProbeCallbacks);
        println!("trust-rustc-dev-native-link-probe: ok");
    })
}
RS
	serial_command "$toolchain/bin/trustc" --sysroot "$toolchain" -Ztrust-verify=off --edition 2024 -C rpath=yes --crate-type bin \
		--crate-name rustc_dev_probe --emit=link -o "$scratch/rustc_dev_probe" \
		"$scratch/rustc_dev_probe.rs" >"$scratch/rustc_dev_probe.log" 2>&1 || rc=$?
	if [[ "$rc" -ne 0 ]]; then
		if refused="$(serial_refusal "$rc" "$scratch/rustc_dev_probe.log")"; then
			printf '    NOT RUN  rustc-dev probe: the serial executor refused to start the compiler, so this says nothing about it: %s\n' "$refused" >&2
			return 2
		fi
		printf '    FAIL  rustc-dev probe: the compiler exited %s building a rustc_private consumer (rustc_dev_probe.log). It said:\n' "$rc" >&2
		said_block "$scratch/rustc_dev_probe.log" >&2
		return 1
	fi
	[[ -f "$scratch/rustc_dev_probe" && -s "$scratch/rustc_dev_probe" && ! -L "$scratch/rustc_dev_probe" ]] \
		|| { printf '    FAIL  rustc-dev probe: the compiler exited 0 without writing an executable\n' >&2; return 1; }
	[[ -x "$scratch/rustc_dev_probe" ]] \
		|| { printf '    FAIL  rustc-dev probe: %s\n' "$(cannot_run_why "$scratch/rustc_dev_probe")" >&2; return 1; }
	serial_command "$scratch/rustc_dev_probe" >"$scratch/rustc_dev_probe.run.log" 2>&1 || rc=$?
	if [[ "$rc" -ne 0 ]]; then
		if refused="$(serial_refusal "$rc" "$scratch/rustc_dev_probe.run.log")"; then
			printf '    NOT RUN  rustc-dev probe: the serial executor refused to start the consumer it built, so this says nothing about it: %s\n' "$refused" >&2
			return 2
		fi
		printf '    FAIL  rustc-dev probe: the consumer it built exited %s when run (rustc_dev_probe.run.log). It said:\n' "$rc" >&2
		said_block "$scratch/rustc_dev_probe.run.log" >&2
		return 1
	fi
	if ! grep -qxF 'trust-rustc-dev-native-link-probe: ok' "$scratch/rustc_dev_probe.run.log"; then
		printf '    FAIL  rustc-dev probe: the consumer it built exited 0 without completing its native driver call (rustc_dev_probe.run.log). It said:\n' >&2
		said_block "$scratch/rustc_dev_probe.run.log" >&2
		return 1
	fi
)

verify_surface() {
	local candidate="$1" label="$2" python="${TRUST_TOOLCHAIN_PYTHON3:-python3}"
	local host resource_work
	# The general verifier can report a partial check when its path-resolution
	# dependencies are absent. Promotion must establish the complete contract.
	[[ -f "$REPO/scripts/lib/trust_toolchain_surface.sh" \
		&& -r "$REPO/scripts/lib/trust_toolchain_surface.sh" ]] \
		|| die "toolchain surface validation requires scripts/lib/trust_toolchain_surface.sh"
	command -v "$python" >/dev/null 2>&1 \
		&& "$python" -c 'import pathlib, sys; assert sys.version_info.major == 3' >/dev/null 2>&1 \
		|| die "toolchain surface validation requires a working Python 3: $python"
	resource_work="$(mktemp -d "${TMPDIR:-/tmp}/trust-promote.XXXXXXXXXX")" || die "cannot retain native Targo discovery"
	[[ "$resource_work" == /* ]] || resource_work="$PWD/$resource_work"
	TRUST_VERIFY_ALLOW_MISSING= TRUST_VERIFY_ALLOW_MISSING_BACKEND= \
		sh "$REPO/tools/verify-toolchain.sh" "$candidate" --resource-receipt="$resource_work/targo-resource.json" \
		|| die "$label violates the complete Trust toolchain output contract; native Targo discovery kept in $resource_work"
	NATIVE_TARGO_RESOURCE_JSON="$(cat "$resource_work/targo-resource.json")" \
		|| die "native Targo discovery produced no retained receipt: $resource_work"
	rm -f "$resource_work/targo-resource.json"
	rmdir "$resource_work"
	# Native resource workers ask the compiler to use its own elastic linker
	# and debug utility. A version-only legacy surface could call a seal ready
	# while every first Cargo build then failed before linking a build script.
	# A qualified supplementary plan is installed only into the new copy; the
	# final copy and every gate-only invocation must carry the actual tools.
	# An SDK with neither tool is recorded by native_linker_surface and goes
	# on: it publishes no elastic surface, and the compiler refuses that mode.
	if [[ "$candidate" != "$SRC" || -z "$NATIVE_TOOLS" || "$GATE_ONLY" -eq 1 ]]; then
		native_linker_surface "$candidate" "$label"
	fi
	# A complete binary set can still carry an incomplete standard library or
	# two public dependency versions. Check the compiler host and every other
	# installed std target before copying and again on the sealed artifact.
	host="$("$candidate/bin/trustc" -vV | sed -n 's/^host: //p')" \
		|| die "$label cannot report its compiler host for library validation"
	[[ -n "$host" ]] || die "$label reports no compiler host for library validation"
	"$python" -I -S -B "$REPO/scripts/verify_sysroot_libraries.py" \
		--sysroot "$candidate" --target "$host" \
		|| die "$label violates the complete Trust sysroot library contract"
}

native_linker_surface() {
	local candidate="$1" label="$2" host verbose rc said
	# Self-contained (scripts/tests/promote_native_tools_surface_test.py runs this
	# function alone). A compiler that could not answer is asked once more for
	# its words: this refusal used to be the first sentence and nothing else.
	verbose="$("$candidate/bin/trustc" -vV 2>/dev/null)" || {
		rc=$?
		said="$({ "$candidate/bin/trustc" -vV 2>&1 || true; } | sed -n '1,6s/^/        | /p')"
		die "$label cannot report its compiler host: \`trustc -vV\` exited $rc. It said:
${said:-        | (it printed nothing)}"
	}
	host="$(printf '%s\n' "$verbose" | sed -n 's/^host: //p')"
	[[ -n "$host" && "$host" != *$'\n'* ]] \
		|| die "$label reports an absent or ambiguous compiler host: its \`trustc -vV\` has $(printf '%s\n' "$verbose" | grep -c '^host: ' || true) \`host:\` lines where one is required"
	# A Darwin requirement. On any other host there is no paired surface, and a
	# caller that reports this check must say so rather than "passed".
	case "$host" in *-apple-darwin) ;; *) return 0 ;; esac
	# Neither tool is there at all: this SDK publishes no paired surface. That
	# is recorded here and is not a refusal (docs/DECISION_QUEUE.md
	# NATIVE-TOOLS-ABSENT-RECORDED). Nothing in the tree produces the tools or
	# their record yet (docs/OPEN_ISSUES.md DARWIN-NATIVE-TOOLS-PRODUCER-1), so
	# the refusal stopped every macOS seal, and the build the fleet runs has
	# never carried them. What such an SDK cannot do it still refuses itself:
	# trustc under --resource-worker-v2 or -v3 ends "native elastic linking
	# needs the paired SDK's bin/rust-lld" (rustc_codegen_ssa back/link.rs).
	# An ordinary build links with the host's linker, and the pack's hello
	# world decides whether this compiler links. A link, a tool that cannot
	# start, or bin/dsymutil without bin/rust-lld is a broken surface and still
	# refuses.
	if [[ ! -e "$candidate/bin/rust-lld" && ! -L "$candidate/bin/rust-lld" \
			&& ! -e "$candidate/bin/dsymutil" && ! -L "$candidate/bin/dsymutil" ]]; then
		printf '    RECORDED  %s publishes no paired bin/rust-lld and bin/dsymutil: native elastic linking (--resource-worker-v2, --resource-worker-v3) is unavailable in it and refuses when asked; ordinary builds use the host linker. Not checked, not passed (DARWIN-NATIVE-TOOLS-PRODUCER-1).\n' "$label" >&2
		return 0
	fi
	[[ -f "$candidate/bin/rust-lld" && -x "$candidate/bin/rust-lld" \
			&& ! -L "$candidate/bin/rust-lld" \
			&& -f "$candidate/bin/dsymutil" && -x "$candidate/bin/dsymutil" \
			&& ! -L "$candidate/bin/dsymutil" ]] \
		|| die "$label native Darwin SDK lacks paired bin/rust-lld or bin/dsymutil; build them from its exact LLVM source and use a qualified --native-tools record"
	"$candidate/bin/rust-lld" -flavor darwin --version >/dev/null \
		|| die "$label paired rust-lld cannot start"
	"$candidate/bin/dsymutil" --version >/dev/null \
		|| die "$label paired dsymutil cannot start"
}

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

# Rows are `<test path>[#<revision>]|<expected status: pass|fail|run-fail>|<required marker>`.
# The status column is asserted against the file's own `//@` directives too,
# so a row that disagrees with its test is itself a refusal.
#
# A `#<revision>` row compiles the test as compiletest compiles that revision:
# the unrevisioned `//@ compile-flags:` line, then every `//@[<revision>]
# compile-flags:` line, then `--cfg <revision>`. The revision must be one the
# test lists in `//@ revisions:`.
#
# `//@ aux-build: <file>` dependencies (and a revision's own) are built first,
# from `auxiliary/` beside the test, with each aux file's own compile-flags and
# edition, and the test is compiled with `-L` on them. Only an aux crate that
# declares `//@ no-prefer-dynamic` is built: this gate links aux crates as
# rlibs, which is what compiletest does only under that directive, and an aux
# it cannot build the way the suite does is a REFUSAL, not a guess.
#
# A `run-fail` row (the test declares `//@ run-fail`) builds the test, runs the
# binary, and requires the panic exit status 101 with the marker on the run's
# STDERR. The marker must also be one of the test's own `//@ error-pattern:`
# lines, so the row cannot assert a different panic than the suite does.
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

	# B1 (docs/audits/2026-10-16-hn-rustc-review.md; catch-up plan SE10): the
	# installed seal `321aaeda7` (store trust 9192) removes an overflow check
	# that a `requires` proved, although no caller was charged the clause. The
	# dependency `requires_dep_default_policy` is verified on the default policy,
	# and its `pub fn add1(x: u32) -> u32 requires x < 100 { x + 1 }` is called
	# with `u32::MAX`. Before the fix every revision built exit 0 and printed
	# `0 0` where vanilla Rust panics (measured on a stage 1 of `71fc7a07cc`,
	# 2026-10-05); B1 measured the same elision on the seal. These two rows have
	# not been run against 9192. Main keeps every check that a `requires` body
	# reachable from another crate proved (ADVISORY-REQUIRES-CROSS-CRATE,
	# KNOWN_HAZARDS, CLOSED 2026-10-05), so each run must panic
	# "attempt to add with overflow". One row per route:
	#
	# the `requires` fn reified to a fn pointer, called from an advisory consumer
	# (`let fp: fn(u32) -> u32 = dep::add1; fp(y)`)...
	"tests/ui/trust/instance_hypothesis/requires_dep_elision_cross_crate_run.rs#advisory_pointer|run-fail|attempt to add with overflow"
	# ...and the `pub` fn called directly from a verify-off consumer.
	"tests/ui/trust/instance_hypothesis/requires_dep_elision_cross_crate_run.rs#off_direct|run-fail|attempt to add with overflow"
)

# Returns 0 when every row passed, 1 when a row FAILED, and 2 when the serial
# executor would not start the compiler for a row (NOT RUN): the caller refuses
# either way and says which, because the second is not a verdict on the
# compiler. A run with a FAIL or a NOT RUN row keeps its scratch directory and
# prints where.
ui_gate() {
	local tc
	local work failures=0 notrun=0 row rel expect marker file flags edition emit rc out combined
	local relrev rev hdr stem auxdir auxname auxfile auxflags auxedition auxrc auxwhy auxout refused runrc
	local -a libs
	# Absolute, as the tool-start gate's is and for one more reason: the serial
	# executor starts an absolute program only, so a toolchain named by a
	# relative path had every row refused (`--gate-only build/host/stage2`).
	tc="$(cd "$1" && pwd -P)" || die "UI gate: cannot resolve the toolchain directory $1"
	work="$(scratch -d)" || die "UI gate: could not create a scratch directory"

	say "UI gate: ${#UI_GATE_ROWS[@]} named tests through $tc/bin/trustc"
	for row in "${UI_GATE_ROWS[@]}"; do
		relrev="${row%%|*}"
		rel="${relrev%%#*}"
		rev=""
		if [[ "$relrev" == *#* ]]; then rev="${relrev#*#}"; fi
		expect="${row#*|}"; expect="${expect%%|*}"
		marker="${row##*|}"
		file="$REPO/$rel"

		[[ -r "$file" ]] || die "UI gate: $rel is missing or unreadable in $REPO.
    The gate names its tests explicitly and cannot silently skip one: a row
    that cannot run is a REFUSAL. Restore the test, or remove the row
    deliberately and say why in the commit that removes it."

		# A header line applies to this row when it is unrevisioned, or when it
		# is `//@[<rev>]` for the row's own revision.
		hdr='//@ '
		if [[ -n "$rev" ]]; then
			[[ "$rev" =~ ^[A-Za-z0-9_]+$ ]] || die "UI gate: row $relrev names a revision that is not a plain word"
			local revisions
			revisions=" $(sed -n 's|^//@ revisions: *||p' "$file" | tr -s ' \n' '  ') "
			[[ "$revisions" == *" $rev "* ]] \
				|| die "UI gate: $rel lists no revision '$rev' in its \`//@ revisions:\` headers — fix the row"
			hdr="//@(\\[$rev])? "
		fi

		# Expectation is the TEST'S, cross-checked against the row so the two
		# can never quietly disagree.
		local declared=fail
		if grep -qE "^${hdr}run-fail\$" "$file"; then
			declared=run-fail
		elif grep -qE "^${hdr}(build-pass|check-pass|run-pass)\$" "$file"; then
			declared=pass
		fi
		[[ "$declared" == "$expect" ]] || die "UI gate: $relrev declares '$declared' in its own \`//@\` headers but this gate's row says '$expect' — fix the row, do not paper over it"
		if [[ "$expect" == run-fail ]]; then
			[[ "$marker" != '!'* ]] || die "UI gate: run-fail row $relrev has a negated marker; a run-fail row requires the panic it names"
			local patterns
			patterns="$(sed -nE "s|^${hdr}error-pattern: *||p" "$file")"
			grep -qxF -- "$marker" <<<"$patterns" \
				|| die "UI gate: $relrev's marker '$marker' is not one of the test's own \`//@ error-pattern:\` lines — the row must require what the test requires"
		fi

		flags="$(sed -n 's|^//@ compile-flags: *||p' "$file" | head -1)"
		if [[ -n "$rev" ]]; then
			flags="$flags $(sed -n "s|^//@\\[$rev] compile-flags: *||p" "$file" | tr '\n' ' ') --cfg $rev"
		fi
		edition="--edition=2015"
		if grep -q '^//@ edition' "$file"; then
			edition="--edition=$(sed -n 's|^//@ edition: *||p' "$file" | head -1)"
		fi
		emit=""
		if grep -qE "^${hdr}check-pass\$" "$file"; then emit="--emit=metadata"; fi

		stem="$(basename "$rel" .rs)"
		out="$work/$stem${rev:+.$rev}"
		mkdir -p "$out"
		combined="$out/output.txt"

		# Aux crates first, each the way compiletest builds it under
		# `no-prefer-dynamic`: its own compile-flags and edition, an rlib unless
		# its flags name a crate type.
		libs=()
		auxwhy=""
		refused=""
		auxdir="$out/aux"
		while IFS= read -r auxname; do
			[[ -n "$auxname" ]] || continue
			auxfile="$(dirname "$file")/auxiliary/$auxname"
			[[ -r "$auxfile" ]] || die "UI gate: $relrev builds aux crate $auxname, but $auxfile is missing or unreadable — a row that cannot run is a REFUSAL"
			grep -qE '^//@ no-prefer-dynamic$' "$auxfile" || die "UI gate: aux crate $auxname of $relrev does not declare \`//@ no-prefer-dynamic\`. This gate links aux crates as rlibs, which compiletest does only under that directive"
			auxflags="$(sed -n 's|^//@ compile-flags: *||p' "$auxfile" | head -1)"
			[[ "$auxflags" == *--crate-type* ]] || auxflags="$auxflags --crate-type=rlib"
			auxedition="--edition=2015"
			if grep -q '^//@ edition' "$auxfile"; then
				auxedition="--edition=$(sed -n 's|^//@ edition: *||p' "$auxfile" | head -1)"
			fi
			mkdir -p "$auxdir"
			auxrc=0
			auxout="$out/aux-$(basename "$auxname" .rs).txt"
			# shellcheck disable=SC2086
			serial_command "$tc/bin/trustc" --sysroot "$tc" $auxedition $auxflags --out-dir "$auxdir" -L "$auxdir" \
				"$auxfile" > "$auxout" 2>&1 || auxrc=$?
			if [[ "$auxrc" -ne 0 ]]; then
				refused="$(serial_refusal "$auxrc" "$auxout")" \
					|| auxwhy="aux crate $auxname did not build (exit $auxrc): $(gate_said "$auxout")"
				break
			fi
			libs=(-L "$auxdir")
		done < <(sed -nE "s|^${hdr}aux-build: *||p" "$file")

		rc=0
		if [[ -z "$auxwhy" && -z "$refused" ]]; then
			# Word splitting on $flags/$emit is intended — they are compiler
			# arguments read from the test header.
			# shellcheck disable=SC2086
			serial_command "$tc/bin/trustc" --sysroot "$tc" $edition $flags $emit ${libs[@]+"${libs[@]}"} \
				--out-dir "$out" "$file" > "$combined" 2>&1 || rc=$?
			# Asked before the expectation is: a row that expects a refusal would
			# otherwise read the executor's exit status as the compiler's.
			if [[ "$rc" -ne 0 ]]; then refused="$(serial_refusal "$rc" "$combined")" || refused=""; fi
		fi

		local verdict=ok why=""
		if [[ -n "$refused" ]]; then
			verdict=NOTRUN
			why="the serial executor refused to start the compiler, so this row says nothing about it: $refused"
		elif [[ -n "$auxwhy" ]]; then
			verdict=FAIL
			why="$auxwhy"
		elif [[ "$expect" == run-fail ]]; then
			if [[ "$rc" -ne 0 ]]; then
				verdict=FAIL
				why="expected it to build and run (//@ run-fail), got exit $rc: $(gate_said "$combined")"
			elif [[ ! -x "$out/$stem" ]]; then
				verdict=FAIL
				why="$(cannot_run_why "$out/$stem") (the row's binary, in $out)"
			else
				runrc=0
				"$out/$stem" > "$out/run-stdout.txt" 2> "$out/run-stderr.txt" || runrc=$?
				if [[ "$runrc" -ne 101 ]]; then
					verdict=FAIL
					# Its stdout when it wrote any, otherwise its stderr: a binary that
					# died before printing left this row ending at its colon.
					if [[ -s "$out/run-stdout.txt" ]]; then
						why="expected the binary to panic (exit 101, //@ run-fail), got exit $runrc; its stdout began: $(gate_said "$out/run-stdout.txt")"
					else
						why="expected the binary to panic (exit 101, //@ run-fail), got exit $runrc; its stdout was empty and its stderr began: $(gate_said "$out/run-stderr.txt")"
					fi
				elif ! grep -qF "$marker" "$out/run-stderr.txt"; then
					verdict=FAIL
					why="it panicked, but the required marker never appeared on its stderr — it failed for a different reason than the test asserts.
          wanted marker: $marker
          got instead:   $(grep -m1 -v -e '^note:' -e '^[[:space:]]*$' "$out/run-stderr.txt" | cut -c1-140 || true)"
					[[ "$why" != *'got instead:   ' ]] || why="$why(its stderr was empty)"
				fi
			fi
		elif [[ "$expect" == pass && "$rc" -ne 0 ]]; then
			verdict=FAIL
			why="expected it to compile (//@ $(grep -oE 'build-pass|check-pass|run-pass' "$file" | head -1)), got exit $rc: $(gate_said "$combined")"
		elif [[ "$expect" == fail && "$rc" -eq 0 ]]; then
			verdict=FAIL
			why="expected a refusal (the test declares no pass directive), but it compiled cleanly"
		elif [[ "$marker" == '!'* ]] && diagnostic_lines "$combined" | grep -qF "${marker#!}"; then
			# NEGATED marker. Some regressions have no output to assert on —
			# their whole point is that the compiler stays silent — so the only
			# honest assertion is that a known failure signature is ABSENT.
			verdict=FAIL
			why="exit $rc is what the row expects, but a FORBIDDEN marker appeared in a diagnostic line.
          forbidden marker: ${marker#!}
          got:              $(diagnostic_lines "$combined" | grep -m1 -F "${marker#!}" | cut -c1-140)"
		elif [[ "$marker" != '!'* ]] && ! diagnostic_lines "$combined" | grep -qF "$marker"; then
			verdict=FAIL
			# The first error or warning it did print; when it printed neither, the
			# first line of anything, so the row never ends at the colon.
			why="exit $rc is a status the row accepts, but the required marker never appeared in a DIAGNOSTIC line — the compiler reached this outcome for a different reason than the test asserts.
          wanted marker: $marker
          got instead:   $(diagnostic_lines "$combined" | grep -m1 -E '^(error|warning)' | cut -c1-140 || true)"
			[[ "$why" != *'got instead:   ' ]] || why="$why(no error or warning line; exit $rc) $(gate_said "$combined")"
		fi

		if [[ "$verdict" == NOTRUN ]]; then
			notrun=$((notrun + 1))
			printf '    NOT RUN  %s\n          %s\n' "$relrev" "$why"
		elif [[ "$verdict" == FAIL ]]; then
			failures=$((failures + 1))
			printf '    FAIL  %s\n          %s\n' "$relrev" "$why"
		else
			printf '    ok    %s (%s)\n' "$relrev" "$expect"
		fi
	done

	if [[ "$failures" -gt 0 || "$notrun" -gt 0 ]]; then
		# Kept, not deleted: the one-line reasons above are excerpts.
		printf '    everything each row printed is kept under %s (output.txt and aux-*.txt in the directory named for the row)\n' "$work"
		# A FAIL row is a verdict on the toolchain whatever else did not run;
		# 2 is for a gate whose only bad rows are NOT RUN.
		[[ "$failures" -eq 0 ]] || return 1
		return 2
	fi
	rm -rf "$work"
	say "UI gate: ${#UI_GATE_ROWS[@]}/${#UI_GATE_ROWS[@]} passed"
	return 0
}

# ---------------------------------------------------------------------------
# THE TOOL-START GATE (steps 1f and 6 below; the second half of --gate-only).
#
# WHY IT EXISTS, as one measured sentence. `trust-2615acef` was sealed on
# 2026-10-12 with every check in this script green, and not one `targo tippy`
# on it could start: `c73702b157` had added `VecDeque` and `BinaryHeap` to
# rustc_span's pre-interned symbols while tippy's own extra-symbol list named
# both, and the interner panics on a string it is handed twice
# (compiler/rustc_span/src/symbol.rs, `Interner::prefill`: "duplicate symbols
# in the rustc symbol list and the extra symbols added by the driver"). aterm's
# merge gate found it, one step before the channel moved.
#
# `--version` IS NOT A START, and that is why nothing here saw it. The output
# contract (verify_surface) asks every tool for its version. tippy-driver
# answers that before it creates a compiler session (src/tools/tippy/src/
# driver.rs, `should_print_tippy_version`), so the interner is never built and
# a driver that dies on every real invocation still prints its banner and
# exits 0. Measured on `trust-2615acef`: `tippy-driver --version`, `tippy
# --version` and `targo-tippy --version` all exit 0; the same driver given a
# one-function crate exits 101. Each row below therefore makes its tool do the
# smallest piece of real work that needs a session.
#
# EXIT STATUS IS NOT ENOUGH, here as in the UI gate above. A lint row expects
# a refusal, and a panic is also a nonzero exit: through the frontend BOTH are
# exit 101 (measured: `trust-1b185739` on the lint crate and `trust-2615acef`
# on anything). So each lint row carries the lint's own text as a required
# marker, and a clean compile must leave the file it was asked for. A tool that
# returns 0 without doing the work fails its row.
#
# THE ROWS, and what each one witnesses:
#   tippy-driver.clean   the driver creates a session with tippy's extra
#                        symbols and compiles a clean crate under `-D warnings`.
#   tippy-driver.lint    the lint passes are registered and run: a
#                        `needless_return` must be reported. Without this row a
#                        driver that started as a plain compiler would pass.
#   tippy.frontend       the route consumers take (`targo tippy`, aterm's gate):
#                        the frontend finds its driver and the driver wraps the
#                        compiler for a real package.
#   tippy.frontend-lint  that route ends in the LINTING driver: the same package
#                        with a `needless_return` must be refused in the lint's
#                        own words. Without this row a frontend that handed its
#                        package to a plain compiler, or to some other driver,
#                        would pass: tippy.frontend asks only for a finished
#                        build, and the two driver rows start the sibling
#                        `tippy-driver` directly, whatever the frontend runs.
#   trust-miri.session   miri's own extra symbols, through `MIRI_BE_RUSTC=target`
#                        (`MiriDepCompilerCalls`; `=host` is a plain rustc and
#                        would prove nothing). No interpreter run: that needs a
#                        Miri sysroot, which costs a std build.
#   trustdoc.session     trustdoc compiles and renders one crate.
#   trustfmt.format      trustfmt parses and formats one file.
# `trustc` itself is started by the UI gate and the hello world of step 6;
# `targo` by its doctor; `ay` by the admission probe of step 6a. `ty`, `clean`,
# `trustd` and `trust-analyzer` are not built on the compiler's session and
# stay with the output contract's version probe.
#
# Every start isolates compiler policy (HOME/CARGO_HOME are scratch), with
# only actual resource transport, custody and ceilings copied explicitly. No
# caller RUSTFLAGS, compiler/wrapper selection or rustup override can make a
# dead tool look alive or a live one look dead.
#
# FAIL-CLOSED, WITH NO OFF SWITCH, like the UI gate. A required tool that is
# missing fails its row. Only a tool the output contract itself does not
# require (trust-miri: tools/verify-toolchain.sh) may be absent, and then the
# row prints `n/a`: not started is never reported as started.
#
# The push row `fast.driver-extra-symbols` (scripts/check_driver_extra_symbols.py)
# catches the measured cause from the two source lists, before any build. This
# gate is the other end: whatever the cause, a toolchain whose shipped tools
# cannot start does not become a seal.
#
# WHAT A SEAL KEEPS OF IT. Until 2026-10-12 the gate's result lived only in the
# log of the promotion that ran it: `trust-f22fc270` passed 7/7 on the candidate
# and 7/7 on the sealed copy that day, and its PROVENANCE does not say the gate
# exists. A passing run now leaves its words in TOOL_START_RESULT (the summary
# line, as printed), TOOL_START_PASSED (the rows that started, by id) and
# TOOL_START_NOT_SHIPPED (the optional rows that were not started), and step 6b
# writes those of the run on the SEALED copy into PROVENANCE: it is the last
# run, and a run that fails ends the promotion, so nothing reads a stale one.
# They are a record of what this promotion measured, like `ay_admission=`:
# nothing re-reads them, and `--gate-only` answers for a toolchain by starting
# its tools again, not by quoting them.
TOOL_START_RESULT=""
TOOL_START_PASSED=""
TOOL_START_NOT_SHIPPED=""

# Rows are `<id>|<tool>|<expected status: pass|fail>|<required marker>|<required file>`,
# `-` for no marker / no file. `<tool>` is the bin/ name the row starts; a
# leading `?` marks one the output contract does not require.
TOOL_START_ROWS=(
	'tippy-driver.clean|tippy-driver|pass|-|libstart_probe.rmeta'
	'tippy-driver.lint|tippy-driver|fail|unneeded `return` statement|-'
	'tippy.frontend|tippy|pass|Finished|-'
	'tippy.frontend-lint|tippy|fail|unneeded `return` statement|-'
	'trust-miri.session|?trust-miri|pass|-|libstart_probe.rmeta'
	'trustdoc.session|trustdoc|pass|-|start_probe/index.html'
	'trustfmt.format|trustfmt|pass|    a.wrapping_add(b)|-'
)

# tool_start_run <row id> <toolchain> <scratch> <row out dir>: start one tool.
# Returns the tool's own exit status; 125 for a row with no command.
tool_start_run() {
	local id="$1" tc="$2" work="$3" out="$4"
	local -a bare=(/usr/bin/env -i "HOME=$work/home" "PATH=/usr/bin:/bin" "TMPDIR=$work/tmp")
	local executor resource
	executor="$(serial_executor)" || return
	# Preserve only the actual resource owner's transport/ceiling/custody.
	# These locators grant nothing; never copy compiler policy or synthesize
	# jobs, flags, protocol epochs, SDK paths or descriptor numbers here.
	for resource in BUILD_SLOT_HELD BUILD_SLOT_DIR BUILD_SLOT_EXCLUSIVE \
		BUILD_SLOT_CPU_PROTOCOL BUILD_SLOT_CPU_MODE BUILD_SLOT_CPU_BUDGET \
		BUILD_SLOT_CPU_SOURCE BUILD_SLOT_POOL_SLOTS BUILD_SLOT_LEGACY_DIR \
		BUILD_SLOT_V2_DIR BUILD_SLOT_V2_SLOTS BUILD_SLOT_FENCE_FDS \
		NUM_JOBS CARGO_BUILD_JOBS CARGO_MAKEFLAGS MAKEFLAGS MFLAGS CARGO_JOBSERVER_HANDOFF \
		TARGO_CALLER_JOBS TARGO_PLANNED_JOBS TARGO_JOB_MEMORY_BYTES \
		TARGO_MEMORY_RESERVE_BYTES TRUST_CPU_HANDOFF TRUST_CPU_IMPLICIT_FD \
		ATERM_SDK_LEASE_V3; do
		if [[ ${!resource+x} ]]; then bare+=("$resource=${!resource}"); fi
	done
	case "$id" in
		tippy-driver.clean)
			# A branded driver derives its sysroot from its own path and
			# refuses a caller's `--sysroot`, so none is passed.
			"${bare[@]}" "$executor" -- "$tc/bin/tippy-driver" --edition 2021 --crate-type lib \
				--crate-name start_probe --emit=metadata -D warnings \
				--out-dir "$out" "$work/clean.rs" ;;
		tippy-driver.lint)
			"${bare[@]}" "$executor" -- "$tc/bin/tippy-driver" --edition 2021 --crate-type lib \
				--crate-name start_probe_lint --emit=metadata -D warnings \
				--out-dir "$out" "$work/lint.rs" ;;
		tippy.frontend)
			( cd "$work/pkg" && "${bare[@]}" "CARGO_HOME=$work/cargo-home" \
				"CARGO_TARGET_DIR=$out/target" \
				"$executor" -- "$tc/bin/tippy" --unverified --offline -- -D warnings ) ;;
		tippy.frontend-lint)
			# The same invocation, in the package whose one function carries
			# the lint: only what the frontend routes to can differ.
			( cd "$work/pkg-lint" && "${bare[@]}" "CARGO_HOME=$work/cargo-home" \
				"CARGO_TARGET_DIR=$out/target" \
				"$executor" -- "$tc/bin/tippy" --unverified --offline -- -D warnings ) ;;
		trust-miri.session)
			"${bare[@]}" MIRI_BE_RUSTC=target "$executor" -- "$tc/bin/trust-miri" --edition 2021 \
				--crate-type lib --crate-name start_probe --emit=metadata \
				--out-dir "$out" "$work/clean.rs" ;;
		trustdoc.session)
			"${bare[@]}" "$executor" -- "$tc/bin/trustdoc" --edition 2021 --crate-type lib \
				--crate-name start_probe -o "$out" "$work/clean.rs" ;;
		trustfmt.format)
			"${bare[@]}" "$executor" -- "$tc/bin/trustfmt" --edition 2021 --emit stdout "$work/clean.rs" ;;
		*) return 125 ;;
	esac
}

# What a failed start printed, shortened: a panic with its message line, else
# the first errors, else the first lines of anything.
tool_start_excerpt() {
	# `grep -a`, and head and tail of a long line, for the reasons gate_said has.
	if grep -aq 'panicked at' "$1" 2>/dev/null; then
		awk '/panicked at/ { print; if ((getline line) > 0) print line; exit }' "$1"
	elif grep -aqE '^error' "$1" 2>/dev/null; then
		grep -a -m2 -E '^error' "$1"
	elif grep -aqv '^[[:space:]]*$' "$1" 2>/dev/null; then
		grep -a -m2 -v '^[[:space:]]*$' "$1"
	else
		printf '(it printed nothing)\n'
	fi | LC_ALL=C tr -d '\000' \
		| awk '{ print (length($0) > 240 ? substr($0, 1, 60) " ... " substr($0, length($0) - 174) : $0) }' 2>/dev/null
}

# Returns 0, 1 or 2 as the UI gate does: 2 is a row the serial executor would
# not start (NOT RUN), which is not a tool that cannot start.
tool_start_gate() {
	local tc
	local work failures=0 notrun=0 started=0 absent=0 row id tool expect marker artifact optional out rc verdict why refused
	local passed_rows="" absent_rows=""
	# Absolute, because the frontend row starts its tool from inside a scratch
	# package: `--gate-only build/host/stage2` names the toolchain relative to
	# the caller's directory, and a relative path would not resolve from there.
	tc="$(cd "$1" && pwd -P)" || die "tool-start gate: cannot resolve the toolchain directory $1"
	work="$(scratch -d)" || die "tool-start gate: could not create a scratch directory"
	work="$(cd "$work" && pwd -P)"
	mkdir -p "$work/home" "$work/tmp" "$work/cargo-home" "$work/pkg/src" "$work/pkg-lint/src"
	# The clean crate is the UI gate's ICE row: nothing in it to lint or prove.
	printf 'pub fn add(a: u8, b: u8) -> u8 { a.wrapping_add(b) }\n' > "$work/clean.rs"
	printf 'pub fn add(a: u8, b: u8) -> u8 { a.wrapping_add(b) }\n' > "$work/pkg/src/lib.rs"
	printf 'pub fn one() -> u8 {\n    return 1;\n}\n' > "$work/lint.rs"
	printf '[package]\nname = "start_probe"\nversion = "0.1.0"\nedition = "2021"\n\n[lib]\npath = "src/lib.rs"\n\n[workspace]\n' \
		> "$work/pkg/Cargo.toml"
	# The lint crate again, as a package, for the frontend's lint row.
	printf 'pub fn one() -> u8 {\n    return 1;\n}\n' > "$work/pkg-lint/src/lib.rs"
	printf '[package]\nname = "start_probe_lint"\nversion = "0.1.0"\nedition = "2021"\n\n[lib]\npath = "src/lib.rs"\n\n[workspace]\n' \
		> "$work/pkg-lint/Cargo.toml"

	say "tool-start gate: ${#TOOL_START_ROWS[@]} starts through $tc/bin"
	for row in "${TOOL_START_ROWS[@]}"; do
		IFS='|' read -r id tool expect marker artifact <<< "$row"
		optional=0
		if [[ "$tool" == '?'* ]]; then optional=1; tool="${tool#\?}"; fi
		if [[ ! -x "$tc/bin/$tool" ]]; then
			if [[ "$optional" -eq 1 ]]; then
				absent=$((absent + 1))
				absent_rows="$absent_rows${absent_rows:+ }$id"
				printf '    n/a   %s (this toolchain ships no bin/%s; not started)\n' "$id" "$tool"
			else
				failures=$((failures + 1))
				printf '    FAIL  %s\n          bin/%s is not in this toolchain\n' "$id" "$tool"
			fi
			continue
		fi

		out="$work/$id"
		mkdir -p "$out"
		rc=0
		# In a subshell: a signal here must leave step 6's EXIT trap the script's own stderr, not this file.
		( tool_start_run "$id" "$tc" "$work" "$out" ) > "$out.txt" 2>&1 || rc=$?

		verdict=ok why=""
		refused=""
		if [[ "$rc" -ne 0 ]]; then refused="$(serial_refusal "$rc" "$out.txt")" || refused=""; fi
		if [[ -n "$refused" ]]; then
			verdict=NOTRUN
			why="the serial executor refused to start bin/$tool, so this row says nothing about it: $refused"
		elif [[ "$rc" -eq 125 && ! -s "$out.txt" ]]; then
			verdict=FAIL
			why="this gate has no start command for the row — a row that cannot run is a REFUSAL"
		elif [[ "$expect" == pass && "$rc" -ne 0 ]]; then
			verdict=FAIL
			why="expected it to start and finish its work, got exit $rc"
		elif [[ "$expect" == fail && "$rc" -eq 0 ]]; then
			verdict=FAIL
			why="expected a refusal (the probe carries a lint that must fire), but it exited 0: it ran without linting"
		elif [[ "$marker" != - ]] && ! grep -qF -- "$marker" "$out.txt"; then
			verdict=FAIL
			why="exit $rc is the expected kind, but the required marker never appeared — it got there for another reason.
          wanted marker: $marker"
		elif [[ "$artifact" != - && ! -s "$out/$artifact" ]]; then
			verdict=FAIL
			why="it exited 0 without writing $artifact — it returned without doing the work"
		fi

		if [[ "$verdict" == NOTRUN ]]; then
			notrun=$((notrun + 1))
			printf '    NOT RUN  %s\n          %s\n' "$id" "$why"
		elif [[ "$verdict" == FAIL ]]; then
			failures=$((failures + 1))
			printf '    FAIL  %s\n          %s\n' "$id" "$why"
			tool_start_excerpt "$out.txt" | sed 's/^/          | /' || true
		else
			started=$((started + 1))
			passed_rows="$passed_rows${passed_rows:+ }$id"
			printf '    ok    %s (%s)\n' "$id" "$expect"
		fi
	done

	if [[ "$failures" -gt 0 || "$notrun" -gt 0 ]]; then
		# Kept, not deleted: the lines above are excerpts.
		printf '    everything each row printed is kept under %s (<row>.txt)\n' "$work"
		# A FAIL row is a verdict on the toolchain whatever else did not run;
		# 2 is for a gate whose only bad rows are NOT RUN.
		[[ "$failures" -eq 0 ]] || return 1
		return 2
	fi
	rm -rf "${work:?}"
	if [[ "$absent" -gt 0 ]]; then
		TOOL_START_RESULT="$started/$started passed ($absent not shipped, not started)"
	else
		TOOL_START_RESULT="$started/${#TOOL_START_ROWS[@]} passed"
	fi
	TOOL_START_PASSED="$passed_rows"
	TOOL_START_NOT_SHIPPED="${absent_rows:-none}"
	say "tool-start gate: $TOOL_START_RESULT"
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
#   (b) THE ARTIFACT FINGERPRINT -- the seal's CONTENT IDENTITY, one sha256
#       over every file, directory and link the seal ships, with their modes
#       (scripts/lib/seal_content_identity.py says exactly which, and why), the
#       same over the private sysroot sealed beside it, plus the sha256
#       of the driver and five binaries by name for readers that bind one file.
#       It establishes IDENTITY, not origin: it cannot say what source produced
#       these bytes, but it lets any future lane ask whether two seals are the
#       same build, which is the question the 2026-08-31 investigation had no
#       way to answer.
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
PROV_CENSUS_SCOPE="" # explicit observed scope; v1 never means recursive
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

# (b) IDENTITY of the artifact itself (plan T13a). `artifact_content_sha256` is
# THE identity: every file, directory and link the seal ships, with their
# modes, so two seals that differ in
# `targo-trust`, `trustd`, a sysroot rlib or any other shipped byte never share
# it (scripts/lib/seal_content_identity.py; about 3 s for a 4 GB seal,
# measured). The per-file lines that follow it are the six files the identity
# used to be, kept by name because consumers bind them one at a time (aterm's
# closure check reads the driver's, its Linux release check trustc's and
# targo's); they are NOT an identity, and nothing may be keyed on them alone.
# Prints nothing and fails when the tree cannot be identified (an unreadable
# file, a fifo), so a caller must capture it before writing anything.
prov_artifact_fingerprint() {
	local dir="$1" f base content
	content="$(python3 -B "$REPO/scripts/lib/seal_content_identity.py" "$dir")" || return 1
	printf '%s\n' "$content"
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

# Read one snapshot: x.py may still be appending the completion fields, or a
# new build may replace the record. Never combine fields from separate reads.
# A start-only, failed, malformed or contradictory stamp is not a completed
# build record, even when its initial tree_state says clean.
prov_validated_record() {
	python3 "$REPO/scripts/lib/trust_build_provenance.py" "$1" "$2" "$REPO"
}

prov_has_recursive_scope() {
	[[ "$PROV_CENSUS_SCOPE" == recursive-worktrees/v1 ]]
}

# THE STAGE RECEIPT (step 1b'' on the candidate, step 6b on the sealed copy).
# scripts/recreate_bootstrap.py leaves `tool-provenance.json` in the stage it
# builds: which stage0 the build started from and every shipped tool bound to
# the x.py artifact it was copied from. It is stage content, so the copy carries
# it into the seal and artifact_content_sha256 covers it; until 2026-10-12
# nothing here opened it, and three seed-built seals of that day say only
# `stage0_lineage=absent` (scripts/lib/stage_receipt_provenance.py tells it whole).
#
# Prints the PROVENANCE lines for the receipt of the toolchain at $1, whose
# compiler reports commit $2: `stage_receipt=absent` when it carries none. FAILS,
# with the reason on stderr and nothing on stdout, for a receipt that is present
# and malformed, that its own writer rejected, or that is not this tree's (a
# recorded file hash or the commit differs). So a caller captures it before it
# writes anything, as with the content identity above.
prov_stage_receipt() {
	if [[ -n "$STAGE_PROVENANCE_RECEIPT" && "$1" == "$SRC" ]]; then
		python3 -B "$PROMOTER_ROOT/scripts/lib/stage_receipt_provenance.py" "${STAGE_PROVENANCE_ARGS[@]}" --source-root "$REPO" "$1" "$2"
	elif [[ -n "$FRONTEND_COMPONENT" && ( "$1" != "$SRC" || "$PROVENANCE_ONLY" -eq 1 ) ]]; then
		local component="$1/FRONTEND-COMPONENT.json"
		[[ "$PROVENANCE_ONLY" -eq 1 ]] && component="$FRONTEND_COMPONENT"
		python3 -B "$PROMOTER_ROOT/scripts/lib/stage_receipt_provenance.py" --frontend-component "$component" --frontend-component-sha256 "$FRONTEND_COMPONENT_SHA" "$1" "$2"
	else
		python3 -B "$PROMOTER_ROOT/scripts/lib/stage_receipt_provenance.py" "$1" "$2"
	fi
}

# --require-llvm-identity: does the toolchain at $1 (compiler commit $2) STATE
# which LLVM it carries? Asked only of a stage whose receipt prov_stage_receipt
# accepted. Succeeds silently; fails with the reason on stderr for a stage with
# no receipt, a receipt with no `llvm_identity` record, and a record that does
# not state the identity. The status word is no part of the question: a receipt
# is internal-release-ready on its source and seed lineage whether or not its
# LLVM is stated (scripts/lib/stage_receipt_provenance.py), which is why the
# requirement is a flag of its own.
prov_require_llvm_identity() {
	if [[ -n "$STAGE_PROVENANCE_RECEIPT" ]]; then
		python3 -B "$PROMOTER_ROOT/scripts/lib/stage_receipt_provenance.py" --require-llvm-identity "${STAGE_PROVENANCE_ARGS[@]}" --source-root "$REPO" "$1" "$2" >/dev/null
	elif [[ -n "$FRONTEND_COMPONENT" && ( "$1" != "$SRC" || "$PROVENANCE_ONLY" -eq 1 ) ]]; then
		local component="$1/FRONTEND-COMPONENT.json"
		[[ "$PROVENANCE_ONLY" -eq 1 ]] && component="$FRONTEND_COMPONENT"
		python3 -B "$PROMOTER_ROOT/scripts/lib/stage_receipt_provenance.py" --require-llvm-identity --frontend-component "$component" --frontend-component-sha256 "$FRONTEND_COMPONENT_SHA" "$1" "$2" >/dev/null
	else
		python3 -B "$PROMOTER_ROOT/scripts/lib/stage_receipt_provenance.py" --require-llvm-identity "$1" "$2" >/dev/null
	fi
}

prov_selected_receipt_action() {
	python3 -B - "$PROMOTER_ROOT/scripts/lib/stage_receipt_provenance.py" "$1" "$SRC" "${COMMIT:-}" "$REPO" "$STAGE_PROVENANCE_RECEIPT" "$STAGE_PROVENANCE_SHA" "$DEST" <<'PY'
from pathlib import Path
import sys
reader = Path(sys.argv[1])
namespace = {'__name__': 'promotion_receipt_copy', '__file__': str(reader)}
exec(compile(reader.read_bytes(), str(reader), 'exec'), namespace)
if sys.argv[2] == 'check':
    namespace['check_receipt_destination'](Path(sys.argv[3]), Path(sys.argv[6]), Path(sys.argv[8]))
elif sys.argv[2] == 'copy':
    namespace['copy_selected_receipt'](Path(sys.argv[3]), sys.argv[4], Path(sys.argv[5]),
                                       Path(sys.argv[6]), sys.argv[7], Path(sys.argv[8]))
else:
    raise ValueError('unknown selected receipt action')
PY
}

# What a --require-llvm-identity refusal says after its reason. $1: the stage2.
llvm_identity_refusal() {
	cat <<REFUSAL
REFUSED (--require-llvm-identity): this stage2 does not state which LLVM it carries (the reason is above) — nothing was copied.

    x.py rebuilds the in-tree LLVM when HEAD:src/llvm-project moves from
    the tree recorded beside it, but it keeps an LLVM that cannot say what
    it was built from (one built before that record, whose own build header
    names no commit this checkout has), and a change to src/bootstrap,
    src/version, the bootstrap config or the native tools rebuilds none,
    so a stage2 built in a reused build directory can carry an LLVM built
    from other sources or with another recipe. The recreator records
    what it could establish in the stage receipt (\`llvm_identity\`),
    and states the identity only of an LLVM it watched being built from
    nothing, or of one whose directory carries the record of such a build
    for the same LLVM sources, bootstrap config and native tools. It
    never states an LLVM linked through --llvm-config (mode external): for
    that claim the stage must be built without --llvm-config.

    Options:
      * Build the stage so that it states it. With the flag the recreator
        refuses before x.py starts when it could not, and names the command
        (one LLVM build from nothing in that build directory):
            cd $REPO && python3 scripts/recreate_bootstrap.py --stage 2 --require-seed --fresh-seed --no-register --require-llvm-identity
      * Seal it without the claim: drop --require-llvm-identity. PROVENANCE
        then says what the receipt says (stage_receipt_llvm_identity=not-stated,
        stage_receipt_llvm=not-recorded, or stage_receipt=absent).
      * Ask again without sealing anything:
            scripts/promote-toolchain.sh --provenance --require-llvm-identity $1
REFUSAL
}

# (c) What promote CAN check at seal time, plus (a) if a build stamp is there.
prov_classify() {
	local src="$1" rec checked state changed tracked untracked diff
	PROV_RECORD=""
	PROV_CENSUS_SCOPE=""
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
	if ! checked="$(prov_validated_record "$rec" "$COMMIT")"; then
		PROV_CLASS=UNVERIFIED-PROVENANCE
		PROV_REASON="unusable build stamp at $rec: $checked"
		return 0
	fi
	PROV_RECORD="$rec"
	IFS=$'\t' read -r state changed tracked untracked diff PROV_CENSUS_SCOPE <<<"$checked"
	if [[ "$state" == clean && "$changed" == no ]] && ! prov_has_recursive_scope; then
		PROV_CLASS=UNVERIFIED-PROVENANCE
		PROV_REASON="historical v1 build stamp is readable but observes only top-level submodules; recursive source admission is unavailable"
	elif [[ "$state" == clean && "$changed" == no ]]; then
		PROV_CLASS=BUILD-STAMPED-CLEAN
		PROV_REASON="the build tree was clean at $COMMIT when the build started, and unchanged when it finished"
	else
		PROV_CLASS=BUILD-STAMPED-DIRTY
		if [[ "$changed" == "YES" ]]; then
			PROV_REASON="the build tree CHANGED while the build was running (start/end fingerprints differ), so no single commit describes what was compiled"
		else
			PROV_REASON="the build tree was DIRTY at $COMMIT: $tracked tracked + $untracked untracked change(s), diff sha256 $diff"
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

# Every mode but --provenance starts the compiler. Ask once, here, whether this
# run can start anything at all (see serial_precondition), and whether it may
# run a program it builds in its scratch directory (see scratch_precondition).
[[ "$PROVENANCE_ONLY" -eq 1 ]] || { serial_precondition; scratch_precondition; }

# `--gate-only` mutates nothing, so it deliberately runs before (and without)
# the mid-build guard below: it is the read-only way to ask whether an
# already-sealed artifact — including the one the channel serves right now —
# still passes this tree's tests.
if [[ "$GATE_ONLY" -eq 1 ]]; then
	[[ -x "$SRC/bin/trustc" ]] || die "no trustc in $SRC/bin — nothing to gate"
	# Every gate runs, including when an earlier gate failed.
	GATE_UI=passed
	GATE_START=passed
	GATE_PRIVATE=passed
	GATE_NATIVE=passed
	# 2 is a gate with a row the serial executor would not start: said as
	# NOT RUN, never as FAILED, and refused all the same.
	GATE_RC=0; ui_gate "$SRC" || GATE_RC=$?
	case "$GATE_RC" in 0) ;; 2) GATE_UI='NOT RUN (the serial executor refused)' ;; *) GATE_UI=FAILED ;; esac
	GATE_RC=0; tool_start_gate "$SRC" || GATE_RC=$?
	case "$GATE_RC" in 0) ;; 2) GATE_START='NOT RUN (the serial executor refused)' ;; *) GATE_START=FAILED ;; esac
	(native_linker_surface "$SRC" 'gate-only SDK') || GATE_NATIVE=FAILED
	#   The paired surface is bin/rust-lld and bin/dsymutil of a Darwin host.
	#   On any other host native_linker_surface returns before it checks
	#   anything, and this line used to read "passed" all the same.
	GATE_HOST="$("$SRC/bin/trustc" -vV 2>/dev/null | sed -n 's/^host: //p' | head -1 || true)"
	GATE_NATIVE_PASS='and the paired native-tool surface'
	if [[ "$GATE_NATIVE" == passed && "$GATE_HOST" != *-apple-darwin ]]; then
		GATE_NATIVE="not applicable (host ${GATE_HOST:-unknown} is not Darwin; nothing was checked)"
		GATE_NATIVE_PASS="(the paired native-tool surface is a Darwin check; host ${GATE_HOST:-unknown} has none and nothing was checked)"
	fi
	#   A Darwin SDK with neither tool is the recorded gap above, and this line
	#   must not read "passed" for it either: nothing started, nothing was checked.
	if [[ "$GATE_NATIVE" == passed && ! -e "$SRC/bin/rust-lld" && ! -L "$SRC/bin/rust-lld" \
			&& ! -e "$SRC/bin/dsymutil" && ! -L "$SRC/bin/dsymutil" ]]; then
		GATE_NATIVE='ABSENT (recorded, not refused: this SDK has no bin/rust-lld and no bin/dsymutil; nothing was checked)'
		GATE_NATIVE_PASS='(the paired native-tool surface is ABSENT and recorded: this SDK has no bin/rust-lld and no bin/dsymutil, so native elastic linking is unavailable in it; nothing was checked)'
	fi
	#   bin/rust-lld alone is the recorded half: the linker started, the pair did not pass.
	if [[ "$GATE_NATIVE" == passed && "$GATE_HOST" == *-apple-darwin && -f "$SRC/bin/rust-lld" \
			&& ! -e "$SRC/bin/dsymutil" && ! -L "$SRC/bin/dsymutil" ]]; then
		GATE_NATIVE='PARTIAL (recorded, not refused: bin/rust-lld starts, this SDK has no bin/dsymutil)'
		GATE_NATIVE_PASS='(the paired native-tool surface is PARTIAL and recorded: bin/rust-lld starts and there is no bin/dsymutil, so native elastic debug linking is unavailable in it)'
	fi
	PROBE_DIR="$(scratch -d)" || die "rustc-dev gate: could not create a scratch directory"
	GATE_RC=0; rustc_dev_probe "$SRC" "$PROBE_DIR" || GATE_RC=$?
	case "$GATE_RC" in
		0) rm -rf "${PROBE_DIR:?}" ;;
		2) GATE_PRIVATE='NOT RUN (the serial executor refused)' ;;
		*) GATE_PRIVATE=FAILED ;;
	esac
	[[ "$GATE_RC" -eq 0 ]] || printf '    the rustc-dev probe: its source and everything it printed are kept in %s\n' "$PROBE_DIR" >&2
	if [[ "$GATE_UI" == passed && "$GATE_START" == passed && "$GATE_PRIVATE" == passed && "$GATE_NATIVE" != FAILED ]]; then
		say "gate-only: PASS — $SRC would clear the pre-promotion UI gate and the tool-start gate and the native rustc-dev gate $GATE_NATIVE_PASS"
		exit 0
	fi
	die "gate-only: REFUSED — $SRC: UI gate $GATE_UI, tool-start gate $GATE_START, native rustc-dev gate $GATE_PRIVATE, paired native-tool surface $GATE_NATIVE (see the rows above)"
fi

# `--provenance` is read-only too. On an ALREADY-SEALED artifact it prints the
# PROVENANCE the seal carries; on a build tree's stage2 it prints the class that
# stage2 WOULD be sealed as. Both without sealing, flipping or mutating anything.
if [[ "$PROVENANCE_ONLY" -eq 1 ]]; then
	if [[ -r "$SRC/PROVENANCE" ]]; then
		if [[ -n "$FRONTEND_COMPONENT" ]]; then
			VERBOSE="$(trustc_answer "$SRC/bin/trustc" -vV "the commit this sealed compiler was built from is not known")" || exit 1
			COMMIT="$(printf '%s\n' "$VERBOSE" | sed -n 's/^commit-hash: //p' | head -1)"
			prov_stage_receipt "$SRC" "$COMMIT" >/dev/null || die "explicit installed frontend provenance refused"
			grep -qx "supplementary_frontend_sha256=$FRONTEND_COMPONENT_SHA" "$SRC/PROVENANCE" \
				|| die "stored provenance does not bind this explicit frontend"
		fi
		cat "$SRC/PROVENANCE"
		# Of a sealed artifact the question is asked of the record it carries.
		if [[ "$REQUIRE_LLVM" -eq 1 ]] && ! grep -qx 'stage_receipt_llvm_identity=stated' "$SRC/PROVENANCE"; then
			SEALED_LLVM_LINES="$(grep -E '^stage_receipt(_llvm|_llvm_identity|_llvm_provenance)?=' "$SRC/PROVENANCE" | tr '\n' ' ' || true)"
			die "REFUSED (--require-llvm-identity): the PROVENANCE of $SRC does not say stage_receipt_llvm_identity=stated.

    It says: ${SEALED_LLVM_LINES:-no stage_receipt line at all (it was sealed before promotion recorded the stage receipt)}
    A seal is never rewritten: one that states its LLVM is a new seal, of a
    stage built with \`recreate_bootstrap.py --require-llvm-identity\`."
		fi
		exit 0
	fi
	[[ -x "$SRC/bin/trustc" ]] || die "no trustc in $SRC/bin and no PROVENANCE file — nothing to report"
	VERBOSE="$(trustc_answer "$SRC/bin/trustc" -vV "the commit this compiler was built from is not known and there is nothing to report")" || exit 1
	COMMIT="$(printf '%s\n' "$VERBOSE" | sed -n 's/^commit-hash: //p' | head -1)"
	[[ -n "$COMMIT" ]] || die "this trustc reports no commit-hash at all; its -vV said:
$(printf '%s\n' "$VERBOSE" | sed -n '1,8s/^/        | /p')"
	say "no PROVENANCE file in $SRC — reporting what it would be sealed as"
	prov_classify "$SRC"
	prov_report
	printf '\n'
	prov_artifact_fingerprint "$SRC" || die "cannot compute the content identity of $SRC (see the error above)"
	printf '\n'
	prov_stage_receipt "$SRC" "$COMMIT" || die "$SRC carries a stage receipt promotion would REFUSE to seal (the reason is above)"
	if [[ "$REQUIRE_LLVM" -eq 1 ]]; then
		prov_require_llvm_identity "$SRC" "$COMMIT" || die "$(llvm_identity_refusal "$SRC")"
	fi
	exit 0
fi

# 1. Refuse to snapshot a half-swapped tree. An x.py run in flight leaves bin/
#    and the stdlib empty or partial; snapshotting that ships a toolchain that
#    cannot compile (or cannot verify).
#
#    Ask the KERNEL, not the process table. bootstrap try_lock()s `$out/lock`
#    for the whole build (src/bootstrap/src/bin/main.rs), so a non-blocking
#    flock on the CANDIDATE's lock answers the question exactly: held = a build
#    is writing its build directory. Command-line matching cannot: `$REPO` is a
#    PREFIX of a sibling checkout (~/trust vs ~/trust-ay-scc), so a substring
#    match reads another agent's concurrent build as our own and blocks
#    promotion indefinitely — measured 2026-09-14, when a bootstrap under
#    /tmp/ay-trust-all-on refused a seal whose own build had completed cleanly
#    minutes earlier. The lock is per-build-dir, so that confusion is not
#    expressible. An explicit stage can belong to another checkout or a custom
#    build directory; the script's own build/ does not protect that stage.
#    Resolve stage symlinks before walking <build>/<host>/stage2 upwards.
SRC="$(cd "$SRC" && pwd -P)" || die "cannot resolve candidate stage directory"
BUILD_DIR="$(dirname "$(dirname "$SRC")")"
#
#    Three answers, not two. Any failure of the probe used to be read as
#    "held": a lock file this user cannot open, and an interpreter that is not
#    there, were both reported as a build in flight that waiting would clear.
if [[ -f "$BUILD_DIR/lock" ]]; then
	LOCK_RC=0
	LOCK_SAID="$(/usr/bin/python3 -c '
import fcntl, sys
try:
    fh = open(sys.argv[1], "a")
    fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    sys.exit(3)
except OSError as error:
    sys.exit(f"{type(error).__name__}: {error}")
sys.exit(0)' "$BUILD_DIR/lock" 2>&1)" || LOCK_RC=$?
	case "$LOCK_RC" in
		0) ;;
		3) die "an x.py/bootstrap build holds $BUILD_DIR/lock — wait for it to finish (a mid-build stage2 is incomplete by definition)" ;;
		*) die "could not ask whether a build holds $BUILD_DIR/lock (the probe exited $LOCK_RC): ${LOCK_SAID:-it printed nothing}

    That is no answer, so nothing was copied. It is not a build in flight, and
    waiting will not clear it: the probe is /usr/bin/python3 opening that file
    for append and asking for a non-blocking exclusive flock." ;;
	esac
fi
#    Use the build's complete output contract, including runnable tools,
#    confined byte-identical rustc/cargo/rustdoc aliases, and forbidden names.
#    Promotion requires the full surface; ambient narrow-build waivers cannot
#    turn a missing backend, formatter, linter, or analyzer into a valid seal.
verify_surface "$SRC" stage2
#    find's own status is kept: a directory under lib/rustlib it cannot read, or
#    one that goes away under it, is refused here, before the first `cp`. (This
#    was a pipeline under pipefail in a plain assignment: it stopped the run at
#    the same place, without a word.)
STD_ERR="$(scratch)" || die "could not create a scratch file to list the stdlib rlibs"
STD_RC=0
STD_LIST="$(find "$SRC/lib/rustlib" -name 'libstd-*.rlib' 2>"$STD_ERR")" || STD_RC=$?
if [[ "$STD_RC" -ne 0 ]]; then
	STD_SAID="$(sed -n '1,3s/^/        | /p' "$STD_ERR")"; rm -f "$STD_ERR"
	die "could not list the stdlib rlibs under $SRC/lib/rustlib: find exited $STD_RC, so nothing was copied. It said:
${STD_SAID:-        | (it printed nothing)}"
fi
rm -f "$STD_ERR"
[[ -n "$STD_LIST" ]] || die "stage2 has no stdlib rlibs — the uplift did not finish"

# 1b. IDENTITY, read before anything is spent on this candidate. This block used
#     to sit AFTER the UI gate; it moved up because the gate runs THIS TREE's
#     tests against the candidate, and a candidate whose rev is not this tree's
#     is being graded with the wrong tests. Establish who the artifact claims to
#     be first, then decide whether that claim is worth anything (1c), then test
#     it (1d).
VERSION_SAID="$(trustc_answer "$SRC/bin/trustc" --version "this stage2 has no readable identity; nothing was copied")" || exit 1
REV="$(printf '%s\n' "$VERSION_SAID" | sed -n 's/.*(\([0-9a-f]\{9\}\) .*/\1/p')"
[[ -n "$REV" ]] || die "could not read the rev out of trustc --version, which said: ${VERSION_SAID:-(nothing)}"
SHORT="${REV:0:8}"
DEST="$ROOT/trust-$SHORT"

#     A directory with no PROVENANCE file is not a seal this script finished:
#     every refusal after the copy step leaves one, and the re-run used to be
#     told only that artifacts are immutable.
[[ ! -e "$DEST" || -e "$DEST/PROVENANCE" ]] || die "artifact $DEST already exists and holds no PROVENANCE file.

    It is not a seal this script wrote to the end. It is either the copy a
    promotion left behind when it was refused after its copy step (that run's
    own message said why), or a seal older than the PROVENANCE record. Nothing
    is ever overwritten here: remove it deliberately, then promote again."
[[ -e "$DEST" ]] && die "artifact $DEST already exists — artifacts are IMMUTABLE (a published one is shipped provenance). Remove it deliberately if it was never published."
if [[ -n "$STAGE_PROVENANCE_RECEIPT" ]]; then
	prov_selected_receipt_action check || die "accepted receipt destination overlaps the original stage or evidence; nothing was copied"
fi

VERBOSE="$(trustc_answer "$SRC/bin/trustc" -vV "the commit this stage2 was built from is not known; nothing was copied")" || exit 1
COMMIT="$(printf '%s\n' "$VERBOSE" | sed -n 's/^commit-hash: //p' | head -1)"
[[ -n "$COMMIT" ]] || die "stage2's trustc does not report a commit-hash, so no private sysroot can be matched to it"

#     A rev this repository has never heard of makes the seal's whole name
#     meaningless — `trust-<rev>` would point at nothing, and every ancestry
#     question asked of it later would error rather than answer. Unambiguous, so
#     it is a hard refusal with no waiver.
COMMIT_SAID="$(git -C "$REPO" cat-file -e "${COMMIT}^{commit}" 2>&1)" || die "this stage2 reports commit-hash $COMMIT, which is NOT a commit in $REPO.

    The seal would be named after a revision this repository cannot resolve, so
    nothing could ever check what is in it. Either this stage2 came from a
    different repository, or the commit was never pushed and has since been
    garbage-collected. Fetch the commit, or rebuild here.

    git said: ${COMMIT_SAID:-(nothing)}
    If that is not about the commit (not a repository, an ownership refusal),
    the fault is in reading $REPO and not in this stage2."

# 1b'. STAGE0 LINEAGE (--lineage). The build stamp says which SOURCE was
#      compiled; nothing in it says which COMPILER compiled it, and every seal
#      before 2026-09-29 was bootstrapped from stock rustc through the genesis
#      adapter without a word in its PROVENANCE (audit TB-7/TP-5). A staircase
#      lineage record answers that, and it is only worth sealing if it names
#      THIS stage2: its commit and the exact bytes of its driver and trustc.
LINEAGE_SHA256=""
LINEAGE_SUMMARY=""
if [[ -n "$LINEAGE" ]]; then
	[[ -f "$LINEAGE" && ! -L "$LINEAGE" && -r "$LINEAGE" ]] \
		|| die "--lineage $LINEAGE is not a readable regular file"
	LINEAGE_SUMMARY="$(python3 - "$LINEAGE" "$SRC" "$COMMIT" 2>&1 <<'PY'
import glob, hashlib, json, sys
path, src, commit = sys.argv[1:4]
def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()
try:
    rec = json.load(open(path))
except ValueError as e:
    sys.exit(f"not JSON: {e}")
if rec.get("schema") != "trust-seed-staircase-v1" or rec.get("kind") != "lineage":
    sys.exit("not a trust-seed-staircase-v1 lineage record")
final = rec.get("final") or {}
drivers = sorted(glob.glob(src + "/lib/librustc_driver-*"))
if len(drivers) != 1:
    sys.exit(f"stage2 ships {len(drivers)} librustc_driver files")
want = {"commit": commit, "trustc_sha256": sha(src + "/bin/trustc"), "driver_sha256": sha(drivers[0])}
for key, value in want.items():
    if final.get(key) != value:
        sys.exit(f"final.{key} is {final.get(key)!r}; this stage2 has {value}")
rungs = rec.get("rungs") or []
root = (rec.get("root") or {}).get("commit", "")
if not rungs or not root:
    sys.exit("the record names no root seed or no rungs")
ddc = rec.get("ddc")
if ddc is None:
    ddc_note = "ddc=none"
elif ddc.get("verdict") in ("identical", "compiler-and-std-identical"):
    ddc_note = f"ddc={ddc['verdict']} relation={ddc.get('relation')} seed={str((ddc.get('ddc_seed') or {}).get('commit'))[:10]}"
else:
    sys.exit(f"its double compile says {ddc.get('verdict')!r}: the compiler or std differ between the two lineages")
# A pinned root seed (a Linux extraction, root.admission.pinned_seed) is admitted by
# a host record of the seed ledger, which seed_staircase.py build_lineage reads into
# root.pin_admission. Without it the record does not say which kind admitted the
# root, or whether that kind discloses an unpinned root; with it, the summary says.
import re
word = lambda value: isinstance(value, str) and re.fullmatch(r"[a-z0-9][a-z0-9-]*", value) is not None
admission = (rec.get("root") or {}).get("admission")
pin = (rec.get("root") or {}).get("pin_admission")
pinned = isinstance(admission, dict) and "pinned_seed" in admission
pin_note = ""
if pinned and not isinstance(pin, dict):
    sys.exit("its root is a pinned seed and it records no root.pin_admission: which host record admitted "
             "that seed is unread (scripts/seed_staircase.py build_lineage writes it)")
# What a fixed point discloses is fixed words (scripts/seed_fixed_point.py DISCLOSURE
# and STOCK_ANCESTOR, the same four scripts/lib/stage_receipt_provenance.py holds in
# FIXED_POINT_DISCLOSED): a disclosure that says anything else contradicts its kind.
fixed_point_disclosed = {"root": "unpinned-host-chain", "predecessor_pin": "none",
                         "double_compile_diverse": "false", "stock_built_ancestor": "inferred-no-receipt"}
if pin is not None:
    # A pinned root with a pin_admission that is not a table stopped above.
    if not pinned:
        sys.exit("it records root.pin_admission for a root that is not a pinned seed")
    if not word(pin.get("kind")):
        sys.exit(f"root.pin_admission.kind is {pin.get('kind')!r}, not an admission kind")
    pin_note = f" pin_admission={pin['kind']}"
    disclosure = pin.get("root_disclosure")
    fixed_point = pin["kind"] == "fixed-point-unpinned-root"
    if disclosure is None and fixed_point:
        sys.exit("root.pin_admission is a fixed point and carries no root_disclosure")
    if disclosure is not None and not fixed_point:
        sys.exit(f"root.pin_admission is kind {pin['kind']} and carries a root_disclosure, which only a "
                 "fixed point (fixed-point-unpinned-root) is admitted with")
    if disclosure is not None:
        if not isinstance(disclosure, dict):
            sys.exit("root.pin_admission.root_disclosure is not a table")
        for key, value in fixed_point_disclosed.items():
            if not word(disclosure.get(key)):
                sys.exit(f"root.pin_admission.root_disclosure.{key} is {disclosure.get(key)!r}, not a word")
            if disclosure[key] != value:
                sys.exit(f"root.pin_admission.root_disclosure.{key} is {disclosure[key]!r}; a fixed point is "
                         f"admitted only with {value}")
        for key in ("root", "predecessor_pin", "stock_built_ancestor"):
            pin_note += f" {key}={disclosure[key]}"
print(f"root={root} rungs={len(rungs)} " + " -> ".join(r.get("commit", "?")[:10] for r in rungs) + f" {ddc_note}{pin_note}")
PY
)" || die "--lineage $LINEAGE does not describe this stage2: $LINEAGE_SUMMARY"
	LINEAGE_SHA256="$(prov_sha256 "$LINEAGE")"
	say "stage0 lineage: $LINEAGE_SUMMARY"
fi

# 1b''. THE STAGE RECEIPT. A stage2 the recreator built says, in its own
#       tool-provenance.json, which stage0 it was built from. That is the answer
#       a seed-built seal owes its reader, and it is worth a line in PROVENANCE
#       only if it is THIS stage2's: checked here, before the first `cp`, so a
#       receipt that cannot be recorded leaves no artifact directory behind.
#       Step 6b reads it again from the sealed copy.
STAGE_RECEIPT="$(prov_stage_receipt "$SRC" "$COMMIT")" || die "REFUSED: $SRC/tool-provenance.json is a stage receipt that cannot be recorded (the reason is above) — nothing was copied.

    That file is what scripts/recreate_bootstrap.py writes about a stage it
    built. One that is malformed, that its own writer rejected, or whose
    recorded hashes or commit are not this stage2's describes some other build,
    and a seal that carried it would quote that build's lineage as its own.

    Options:
      * Rebuild through the recreator, which writes the receipt of what it builds:
            cd $REPO && python3 scripts/recreate_bootstrap.py --stage 2 --require-seed --fresh-seed --no-register
      * If this stage2 was rebuilt or changed after the receipt was written (a
        plain x.py build, a tool replaced by hand), the receipt is stale. Remove
        it deliberately; the seal will then say \`stage_receipt=absent\`:
            rm $SRC/tool-provenance.json
      * Ask again without sealing anything:
            scripts/promote-toolchain.sh --provenance $SRC"
if [[ "$STAGE_RECEIPT" == stage_receipt=absent ]]; then
	say "stage receipt: none in this stage2 (the seal will say stage_receipt=absent)"
else
	receipt_line() { printf '%s\n' "$STAGE_RECEIPT" | sed -n "s/^stage_receipt_$1=//p"; }
	say "stage receipt: tool-provenance.json names this stage2's commit and files (status $(receipt_line status), lineage mode $(receipt_line lineage_mode), $(receipt_line files_verified) recorded file hashes verified)"
fi
# --require-llvm-identity, before the first `cp` as well. Asked of the candidate
# only: step 6b holds the sealed copy's receipt lines to the candidate's, and
# the answer is a function of those lines.
if [[ "$REQUIRE_LLVM" -eq 1 ]]; then
	prov_require_llvm_identity "$SRC" "$COMMIT" || die "$(llvm_identity_refusal "$SRC")"
	say "LLVM identity: stated by the stage receipt (--require-llvm-identity)"
fi

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

if [[ "$REQUIRE_PROV" == 1 ]] && {
    [[ "$PROV_CLASS" == UNVERIFIED-PROVENANCE ]] || ! prov_has_recursive_scope;
}; then
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
GATE_RC=0; ui_gate "$SRC" || GATE_RC=$?
[[ "$GATE_RC" -ne 2 ]] || gate_not_run "the UI gate on the stage2 at $SRC" "refusing to seal it; nothing was copied"
[[ "$GATE_RC" -eq 0 ]] || die "stage2 at $SRC FAILS this tree's named UI tests (listed above) — refusing to seal it.

    A promoted toolchain that fails the compiler's own checked-in tests is
    exactly how the stale seal shipped for 322 commits without anyone
    noticing. Each FAIL row says what the compiler printed. Where that is the
    compiler's own diagnosis, fix the compiler, or rebuild:
        cd $REPO && python3 x.py build --stage 2 -j 8
    A row that quotes no compiler diagnostic (a compiler that was killed, or
    could not be loaded) is a fault to find before blaming the source: all
    that each row printed is kept in the directory named above.
    To inspect any toolchain without promoting anything:
        scripts/promote-toolchain.sh --gate-only <toolchain-dir>"

# 1e. rustc-dev, asked of the candidate BEFORE the first `cp` (as 1d is), so a
#     stage2 without the closure leaves no artifact directory behind; a refusal
#     after the copy leaves `$DEST` sealed on disk and every re-run then stops
#     at "artifacts are IMMUTABLE". Step 6 asks again of the sealed copy.
#     Why the closure is required: see step 6.
PROBE_DIR="$(scratch -d)" || die "rustc-dev gate: could not create a scratch directory"
GATE_RC=0; rustc_dev_probe "$SRC" "$PROBE_DIR" || GATE_RC=$?
[[ "$GATE_RC" -ne 2 ]] || printf '    the rustc-dev probe: its source and everything it printed are kept in %s\n' "$PROBE_DIR" >&2
[[ "$GATE_RC" -ne 2 ]] || gate_not_run "the rustc-dev gate on the stage2 at $SRC" "refusing to seal it; nothing was copied"
[[ "$GATE_RC" -eq 0 ]] || die "stage2 at $SRC cannot build a rustc_private consumer from its own sysroot (rustc_driver, rustc_middle, rustc_public, rustc_public_bridge) — trust-mc could not build on this channel; nothing was copied.

    The probe said why above. Its source and everything it printed are kept in
    $PROBE_DIR"
rm -rf "${PROBE_DIR:?}"

# 1f. Can its shipped tools START? Asked of the candidate before the first `cp`,
#     for the reason 1d and 1e are: a refusal here leaves no artifact directory
#     behind. Step 6 asks again of the sealed copy. See the block above the
#     rows for why the output contract's `--version` probes could not see a
#     tippy that dies on every invocation.
GATE_RC=0; tool_start_gate "$SRC" || GATE_RC=$?
[[ "$GATE_RC" -ne 2 ]] || gate_not_run "the tool-start gate on the stage2 at $SRC" "refusing to seal it; nothing was copied"
[[ "$GATE_RC" -eq 0 ]] || die "stage2 at $SRC ships a tool that CANNOT START (rows above) — refusing to seal it; nothing was copied.

    Every tool here answered \`--version\`; that is not a start. If the failing
    rows are tippy's and the message is \"duplicate symbols in the rustc symbol
    list and the extra symbols added by the driver\", a string was added to
    compiler/rustc_span/src/symbol.rs that a driver's own list still names:
        python3 scripts/check_driver_extra_symbols.py
    names it from source, with no build. Fix the tree and rebuild:
        cd $REPO && python3 x.py build --stage 2 -j 8
    To ask any toolchain the same question without promoting anything:
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
#    Started by its absolute path (the serial executor starts no other), with
#    what it printed kept: under `set -e` a failure here used to end the script
#    with no line at all.
LIBDIR_SAID="$(scratch)" || die "could not create a scratch file"
TARGET_LIBDIR="$(serial_command "$(cd "$SRC" && pwd -P)/bin/trustc" --print target-libdir 2>"$LIBDIR_SAID")" \
	|| { LIBDIR_RC=$?
		LIBDIR_REFUSED="$(serial_refusal "$LIBDIR_RC" "$LIBDIR_SAID")" || LIBDIR_REFUSED=""
		LIBDIR_WHY="$(gate_said "$LIBDIR_SAID")"; rm -f "$LIBDIR_SAID"
		[[ -z "$LIBDIR_REFUSED" ]] || step_not_run "\`trustc --print target-libdir\` on the stage2 at $SRC" "nothing was copied" "$LIBDIR_REFUSED"
		die "\`trustc --print target-libdir\` failed on the stage2 at $SRC (exit $LIBDIR_RC): $LIBDIR_WHY"; }
rm -f "$LIBDIR_SAID"
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

# Supplementary native tools are a separately observed component, never a claim
# that the original immutable mint built files it did not contain.
if [[ -n "$NATIVE_TOOLS" ]]; then
	python3 -B "$PROMOTER_ROOT/scripts/native_sdk_tools.py" validate \
		--source-root "$REPO" --stage "$SRC" --commit "$COMMIT" \
		${STAGE_PROVENANCE_ARGS[@]+"${STAGE_PROVENANCE_ARGS[@]}"} \
		--record "$NATIVE_TOOLS" --sha256 "$NATIVE_TOOLS_SHA" \
		|| die "paired native tools failed source/origin/runtime qualification; nothing was copied"
fi

# A prepared frontend is an explicit separately built component. It permits
# only installation into this new copy, never stage/runtime qualification.
if [[ -n "$FRONTEND_COMPONENT" ]]; then
	python3 -B "$PROMOTER_ROOT/scripts/sdk_frontend_component.py" validate \
		--record "$FRONTEND_COMPONENT" --sha256 "$FRONTEND_COMPONENT_SHA" \
		--source-root "$REPO" --stage "$SRC" --compiler-source "$COMMIT" \
		|| die "prepared frontend source/build/transport identity refused; nothing was copied"
fi

# 3. Copy (APFS clone where possible — near-free and atomic per-file).
say "sealing $SRC -> $DEST (rev $REV)"
mkdir -p "$ROOT"
cp -ac "$SRC" "$DEST" 2>/dev/null || cp -a "$SRC" "$DEST"
if [[ -n "$STAGE_PROVENANCE_RECEIPT" ]]; then
	prov_selected_receipt_action copy || die "accepted stage receipt could not be carried into the new seal"
fi
if [[ -n "$LINEAGE" ]]; then
	cp "$LINEAGE" "$DEST/STAGE0-LINEAGE"
	[[ "$(prov_sha256 "$DEST/STAGE0-LINEAGE")" == "$LINEAGE_SHA256" ]] \
		|| die "the lineage record changed while it was being sealed"
fi

# Bootstrap exposes rust-src through an absolute symlink to the live checkout.
# Freeze those sources at the compiler's recorded revision BEFORE the general
# escaping-link pass, which otherwise correctly drops these live source links.
# Never traverse a copied directory symlink while replacing those entries:
# pruning runs later, and such a parent could redirect writes outside the seal.
for source_parent in "$DEST/lib" "$DEST/lib/rustlib" \
	"$DEST/lib/rustlib/src" "$DEST/lib/rustlib/rustc-src"; do
	[[ ! -L "$source_parent" && ( ! -e "$source_parent" || -d "$source_parent" ) ]] \
		|| die "source snapshot parent is not a real directory: $source_parent"
done
SOURCE_ENTRY="$DEST/lib/rustlib/src/rust"
if [[ -L "$SOURCE_ENTRY" ]]; then
	say "sealing compiler and standard-library sources at $COMMIT"
	rm "$SOURCE_ENTRY"
	mkdir -p "$SOURCE_ENTRY"
	# The standard library also takes two Trust leaves and LLVM libunwind from
	# outside library/. Freeze those exact committed inputs and normalize only
	# the leaves' workspace-dependent manifests by the existing trust-src rules.
	"${TRUST_TOOLCHAIN_PYTHON3:-python3}" "$REPO/scripts/freeze_toolchain_sources.py" \
		"$REPO" "$COMMIT" "$SOURCE_ENTRY" \
		|| die "could not freeze the committed compiler/standard-library source closure"
fi
COMPILER_SOURCE_ENTRY="$DEST/lib/rustlib/rustc-src/rust"
if [[ -L "$COMPILER_SOURCE_ENTRY" ]]; then
	[[ -d "$SOURCE_ENTRY/compiler" ]] || die "sealed compiler sources are missing"
	rm "$COMPILER_SOURCE_ENTRY"
	ln -s ../src/rust "$COMPILER_SOURCE_ENTRY"
fi

# 3b. A sealed artifact may not point outside itself. `cp -a` preserves symlinks
#     verbatim, so stage2's `lib/rustlib/rustc-src/rust` — which x.py aims at
#     whatever source tree built it — was copied into every seal and then went
#     stale. Measured on the live roots before this fix:
#
#       trust-6500fd4d -> <agent-session-scratch>/seal-wt                 DANGLING
#       trust-1979a7b8 -> /private/tmp/tcg-p2                             DANGLING
#       trust-ca497bef -> /private/tmp/ice-land                           DANGLING
#       trust-3ae9948d -> ~/trust                                         the MUTABLE dev tree
#
#     Both outcomes defeat sealing. A dangling rustc-src breaks every
#     source-resolving tool; a LIVE one re-attaches the "immutable" artifact to
#     the build tree the seal exists to escape — and trust-6500fd4d is the root
#     the whole constellation resolves through `channel = "trust"`.
#     trust-ir's check_trust_default_authority.py is the one thing that checks
#     this ("sealed sysroot contains a symlinked artifact"), and nothing runs it.
#
#     The two known source links above now resolve to recorded source bytes
#     inside the seal. Drop every remaining escaping link rather than copying
#     arbitrary external contents into the installed compiler's closure.
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

# Copying preserves source permissions, including a developer's umask 0002.
# Authenticated tool discovery requires artifacts that other users cannot write.
chmod -R go-w "$DEST" "$PRIV_DEST"

if [[ -n "$NATIVE_TOOLS" ]]; then
	python3 -B "$PROMOTER_ROOT/scripts/native_sdk_tools.py" install \
		--source-root "$REPO" --stage "$SRC" --commit "$COMMIT" \
		${STAGE_PROVENANCE_ARGS[@]+"${STAGE_PROVENANCE_ARGS[@]}"} \
		--record "$NATIVE_TOOLS" --sha256 "$NATIVE_TOOLS_SHA" --destination "$DEST" \
		|| die "could not bind supplementary native tools into the new seal"
fi

if [[ -n "$FRONTEND_COMPONENT" ]]; then
	python3 -B "$PROMOTER_ROOT/scripts/sdk_frontend_component.py" install \
		--record "$FRONTEND_COMPONENT" --sha256 "$FRONTEND_COMPONENT_SHA" \
		--source-root "$REPO" --stage "$SRC" --compiler-source "$COMMIT" --destination "$DEST" \
		|| die "prepared frontend could not be installed into the new prospective seal"
fi

# 5. Preserve the canonical surface emitted by bootstrap. The copy carries
#    the three supported aliases (rustc, cargo, rustdoc); promotion must not
#    manufacture retired cargo-fmt/cargo-clippy names or repair missing tools.
#    Replay the unwaived contract on the sealed copy before changing a channel.
say "verifying"
verify_surface "$DEST" 'sealed toolchain'

# 6. Verify compilation and the matching private sysroot.
#    What this step writes is deleted when the script reaches one of its two
#    successful ends and KEPT when it stops any other way, a signal included
#    (bash runs this trap on a fatal signal with the last command's status, so
#    the status alone cannot tell): each refusal from here on quotes a line or a
#    few of a file in that directory, and the directory used to be removed with
#    the reason in it.
#    The trap's line goes to the script's own stderr. bash applies the
#    redirections of a shell-function call to the shell itself, and a fatal
#    signal runs the trap with them still in force: the line that names the
#    directory went into the interrupted call's output file, inside that
#    directory. So each redirected function call that step 6 reaches (the three
#    below and the tool-start gate's row) runs in a subshell.
HELLO="$(scratch -d)" || die "could not create a scratch directory for the checks of the sealed copy"
#    Absolute: under a relative TMPDIR `scratch -d` names a relative directory,
#    and this one is named to the caller and recorded as the doctor's CARGO_HOME.
[[ "$HELLO" == /* ]] || HELLO="$PWD/$HELLO"
PROMOTE_FINISHED=0
trap 'PROMOTE_EXIT=$?
if [[ "$PROMOTE_EXIT" -eq 0 && "$PROMOTE_FINISHED" -eq 1 ]]; then rm -rf "$HELLO"
else printf "promote: everything the checks of the sealed copy wrote is kept in %s\n" "$HELLO" >&2; fi' EXIT
printf 'fn main(){println!("ok")}\n' > "$HELLO/h.rs"
STEP_RC=0
#    In a subshell: a signal during the compile must leave the trap the script's own stderr, not h.txt.
( serial_command "$DEST/bin/trustc" --sysroot "$DEST" -Ztrust-verify=off -o "$HELLO/h" "$HELLO/h.rs" ) >"$HELLO/h.txt" 2>&1 || STEP_RC=$?
if [[ "$STEP_RC" -ne 0 ]]; then
	STEP_REFUSED="$(serial_refusal "$STEP_RC" "$HELLO/h.txt")" || STEP_REFUSED=""
	[[ -z "$STEP_REFUSED" ]] || step_not_run "the hello world of the sealed copy at $DEST" "the channel was not moved" "$STEP_REFUSED"
	die "sealed toolchain cannot compile a hello world (exit $STEP_RC): $(gate_said "$HELLO/h.txt")"
fi
HELLO_RC=0
HELLO_SAID="$("$HELLO/h" 2>"$HELLO/h.run-stderr.txt")" || HELLO_RC=$?
[[ "$HELLO_RC" -eq 0 && "$HELLO_SAID" == ok ]] \
	|| die "hello world did not run: the program the sealed compiler built exited $HELLO_RC and printed '${HELLO_SAID:0:140}' (exit 0 and 'ok' were required); it said on stderr: $(gate_said "$HELLO/h.run-stderr.txt")"
#    Two questions, so that a rustc that would not print its help is not
#    reported as one that has no such flag.
STEP_RC=0
#    In a subshell: a signal while it prints must leave the trap the script's own stderr, not zhelp.err.
( serial_command "$DEST/bin/rustc" -Z help ) >"$HELLO/zhelp.txt" 2>"$HELLO/zhelp.err" || STEP_RC=$?
if [[ "$STEP_RC" -ne 0 ]]; then
	STEP_REFUSED="$(serial_refusal "$STEP_RC" "$HELLO/zhelp.err")" || STEP_REFUSED=""
	[[ -z "$STEP_REFUSED" ]] || step_not_run "\`rustc -Z help\` of the sealed copy at $DEST" "the channel was not moved" "$STEP_REFUSED"
	die "the sealed rustc did not print its -Z help (exit $STEP_RC): $(gate_said "$HELLO/zhelp.err")"
fi
grep -q 'trust-verify' "$HELLO/zhelp.txt" \
	|| die "sealed toolchain has no -Ztrust-verify flag — it cannot verify, so it is not a Trust toolchain"

#    The sealed compiler must read rustc-dev from its OWN sysroot, with no
#    overlay. trust-mc names `rustc_public` and the rest of this closure
#    directly; its rustc-wrapper is a pass-through until TRUST_PRIVATE_SYSROOTS
#    is set, so on a seal without this closure every trust-mc build stops at
#    `E0463: can't find crate for rustc_public`. A local `x.py build --stage 2`
#    restores that closure (compile.rs `Assemble`, the Kind::Build top-up after
#    `prune_public_sysroot_compiler_artifacts`), and seal 9192 carries it. An
#    `x.py dist` run over the same build dir prunes it again (Kind::Dist;
#    measured 2026-10-06, 88 -> 10 librustc_*), which is why the pack cut runs
#    dist before its full build. No other gate here notices if it goes missing. Ask the compiler that will ship
#    rather than listing files: rmeta written by another compiler is E0514 even
#    when the file is present. Measured 2026-10-06: a build-tree stage1 fails
#    this probe by design (E0463 bare; E0514 with its stage0-written private
#    sysroot), so only a stage2 can satisfy it.
GATE_RC=0; rustc_dev_probe "$DEST" "$HELLO" || GATE_RC=$?
[[ "$GATE_RC" -ne 2 ]] || gate_not_run "the rustc-dev gate on the sealed copy at $DEST" "the channel was not moved"
[[ "$GATE_RC" -eq 0 ]] || die "sealed toolchain cannot build a rustc_private consumer from its own sysroot (rustc_driver, rustc_middle, rustc_public, rustc_public_bridge) — trust-mc could not build on this channel. The probe said why above; the channel was not moved"

#    The shipped tools start FROM THE SEAL. Step 1f asked the build tree; the
#    copy, the source freeze and the symlink pruning above all happened since,
#    and a branded driver takes its sysroot from where it now stands.
GATE_RC=0; tool_start_gate "$DEST" || GATE_RC=$?
[[ "$GATE_RC" -ne 2 ]] || gate_not_run "the tool-start gate on the sealed copy at $DEST" "the channel was not moved"
[[ "$GATE_RC" -eq 0 ]] || die "sealed toolchain ships a tool that cannot start from the seal (rows above) — the channel was not moved"

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

# Run the installed product's own inventory validator before any channel flip.
# A runnable compiler alone cannot catch forbidden entrypoints or tool pairing.
if [[ -n "$FRONTEND_COMPONENT" ]]; then
	# This is the SAME installed doctor gate, once, with an exclusive empty
	# capability cache. Cache absence is context, never runtime authority.
	FRONTEND_DOCTOR_HOME="$HELLO/frontend-doctor-cargo-home"
	mkdir -m 700 "$FRONTEND_DOCTOR_HOME" || die "cannot create exclusive doctor Cargo home"
	FRONTEND_DOCTOR_EXIT=0
	CARGO_HOME="$FRONTEND_DOCTOR_HOME" "$DEST/bin/targo" trust doctor --format json \
		>"$DEST/FRONTEND-COMPONENT.evidence/doctor-candidate.stdout" 2>"$DEST/FRONTEND-COMPONENT.evidence/doctor-candidate.stderr" || FRONTEND_DOCTOR_EXIT=$?
	# Preserve the actual result before qualification/postchecks can refuse.
	python3 -B - "$DEST/FRONTEND-COMPONENT.evidence/doctor-candidate.result.json" "$FRONTEND_DOCTOR_EXIT" "$FRONTEND_DOCTOR_HOME" "$DEST" <<'PY_DOCTOR'
import json, sys
from pathlib import Path
value = {'actual_exit':int(sys.argv[2]), 'argv':[str(Path(sys.argv[4])/'bin/targo'), 'trust', 'doctor', '--format', 'json'],
         'cargo_home':sys.argv[3], 'cache_preparation':'exclusive empty private directory; diagnostic context only', 'initially_empty':True}
with open(sys.argv[1], 'x') as stream:
    json.dump(value, stream, indent=2); stream.write('\n')
PY_DOCTOR
	python3 -B "$PROMOTER_ROOT/scripts/sdk_frontend_component.py" qualify \
		--record "$DEST/FRONTEND-COMPONENT.json" --sha256 "$FRONTEND_COMPONENT_SHA" \
		--compiler-source "$COMMIT" --destination "$DEST" --actual-exit "$FRONTEND_DOCTOR_EXIT" \
		--stdout "$DEST/FRONTEND-COMPONENT.evidence/doctor-candidate.stdout" --stderr "$DEST/FRONTEND-COMPONENT.evidence/doctor-candidate.stderr" \
		--context "$DEST/FRONTEND-COMPONENT.evidence/doctor-candidate.result.json" \
		|| die "new frontend failed its actual installed doctor; prepared input is not qualification"
else
#   Two refusals, each with its reason. This was one pipeline into one
#   sentence: a doctor that printed no JSON left a Python traceback, and one
#   that printed `ready` and exited nonzero left nothing but the sentence.
DOCTOR_RC=0
"$DEST/bin/targo" trust doctor --format json >"$HELLO/doctor.json" 2>"$HELLO/doctor-stderr.txt" || DOCTOR_RC=$?
cat "$HELLO/doctor-stderr.txt" >&2
python3 -c '
import json, sys
try:
    with open(sys.argv[1], encoding="utf-8") as stream:
        report = json.load(stream)
    if not isinstance(report, dict):
        raise ValueError("the report is not a JSON object")
except (OSError, ValueError) as error:
    print("promote: `targo trust doctor --format json` did not print a JSON report: " + str(error), file=sys.stderr)
    raise SystemExit(1)
if not report.get("ready"):
    surface = report.get("compiler", {}).get("daily_driver", {})
    print("promote: installed toolchain is not ready: " + str(surface.get("detail", report.get("status"))), file=sys.stderr)
    raise SystemExit(1)
' "$HELLO/doctor.json" \
	|| die "sealed toolchain fails its installed inventory validation: the line above is why (\`targo trust doctor --format json\` exited $DOCTOR_RC; its stderr began: $(gate_said "$HELLO/doctor-stderr.txt")). The channel was not moved"
[[ "$DOCTOR_RC" -eq 0 ]] \
	|| die "sealed toolchain fails its installed inventory validation: \`targo trust doctor --format json\` reported ready and exited $DOCTOR_RC, and a doctor that fails is not a pass (its stderr began: $(gate_said "$HELLO/doctor-stderr.txt")). The channel was not moved"
fi

# 6a. The sealed compiler admits the `ay` it ships. trust-cg-verify, linked into
#     the driver, starts only an `ay` whose bytes equal the digest its build
#     recorded, and a hosted compiler names its OWN `bin/ay`
#     (first-party/trust-cg, crates/trust-cg-verify/src/ay_identity.rs). Ask
#     that rule itself: a probe linked against the sealed driver, through the
#     sealed private sysroot, resolves the sealed `bin/ay`. Measured 2026-10-01:
#     a seed-built stage2 of b0221789da passed every gate above, and this probe
#     answered "[TCG-AY-IDENTITY-MISMATCH] .../bin/ay ... has sha256 503d4aa1...,
#     not the recorded toolchain AY [... sha256 d619e096...]" — the compiler had
#     pinned the previous stage's battery (bootstrap c2a7c6000c). Without
#     trust-cg-verify in the private sysroot there is no such rule to ask, and
#     the seal says so.
AY_ADMISSION="not-checked: the sealed private sysroot carries no trust_cg_verify"
if compgen -G "$RESOLVED/$TRIPLE/libtrust_cg_verify-*.rmeta" >/dev/null; then
	[[ -x "$DEST/bin/ay" ]] || die "the sealed compiler links trust-cg-verify but the seal ships no bin/ay"
	cat > "$HELLO/ay_probe.rs" <<'RS'
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate trust_cg_verify;
fn main() {
    let path = std::env::args().nth(1).expect("an ay path");
    match trust_cg_verify::ay_identity::resolve_explicit_path(&path) {
        Ok(pinned) => println!("ADMITTED {}", pinned.sha256()),
        Err(refusal) => println!("REFUSED {refusal}"),
    }
}
RS
	STEP_RC=0
	# In a subshell: a signal during the build must leave the trap the script's own stderr, not ay_probe.log.
	( serial_command "$DEST/bin/trustc" --sysroot "$DEST" -Ztrust-verify=off --edition 2021 \
		-L "$RESOLVED/$TRIPLE" -L "$RESOLVED/host" -o "$HELLO/ay_probe" "$HELLO/ay_probe.rs" ) \
		>"$HELLO/ay_probe.log" 2>&1 || STEP_RC=$?
	if [[ "$STEP_RC" -ne 0 ]]; then
		STEP_REFUSED="$(serial_refusal "$STEP_RC" "$HELLO/ay_probe.log")" || STEP_REFUSED=""
		[[ -z "$STEP_REFUSED" ]] || step_not_run "the build of the AY-admission probe against the sealed copy at $DEST" "the channel was not moved" "$STEP_REFUSED"
		die "could not build the AY-admission probe against the sealed driver (exit $STEP_RC; ay_probe.log). The compiler said:
$(said_block "$HELLO/ay_probe.log")"
	fi
	# The probe's own exit status and words: "failed to run" alone left a loader
	# error, a panic and a signal indistinguishable (its stderr went to the
	# terminal above the refusal, or nowhere).
	STEP_RC=0
	AY_VERDICT="$(DYLD_LIBRARY_PATH="$DEST/lib" LD_LIBRARY_PATH="$DEST/lib" "$HELLO/ay_probe" "$DEST/bin/ay" 2>"$HELLO/ay_probe.err")" \
		|| STEP_RC=$?
	[[ "$STEP_RC" -eq 0 ]] \
		|| die "the AY-admission probe did not run against the sealed driver: it exited $STEP_RC and printed '$AY_VERDICT'; it said on stderr: $(gate_said "$HELLO/ay_probe.err")"
	[[ "$AY_VERDICT" == "ADMITTED $(prov_sha256 "$DEST/bin/ay")" ]] \
		|| die "the sealed compiler refuses the ay it ships: $AY_VERDICT"
	AY_ADMISSION="admitted sha256=${AY_VERDICT#ADMITTED }"
	say "sealed compiler admits its own ay (${AY_VERDICT#ADMITTED })"
else
	say "ay admission not checked: no trust_cg_verify in the sealed private sysroot"
fi

# 6b. WRITE THE PROVENANCE INTO THE SEAL, before anything points at it. This is
#     the durable half: the classification above is a decision made once, at a
#     moment nobody will be able to reconstruct, and a seal that does not carry
#     it is a seal whose only self-description is a name that may be a lie.
#
#     It is written for a reader who has ONLY this directory — hence the prose.
#     Every seal gets one, including UNVERIFIED-PROVENANCE ones.
#
#     The content identity is read once, now that nothing but the records below
#     will be written into the seal (they are outside it by definition), and
#     before the first of them, so a seal that cannot be identified gets no
#     PROVENANCE at all.
ARTIFACT_FINGERPRINT="$(prov_artifact_fingerprint "$DEST")" \
	|| die "cannot compute the content identity of the sealed toolchain $DEST (see the error above) — a seal without one is not recorded"
#     The rustc-private sysroot this seal resolves is outside it, and the driver's
#     bytes alone bind it: two sealed private sysroots with one driver can differ
#     in any other rmeta (libtrust_cg_verify, say), and rustc_private consumers
#     (trust-mc) link them. Record its content identity beside its name, by the
#     same rule as the seal's.
PRIVATE_SYSROOT_IDENTITY="$(python3 -B "$REPO/scripts/lib/seal_content_identity.py" \
	--prefix private_sysroot_content "$RESOLVED")" \
	|| die "cannot compute the content identity of the sealed private sysroot $RESOLVED (see the error above)"
#     The stage receipt, read again from the SEALED copy: its sha256 is the sealed
#     file's, and its hashes of this stage2's own files are compared with those files.
#     Step 1b'' asked the candidate; the copy, the source freeze, the symlink
#     pruning and the chmod all happened since. The two answers are the same
#     lines or there is no seal record.
SEALED_STAGE_RECEIPT="$(prov_stage_receipt "$DEST" "$COMMIT")" \
	|| die "the sealed copy's stage receipt can no longer be recorded (the reason is above): the copy changed the receipt or a file it binds — the channel was not moved"
SEALED_BASE_RECEIPT="$SEALED_STAGE_RECEIPT"
if [[ -n "$FRONTEND_COMPONENT" ]]; then
	CANDIDATE_FILES_VERIFIED="$(printf '%s\n' "$STAGE_RECEIPT" | sed -n 's/^stage_receipt_files_verified=//p')"
	SEALED_FILES_VERIFIED="$(printf '%s\n' "$SEALED_STAGE_RECEIPT" | sed -n 's/^stage_receipt_files_verified=//p')"
	[[ "$CANDIDATE_FILES_VERIFIED" =~ ^[0-9]+$ && "$SEALED_FILES_VERIFIED" =~ ^[0-9]+$ \
		&& "$CANDIDATE_FILES_VERIFIED" -eq $((SEALED_FILES_VERIFIED + 1)) ]] \
		|| die "frontend substitution did not preserve every other original receipt entry"
	SEALED_BASE_RECEIPT="$(printf '%s\n' "$SEALED_STAGE_RECEIPT" | sed '/^stage_frontend_/d; /^stage_receipt_files_verified=/d')"
	STAGE_RECEIPT_COMPARE="$(printf '%s\n' "$STAGE_RECEIPT" | sed '/^stage_receipt_files_verified=/d')"
else
	STAGE_RECEIPT_COMPARE="$STAGE_RECEIPT"
fi
[[ "$SEALED_BASE_RECEIPT" == "$STAGE_RECEIPT_COMPARE" ]] \
	|| die "the stage receipt changed while it was being sealed (the candidate and the sealed copy give different records) — the channel was not moved"
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
	printf 'source_census_scope=%s\n' "${PROV_CENSUS_SCOPE:-unavailable}"
	printf 'provenance_reason=%s\n' "$PROV_REASON"
	printf 'sealed_at=%s\n' "$(date +%Y-%m-%dT%H:%M:%S%z)"
	printf 'sealed_by=%s\n' "scripts/promote-toolchain.sh"
	printf 'seal_name=%s\n' "trust-$SHORT"
	printf 'reported_rev=%s\n' "$REV"
	printf 'reported_commit=%s\n' "$COMMIT"
	printf 'private_sysroot=%s\n' "$(basename "$RESOLVED")"
	printf '%s\n' "$PRIVATE_SYSROOT_IDENTITY"
	printf 'ay_admission=%s\n' "$AY_ADMISSION"
	printf '# THE TOOL-START GATE, as it ran on this sealed copy before this file was\n'
	printf '# written: each row made a shipped tool that is built on the compiler do a\n'
	printf '# piece of real work (a `--version` that answers is not a start). A row under\n'
	printf '# tool_start_gate_not_shipped was NOT started: this toolchain ships no such\n'
	printf '# tool. A record of that one run; `promote-toolchain.sh --gate-only` asks again.\n'
	printf 'tool_start_gate=%s\n' "$TOOL_START_RESULT"
	printf 'tool_start_gate_rows=%s\n' "$TOOL_START_PASSED"
	printf 'tool_start_gate_not_shipped=%s\n' "$TOOL_START_NOT_SHIPPED"
	printf '# Read-only native Targo discovery binds the shipped frontend/compiler cohort\n'
	printf '# and complete invocation/response; it grants no CPU, proof or whole-SDK readiness.\n'
	printf 'native_targo_resource_qualification_json=%s\n' "$NATIVE_TARGO_RESOURCE_JSON"
	printf '\n# (b) ARTIFACT IDENTITY — establishes SAMENESS, not origin. Two seals with\n'
	printf '#     the same artifact_content_sha256 ship the same files, whatever they are\n'
	printf '#     named: every file, directory and link here but these records\n'
	printf '#     (artifact_content_scope). The private sysroot above has its own.\n'
	printf '#     The per-file sha256 lines after it are kept for readers that bind one\n'
	printf '#     file; two seals can agree on all of them and still differ.\n'
	printf '%s\n' "$ARTIFACT_FINGERPRINT"
	printf '\n# (c) SEAL-TIME CROSS-CHECK — NECESSARY, NEVER SUFFICIENT. A clean tree\n'
	printf '#     at seal time is equally consistent with a clean build and with a\n'
	printf '#     dirty build whose diff was since stashed, committed or reverted.\n'
	printf 'sealtime_repo_head=%s\n' "$PROV_SEAL_HEAD"
	printf 'sealtime_repo_tree=%s\n' "$PROV_SEAL_TREE"
	printf 'sealtime_head_matches_binary=%s\n' "$PROV_HEAD_MATCHES"
	if [[ -n "$SOURCE_ROOT" || -n "$NATIVE_TOOLS" || -n "$STAGE_PROVENANCE_RECEIPT" || -n "$FRONTEND_COMPONENT" ]]; then
		printf 'promoter_repo_head=%s\n' "$(git -C "$PROMOTER_ROOT" rev-parse HEAD)"
		printf 'promoter_script_sha256=%s\n' "$(prov_sha256 "$PROMOTER_ROOT/scripts/promote-toolchain.sh")"
	fi
	if [[ -n "$NATIVE_TOOLS" ]]; then
		printf 'supplementary_native_tools=NATIVE-TOOLS.json\n'
		printf 'supplementary_native_tools_sha256=%s\n' "$(prov_sha256 "$DEST/NATIVE-TOOLS.json")"
	fi
	if [[ -n "$FRONTEND_COMPONENT" ]]; then
		printf 'supplementary_frontend=FRONTEND-COMPONENT.json\n'
		printf 'supplementary_frontend_sha256=%s\n' "$FRONTEND_COMPONENT_SHA"
		printf 'supplementary_frontend_qualification_sha256=%s\n' "$(prov_sha256 "$DEST/FRONTEND-QUALIFIED.json")"
		printf '# Only the new seal frontend changed; original compiler/mint/receipt remain.\n'
	fi
	if [[ -n "$STAGE_PROVENANCE_RECEIPT" ]]; then
		printf 'stage_receipt_selected_sha256=%s\n' "$STAGE_PROVENANCE_SHA"
		printf '# The accepted external audit was carried into this new seal only.\n'
		printf '# The original producer stage and its prior receipt were preserved.\n'
	fi
	if [[ "$ALLOW_DIRTY" -eq 1 ]]; then
		printf '\n# WAIVER — a dirty-tree build was promoted deliberately.\n'
		printf 'dirty_provenance_waived=yes\n'
		printf 'dirty_provenance_waiver_reason=%s\n' "${TRUST_PROVENANCE_WAIVER_REASON:-<none given>}"
	fi
	if [[ -r "$BUILD_DIR/trust-seed-mint" ]]; then
		printf '\n# (d) THE PACK CUT. scripts/mint_and_prove_seed.sh built this stage2 from the\n'
		printf '#     src/stage0 pin and double-compiled it from an independent seed.\n'
		printf '#     SEED-MINT beside this file is its receipt, with every compared file;\n'
		printf '#     aterm'"'"'s atpkg-publish (pack-bundle, publish-group rustc) refuses a trust\n'
		printf '#     pack with no receipt unless trust main'"'"'s seed ledger reads dormant (no\n'
		printf '#     [release.mint]).\n'
		printf 'seed_mint_sha256=%s\n' "$(prov_sha256 "$BUILD_DIR/trust-seed-mint")"
	fi
	printf '\n# (e) STAGE0 LINEAGE — which compilers built the compiler that built this.\n'
	if [[ -n "$LINEAGE" ]]; then
		printf 'stage0_lineage=STAGE0-LINEAGE\n'
		printf 'stage0_lineage_sha256=%s\n' "$LINEAGE_SHA256"
		printf 'stage0_lineage_summary=%s\n' "$LINEAGE_SUMMARY"
	elif [[ "$SEALED_STAGE_RECEIPT" == stage_receipt=absent ]]; then
		printf '#     Not recorded: promote was given no --lineage record, and nothing\n'
		printf '#     else on this path observes stage0. Absence is not evidence either way.\n'
		printf 'stage0_lineage=absent\n'
	else
		printf '#     No seed-STAIRCASE record: promote was given no --lineage. What this\n'
		printf '#     seal does say about its stage0 is the stage receipt, (f) below.\n'
		printf 'stage0_lineage=absent\n'
	fi
	printf '\n# (f) THE STAGE RECEIPT — the build record this stage2 carried, if it carried one.\n'
	if [[ "$SEALED_STAGE_RECEIPT" == stage_receipt=absent ]]; then
		printf '#     None: this stage2 carried no tool-provenance.json, the receipt\n'
		printf '#     scripts/recreate_bootstrap.py writes when it completes a Stage2+ build.\n'
	else
		printf '#     This stage2 carried tool-provenance.json, the receipt\n'
		printf '#     scripts/recreate_bootstrap.py writes into a stage2 it builds. It is sealed\n'
		printf '#     here as content: artifact_content_sha256 covers it.\n'
		printf '#     CHECKED by promotion, on the candidate and again on this sealed copy:\n'
		printf '#     it names reported_commit, and the hashes it records for THIS STAGE2'"'"'S OWN\n'
		printf '#     FILES are each the sha256 of that file here. Promotion takes those to be\n'
		printf '#     the hash in each of its tool rows and the hashes of the compiler, of the\n'
		printf '#     compiler'"'"'s rustc name, of the rustdoc name and of the proc-macro helper:\n'
		printf '#     stage_receipt_files_verified hashes. It compares no other with a file.\n'
		printf '#     NOT CHECKED: who wrote the receipt; any other hash the receipt records;\n'
		printf '#     any file of this stage2 the receipt records no such hash for.\n'
		printf '#     The other hashes, measured 2026-10-13 on the receipt of trust-f22fc270 (a\n'
		printf '#     seed build): it holds 351 sha256 values and 21 of them are the ones\n'
		printf '#     compared; among the other 330 are the seed'"'"'s stage0 tree with that\n'
		printf '#     tree'"'"'s own lib/, seed archives, native tools and source snapshots.\n'
		printf '#     The files without one: the recreator writes these hashes for executables\n'
		printf '#     only, so nothing under this stage2'"'"'s lib/ (the compiler'"'"'s driver library,\n'
		printf '#     the standard library) has one, nor has an executable outside those named.\n'
		printf '#     NOT RE-DERIVED by promotion: its status and its lineage, i.e. which\n'
		printf '#     stage0 the build started from. Those are the receipt'"'"'s own statements;\n'
		printf '#     `recreate_bootstrap.py --verify-stage-provenance`, in the build tree, is\n'
		printf '#     what recomputes them. stage_receipt_recreator_argv is what the build\n'
		printf '#     said it was started with; nothing can re-derive a command line. It is\n'
		printf '#     shell-quoted in ASCII; a value in parentheses is promotion'"'"'s own word.\n'
		printf '#     So is the bare word not-recorded when it is the whole value: the receipt\n'
		printf '#     holds no record of the arguments (it was written before the recreator\n'
		printf '#     recorded them, or not by the recreator), whereas the one argument\n'
		printf '#     not-recorded is written quoted, as '"'"'not-recorded'"'"'.\n'
		printf '#     THE LLVM this stage2 carries, stage_receipt_llvm*, is the receipt'"'"'s own\n'
		printf '#     statement as well, and promotion compares it with no file: a seal holds\n'
		printf '#     no build directory. x.py rebuilds the in-tree LLVM when\n'
		printf '#     HEAD:src/llvm-project moves from the tree recorded beside it, but it\n'
		printf '#     keeps an LLVM that cannot say what it was built from (one built\n'
		printf '#     before that record, whose own build header names no commit this\n'
		printf '#     checkout has), and a change to src/bootstrap, src/version, the\n'
		printf '#     bootstrap config or the native tools rebuilds none, so a reused build\n'
		printf '#     directory can carry an LLVM built from other sources or with another\n'
		printf '#     recipe. _identity=stated: the build could say which sources its\n'
		printf '#     LLVM was built from. Either it watched build/<host>/llvm being built from\n'
		printf '#     nothing (_provenance=built-in-this-run), or it reused one whose directory\n'
		printf '#     held the record of such a build for the same LLVM sources, bootstrap\n'
		printf '#     config and native tools, its installed files unchanged since\n'
		printf '#     (_provenance=reused; _built_at_commit is the commit of that build).\n'
		printf '#     _source_sha256 is one sha256 over the git ids of the LLVM inputs in the\n'
		printf '#     source tree, _source_tree the id of src/llvm-project among them; both\n'
		printf '#     are written for stage_receipt_llvm=in-tree only.\n'
		printf '#     stage_receipt_llvm=external: this stage2 links an LLVM through the\n'
		printf '#     recreator'"'"'s --llvm-config, and its identity is NEVER stated. The build\n'
		printf '#     did not watch that LLVM being built and has no record of such a build;\n'
		printf '#     what the receipt binds of it is the llvm-config executable (path, sha256,\n'
		printf '#     version) and its dylib closure, not the libraries it points at. Its\n'
		printf '#     other four lines say not-recorded: the src/llvm-project of the source\n'
		printf '#     tree is not what that LLVM was built from.\n'
		printf '#     stage_receipt_llvm=unknown: the build could not tell which LLVM x.py\n'
		printf '#     links, and its identity is NEVER stated. The bootstrap config x.py\n'
		printf '#     obeys did not itself say (it names an llvm-config other than the\n'
		printf '#     build'"'"'s --llvm-config, or none where the build was given one; it has\n'
		printf '#     an include key; it does not set llvm.download-ci-llvm = false), or it\n'
		printf '#     could not be read, or the LLVM could not be observed or recorded; the\n'
		printf '#     receipt'"'"'s llvm_identity.reasons say which. Its other four lines say\n'
		printf '#     not-recorded: neither the src/llvm-project of the source tree nor\n'
		printf '#     anything in the build directory is known to be what this stage2 links.\n'
		printf '#     CHECKED by promotion: the form of that record, and that it contradicts\n'
		printf '#     neither itself nor this receipt. stage_receipt_status does NOT depend on\n'
		printf '#     it: a receipt is internal-release-ready on its source and seed lineage\n'
		printf '#     whether or not _identity=stated, and a seal is cut either way unless\n'
		printf '#     promotion was run with --require-llvm-identity, which refuses anything\n'
		printf '#     but stated. stage_receipt_llvm=not-recorded: the receipt holds no such\n'
		printf '#     record (it was written before 2026-10-13, or not by the recreator), and\n'
		printf '#     nothing in this file says which LLVM this stage2 carries.\n'
	fi
	printf '%s\n' "$SEALED_STAGE_RECEIPT"
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
if [[ -r "$BUILD_DIR/trust-seed-mint" ]]; then
	cp "$BUILD_DIR/trust-seed-mint" "$DEST/SEED-MINT"
fi

# 7. Flip. `ln -sfn` replaces the symlink via rename(2) — atomic, so no
#    invocation ever observes a missing toolchain.
if [[ "$NO_FLIP" -eq 1 ]]; then
	say "sealed, NOT flipped (--no-flip): $DEST"
	say "provenance: $PROV_CLASS (full record: $DEST/PROVENANCE)"
	say "channel unchanged: $RUSTUP_LINK -> $(readlink "$RUSTUP_LINK" 2>/dev/null || echo none)"
	echo
	echo "Admit it later with:  ln -sfn $DEST $RUSTUP_LINK && ln -sfn $DEST $ROOT/trust-current"
	PROMOTE_FINISHED=1
	exit 0
fi
mkdir -p "$(dirname "$RUSTUP_LINK")"
PREV="$(readlink "$RUSTUP_LINK" 2>/dev/null || echo none)"
ln -sfn "$DEST" "$RUSTUP_LINK"
ln -sfn "$DEST" "$ROOT/trust-current"

say "promoted: rustup channel \`trust\` -> $DEST"
say "previous: $PREV"
say "provenance: $PROV_CLASS (full record: $DEST/PROVENANCE)"
echo
echo "Verify:  \"$DEST/bin/trustc\" --version && \"$DEST/bin/trustfmt\" --version && \"$DEST/bin/targo\" trust doctor"
echo "Rollback: ln -sfn $PREV $RUSTUP_LINK"
PROMOTE_FINISHED=1
