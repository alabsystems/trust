#!/bin/bash
# Two-language program battery: REAL programs, compiled by the REAL compiler,
# run, and their output compared — the executable evidence behind
# docs/TWO_LANGUAGE_100_PERCENT_GOAL.md. Every row is a complete program (or a
# standalone Lean file, or a Targo package), not a unit test of a lowering.
#
# One row = one directory under tests/two-language-programs/. The table below
# names the lane each row exercises and what "green" means for it:
#
#   trustc-run   compile with trustc, run the binary, diff stdout with expected.txt
#   trustc-lib   compile a lib crate with verification ON; green = exit 0 (`ok`)
#                or a normal REFUSAL with the named failed JSON obligation
#                (`refused`) for the false-twin rows; crashes never pass
#   trustc-refused
#                a NEGATIVE CONTROL: compile a bin with verification ON to the
#                JSON wire; green = REFUSED (exit != 0) WITH the named diagnostic,
#                the wire carries the named `failed` row, and the tolerant grader
#                still reads clean=no on it
#   trustc-wire-not-clean
#                a NEGATIVE CONTROL for the wire itself: the crate COMPILES and
#                RUNS (stdout diffed), but the tolerant grader must read
#                clean=no with the named non-clean label — a tolerance that
#                covered this row would be a vacuous green
#   lean         `targo trust check <file.lean>`; green = PROVED / REJECTED as named
#                (a REJECTED row must also match its stated diagnostic, so a
#                refusal for an unrelated reason is not a green)
#                There was a `row_lean_disclosed` here — PROVED AND a named
#                disclosure line — for r26's prelude stand-in. The check lane
#                REFUSES a stand-in import as of 2026-09-24 (`d10a6eeb2eb`), so
#                its one caller became `row_lean … REJECTED` and the grader had
#                no callers left. Deleted rather than kept: a grader nothing
#                calls is one a later row can be wired to by mistake, and this
#                one now encodes a superseded policy. The island lane still
#                discloses, but no battery row covers it — its fixtures are
#                `tests/ui/trust/clean_island_standin_import_disclosed*.rs`.
#   package      a Targo package: `targo --unverified run` (diff stdout) or
#                `targo trust build` (verified lane; green = exit 0)
#   cross-crate  aux rlib + main, both trustc; run, diff stdout
#   targo-file   `targo trust check main.rs` (authenticated lane, single-file
#                mode) on Lean-discharged contracts; green = the kernel rows
#                PUBLISH (`Gate: PASS`, `(0 withheld)`, both kernel solver labels
#                `[PROVED]`), or a REFUSAL for the false twin
#   trustc-ir    the PRODUCER RATCHETS (roadmap WS5.1): the Part A and Part A-Lean
#                rows of the 2026-09-17 two-language proof program, one `ir-*`
#                directory per source (a Rust crate with a `clean {}` island, a
#                standalone `.lean` file, a hand-written trust-ir module). The judge
#                scripts/two_language_producer_ratchets.py compiles it with THIS
#                trustc/targo, emits trust-ir, and judges the module with the
#                trust-ir CLI (and `clean`, `trust-cg`) BUILT FROM THE first-party/
#                GITLINKS, never an installed binary. Green = every ratchet the row
#                measures equals its pin in the row's expected.json: a PASS, or a
#                GAP / REFUSED asserted by its NAMED signature only (the verbatim
#                refusal, or a named absence over a key set and its value). A GAP
#                that turns PASS, a refusal that changes class, a regression, or
#                an unnamed FAIL turns the row red until expected.json is updated
#                in the same commit — this lane is its own flip-on-fix ratchet, so
#                its rows never need a KNOWN_RED line. `audit-check` (in the
#                selftest lane) holds every pin to the audit corpus. The lane's
#                MUTATION CONTROL is the row ir-ta-island_mutant (WS8.8): p10
#                with one Clean-island line edited must move the native value
#                and FAIL both cross interpreter-vs-native differentials —
#                the evidence that every `.exec` PASS is executing the emitted
#                Clean body.
#
# This script is the manifest row `release.two-language-programs` of
# tests/run_trust_comprehensive_harness.sh (release tier; it needs a built
# compiler). scripts/run_e2e_shell_corpus.sh skips it by name so the battery
# runs once per release. `--selftest` stays the fast-tier row.
#
# KNOWN-RED rows are the honest frontier: they are RUN, their failure is
# EXPECTED and named, and — this is the ratchet — a known-red row that PASSES
# fails the script until its entry is deleted. A row can never be silently
# green or silently red. Nothing here weakens a refusal to gain a green.
#
# A verification-ON row is graded on the JSON WIRE by
# tests/two-language-programs/wire_grade.py: every transport outcome is
# tallied, at least one obligation must be PROVED, the crate_summary must
# agree, the compiler run that WROTE the wire must have exited 0 (rows precede
# a teardown panic, so the wire alone cannot say the process survived), and
# the only tolerances are named on the printed line. `--selftest`
# runs that grader's own mutation cases (no toolchain needed) — it is also the
# gate lane `fast.two-language-wire-grader-selftest`.
#
# The summary names the COMPILER IDENTITY it measured (the build stamp's
# `head=` for a driver under build/, else the binary's commit-hash) beside the
# checkout's HEAD. A pass or a fail is evidence about THAT compiler; a
# KNOWN_RED line may be deleted only when the two agree (audit §4e,
# 2026-09-15: three "unexpected passes" were an old compiler under a new
# ratchet).
#
# Usage:
#   tests/e2e_two_language_programs.sh                 # sealed/PATH toolchain
#   TRUSTC=build/host/stage1/bin/trustc tests/e2e_two_language_programs.sh
#   tests/e2e_two_language_programs.sh --out report.md # also write the table
#   tests/e2e_two_language_programs.sh --selftest      # grader mutation cases only
#   tests/e2e_two_language_programs.sh --lane trustc-ir # only the rows of one lane
#   tests/e2e_two_language_programs.sh --only ir-ta10_lean_wrapping_uint64
#   tests/e2e_two_language_programs.sh --lane trustc-ir --ir-evidence ev.json
#                      # also aggregate the trustc-ir row reports into the
#                      # G1/G2/G3/G5/G6-tagged completion-gate evidence artifact
#
# Scratch lives under build/tmp (self-owned): `targo trust` refuses a
# world-writable path component such as /tmp by design.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ROWS_DIR="$TRUST_ROOT/tests/two-language-programs"
WIRE_GRADER="$ROWS_DIR/wire_grade.py"
WIRE_READER="$TRUST_ROOT/scripts/lib/trust_program_wire.py"

OUT_FILE=""
ONLY=""
LANE=""
IR_EVIDENCE=""
while [ $# -gt 0 ]; do
    case "$1" in
        --out) OUT_FILE="$2"; shift 2 ;;
        --only) ONLY="$2"; shift 2 ;;
        --lane) LANE="$2"; shift 2 ;;
        --ir-evidence) IR_EVIDENCE="$2"; shift 2 ;;
        --selftest)
            python3 "$WIRE_GRADER" --selftest || exit $?
            python3 "$TRUST_ROOT/scripts/tests/two_language_program_inventory_test.py" || exit $?
            exec python3 "$TRUST_ROOT/scripts/tests/two_language_program_refusal_test.py" ;;
        -h|--help) sed -n '2,83p' "$0"; exit 0 ;;
        *) echo "unknown argument: $1" >&2; exit 2 ;;
    esac
done
if [ ! -f "$WIRE_GRADER" ]; then
    echo "ERROR: wire grader missing: $WIRE_GRADER" >&2
    exit 2
fi
if [ ! -f "$WIRE_READER" ]; then
    echo "ERROR: verification wire reader missing: $WIRE_READER" >&2
    exit 2
fi

# ---- toolchain resolution ---------------------------------------------------
if [ -z "${TRUSTC:-}" ]; then
    if command -v trustc >/dev/null 2>&1; then
        TRUSTC="$(command -v trustc)"
    elif [ -x "$HOME/Library/Application Support/aterm/pkg/bin/trustc" ]; then
        TRUSTC="$HOME/Library/Application Support/aterm/pkg/bin/trustc"
    else
        echo "ERROR: no trustc on PATH and \$TRUSTC unset" >&2
        exit 2
    fi
fi
TRUSTC="$(cd "$(dirname "$TRUSTC")" && pwd)/$(basename "$TRUSTC")"
TARGO="${TARGO:-$(dirname "$TRUSTC")/targo}"
if [ ! -x "$TARGO" ]; then
    echo "ERROR: no targo beside trustc: $TARGO" >&2
    exit 2
fi
# A real targo accepts --unverified; cargo-in-disguise rejects it (CLAUDE.md).
if ! "$TARGO" --unverified --version >/dev/null 2>&1; then
    echo "ERROR: $TARGO is not a real targo (rejects --unverified)" >&2
    exit 2
fi

mkdir -p "$TRUST_ROOT/build/tmp"
SCRATCH="$(mktemp -d "$TRUST_ROOT/build/tmp/two-language-programs.XXXXXX")"
trap 'rm -rf "$SCRATCH"' EXIT

# Scrub every ambient toolchain override so the row tests THIS trustc.
scrub() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC -u RUSTFLAGS \
        -u CARGO_ENCODED_RUSTFLAGS -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC -u CARGO_TARGET_DIR "$@"
}

# ---- the frontier: rows whose failure is EXPECTED today --------------------
# name|reason. Delete a line when its row goes green; the script fails on an
# unexpected pass so the list cannot go stale.
#
# HISTORY — rows that have LEFT this list, kept because each line is a dated
# measurement and the reason it stopped being red is the evidence:
#   r08, r14 (assert-only and package shapes) left with 3cd585a1e6; r24 left
#   with the let temporary.
#   r09_println_verify_on was red as: UPSTREAM trust-ir v41 residue (not this
#   instrument): a CALL in println! argument position (double(21)) is dropped
#   with the whole Arguments::new(..) subtree by the wave-FA lane before
#   fmt::Arguments is registered, so std::io::_print cannot be signed and the
#   v41 module validator refuses at finalization [RustAbiVararg]; the fleet
#   owned that lane (reports/2026-09-14-rust-abi-vararg-producer-half.md).
#   It left this list when the row became an EXPLICIT tolerated-gap row —
#   `row_trustc_run --tolerated-print-gap --tolerated-requires` — so the gap is
#   now named on the grader line instead of excused by a KNOWN_RED entry. That
#   is a narrowing, not a loosening: see the row_trustc_run header for the
#   measured shapes the grader accepts (2026-09-13 and 2026-09-17 stage1s).
#   r07's REASON (not the row) was rewritten 2026-09-27. It had blamed the
#   missing producer `exact` attestation ("the compiler emits only the
#   negative value — BY DESIGN"). 8cffe047971 began emitting `exact` for
#   acyclic, unpruned, fully determined bodies, and its message says r07's
#   refutation passes that gate. The diagnostic that holds the row now was
#   measured on pack 5ab8dcccfcb
#   (reports/2026-09-27-new-pack-5ab8dcccfcb-measured.md §2). The row stays RED.
KNOWN_RED='
r07_rust_contract_refuted_strict|the counterexample EXISTS and is not transported: trust-mc refutes the encoded VC (native trust_mc typed CHC/PDR full-verification runner refuted obligation ...; refusing to emit proof evidence), but the published row is UNKNOWN, so the wire reads 1 proved / 0 failed / 2 unknown while refused_wire requires required_failed=yes. THE BUILD IS STILL REFUSED (exit 1, Trust strict verification failed for lib::double) — a lost counterexample, not an accepted false contract. NOTHING REGRESSED: the 2026-09-17 trust-ir report records this row PASSING on the identical compiler output, graded on the human refusal alone; ee61441a095 (2026-09-21) added the wire requirement and exposed the gap. WHAT HOLDS IT (measured 2026-09-27, pack 5ab8dcccfcb, trustc --crate-type lib on the row source, exit 1): [postcond] UNKNOWN (trust-full-verifier): generic native SAT cannot be re-keyed onto a proof-only precise obligation — the same reason on the trust-exact-source-clause-discharge row for ensures clause #2. That is a gate about WHICH obligation a generic SAT verdict may speak for. It is not the producer-fidelity gate: since 8cffe047971 the compiler emits the exact fidelity attestation for acyclic, unpruned, fully determined bodies, and per that commit this refutation passes it (the earlier reason here, that the compiler emits only the negative value, is superseded). So this row waits on that re-keying edge, NOT on widening a gate. WHERE THE SEAM IS (re-measured 2026-09-27 on the local line): the compiler stamps fidelity=exact on vc:lib__double:postcondition:0 (TRUST_NATIVE_DEBUG_VC_PAYLOAD prints it; the payload grounds every name it mentions: x is an input, _2.0#s0_0 and _0 are defined by equalities, and the overflow flag is pinned by NOT _2.1#s0_0), and the refutation is discarded by the ay re-key bridge in trust_verify.rs, which admits only a Proved for a Postcondition (bridge_ay_verdict_is_admissible) and demotes WITHOUT consulting the exact attestation, although its own stated reason (a formula under-approximating body facts over free params) is exactly what exact rules out. Letting that seam admit an exact-attested Postcondition SAT grants refutation authority on a new path, an owner decision: docs/DECISION_QUEUE.md "May an exact-attested Postcondition SAT cross the ay re-key bridge as a refutation?" (OPEN). No accept/reject outcome changes either way (strict refuses on unknown and on failed alike); what changes is whether a refutation CLAIM is published. Refutation authority stays fail-closed, because widening it admits FALSE REFUTATIONS against correct code: docs/OPEN_ISSUES.md D92
'

known_red_reason() {
    printf '%s\n' "$KNOWN_RED" | awk -F'|' -v n="$1" '$1==n {sub(/^[^|]*\|/, ""); print; exit}'
}

# ---- bookkeeping ------------------------------------------------------------
declare -a RESULT_ROWS=()
declare -a EXECUTED_ROWS=()
FAILS=0
UNEXPECTED=0
PASSES=0
REDS=0

record() { # name lane verdict detail
    local name="$1" lane="$2" verdict="$3" detail="$4"
    RESULT_ROWS+=("| $name | $lane | $verdict | $detail |")
    EXECUTED_ROWS+=("$name")
    case "$verdict" in
        PASS) PASSES=$((PASSES+1)) ;;
        RED) REDS=$((REDS+1)) ;;
        FAIL) FAILS=$((FAILS+1)) ;;
        UNEXPECTED-PASS) UNEXPECTED=$((UNEXPECTED+1)) ;;
    esac
    printf '%-36s %-12s %-16s %s\n' "$name" "$lane" "$verdict" "$detail"
}

# Turn a raw outcome (ok/fail + detail) into a verdict against the frontier.
judge() { # name lane ok(0/1) detail
    local name="$1" lane="$2" ok="$3" detail="$4"
    local reason
    reason="$(known_red_reason "$name")"
    if [ -n "$reason" ]; then
        if [ "$ok" != 0 ]; then
            record "$name" "$lane" "RED" "expected today ($detail) — $reason"
        else
            if [ "${ID_MATCH:-unknown}" = yes ]; then
                record "$name" "$lane" "UNEXPECTED-PASS" "known-red row passed on a compiler built from HEAD — delete its KNOWN_RED line ($detail)"
            else
                record "$name" "$lane" "UNEXPECTED-PASS" "known-red row passed, but compiler-identity match=${ID_MATCH:-unknown}: this is evidence about a DIFFERENT compiler than HEAD, so do NOT delete its KNOWN_RED line on this run (audit §4e) ($detail)"
            fi
        fi
    else
        if [ "$ok" = 0 ]; then
            record "$name" "$lane" "PASS" "$detail"
        else
            record "$name" "$lane" "FAIL" "$detail"
        fi
    fi
}

stage() { # name -> copies the row into scratch, echoes the dir
    local name="$1" dir="$SCRATCH/$name"
    rm -rf "$dir"; cp -R "$ROWS_DIR/$name" "$dir"
    printf '%s\n' "$dir"
}

first_error_line() { # log
    grep -m1 -E '^error(\[|:)' "$1" | cut -c1-140 || true
}

normal_refusal() { # measured exit status, complete log
    # A crash, signal, loader error or wrapper-swallowed panic is not a
    # semantic refusal, even when an expected diagnostic preceded it.
    [ "$1" = 1 ] || return 1
    local scan_status
    LC_ALL=C grep -qE 'panicked at|internal compiler error|the compiler unexpectedly panicked' "$2"
    scan_status=$?
    [ "$scan_status" = 1 ] # no match; an unreadable log also fails
}

refused_wire() { # log, measured exit status, FUNCTION=OBLIGATION-SUBSTRING
    local log="$1" rc="$2" required="$3" wire
    normal_refusal "$rc" "$log" || { printf 'abnormal refusal process (exit %s)\n' "$rc"; return 1; }
    wire="$(python3 "$WIRE_GRADER" --exit-code "$rc" --tolerate-print-gap --tolerate-requires-assumption \
        --require-failed-in "${required%%=*}" --require-failed-obligation "${required#*=}" < "$log")" || return 1
    printf '%s\n' "$wire"
    # A named failed row without the complete agreeing summary can be a
    # partial transcript. Merely reading clean=no proves no specific refusal.
    case "$wire" in
        *"| summary=agree | exit=1 | clean=no("*"| required_failed=yes") return 0 ;;
        *) return 1 ;;
    esac
}

want_row() { # name lane -> 0 when this row runs under --only / --lane
    [ -n "$ONLY" ] && [ "$ONLY" != "$1" ] && return 1
    [ -n "$LANE" ] && [ "$LANE" != "$2" ] && return 1
    return 0
}

# ---- lanes ------------------------------------------------------------------
row_trustc_run() { # [--tolerated-print-gap] [--tolerated-requires] name flags...
    # `--tolerated-print-gap`: this row is a policy-B COMPLETENESS-GAP row (a
    # `println!`). The std print backend is deliberately NOT verified (docs/TCB.md)
    # and the owner ruling B REPORTS its gap rather than failing the build, so a
    # clean wire is structurally unreachable for ANY `println!` — and no proof can
    # ever make it clean, because std's `_print` panics on write failure BY
    # DEFINITION. The gap has ridden the wire in two shapes: an `unknown` row of
    # kind `native-verification-gap` (the bundled `ReentrantLock` member, as
    # measured on a 2026-09-13 stage1) and, measured 2026-09-17 on a HEAD stage1,
    # a `runtime_checked` `assert` row that the COMPILER classes
    # `"gap_class": "std-print-dispatch"`. That row is the whole-function
    # panic-freedom AGGREGATE, and the class is the compiler's attestation, made
    # where the fold is visible, that `std::io::_print` reached as an absent
    # callee is its SOLE panic source. The grader accepts exactly those, named on
    # its line under `tolerated=`; an unclassed runtime-checked row (one more
    # panic source folded under it), a `failed` row, or a class it does not know
    # stays non-clean. So this row is green when the compiler ACCEPTS it (exit
    # 0), the only non-clean wire rows are that classed gap (plus the `requires`
    # rows below), and the program runs with matching stdout. A REAL unmodeled
    # construct exits 1 (→ "compile refused") and a refutation shows as `failed`
    # (still fatal), so this can never green a genuine gap — r27 (a violated
    # callsite contract refuses) and r28 (one folded user assert leaves the row
    # unclassed and non-clean) are the pinned negative controls. The class is
    # deliberately NARROW: any other panic source folded under the aggregate —
    # a bundled member's assert of any kind, a discharged drop-glue row for an
    # owned `String`/`Vec`, a second absent callee — leaves the row unclassed,
    # so a println row over a program that owns a heap value reads non-clean
    # here until the class is widened by an explicit allowlist, never by
    # loosening the recognizer. That is a boundary, not a regression.
    # `--tolerated-requires`: the program's own `requires` clauses ride the wire
    # as `skipped` rows of kind `assumption:requires` (the callee ASSUMES them;
    # every caller must PROVE them, and r27 pins that a violated one refuses).
    local tolerated_gap=0 tolerated_requires=0
    while :; do
        case "${1:-}" in
            --tolerated-print-gap) tolerated_gap=1; shift ;;
            --tolerated-requires) tolerated_requires=1; shift ;;
            *) break ;;
        esac
    done
    local name="$1"; shift
    want_row "$name" trustc-run || return
    local dir; dir="$(stage "$name")"
    local log="$dir/compile.log"
    local ok=1 detail
    if (cd "$dir" && scrub "$TRUSTC" "$@" main.rs -o prog >"$log" 2>&1); then
        local run_log="$dir/run.log"
        # A verification-ON row is green only if the WIRE (what `targo trust`
        # reads) says every obligation was PROVED: the default policy may
        # tolerate a gap and still exit 0, and that is not "verified". The
        # grader (`wire_grade.py`) tallies EVERY outcome the transport can
        # carry, requires proved >= 1, requires the crate_summary to agree, and
        # prints `clean=yes` only then — its predecessor tested only
        # ", 0 unknown, 0 failed" and graded a single `runtime_checked` row as
        # clean (r08 on the 2026-09-12 pack). An EMPTY wire on a verify-on row
        # is `clean=no`, never a pass.
        local wire="" wire_ok=0
        case " $* " in
            *" -Ztrust-verify=off "*) ;;
            *)
                local wire_session wire_stdout="$dir/wire.stdout" wire_stderr="$dir/wire.stderr"
                local tol=""
                [ "$tolerated_gap" = 1 ] && tol="--tolerate-print-gap"
                [ "$tolerated_requires" = 1 ] && tol="$tol --tolerate-requires-assumption"
                wire_ok=1
                if ! wire_session="$(python3 -c 'import secrets; print(secrets.token_hex(16))')"; then
                    wire="could not create verification session"
                elif (cd "$dir" && scrub "$TRUSTC" "$@" -Ztrust-verify-output=json \
                        -Ztrust-verify-session="$wire_session" main.rs -o prog.json.bin \
                        >"$wire_stdout" 2>"$wire_stderr"); then
                    # Accounting must pass before the existing outcome policy:
                    # a present zero-obligation body is not a verified program.
                    if wire="$(python3 "$WIRE_READER" --stderr "$wire_stderr" --stdout "$wire_stdout" \
                            --crate-name main --session "$wire_session" --require-function main::main \
                            --check-accounting-only 2>&1)"; then
                        # The compiler's EXIT STATUS is graded WITH its rows.
                        # `--exit-code 0` is not decoration: the grader refuses a
                        # wire whose status it was not told, because a compiler
                        # that writes every row and then panics at teardown (the
                        # `trimmed_def_paths` ICE, exit 101 — measured
                        # 2026-09-16) is otherwise indistinguishable from a real
                        # green. Here 0 is the measured status: a nonzero one
                        # took the `else` branch below and never reaches this
                        # line.
                        if wire="$(python3 "$WIRE_GRADER" --exit-code 0 $tol < "$wire_stderr" 2>&1)"; then
                            case "$wire" in
                                *"| clean=yes") wire_ok=0 ;;
                            esac
                        fi
                    fi
                else
                    local wire_status=$?
                    wire="wire compiler exited $wire_status: $(first_error_line "$wire_stderr")"
                fi ;;
        esac
        if [ "$wire_ok" != 0 ]; then
            detail="compiled, but the verification wire is not clean: $wire"
        elif (cd "$dir" && ./prog >"$run_log" 2>"$dir/run.err"); then
            if diff -q "$dir/expected.txt" "$run_log" >/dev/null; then
                ok=0; detail="compiled, ran, stdout matches ($(tr '\n' ' ' <"$dir/expected.txt"))${wire:+; $wire}"
            else
                detail="stdout mismatch: got '$(tr '\n' ' ' <"$run_log")' expected '$(tr '\n' ' ' <"$dir/expected.txt")'"
            fi
        else
            detail="binary exited $? : $(head -c 140 "$dir/run.err")"
        fi
    else
        detail="compile refused: $(first_error_line "$log")"
    fi
    judge "$name" "trustc-run" "$ok" "$detail"
}

row_trustc_lib() { # name expect(ok|refused) [FUNCTION=OBLIGATION-SUBSTRING]
    local name="$1" expect="$2" required="${3:-}"
    want_row "$name" trustc-lib || return
    local dir; dir="$(stage "$name")"
    local log="$dir/compile.log"
    local ok=1 detail
    if (cd "$dir" && scrub "$TRUSTC" --crate-type lib lib.rs >"$log" 2>&1); then
        local proved; proved="$(grep -o 'Trust verification: [0-9]* proved[^)]*' "$log" | head -1)"
        if [ "$expect" = ok ]; then
            # The human summary is not the product's evidence: `targo trust`
            # reads the JSON transport. Both must agree, row for row — a
            # "proved" that the wire calls "unknown" is the honesty gap the
            # 2026-09-12 sentinel retirement closed. The grader requires every
            # row PROVED; the one tolerance a lib row gets is its OWN `requires`
            # clause, which the body assumes and callers prove — `skipped` with
            # kind `assumption:requires`, named on the wire line. Measured
            # 2026-09-16: r06's human line reads "5 proved" while its wire is
            # 3 proved + 2 such rows; the detail below prints the wire.
            #
            # The JSON run's exit status is graded too (see `row_trustc_run`):
            # a contract-only lib is EXACTLY the shape that wrote its proved
            # rows and then ICEd at teardown, and the piped form graded it clean.
            local wire wire_log="$dir/wire.log" wire_rc=0
            (cd "$dir" && scrub "$TRUSTC" --crate-type lib -Ztrust-verify-output=json lib.rs >"$wire_log" 2>&1) || wire_rc=$?
            wire="$(python3 "$WIRE_GRADER" --exit-code "$wire_rc" --tolerate-requires-assumption <"$wire_log")"
            case "$wire" in
                *"| clean=yes") ok=0; detail="verified: ${proved:-exit 0}; $wire" ;;
                *) detail="human summary says '${proved:-exit 0}', but the JSON transport run is not clean: $wire" ;;
            esac
        else detail="ACCEPTED a false contract: $proved"; fi
    else
        local rc=$?
        detail="refused: $(first_error_line "$log")"
        if [ "$expect" = refused ]; then
            local diag="Trust strict verification failed for \`${required%%=*}\`"
            if [ -z "$required" ] || ! normal_refusal "$rc" "$log" || ! grep -qF -- "$diag" "$log"; then
                detail="not the expected contract refusal (exit $rc): $(first_error_line "$log")"
            else
                local wire wire_log="$dir/wire.log" wire_rc=0
                (cd "$dir" && scrub "$TRUSTC" --crate-type lib -Ztrust-verify-output=json lib.rs >"$wire_log" 2>&1) || wire_rc=$?
                if grep -qF -- "$diag" "$wire_log" && wire="$(refused_wire "$wire_log" "$wire_rc" "$required")"; then
                    ok=0; detail="refused on the named contract: $(first_error_line "$log"); $wire"
                else
                    detail="contract refusal did not survive the JSON run (exit $wire_rc): ${wire:-$(first_error_line "$wire_log")}"
                fi
            fi
        fi
    fi
    judge "$name" "trustc-lib" "$ok" "$detail"
}

row_trustc_audit_refused() { # name function citation
    # A rejected citation is an audit refusal, not a solver counterexample:
    # r43 historically reports unknown obligations after the kernel type
    # mismatch. Require that exact boundary and an ordinary compiler exit.
    local name="$1" function="$2" citation="$3"
    want_row "$name" trustc-audit-refused || return
    local dir; dir="$(stage "$name")"
    local log="$dir/compile.log" rc=0 ok=1 detail
    # Exactly two audit heads. Since cb1/B2 (2026-09-28) a `result`-binding
    # clause whose POSTCONDITION goal was built and refuted leads with that goal
    # ("… audit against this postcondition with `result` bound to the imported
    # definition of `f`:"); any other refusal keeps the bare head. Both name the
    # citation, and the function's last path segment names the import.
    local audit="error: citation \`$citation\` failed the strict Clean statement/certification audit:"
    local audit_post="error: citation \`$citation\` failed the strict Clean statement/certification audit against this postcondition with \`result\` bound to the imported definition of \`${function##*::}\`:"
    local refusal="Trust strict verification failed for \`$function\`"
    (cd "$dir" && scrub "$TRUSTC" --crate-type lib lib.rs >"$log" 2>&1) || rc=$?
    if normal_refusal "$rc" "$log" \
            && { grep -qF -- "$audit" "$log" || grep -qF -- "$audit_post" "$log"; } \
            && grep -qF 'TypeMismatch' "$log" && grep -qF -- "$refusal" "$log"; then
        ok=0; detail="named citation rejected by the strict kernel statement audit: $(first_error_line "$log")"
    else
        detail="not the expected citation type-mismatch refusal (exit $rc): $(first_error_line "$log")"
    fi
    judge "$name" "trustc-audit-refused" "$ok" "$detail"
}

row_trustc_refused() { # name diag-substring required-failed(FUNCTION=OBLIGATION-SUBSTRING)
    # A NEGATIVE CONTROL: the crate must be REFUSED (non-zero exit) with the named
    # diagnostic, and the wire must carry the named `failed` row in the named
    # function even under every tolerance — a tolerance elsewhere in this battery
    # is only honest if the same compiler still refuses the neighbouring program
    # that violates a contract, and the same grader still sees the refusal.
    local name="$1" diag="$2" required="$3"
    want_row "$name" trustc-refused || return
    local dir; dir="$(stage "$name")"
    local log="$dir/compile.log"
    local ok=1 detail rc=0
    (cd "$dir" && scrub "$TRUSTC" -Ztrust-verify-output=json main.rs -o prog >"$log" 2>&1) || rc=$?
    if [ "$rc" = 0 ]; then
        detail="ACCEPTED a program that violates a contract (exit 0)"
    elif ! normal_refusal "$rc" "$log"; then
        detail="abnormal refusal process (exit $rc): $(first_error_line "$log")"
    elif ! grep -q -F -- "$diag" "$log"; then
        detail="refused, but not with the expected diagnostic '$diag': $(first_error_line "$log")"
    else
        # The grader runs with EVERY tolerance the positive rows use, and must
        # still read clean=no on the failed row AND find the named failed row
        # in the named function — so the tolerances provably do not cover it.
        # The measured exit status goes in with the rows (the grader refuses a
        # wire whose status it was not told); here it is the REFUSAL's own
        # nonzero status, so `clean=no` names the process first and the row
        # evidence is read out of `nonclean=` instead of the reason text.
        local wire
        if wire="$(refused_wire "$log" "$rc" "$required")"; then
            ok=0; detail="refused as required: $(first_error_line "$log"); $wire"
        else
            detail="refused with the diagnostic, but no complete matching failed wire (\`$required\`): $wire"
        fi
    fi
    judge "$name" "trustc-refused" "$ok" "$detail"
}

row_trustc_wire_not_clean() { # name nonclean-label
    # A NEGATIVE CONTROL for the WIRE: the crate compiles and runs (the default
    # policy tolerates a runtime-checked user assertion), stdout matches, and
    # the grader — with every tolerance the positive rows use — must still read
    # clean=no with the named non-clean label. This is how a tolerance is shown
    # to be narrow: the neighbouring program that folds one more panic source
    # under the same row is graded non-clean by the same grader.
    local name="$1" label="$2"
    want_row "$name" trustc-wire-not-clean || return
    local dir; dir="$(stage "$name")"
    local log="$dir/compile.log"
    local ok=1 detail
    if ! (cd "$dir" && scrub "$TRUSTC" -Ztrust-verify-output=json main.rs -o prog >"$log" 2>&1); then
        detail="compile refused (this control expects the default policy to ACCEPT it): $(first_error_line "$log")"
    elif ! (cd "$dir" && ./prog >"$dir/run.log" 2>"$dir/run.err") || ! diff -q "$dir/run.log" "$dir/expected.txt" >/dev/null 2>&1; then
        detail="compiled, but did not run to the expected stdout: $(head -c 200 "$dir/run.err" 2>/dev/null)"
    else
        # `--exit-code 0` is the measured status: this branch is reached only
        # after the compile SUCCEEDED (the `if !` above) and the program ran.
        local wire; wire="$(python3 "$WIRE_GRADER" --exit-code 0 --tolerate-print-gap --tolerate-requires-assumption < "$log")"
        case "$wire" in
            *"| clean=no("*)
                # Exact ELEMENT match inside the `nonclean=` field only: a prefix
                # (`assertion`), a longer label, or the same token under
                # `tolerated=` or inside the clean=no(...) reason must not satisfy
                # this control.
                local nc="${wire#*| nonclean=}"; nc="${nc%% |*}"
                case ",$nc," in
                    *",$label,"*) ok=0; detail="not clean, as required: $wire" ;;
                    *) detail="not clean, but not for the named reason \`$label\`: $wire" ;;
                esac ;;
            *) detail="GRADED CLEAN — the tolerance covers a row it must not: $wire" ;;
        esac
    fi
    judge "$name" "trustc-wire-not-clean" "$ok" "$detail"
}

row_lean() { # name file expect(PROVED|REJECTED) [required rejection diagnostic]
    local name="$1" file="$2" expect="$3" reason="${4:-}"
    want_row "$name" lean || return
    local dir; dir="$(stage "$name")"
    local log="$dir/check.log"
    local ok=1 detail
    (cd "$dir" && scrub "$TARGO" trust check "$file" >"$log" 2>&1)
    local rc=$?
    if [ "$expect" = PROVED ]; then
        if [ $rc = 0 ] && grep -q "^PROVED" "$log"; then ok=0; detail="$(grep -m1 '^PROVED' "$log")"; else detail="exit $rc: $(head -c 140 "$log")"; fi
    else
        if normal_refusal "$rc" "$log" && grep -qxF "REJECTED $file" "$log" \
                && [ -n "$reason" ] && grep -qF -- "$reason" "$log"; then
            ok=0; detail="rejected with the open goal: $(grep -m1 -F -- "$reason" "$log" | cut -c1-100)"
        else
            detail="exit $rc, expected REJECTED with '$reason': $(head -c 140 "$log")"
        fi
    fi
    judge "$name" "lean" "$ok" "$detail"
}

row_lean_multi() { # name expect(PROVED) files...
    local name="$1" expect="$2"; shift 2
    want_row "$name" lean-multi || return
    local dir; dir="$(stage "$name")"
    local log="$dir/check.log"
    local ok=1 detail
    (cd "$dir" && scrub "$TARGO" trust check "$@" >"$log" 2>&1)
    local rc=$?
    local proved; proved="$(grep -c '^PROVED' "$log")"
    if [ $rc = 0 ] && [ "$proved" = "$#" ]; then
        # The citing file alone must be REJECTED: the citation is real, not a
        # name that happens to resolve in some ambient environment.
        local lone="${@: -1}"
        local lone_rc=0
        (cd "$dir" && scrub "$TARGO" trust check "$lone" >"$dir/lone.log" 2>&1) || lone_rc=$?
        if [ "$lone_rc" = 0 ]; then
            detail="'$lone' alone PROVED — the citation is not doing any work"
        elif normal_refusal "$lone_rc" "$dir/lone.log" \
                && grep -qxF "REJECTED $lone" "$dir/lone.log" \
                && grep -qE 'Unknown identifier: base(_eq)?([[:space:];]|$)' "$dir/lone.log"; then
            # r17's B.lean needs A.lean's base/base_eq. An unrelated missing
            # name or an inability to start the checker is not this control.
            ok=0; detail="$# files PROVED as one resolution unit; '$lone' alone is REJECTED for the missing citation"
        else
            detail="'$lone' alone failed without the expected citation refusal (exit $lone_rc): $(first_error_line "$dir/lone.log")"
        fi
    else
        detail="exit $rc, $proved/$# PROVED: $(grep -m1 '^error' "$log" | cut -c1-120)"
    fi
    judge "$name" "lean-multi" "$ok" "$detail"
}

row_package() { # name lane(unverified|trust)
    local name="$1" lane="$2"
    want_row "$name" "$([ "$lane" = unverified ] && echo package || echo package-trust)" || return
    local dir; dir="$(stage "$name")"
    local log="$dir/targo.log"
    local ok=1 detail
    if [ "$lane" = unverified ]; then
        if (cd "$dir" && scrub "$TARGO" --unverified run --quiet >"$dir/run.log" 2>"$log"); then
            if diff -q "$dir/expected.txt" "$dir/run.log" >/dev/null; then ok=0; detail="targo --unverified run: stdout matches"; else detail="stdout mismatch: '$(tr '\n' ' ' <"$dir/run.log")'"; fi
        else
            detail="targo --unverified run failed: $(first_error_line "$log")"
        fi
        judge "$name" "package" "$ok" "$detail"
    else
        if (cd "$dir" && scrub "$TARGO" trust build >"$log" 2>&1); then
            ok=0; detail="targo trust build: $(grep -m1 'Gate:' "$log" | cut -c1-100)"
        else
            detail="targo trust build refused: $(grep -m1 -E 'Gate:|^error' "$log" | cut -c1-120)"
        fi
        judge "$name" "package-trust" "$ok" "$detail"
    fi
}

row_targo_file() { # name expect(published|refused)
    # `targo trust check main.rs` — the AUTHENTICATED lane in single-file mode,
    # on a program whose contracts are discharged by the Clean kernel (a cited
    # island theorem and an uncited island definitional equality).
    #
    # `published` is deliberately NOT "exit 0". The defect this lane pins
    # (wf1-probe-package a2) was a compiler that said `proved` while the
    # publication boundary WITHHELD every such row for want of a `clean_cic`
    # artifact, so green requires the PUBLICATION facts themselves:
    #   * `Gate: PASS`, exit 0;
    #   * the boundary line reads `(0 withheld)` — nothing the compiler passed
    #     was relabelled or dropped on the way out;
    #   * BOTH kernel routes appear as `[PROVED]` rows under their own solver
    #     label, and no row is `[UNKNOWN]`.
    #
    # `refused` is the false twin, and it is graded on the REFUSAL, not on the
    # exit status: a lane that publishes kernel rows fails many other ways, so
    # "non-zero exit and no `Gate: PASS`" would pass for reasons that have
    # nothing to do with the false clause. Green requires all four of
    #   * exit non-zero and no `Gate: PASS`;
    #   * the compiler's own defeq refusal reaches the authenticated lane's log
    #     (`was not discharged by definitional equality`);
    #   * NO `[PROVED]` row under `clean-kernel-defeq` — the false clause must
    #     not publish;
    #   * the HONEST cited clause still publishes (`clean-kernel-citation`), so
    #     a refusal that merely broke the whole run is not mistaken for a
    #     refusal of the false clause.
    local name="$1" expect="$2"
    want_row "$name" targo-file || return
    local dir; dir="$(stage "$name")"
    local log="$dir/check.log"
    local ok=1 detail
    (cd "$dir" && scrub "$TARGO" trust check main.rs >"$log" 2>&1)
    local rc=$?
    local gate; gate="$(grep -m1 'Gate:' "$log" | sed 's/^ *//' | cut -c1-110)"
    if [ "$expect" = published ]; then
        local cited defeq unknown
        # Trust (ref-self I1): `clean-kernel-view-citation` /
        # `clean-kernel-view-defeq` are the SAME two lanes over a borrow-erased
        # E6 parameter view. The patterns are widened to `*citation` / `*defeq`
        # so the NEGATIVE gate below cannot be walked past by writing a false
        # clause on a `&self` method: the narrow patterns matched neither label.
        cited="$(grep -cE '^ *\[PROVED\].*\(clean-kernel-(view-)?citation' "$log")"
        defeq="$(grep -cE '^ *\[PROVED\].*\(clean-kernel-(view-)?defeq' "$log")"
        unknown="$(grep -c '^ *\[UNKNOWN\]' "$log")"
        if [ $rc != 0 ] || ! grep -q 'Gate: PASS' "$log"; then
            detail="exit $rc: ${gate:-no Gate line}; $(grep -m1 'Publication boundary:' "$log" | cut -c1-150)"
        elif ! grep -q 'Publication boundary: .*(0 withheld)' "$log"; then
            detail="Gate PASS but the publication boundary withheld rows: $(grep -m1 'Publication boundary:' "$log" | cut -c1-150)"
        elif [ "$cited" = 0 ] || [ "$defeq" = 0 ] || [ "$unknown" != 0 ]; then
            detail="Gate PASS but the kernel rows did not publish as proved: cited=$cited defeq=$defeq unknown=$unknown"
        else
            ok=0; detail="$gate; $(grep -m1 'Publication boundary:' "$log" | cut -c1-90); kernel rows proved: cited=$cited defeq=$defeq"
        fi
    else
        local cited defeq reason
        # Trust (ref-self I1): `clean-kernel-view-citation` /
        # `clean-kernel-view-defeq` are the SAME two lanes over a borrow-erased
        # E6 parameter view. The patterns are widened to `*citation` / `*defeq`
        # so the NEGATIVE gate below cannot be walked past by writing a false
        # clause on a `&self` method: the narrow patterns matched neither label.
        cited="$(grep -cE '^ *\[PROVED\].*\(clean-kernel-(view-)?citation' "$log")"
        defeq="$(grep -cE '^ *\[PROVED\].*\(clean-kernel-(view-)?defeq' "$log")"
        reason="$(grep -m1 'was not discharged by definitional equality' "$log" | sed 's/^ *//' | cut -c1-130)"
        if [ $rc = 0 ] || grep -q 'Gate: PASS' "$log"; then
            detail="ACCEPTED a false Lean-discharged contract (exit $rc): ${gate:-no Gate line}"
        elif ! normal_refusal "$rc" "$log"; then
            detail="abnormal refusal process (exit $rc): $(first_error_line "$log")"
        elif [ -z "$reason" ]; then
            detail="refused, but NOT on the false clause — no defeq refusal in the log: $(grep -m1 '^error' "$log" | cut -c1-130)"
        elif [ "$defeq" != 0 ]; then
            detail="the false clause PUBLISHED anyway: $defeq [PROVED] clean-kernel-defeq row(s)"
        elif [ "$cited" = 0 ]; then
            detail="refused, but the honest cited clause stopped publishing too (collateral damage): cited=$cited"
        else
            ok=0; detail="refused on the false clause (exit $rc, honest cited rows still published: $cited): $reason"
        fi
    fi
    judge "$name" "targo-file" "$ok" "$detail"
}

row_cross_crate() { # name flags...
    local name="$1"; shift
    want_row "$name" cross-crate || return
    local dir; dir="$(stage "$name")"
    local log="$dir/compile.log"
    local ok=1 detail
    if (cd "$dir" && scrub "$TRUSTC" "$@" --crate-type rlib clean_origin_aux.rs >"$log" 2>&1) \
        && (cd "$dir" && scrub "$TRUSTC" "$@" --extern clean_origin_aux="$(ls "$dir"/libclean_origin_aux*.rlib)" -L "$dir" main.rs -o prog >>"$log" 2>&1); then
        if (cd "$dir" && ./prog >"$dir/run.log" 2>"$dir/run.err") && diff -q "$dir/expected.txt" "$dir/run.log" >/dev/null; then
            ok=0; detail="aux rlib + main compiled, ran, stdout matches"
        else
            detail="ran but wrong: '$(tr '\n' ' ' <"$dir/run.log")' $(head -c 100 "$dir/run.err")"
        fi
    else
        detail="compile refused: $(first_error_line "$log")"
    fi
    judge "$name" "cross-crate" "$ok" "$detail"
}

IR_JUDGE="$TRUST_ROOT/scripts/two_language_producer_ratchets.py"
IR_TOOLS_DONE=""
row_trustc_ir() { # name
    # The PRODUCER RATCHETS (WS5.1). One judge run per row; every unit a row
    # needs is measured once into $SCRATCH/ir and reused by the aggregate rows
    # (ir-ta-surface, ir-ta-format, ir-tl-general) that read all of them. The
    # judges are built from the first-party/ gitlinks on first use (`tools
    # --build`, a cargo no-op once built); a judge that cannot be built makes
    # every row FAIL by name — the lane never falls back to an installed CLI.
    local name="$1"
    want_row "$name" trustc-ir || return
    local ok=1 detail log="$SCRATCH/ir-logs/$name.log"
    mkdir -p "$SCRATCH/ir-logs"
    if [ -z "$IR_TOOLS_DONE" ]; then
        IR_TOOLS_DONE=1
        python3 "$IR_JUDGE" tools --build >"$SCRATCH/ir-logs/tools.log" 2>&1 || true
        sed 's/^/  /' "$SCRATCH/ir-logs/tools.log" | grep '^  TOOL'
    fi
    # Trust (2026-09-26): `--write-expected` re-pins a row from the measurement,
    # and until now it was UNREACHABLE through this wrapper. That matters because
    # the aggregate rows (`ir-tl-format_home`, `ir-ta-surface`, `ir-ta-format`,
    # `ir-tl-general`) read units this script measures across the WHOLE run, so
    # invoking the judge standalone on one of them measures nothing and reports
    # every probe FAIL — there was no way to re-pin one without hand-editing
    # `expected.json`, which is how a moved pin loses its reason.
    #
    # ROW-SCOPED ON PURPOSE. A blanket pass-through would re-pin every ir-* row
    # in one run and bless moves nobody looked at. `IR_WRITE_EXPECTED_ROWS` is a
    # space-separated allow-list and defaults to empty, so an ordinary run cannot
    # write a pin. The judge still marks every moved pin UNREVIEWED until a reason
    # is written, so this shortens the loop without weakening the gate.
    local write_expected=()
    case " ${IR_WRITE_EXPECTED_ROWS:-} " in
        *" $name "*) write_expected=(--write-expected) ;;
    esac
    if python3 "$IR_JUDGE" run --row "$name" --work "$SCRATCH/ir" --trustc "$TRUSTC" --targo "$TARGO" "${write_expected[@]+"${write_expected[@]}"}" >"$log" 2>&1; then
        ok=0; detail="$(grep -m1 '^IR-ROW' "$log" | cut -d' ' -f3-)"
    else
        detail="$(grep -m1 '^IR-ROW' "$log" | cut -d' ' -f3-); $(grep -E '^RATCHET [^ ]+ (FLIPPED|FAIL)' "$log" | head -3 | cut -c9-220 | tr '\n' ' ')"
        [ -n "$(grep -m1 '^IR-ROW' "$log")" ] || detail="judge crashed: $(tail -3 "$log" | tr '\n' ' ' | cut -c1-300)"
    fi
    judge "$name" "trustc-ir" "$ok" "$detail"
}

# ---- the battery ------------------------------------------------------------
echo "=== Trust two-language program battery ==="
echo "trustc: $TRUSTC"
echo "        $("$TRUSTC" --version 2>&1 | head -1)"
echo "targo:  $TARGO"
echo "        $("$TARGO" --unverified --version 2>&1 | head -1)"

# ---- compiler identity: what this run is evidence ABOUT ----------------------
# A driver under build/ reports `commit-hash: unknown`; its identity is the
# build stamp x.py wrote at build START (docs/TOOLCHAIN_POSTURE.md 2b). A
# sealed driver names its rev itself. Either is compared with the checkout's
# HEAD: `match=no` means the rows below measure a DIFFERENT compiler than the
# KNOWN_RED list was written against, and no KNOWN_RED line may be deleted on
# this run's say-so. `unknown` is disclosed as such, never read as a match.
CHECKOUT_HEAD="$(git -C "$TRUST_ROOT" rev-parse HEAD 2>/dev/null || echo unknown)"
COMPILER_ID="unknown"; COMPILER_ID_SOURCE="none"
case "$TRUSTC" in
    */build/*|*/build.noindex/*)
        # The build tree the driver lives in, which need not be this checkout
        # (a sibling worktree may measure the main tree's build). A physical
        # path names the Spotlight-excluded `build.noindex` that `build` links
        # to (docs/BUILD_AND_INSTALL.md); the provenance file is the same one.
        case "$TRUSTC" in
            */build/*) BUILD_TREE="${TRUSTC%%/build/*}/build" ;;
            *) BUILD_TREE="${TRUSTC%%/build.noindex/*}/build.noindex" ;;
        esac
        if [ -f "$BUILD_TREE/trust-build-provenance" ]; then
            COMPILER_ID="$(sed -n 's/^head=//p' "$BUILD_TREE/trust-build-provenance" | head -1)"
            COMPILER_ID_SOURCE="$BUILD_TREE/trust-build-provenance (head=; tree_state=$(sed -n 's/^tree_state=//p' "$BUILD_TREE/trust-build-provenance" | head -1))"
        fi ;;
    *)
        COMPILER_ID="$("$TRUSTC" -Vv 2>/dev/null | sed -n 's/^commit-hash: //p' | head -1)"
        COMPILER_ID_SOURCE="trustc -Vv commit-hash" ;;
esac
[ -z "$COMPILER_ID" ] && COMPILER_ID="unknown"
if [ "$COMPILER_ID" = unknown ] || [ "$CHECKOUT_HEAD" = unknown ]; then
    ID_MATCH="unknown"
elif [ "$COMPILER_ID" = "$CHECKOUT_HEAD" ]; then
    ID_MATCH="yes"
else
    ID_MATCH="no"
fi
IDENTITY_LINE="compiler-identity: $COMPILER_ID ($COMPILER_ID_SOURCE); checkout HEAD: $CHECKOUT_HEAD; match=$ID_MATCH"
echo "$IDENTITY_LINE"
echo

row_trustc_run  r01_rust_calls_clean_select        -Ztrust-verify=off
row_trustc_run  r02_rust_calls_clean_unit_file     -Ztrust-verify=off
row_trustc_run  r03_rust_calls_clean_recursive_gcd -Ztrust-verify=off
row_lean        r04_lean_standalone_proved   Basic.lean PROVED
row_lean        r05_lean_standalone_rejected Bad.lean   REJECTED 'unsolved goals'
row_trustc_lib  r06_rust_contract_proved_strict   ok
row_trustc_lib  r07_rust_contract_refuted_strict  refused lib::double=postcondition
row_trustc_run  r08_clean_origin_call_verify_on
row_trustc_run  --tolerated-print-gap --tolerated-requires r09_println_verify_on
row_trustc_run  r10_island_unicode                 -Ztrust-verify=off
row_trustc_run  r11_island_tactic_theorem          -Ztrust-verify=off
row_trustc_run  r12_island_term_theorem            -Ztrust-verify=off
row_package     r13_package_unverified_run  unverified
row_package     r14_package_trust_build     trust
row_trustc_lib  r15_citation_by_theorem           ok
row_cross_crate r16_cross_crate_clean_origin       -Ztrust-verify=off
row_lean_multi  r17_lean_multi_file_citation PROVED A.lean B.lean
row_lean        r26_lean_standin_import_refused     WithMathlib.lean REJECTED "\`import Mathlib\` was served by Clean's built-in prelude stand-in"
row_trustc_run  r18_lean_calls_rust                -Ztrust-verify=off
row_trustc_run  r19_rust_calls_lean_unit_file      -Ztrust-verify=off
row_trustc_run  r20_island_tactic_theorem_nat      -Ztrust-verify=off
row_trustc_run  r21_clean_let                      -Ztrust-verify=off
row_trustc_run  r22_clean_bool_decide               -Ztrust-verify=off
row_trustc_run  r23_clean_bool_connective           -Ztrust-verify=off
row_trustc_run  r24_clean_pure_callee_let           -Ztrust-verify=off
row_trustc_run  r25_clean_trait_impl_callee         -Ztrust-verify=off
row_trustc_refused r27_println_verify_on_violated_requires 'Trust strict verification failed for `main::main`' main::main=precondition
row_trustc_wire_not_clean r28_println_with_unproved_assert_wire_not_clean runtime_checked:assert
row_targo_file  r29_targo_trust_check_lean_discharged published
row_targo_file  r30_targo_trust_check_lean_false_twin refused
# The first ALab-derived pair: the scalar core of `~/a3d/crates/a3d-kernel`
# (`range_in_bounds`, `min4`), converted to the two-language surface, through
# the same authenticated lane. r32 mutates ONE token of the Lean model — a
# half-open bound written closed — and must be refused with `min_span`'s honest
# citation still publishing. See each row's header for the source file and the
# exact simplifications.
#
# READ r31 AND r32 TOGETHER. The `refused` needle
# (`was not discharged by definitional equality`) is also what a clause that
# never reached the kernel emits, so a green r32 beside a RED r31 means the
# clause shape is wrong on this compiler, not that the false model was caught.
# The same pair-reading rule applies to r29/r30.
#
# r33 is r31 with the island moved verbatim into a `clean mod` unit file: the
# tree's only measurement of a CONTRACT discharging from an out-of-line unit,
# which the conversion guide recommends and nothing else pins.
row_targo_file  r31_alab_a3d_kernel_bounds       published
row_targo_file  r32_alab_a3d_kernel_false_model  refused
row_targo_file  r33_alab_a3d_kernel_unit_file    published
# r34/r35 were authored as r26/r27, renumbered to r31/r32 at the first merge, and
# renumbered AGAIN here: the fleet claimed r26-r30 in that merge and r31-r33 in the
# next one, both while this landing was in flight. Same rows, same programs, third
# spelling. The collision is structural, not bad luck — row numbers are allocated by
# whoever lands first and nothing reserves them — so a lane holding rows across a
# merge should expect to renumber and should grep the whole repo for the old names.
row_trustc_run  r34_ay_pb_certificate_joint         -Ztrust-verify=off
row_trustc_run  r35_ay_pb_evaluator_model           -Ztrust-verify=off
row_trustc_run  r36_joint_cited_lean_theorem
#
# The aterm pair below was renumbered r34-r35 -> r38-r39 for exactly
# the reason the note above gives: the fleet claimed r34-r36 while they were in
# flight. Every reference moved with the directories — the registrations here,
# the fixture headers, `crates/trust-certify/tests/alab_pilot_shapes.rs`,
# `docs/TWO_LANGUAGE_CONVERSION_GUIDE.md` and its path checker.
#
# The aterm ALab pair. Same lane, same pair discipline as r31/r32:
# one function carries the uncited island-defeq clause the twin mutates, another
# carries an untouched citation, and they are kept on SEPARATE functions so the
# twin's refusal cannot be collateral damage.
#
# r38/r39 — `~/aterm`'s `constant_time_eq` length seed. r35's island is not a
# mutated token: it is aterm's OWN pre-47cca4b seed, the one the fix removed,
# which agrees with the honest model on every length delta below 65536 and so
# survives any realistic test.
row_targo_file  r38_alab_aterm_ct_eq_seed        published
row_targo_file  r39_alab_aterm_ct_eq_lossy_seed  refused

# The PRODUCER RATCHETS (roadmap WS5.1): the Part A (`ir-ta*`, Rust + Clean
# island -> trust-ir) and Part A-Lean (`ir-tl*`, standalone Lean lane, format
# homes, Clean general pipeline) rows of the 2026-09-17 proof program. The row
# list is the judge's own (`two_language_producer_ratchets.py list`), in
# dependency order: every aggregate row follows the units it reads.
# The row list is read ONCE and must be non-empty: a judge that cannot even
# list its rows (a syntax error, a missing python) would otherwise make the
# whole lane vanish from the battery silently, and a battery with no ir-* rows
# would still print PASS. That is a FAIL row of its own, never zero rows.
IR_ROW_LIST="$(python3 "$IR_JUDGE" list 2>"$SCRATCH/ir-list.err")" || IR_ROW_LIST=""
if [ -z "$IR_ROW_LIST" ]; then
    if want_row ir-lane-rows trustc-ir; then
        judge ir-lane-rows trustc-ir 1 "the producer-ratchet judge listed no rows: $(head -c 300 "$SCRATCH/ir-list.err" | tr '\n' ' ')"
    fi
fi
for ir_row in $IR_ROW_LIST; do
    row_trustc_ir "$ir_row"
done
if [ -n "$IR_EVIDENCE" ]; then
    # Only THIS run's reports; a row that did not run is recorded as missing
    # (the artifact then says complete=false), never filled from a pin.
    python3 "$IR_JUDGE" evidence --work "$SCRATCH/ir" --out "$IR_EVIDENCE" || true
fi
#
# r42/r43/r44 — the "THIS MAGIC CONSTANT IS THE RIGHT ONE" shape, from ~/a3d's
# conversion ledger, which calls it "the single most valuable thing left undone
# in this conversion". a3d's `octree_depth_fits` proves its body IS the decision
# `depth < 21`; nothing proved that 21 is the right number. r42 links the two:
# a CITED clause whose Lean theorem proves the body's decision EQUALS a decision
# over a different predicate at a different carrier (`3 * (depth + 1) < 64`, at
# Nat). The congruence that makes that expressible is Lean core's
# `decide_eq_decide` (`Init/PropLemmas.lean:512`, v4.30.0-rc2), which this
# Clean's prelude does NOT carry — r42's island writes out the one direction it
# needs as a `Decidable.rec` term, axiom-free.
#
# Two twins, because the link has two halves that can rot independently:
#   * r43 mutates the RUST (`21` -> `22`) and keeps the honest citation — the
#     citation audit refuses. This is the case a3d's existing uncited clause
#     cannot catch, since moving the constant in the Lean model too would make
#     Rust and Lean agree with each other and both be wrong.
#   * r44 mutates the LEAN (span bound `64` -> `63`) — `span_fwd`'s ground step
#     becomes `63 < 63` and the declaration stops checking, before any contract
#     is considered.
# Each twin's header records the mutation control measured beside it.
row_targo_file  r42_alab_a3d_decide_link                published
row_trustc_audit_refused r43_alab_a3d_decide_link_false_constant lib::octree_depth_fits depth_fits_is_span_fits
row_lean        r44_alab_a3d_decide_link_false_span     FalseSpan.lean REJECTED 'Tactic failed: decide: comparison is false'
# The F-131 checker-level negative twin (roadmap WS8.8): the proof program's
# `p19_false_theorem` (a `:= rfl` proof of `dbl a = a`) must be REJECTED by
# `targo trust check` naming `dbl_wrong`. Its EMIT-lane refusal is the judge
# row ir-tl19_false_theorem; the sibling twin `p16_tree_33_nodes` is NOT here
# because the checker PROVES it (measured 2026-09-21: `PROVED ... 1
# declaration(s) kernel-checked`) — its refusal is emit-only and is pinned by
# ir-tl16_tree_33_nodes. The third F-131 twin, GENERAL.link.no_shims, is
# pinned by ir-tl-general. One lane per fact; nothing is written twice.
# (Numbered r45: this landed beside origin's r42..r44 a3d decide-link rows.)
row_lean        r45_lean_false_rfl_theorem_rejected p19_false_theorem.lean REJECTED '`dbl_wrong` did not elaborate'
echo
echo "PASS=$PASSES RED(expected)=$REDS FAIL=$FAILS UNEXPECTED-PASS=$UNEXPECTED"
echo "$IDENTITY_LINE"

# Derive the full denominator from fixture directories, independently of the
# registrations above. An omitted row (or a mistyped filter running zero rows)
# must fail even when every executed compiler command had its expected outcome.
INVENTORY_STATUS=0
INVENTORY_DETAIL="$(printf '%s\n' "${EXECUTED_ROWS[@]}" | python3 \
    "$TRUST_ROOT/scripts/check_two_language_program_inventory.py" \
    --rows-dir "$ROWS_DIR" --only "$ONLY" --lane "$LANE" 2>&1)" || INVENTORY_STATUS=$?
echo "$INVENTORY_DETAIL"

if [ -n "$OUT_FILE" ]; then
    {
        echo "# Two-language program battery"
        echo
        echo "- trustc: \`$("$TRUSTC" --version 2>&1 | head -1)\` at \`$TRUSTC\`"
        echo "- targo: \`$("$TARGO" --unverified --version 2>&1 | head -1)\`"
        echo "- $IDENTITY_LINE"
        echo "- date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
        echo "- result: PASS=$PASSES RED(expected)=$REDS FAIL=$FAILS UNEXPECTED-PASS=$UNEXPECTED"
        echo "- inventory exit: $INVENTORY_STATUS"
        printf '%s\n' "$INVENTORY_DETAIL"
        echo
        echo "| row | lane | verdict | detail |"
        echo "|---|---|---|---|"
        printf '%s\n' "${RESULT_ROWS[@]}"
    } > "$OUT_FILE"
    echo "wrote $OUT_FILE"
fi

if [ "$FAILS" != 0 ] || [ "$UNEXPECTED" != 0 ] || [ "$INVENTORY_STATUS" != 0 ]; then
    exit 1
fi
exit 0
