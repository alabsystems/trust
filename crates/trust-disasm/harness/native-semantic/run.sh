#!/bin/sh
# ============================================================================
# THE NATIVE SEMANTIC DIFFERENTIAL — a STANDING GATE, not a measurement.
#
#   for every word W and starting state S:
#       decode(W) ok  ∧  effects(W) ok  ∧  W executes natively from S
#   ⟹ replaying effects(W) on S agrees with the HARDWARE on
#       x0..x30, sp, V0..V31, NZCV, the next pc, and memory.
#
# WHY THIS EXISTS. `native-invariant` beside it checks that a word the gate
# accepts is a word the CPU will RUN, and its own limits section says plainly
# that it checks FAULT vs NO-FAULT and never SEMANTICS. But the output gate
# does not merely need the word to run — it re-derives the object's meaning
# from `Aarch64Semantics::effects` and proves a theorem about THAT. A wrong
# effect list is a false Proven exactly as much as an unexecutable word, and it
# is the quieter of the two: nothing faults, nothing is refused, the answer is
# simply about a different instruction.
#
# WHY IT IS A GATE AND NOT A REPORT. Four fault families were found one at a
# time, each after the previous was declared closed. A differential that ran
# once would have caught all four and then gone stale before the fifth. The
# only version of this that is worth anything is the version that runs again.
#
# ---------------------------------------------------------------------------
# THREE STAGES, IN THIS ORDER, AND STAGE 2 IS THE ONE THAT MATTERS
# ---------------------------------------------------------------------------
#
#   1. GROUND TRUTH   the unmutated model must agree with the hardware on every
#                     word of `selftest.s` — clang-assembled, so each is an
#                     instruction the assembler chose to emit.
#
#   2. NON-VACUITY    the differential is re-run against SEVEN DELIBERATELY
#                     WRONG models, and every one must be CAUGHT. Each mutation
#                     is a bug that actually escaped into this codebase (see
#                     `src/mutate.rs`). This is the stage that makes stage 3
#                     mean anything: a harness that has gone blind — an
#                     unloaded register file, a swallowed exclusion, a field
#                     that is zero on both sides — still prints a large
#                     `compared` count and `0 mismatches`. THAT NUMBER IS NOT
#                     EVIDENCE UNLESS A WRONG MODEL WOULD HAVE BEEN RED, and
#                     stage 2 is where that is demonstrated, on this run, on
#                     this host, not remembered from the day it was written.
#
#   3. SWEEP          the stratified population at this tier's cap, checked
#                     against the recorded baseline.
#
# ---------------------------------------------------------------------------
# TIERS — measured on an M-series macOS host, WORKERS=8
# ---------------------------------------------------------------------------
#
#   ./run.sh --selftest    stages 1-2 only                       ~2 s
#   ./run.sh --fast        stages 1-3 over a FROZEN population   ~3 s
#   ./run.sh               stages 1-3, rescanned, cap 3000      ~22 s   (DEFAULT)
#   ./run.sh --accept      rerun the chosen tier and rewrite its baseline entry
#
# Wall clock on an idle host with a warm tree, builds included (they are no-ops
# when nothing changed; a cold `cargo build` of the driver adds ~40 s). CPU cost:
# the full tier is ~90 CPU-seconds — it saturates 8 cores for 20 seconds — and
# the fast tier ~2. NOTHING HERE IS EXPENSIVE ENOUGH TO JUSTIFY SKIPPING IT,
# which is the only reason the tiering exists at all: not to make the check
# affordable, but to make the pre-commit one instant.
#
# WHICH TIER IS WHICH, AND WHY THE SEAM IS THERE. The two tiers differ in HOW
# THEY CHOOSE WORDS, not in how hard they check them:
#
#   --fast  replays `population-fast.txt`, a committed 17,194-word stratified
#           population. Zero scan cost, byte-identical on every host, and
#           reviewable as a diff. It is a REGRESSION detector: a fixed set of
#           words whose verdicts must not change.
#
#   default rescans the 2^32 space and re-stratifies at cap 3000. It costs ~10 s
#           more because the scan walks 320M indices to reach the rare opcodes.
#           It is a DISCOVERY check: it sees forms that a decoder or semantics
#           change has newly admitted, which a frozen list never can.
#
# The fast tier is not a weaker check — same three stages, same seven mutations,
# same 86 opcodes compared. It is a smaller population. Run it before every
# commit; run the default tier before landing anything that touches
# `Aarch64Semantics` or the decoder, because only it can find a NEW form.
#
# NEITHER TIER IS EXHAUSTIVE. Both sample the 2^32 encoding space. Exhaustiveness
# belongs to `native-invariant`, which checks the weaker fault-class invariant
# and can afford all 2^32 words.
#
# DETERMINISM. The population is a pure function of the tier's cap and does NOT
# depend on `--workers` — that controls execution parallelism only. This was not
# always true: both selectors used to shard by thread count, so a baseline
# recorded at `--workers 8` could not be reproduced at `--workers 4`. Verified
# identical at 3, 8 and 11 workers. Every run prints a population digest and the
# gate fails on a mismatch, because a moved population means the counts are not
# comparable to the baseline — a harness change, not a model regression, and it
# must not be reported as one.
#
# THE BASELINE IS NOT ZERO, AND THAT IS THE POINT. Eight scalar-FP families are
# known-diverging and open (see baseline.json — they are bitvector
# approximations of IEEE operations, and the correct resolution is REFUSAL, not
# this entry). The gate fails on any opcode OUTSIDE that recorded set — a NEW
# family — on any lost coverage, and on any mutation that escapes. Recording the
# known set is what makes a new one visible; baselining at zero would require
# either fixing them first or lying.
#
# REQUIREMENTS: aarch64 macOS host; clang (Command Line Tools); cargo +beta.
#
# IT IS NOT PART OF `cargo test`, AND CANNOT BE. It assembles code, executes
# arbitrary instruction encodings, and reads a trap ucontext; it needs an
# aarch64 host with an assembler. That is a reason to run it deliberately, not a
# reason to treat it as optional — see ../README.md for when.
# ============================================================================
set -e
cd "$(dirname "$0")"
HERE=$(pwd)

CLANG=${CLANG:-/Library/Developer/CommandLineTools/usr/bin/clang}
SDK=${SDK:-/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk}
WORKERS=${WORKERS:-8}
WORK=${WORK:-/tmp/natsem}

TIER=full
ACCEPT=0
for a in "$@"; do
    case "$a" in
    --selftest) TIER=selftest ;;
    --fast) TIER=fast ;;
    --full) TIER=full ;;
    --accept) ACCEPT=1 ;;
    *) echo "usage: $0 [--selftest|--fast|--full] [--accept]" >&2; exit 2 ;;
    esac
done
# The fast tier REPLAYS a committed population; the full tier RESCANS.
case "$TIER" in
fast) CAP=200; SELECT="--words $HERE/population-fast.txt" ;;
*) CAP=3000; SELECT="--stratify 3000" ;;
esac

mkdir -p "$WORK"
# STALE RESULTS ARE WORSE THAN NO RESULTS. Every verdict below is read from a
# `*.result.json` the driver writes. If a driver run dies without writing one,
# a leftover file from the PREVIOUS run would be read in its place and the gate
# would confidently report a stale PASS — a broken harness reporting success,
# which is the exact failure mode this gate exists to prevent. Removing them
# first turns that into the loud "produced no result json" error instead.
rm -f "$WORK"/*.result.json "$WORK"/battery.txt

echo "== building the native semantic executor =="
"$CLANG" -arch arm64 -isysroot "$SDK" -O2 -o natsem natsem.c

echo "== building the differential driver =="
CFG_RELEASE="1.99.0-dev" CFG_RELEASE_CHANNEL=dev RUSTC_BOOTSTRAP=1 \
    cargo +beta build --release --quiet

DIFF=./target/release/natsem-diff

# ---------------------------------------------------------------------------
# STAGE 1 — GROUND TRUTH
# ---------------------------------------------------------------------------
echo
echo "== stage 1/3: ground truth — clang-assembled words must agree =="
"$CLANG" -arch arm64 -c selftest.s -o "$WORK/selftest.o"
objdump -d "$WORK/selftest.o" | awk '$1 ~ /^[0-9a-f]+:$/ {print $2}' > "$WORK/selftest.txt"
$DIFF --words "$WORK/selftest.txt" --workers "$WORKERS" --out "$WORK/selftest" \
    > "$WORK/selftest.out" 2>&1 || true

# ---------------------------------------------------------------------------
# STAGE 2 — NON-VACUITY
#
# Runs BEFORE the sweep on purpose. If the differential has gone blind there is
# no point spending four minutes producing a green number from it, and worse,
# that green number would be believed.
# ---------------------------------------------------------------------------
echo
echo "== stage 2/3: NON-VACUITY — every deliberately wrong model must be caught =="
# THE BATTERY COMES FROM THE CODE, not from the baseline. A mutation added to
# mutate.rs but missing from baseline.json must be a LOUD failure, not a
# silently skipped check — see the verdict block, which cross-checks the two.
$DIFF --list-mutations > "$WORK/battery.txt"
while read -r m; do
    [ -n "$m" ] || continue
    $DIFF --words "$WORK/selftest.txt" --workers "$WORKERS" --mutate "$m" \
        --out "$WORK/mut_$m" > "$WORK/mut_$m.out" 2>&1 || true
done < "$WORK/battery.txt"

# ---------------------------------------------------------------------------
# STAGE 3 — SWEEP
# ---------------------------------------------------------------------------
if [ "$TIER" != selftest ]; then
    echo
    echo "== stage 3/3: sweep — $TIER tier, per-opcode cap $CAP =="
    # shellcheck disable=SC2086
    $DIFF $SELECT --workers "$WORKERS" --out "$WORK/sweep" > "$WORK/sweep.out" 2>&1 || true
    sed -n '/^elapsed/,/TOTAL EXCLUDED/p' "$WORK/sweep.out"
fi

# ---------------------------------------------------------------------------
# THE VERDICT
# ---------------------------------------------------------------------------
python3 - "$HERE" "$WORK" "$TIER" "$CAP" "$ACCEPT" <<'PY'
import json, os, sys

here, work, tier, cap, accept = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5] == '1'
bpath = os.path.join(here, 'baseline.json')
base = json.load(open(bpath))
fail = []
note = []


def result(name):
    p = os.path.join(work, name + '.result.json')
    if not os.path.exists(p):
        sys.exit(f'FATAL: {name} produced no result json — the driver did not finish. '
                 f'See {os.path.join(work, name + ".out")}')
    return json.load(open(p))


# ---- stage 1: ground truth -------------------------------------------------
st = result('selftest')
nv = base['nonvacuity']
print()
print('-- stage 1: ground truth (clang-assembled) --')
print(f'   compared {st["compared"]} across {st["opcodes_compared"]} opcodes, '
      f'mismatches {st["mismatched"]}')
if st['mismatched']:
    fail.append(f'stage 1: the model disagrees with clang-assembled ground truth on '
                f'{st["mismatched"]} comparisons — {st["mismatch_families"]}')
st_cov = (st['compared'] + st['excluded']['platform_register_x18']
          + st['excluded']['native_timeout'])
if st_cov < nv['corpus_coverage_floor']:
    fail.append(f'stage 1: coverage {st_cov} (compared {st["compared"]} + x18-excluded), '
                f'floor is {nv["corpus_coverage_floor"]} — the corpus stopped reaching the '
                f'model. A shrinking denominator is how "0 mismatches" becomes meaningless.')
if st['population_digest'] != nv['corpus_digest'] and not accept:
    note.append(f'stage 1: corpus digest {st["population_digest"]} != recorded '
                f'{nv["corpus_digest"]} — selftest.s changed; counts below are against a '
                f'different corpus. Rerun with --accept once the change is intended.')

# ---- stage 2: non-vacuity --------------------------------------------------
print()
print('-- stage 2: NON-VACUITY — a wrong model must be caught --')

# The battery is whatever `mutate.rs` declares. A mutation present in the code
# but absent from the baseline would otherwise be a check that never runs and
# never complains.
battery = [l.strip() for l in open(os.path.join(work, 'battery.txt')) if l.strip()]
missing = [m for m in battery if m not in nv['caught']]
stale = [m for m in nv['caught'] if m not in battery]
if missing and not accept:
    fail.append(f'stage 2: mutations {missing} are declared in src/mutate.rs but have no '
                f'baseline entry. They ran, but with nothing to check them against. Rerun '
                f'with --accept to record them.')
if stale and not accept:
    fail.append(f'stage 2: baseline records mutations {stale} that src/mutate.rs no longer '
                f'declares. A recorded check that cannot run is worse than no check.')

caught = {}
for m, recorded in sorted((k, v) for k, v in nv['caught'].items() if k in battery):
    r = result('mut_' + m)
    caught[m] = r['mismatched']
    if r['mismatched'] == 0:
        mark = 'BLIND'
        fail.append(f'stage 2: mutation {m!r} was NOT caught. The differential can no longer '
                    f'see this class of error, so its "0 mismatches" is not evidence. '
                    f'This mutation exists because that bug already shipped once.')
    elif r['mismatched'] < recorded:
        mark = 'WEAKER'
        fail.append(f'stage 2: mutation {m!r} caught {r["mismatched"]} of a recorded '
                    f'{recorded}. Detection power may only increase; a drop means coverage '
                    f'was lost somewhere. Investigate, then --accept if it is intended.')
    else:
        mark = 'ok' + ('' if r['mismatched'] == recorded else ' (+)')
    print(f'   {mark:<8} {m:<21} caught {r["mismatched"]:>4}  (recorded {recorded})')

# ---- stage 3: the sweep ----------------------------------------------------
sw = None
if tier != 'selftest':
    sw = result('sweep')
    tb = base['tiers'][tier]
    fams = sw['mismatch_families']
    known = set(tb['known_mismatch_opcodes'])
    print()
    print(f'-- stage 3: sweep ({tier} tier, cap {cap}) --')
    print(f'   population {sw["population_words"]} words, digest {sw["population_digest"]}')
    print(f'   compared {sw["compared"]} across {sw["opcodes_compared"]} opcodes '
          f'in {sw["scan_s"]:.0f}s scan + {sw["sweep_s"]:.0f}s sweep')
    print(f'   coverage  : {sw["compared"] + sw["excluded"]["platform_register_x18"] + sw["excluded"]["native_timeout"]} '
          f'(compared + x18-excluded + timed-out; floor {tb["coverage_floor"]})')
    print('   families  : ' + (', '.join(f'{k}={v}' for k, v in sorted(fams.items())) or 'none'))
    print('   known-open: ' + (', '.join(sorted(known)) or 'none'))

    if sw['population_digest'] != tb['population_digest'] and not accept:
        fail.append(f'stage 3: population digest {sw["population_digest"]} != recorded '
                    f'{tb["population_digest"]}. A DIFFERENT SET OF WORDS was checked, so no '
                    f'count below is comparable to the baseline. This is a harness/selector '
                    f'change, not a model regression — do not read it as one.')
    if sw['sigill_violations']:
        fail.append(f'stage 3: {sw["sigill_violations"]} SIGILL — the CPU refuses a word the '
                    f'model accepts. That is the fault-class invariant, violated; run '
                    f'../native-invariant to characterise it.')
    new = sorted(set(fams) - known)
    if new:
        fail.append('stage 3: NEW MISMATCH FAMILY: ' + ', '.join(
            f'{k}={fams[k]}' for k in new) + '. A model/hardware divergence outside the '
            'recorded set. Reproduce one word with --words, then either fix the semantics '
            'or REFUSE the form. Approximating onto a neighbouring value is never acceptable.')
    # A NEW FAMILY IS NOT THE ONLY REGRESSION SHAPE.
    #
    # `known_mismatch_opcodes` is a set of NAMES, so a regression INSIDE an
    # already-open family was invisible: break `sem_fcmp` so that every `Fcmp`
    # word disagrees with the hardware and the family is still just `Fcmp`,
    # `new` is still empty, and this gate still passed. The counts were computed
    # and then discarded at record time.
    #
    # So a known family's count is a CEILING, not a licence. Growth means words
    # that used to agree now do not.
    counts = tb.get('known_mismatch_counts')
    if counts is None:
        note.append('stage 3: this baseline predates per-family mismatch counts, so growth '
                    'INSIDE a known-open family is not gated. Rerun with --accept to record '
                    'them.')
    else:
        grew = sorted(k for k in fams if k in known and fams[k] > counts.get(k, 0))
        if grew:
            fail.append('stage 3: KNOWN FAMILY GREW: ' + ', '.join(
                f'{k}={fams[k]} > {counts.get(k, 0)}' for k in grew) + '. Words that used to '
                'AGREE with the hardware no longer do. The family being already-open is not '
                'a licence for more of it — reproduce one of the new words with --words.')
    # COVERAGE IS GATED ON `compared + x18-excluded + timed-out`, NOT ON
    # `compared`.
    #
    # Two of the buckets are not functions of the word, and both were learned
    # from a false FAIL rather than reasoned out in advance.
    #
    #   x18: two full-tier runs of the identical population differed by exactly
    #   ONE comparison, with `platform_register_x18` moving 14232 -> 14233.
    #   Whether the OS has already reset x18 in a given worker process decides
    #   whether a word that READS x18 is comparable, so a word can move between
    #   `compared` and `platform_register_x18` — and between those two ONLY,
    #   since the x18 test is the last gate before the comparison.
    #
    #   TIMEOUT: a fast-tier run during a stage-1 rustc rebuild reported
    #   coverage 47300 against a floor of 47320 recorded on an idle host. The
    #   20 words were TIMEOUTs — decided by how many other processes wanted the
    #   core inside the alarm window, not by the candidate. Folded into
    #   `native fault`, as it used to be, it made this floor depend on what else
    #   the machine was doing, and a gate that fails because someone started a
    #   build is a gate people learn to re-run instead of read.
    #
    # Every OTHER exclusion is deterministic in (word, profile), so the sum of
    # these three is exactly reproducible and is the honest coverage invariant.
    # A blanket tolerance on `compared` would have hidden the same amount of
    # REAL coverage loss; this hides none. The second check below is what stops
    # either race from becoming a systematic exclusion under cover of the first.
    x18 = sw['excluded']['platform_register_x18']
    timeout = sw['excluded']['native_timeout']
    coverage = sw['compared'] + x18 + timeout
    if coverage < tb['coverage_floor']:
        fail.append(f'stage 3: coverage {coverage} (compared {sw["compared"]} + x18-excluded '
                    f'{x18} + timed-out {timeout}), floor {tb["coverage_floor"]}. Real '
                    f'coverage regressed — read the blind-spot ledger in the run output to '
                    f'see which exclusion swallowed it.')
    if timeout > tb.get('timeout_excluded', 0) * 1.5 + 32:
        fail.append(f'stage 3: {timeout} timeouts vs recorded {tb.get("timeout_excluded", 0)}. '
                    f'The host was too loaded for this run to be a measurement, or a '
                    f'candidate class has started hanging. Either way the numbers below are '
                    f'not comparable to the baseline.')
    if x18 > tb['x18_excluded'] * 1.01 + 1:
        fail.append(f'stage 3: x18 exclusions {x18} vs recorded {tb["x18_excluded"]}. The '
                    f'platform-register race has become a systematic exclusion; words are '
                    f'leaving the comparison rather than flaking between runs.')
    if sw['opcodes_compared'] < tb['opcodes_floor']:
        fail.append(f'stage 3: {sw["opcodes_compared"]} opcodes compared, floor '
                    f'{tb["opcodes_floor"]}. An opcode with 0 compared words is not evidence '
                    f'about that opcode.')
    gone = sorted(known - set(fams))
    if gone:
        note.append('stage 3: no longer diverging: ' + ', '.join(gone) +
                    ' — rerun with --accept to tighten the baseline.')

# ---- accept ----------------------------------------------------------------
if accept:
    nv['corpus_digest'] = st['population_digest']
    nv['corpus_coverage_floor'] = st_cov
    # Re-record from the BATTERY, so accepting also prunes entries whose
    # mutation no longer exists and adds ones that were newly declared.
    nv['caught'] = {m: result('mut_' + m)['mismatched'] for m in battery}
    if sw is not None:
        base['tiers'][tier] = {
            **base['tiers'][tier],
            'cap': cap,
            'population_words': sw['population_words'],
            'population_digest': sw['population_digest'],
            'coverage_floor': (sw['compared'] + sw['excluded']['platform_register_x18']
                               + sw['excluded']['native_timeout']),
            'compared_observed': sw['compared'],
            'x18_excluded': sw['excluded']['platform_register_x18'],
            'timeout_excluded': sw['excluded']['native_timeout'],
            'opcodes_floor': sw['opcodes_compared'],
            'known_mismatch_opcodes': sorted(sw['mismatch_families']),
            # Per-family COUNTS, so growth inside an already-open family is a
            # regression rather than a silent pass. Names alone made a broken
            # `sem_fcmp` — every Fcmp word diverging — indistinguishable from
            # the recorded state.
            'known_mismatch_counts': dict(sorted(sw['mismatch_families'].items())),
            'mismatches': sw['mismatched'],
            'scan_s': round(sw['scan_s'], 1),
            'sweep_s': round(sw['sweep_s'], 1),
        }
    # ensure_ascii=False: the prose in this file is full of em dashes, and
    # escaping them to \uXXXX turns every --accept into a hundred-line diff that
    # buries the four numbers that actually changed. A baseline nobody can read
    # the diff of is a baseline nobody reviews.
    json.dump(base, open(bpath, 'w'), indent=2, ensure_ascii=False)
    open(bpath, 'a').write('\n')
    print()
    print(f'baseline REWRITTEN for tier {tier!r}. Read the diff before committing it: '
          f'accepting a baseline is accepting every divergence in it.')
    sys.exit(0)

# ---- verdict ---------------------------------------------------------------
print()
print('=' * 74)
for n in note:
    print('  NOTE: ' + n)
if fail:
    for f in fail:
        print('  FAIL: ' + f)
    print()
    print('  RESULT: FAIL')
    print('=' * 74)
    sys.exit(1)
print(f'  RESULT: PASS — ground truth exact, all {len(caught)} mutations caught, '
      f'no new family.')
print('=' * 74)
PY
