#!/bin/sh
# ============================================================================
# THE NATIVE INVARIANT CHECK — a STANDING GATE, not a measurement.
#
#   for every word W:
#       trust_disasm::decode_aarch64(W) is Ok
#     ∧ trust_machine_sem::Aarch64Semantics::effects(W) is Ok
#   ⟹ W does not fault when executed natively.
#
# Four soundness families have been found one at a time, each after the previous
# was declared closed, and every one was a word the gate ACCEPTED and the CPU
# REFUSES. This checks the whole CLASS by executing candidates on the hardware,
# which is the only oracle that sees it: a mnemonic differential compares NAMES,
# and both aliasing and reserved-field words can carry correct names.
#
# WHAT IT DOES NOT CHECK: SEMANTICS. This is a fault vs no-fault oracle. A word
# that runs but does something other than what `effects` says is invisible here
# and is a false Proven all the same. That class belongs to ../native-semantic,
# which found three live families the moment it existed. Run both.
#
# ---------------------------------------------------------------------------
# THREE STAGES, IN THIS ORDER
# ---------------------------------------------------------------------------
#
#   1. EXECUTOR GROUND TRUTH  three CONSTRAINED UNPREDICTABLE words the CPU
#                             refuses, each paired with a one-register control
#                             it runs, plus udf and nop. If `natexec` cannot
#                             tell these apart it is not an oracle.
#
#   2. SWEEP NON-VACUITY      the same three known-refused words are driven
#                             through the WHOLE Rust sweep with the antecedent
#                             bypassed (`--force-candidates`), and must be
#                             reported as violations while the controls are not.
#
#                             THIS STAGE EXISTS BECAUSE THE BASELINE IS ZERO.
#                             Every word that would violate the invariant has
#                             been fixed, so a real population can no longer
#                             produce a violation — which means "0 violations"
#                             and "the violation path is broken" print exactly
#                             the same thing. Stage 1 proves the C executor
#                             works; stage 2 proves the chunking, the PC-based
#                             classification, the counting, the report and the
#                             baseline emission are all still wired to it.
#
#   3. SWEEP                  the population, checked against baseline.json.
#
# ---------------------------------------------------------------------------
# TIERS — measured on an M-series macOS host, WORKERS=12
# ---------------------------------------------------------------------------
#
#   ./run.sh --quick   stages 1-3, 40M-word unbiased sample     ~25 s
#   ./run.sh           stages 1-3, EXHAUSTIVE: all 2^32 words   ~40 min  (DEFAULT)
#   ./run.sh --accept  rerun and rewrite baseline.json
#
# THE DEFAULT TIER IS EXHAUSTIVE, and that is the point of this harness: unlike
# ../native-semantic — which must sample, because it needs a starting state and
# a post-state comparison per word — this one asks a question cheap enough to
# ask of EVERY word there is. "0 violations over all 4,294,967,296 words" is a
# claim that gets cited; it is recorded here with its cost so it can be
# RE-DERIVED instead. `--quick` is the pre-commit tier and is a sample: it is
# unbiased (a Weyl permutation prefix, so it cannot align with the encoding's
# bitfield structure) but it is not a proof about the space.
#
# The check FAILS if the violation count exceeds the baseline. The baseline is
# 0 and there is no reason for it ever to be anything else: a violation is a
# word the model accepts and the CPU refuses, i.e. a potential false Proven.
#
# REQUIREMENTS: aarch64 macOS host; clang (Command Line Tools); cargo +beta.
# ============================================================================
set -e
cd "$(dirname "$0")"
HERE=$(pwd)

CLANG=${CLANG:-/Library/Developer/CommandLineTools/usr/bin/clang}
SDK=${SDK:-/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk}
WORKERS=${WORKERS:-12}

MODE=--full
TIER=full
ACCEPT=0
for a in "$@"; do
    case "$a" in
    --quick) MODE="--sample 40000000"; TIER=quick ;;
    --accept) ACCEPT=1 ;;
    esac
done

echo "== building the native executor =="
"$CLANG" -arch arm64 -isysroot "$SDK" -O2 -o natexec natexec.c

echo "== building the sweep driver =="
CFG_RELEASE="1.99.0-dev" CFG_RELEASE_CHANNEL=dev RUSTC_BOOTSTRAP=1 \
    cargo +beta build --release --quiet

mkdir -p /tmp/natinv
# STALE RESULTS ARE WORSE THAN NO RESULTS — see the same note in
# ../native-semantic/run.sh. The verdict is read from `result.baseline.json`;
# if this run dies before writing one, the previous run's file must not be
# mistaken for it.
rm -f "$HERE/result.baseline.json" /tmp/natinv/nv_bad.baseline.json /tmp/natinv/nv_ok.baseline.json

# ---------------------------------------------------------------------------
# STAGE 1 — EXECUTOR GROUND TRUTH
# ---------------------------------------------------------------------------
echo
echo "== stage 1/3: the executor must reproduce known ground truth =="
python3 - <<'PY'
import struct
# Three CONSTRAINED UNPREDICTABLE words the CPU refuses, each with the
# one-register control that the CPU runs, plus udf/nop.
w=[0xf81eb7de,0xf81eb7dd,0x7843dd8c,0x7843dd8b,0xa97b8040,0xa97b8440,0x00000000,0xd503201f]
open('/tmp/natinv/selftest.bin','wb').write(b''.join(struct.pack('<I',x) for x in w))
# The same refused words, and the same controls, as hex for the stage-2 probe.
open('/tmp/natinv/known-sigill.txt','w').write('f81eb7de\n7843dd8c\na97b8040\n')
open('/tmp/natinv/controls.txt','w').write('f81eb7dd\n7843dd8b\na97b8440\n')
PY
./natexec /tmp/natinv/selftest.bin /tmp/natinv/selftest.out 2>/dev/null
python3 - <<'PY'
import sys
got=list(open('/tmp/natinv/selftest.out','rb').read())
want=[1,0,1,0,1,0,1,0]   # SIGILL, EXECUTED, ... ; 1=SIGILL 0=EXECUTED
names=['EXECUTED','SIGILL','MEMFAULT','TRAP_SELF','ESCAPED','SIGSYS','SIGFPE','TIMEOUT','OTHER']
tags=['f81eb7de str x30,[x30],#-21 (Rt==Rn)','f81eb7dd control',
      '7843dd8c ldrh w12,[x12,#61]! (Rt==Rn)','7843dd8b control',
      'a97b8040 ldp x0,x0,[x2,#-72] (Rt1==Rt2)','a97b8440 control',
      '00000000 udf #0','d503201f nop']
ok = got==want
for t,g,e in zip(tags,got,want):
    mark='ok ' if g==e else 'BAD'
    print(f'  {mark} {names[g]:<9} {t}')
if not ok:
    print('STAGE 1 FAILED — the executor does not reproduce known ground truth.')
    sys.exit(1)
print('  stage 1 PASSED (3 aliasing/control pairs + udf + nop)')
PY

# ---------------------------------------------------------------------------
# STAGE 2 — SWEEP NON-VACUITY
#
# Runs BEFORE the sweep on purpose: if the violation path is dead there is no
# point spending forty minutes producing a zero from it, and worse, that zero
# would be believed.
# ---------------------------------------------------------------------------
echo
echo "== stage 2/3: NON-VACUITY — the sweep must still be able to REPORT a violation =="
./target/release/native-invariant --words /tmp/natinv/known-sigill.txt --force-candidates \
    --workers 3 --workdir /tmp/natinv --out /tmp/natinv/nv_bad > /tmp/natinv/nv_bad.out 2>&1
./target/release/native-invariant --words /tmp/natinv/controls.txt --force-candidates \
    --workers 3 --workdir /tmp/natinv --out /tmp/natinv/nv_ok > /tmp/natinv/nv_ok.out 2>&1
python3 - <<'PY'
import json, sys
bad = json.load(open('/tmp/natinv/nv_bad.baseline.json'))
ok  = json.load(open('/tmp/natinv/nv_ok.baseline.json'))
print(f'  known-refused words : {bad["violations"]} violations (want 3)')
print(f'  controls            : {ok["violations"]} violations (want 0)')
if bad['violations'] != 3:
    print('STAGE 2 FAILED — the sweep did not report violations for words the CPU')
    print('demonstrably refuses. Its "0 violations" is therefore not evidence: the')
    print('violation path is broken, not the invariant confirmed.')
    sys.exit(1)
if ok['violations'] != 0:
    print('STAGE 2 FAILED — the sweep reported a violation for a control word the CPU')
    print('runs. It is over-reporting, and every count it produces is suspect.')
    sys.exit(1)
print('  stage 2 PASSED (the violation path is live in both directions)')
PY

# ---------------------------------------------------------------------------
# STAGE 3 — SWEEP
# ---------------------------------------------------------------------------
echo
echo "== stage 3/3: sweep — $TIER tier =="
# shellcheck disable=SC2086
./target/release/native-invariant $MODE --workers "$WORKERS" \
    --workdir /tmp/natinv --out "$HERE/result"

python3 - "$HERE" "$TIER" "$ACCEPT" <<'PY'
import json, sys, os, datetime
here, tier, accept = sys.argv[1], sys.argv[2], sys.argv[3] == '1'
run = json.load(open(os.path.join(here, 'result.baseline.json')))
bpath = os.path.join(here, 'baseline.json')

if accept:
    if tier != 'full':
        sys.exit('refusing to record a baseline from the --quick tier: the recorded result '
                 'is the EXHAUSTIVE one, and a sample cannot replace it.')
    out = {
        '_comment': [
            'THE RECORDED RESULT of the native invariant check, EXHAUSTIVE over the whole',
            '2^32 AArch64 encoding space. Rewritten only by `./run.sh --accept`.',
            '',
            'RE-DERIVE, DO NOT CITE. Everything needed to reproduce this is in this file:',
            'the population is the entire space (no sampling, no seed), the cost is',
            "`elapsed_s` below at `workers` workers, and `./run.sh` is the command.",
            'A number that can only be quoted is a number that stops being true quietly.',
            '',
            'THE BASELINE IS ZERO AND MUST STAY ZERO. Each violation would be a word the',
            'model accepts and the CPU refuses — a potential false Proven. `--accept` will',
            'happily record a nonzero one; do not let it.',
            '',
            'THIS IS A FAULT-CLASS RESULT ONLY. It says the CPU RUNS every word the gate',
            'admits. It does NOT say the CPU does what was certified — that is',
            '../native-semantic, whose baseline is not zero.',
            '',
            'WHICH NUMBERS ARE EXACT. `scanned`, `candidates` and `violations` are exact and',
            'reproducible: the population is the whole space and the antecedent is a pure',
            'function of the word. The `outcomes` split is NOT — `TIMEOUT` is a wall-clock',
            'judgement, so a loaded machine moves words from EXECUTED/ESCAPED into it.',
            'Measured across two exhaustive runs: candidates identical to the word',
            '(956,047,373 both times), violations 0 both times, TIMEOUT 77,723 -> 83,852 with',
            'other work running. The gate compares `violations` alone, for exactly this',
            'reason; the outcome split is context, not a checked quantity.',
            '',
            'HOST-RELATIVE. One Apple aarch64 part at EL0, no SVE/SME/PAC/MTE. See the',
            'BLIND SPOTS header in src/main.rs, which is normative.',
        ],
        'derived': {
            'command': './run.sh --accept',
            'tier': 'full (exhaustive, all 2^32 words)',
            'date': datetime.date.today().isoformat(),
            'host': 'aarch64 macOS',
        },
        **run,
    }
    # ensure_ascii=False — see the same note in ../native-semantic/run.sh: a
    # baseline whose diff is unreadable is a baseline nobody reviews.
    json.dump(out, open(bpath, 'w'), indent=2, ensure_ascii=False)
    open(bpath, 'a').write('\n')
    print()
    print('baseline REWRITTEN from this run.')
    sys.exit(0)

if not os.path.exists(bpath):
    print('NO BASELINE — run with --accept to record one.'); sys.exit(1)
base = json.load(open(bpath))
v, bv = run['violations'], base['violations']
print()
print('=' * 70)
print(f'  tier                : {tier}')
print(f'  scanned this run    : {run["scanned"]} words in {run.get("elapsed_s", "?")}s')
print(f'  recorded baseline   : {base["scanned"]} words scanned, {bv} violations')
print(f'  violations this run : {v}')
if run.get('attribution_errors'):
    print(f'  ATTRIBUTION ERRORS  : {run["attribution_errors"]} — the decoder-function')
    print('                        ranking is unreliable this run (the dispatch mirror in')
    print('                        attribute.rs has drifted from the decoder it mirrors).')
if v > bv:
    print('  RESULT: FAIL — the invariant is violated beyond the baseline.')
    print('  Each violation is a word the model accepts and the CPU refuses,')
    print('  i.e. a potential FALSE PROVEN. See result.violations.bin, and')
    print('  re-check just those words with --words to characterise the family.')
    print('=' * 70); sys.exit(1)
if v < bv:
    print('  RESULT: PASS (improved — rerun with --accept to tighten baseline)')
elif tier != 'full':
    print('  RESULT: PASS (sampled — the recorded result is the exhaustive one)')
else:
    print('  RESULT: PASS')
print('=' * 70)
PY
