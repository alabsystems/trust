#!/bin/sh
# ============================================================================
# THE MACHINE-MODEL GATE — both harnesses, one verdict.
#
# Run this before you touch `trust-machine-sem` or `trust-disasm`, and again
# before you land the change. See README.md beside this file for what a failure
# means and what to do about it.
#
#   ./gate.sh --fast     pre-commit tier                        ~30 s
#   ./gate.sh            pre-landing tier                       ~40 min
#   ./gate.sh --semantic-only | --invariant-only
#
# THE TWO HARNESSES ANSWER DIFFERENT QUESTIONS AND NEITHER SUBSUMES THE OTHER:
#
#   native-invariant   if the gate certifies an object, the CPU EXECUTES it.
#                      Fault vs no-fault. Cheap enough to run over ALL 2^32
#                      words, and the recorded result is exhaustive. TRUE:
#                      0 violations over the whole space.
#
#   native-semantic    if the gate certifies an object, the CPU DOES WHAT WAS
#                      CERTIFIED. Compares the whole architectural post-state
#                      against hardware. Must sample. NOT yet true: eight
#                      scalar-FP families still diverge, and are recorded.
#
# A word can pass the first and fail the second — three families did, and they
# were live model bugs. Running only the cheap one is how this class survived
# four separate discoveries.
# ============================================================================
set -e
cd "$(dirname "$0")"

FAST=0
RUN_SEM=1
RUN_INV=1
for a in "$@"; do
    case "$a" in
    --fast) FAST=1 ;;
    --semantic-only) RUN_INV=0 ;;
    --invariant-only) RUN_SEM=0 ;;
    *) echo "usage: $0 [--fast] [--semantic-only|--invariant-only]" >&2; exit 2 ;;
    esac
done

rc=0
if [ "$RUN_INV" = 1 ]; then
    echo "###############################################################"
    echo "# 1/2  native-invariant — does the CPU RUN what the gate admits?"
    echo "###############################################################"
    if [ "$FAST" = 1 ]; then
        ./native-invariant/run.sh --quick || rc=1
    else
        ./native-invariant/run.sh || rc=1
    fi
fi

if [ "$RUN_SEM" = 1 ]; then
    echo
    echo "###############################################################"
    echo "# 2/2  native-semantic — does it DO what the gate certified?"
    echo "###############################################################"
    if [ "$FAST" = 1 ]; then
        ./native-semantic/run.sh --fast || rc=1
    else
        ./native-semantic/run.sh || rc=1
    fi
fi

echo
echo "==============================================================="
if [ "$rc" = 0 ]; then
    echo "  MACHINE-MODEL GATE: PASS"
    echo "  Both harnesses proved their own non-vacuity on this run:"
    echo "  the invariant sweep still reports known-refused words as"
    echo "  violations, and the differential still catches every"
    echo "  injected model bug (counts above). A green run from a blind oracle is the"
    echo "  failure this gate is built to prevent."
else
    echo "  MACHINE-MODEL GATE: FAIL — see above, and README.md."
fi
echo "==============================================================="
exit $rc
