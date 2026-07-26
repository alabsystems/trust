#!/usr/bin/env bash
# scripts/showcase-demo.sh -- Trust Internal Model-Check Showcase Demo
#
# Internal/deeper model-check demo for Trust's three-tier checking stack.
# This is not the canonical first-run entrypoint; start with README.md,
# INSTALL.md, or targo-trust/README.md for public onboarding and standard
# setup.
#
# Demonstrates Trust's three-tier checking capabilities:
#   Tier 1: Error Detection -- finds real bugs in example programs
#   Tier 2: Pipeline Model Checks -- hand-built models of Trust pipeline code
#   Tier 3: ay Component Model Checks -- hand-built models of ay components
#
# Usage:
#   ./scripts/showcase-demo.sh          # run all internal demo tiers
#   ./scripts/showcase-demo.sh --tier1  # run only Tier 1
#   ./scripts/showcase-demo.sh --tier2  # run only Tier 2
#   ./scripts/showcase-demo.sh --tier3  # run only Tier 3
#   ./scripts/showcase-demo.sh --quick  # run Tier 1 + Tier 2 (no ay required)
#
# Requirements:
#   - Rust toolchain (cargo)
#   - ay on PATH for Tier 3 real solving (gracefully skipped if absent)
#   - Lean5/gamma-crown/trust-extra are optional proof-backend/provenance gates elsewhere.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
# Issue: #660 | Epic: #549

set -euo pipefail

# ---------------------------------------------------------------------------
# Colors and formatting
# ---------------------------------------------------------------------------

BOLD='\033[1m'
DIM='\033[2m'
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
RESET='\033[0m'

# Detect if stdout is a terminal; disable colors if not
if [ ! -t 1 ]; then
    BOLD='' DIM='' RED='' GREEN='' YELLOW='' BLUE='' CYAN='' RESET=''
fi

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

PASS_COUNT=0
FAIL_COUNT=0
SKIP_COUNT=0
TIER_PASS=0
TIER_FAIL=0
TIER_SKIP=0

print_header() {
    echo ""
    echo -e "${BOLD}${BLUE}================================================================${RESET}"
    echo -e "${BOLD}${BLUE}  $1${RESET}"
    echo -e "${BOLD}${BLUE}================================================================${RESET}"
    echo ""
}

print_tier_header() {
    echo -e "  ${BOLD}${CYAN}--- $1 ---${RESET}"
    echo ""
}

print_pass() {
    echo -e "    ${GREEN}PASS${RESET}  $1"
    PASS_COUNT=$((PASS_COUNT + 1))
    TIER_PASS=$((TIER_PASS + 1))
}

print_fail() {
    echo -e "    ${RED}FAIL${RESET}  $1"
    FAIL_COUNT=$((FAIL_COUNT + 1))
    TIER_FAIL=$((TIER_FAIL + 1))
}

print_skip() {
    echo -e "    ${YELLOW}SKIP${RESET}  $1"
    SKIP_COUNT=$((SKIP_COUNT + 1))
    TIER_SKIP=$((TIER_SKIP + 1))
}

print_info() {
    echo -e "    ${DIM}$1${RESET}"
}

print_tier_summary() {
    local tier_name="$1"
    echo ""
    echo -e "  ${BOLD}${tier_name} results:${RESET} ${GREEN}${TIER_PASS} passed${RESET}, ${RED}${TIER_FAIL} failed${RESET}, ${YELLOW}${TIER_SKIP} skipped${RESET}"
    TIER_PASS=0
    TIER_FAIL=0
    TIER_SKIP=0
}

reset_tier_counts() {
    TIER_PASS=0
    TIER_FAIL=0
    TIER_SKIP=0
}

# Check ay availability and print version info
check_ay() {
    if command -v ay >/dev/null 2>&1; then
        AY_VERSION=$(ay --version 2>&1 | head -1)
        AY_AVAILABLE=true
        echo -e "  ay solver: ${GREEN}available${RESET} (${AY_VERSION})"
    else
        AY_AVAILABLE=false
        echo -e "  ay solver: ${YELLOW}not found${RESET} -- Tier 3 will be skipped"
    fi
}

# Run a single cargo test and capture pass/fail
# Usage: run_test <package> <test_name> <display_name> <description>
run_test() {
    local pkg="$1"
    local test_name="$2"
    local display_name="$3"
    local description="$4"

    echo -e "  ${BOLD}${display_name}${RESET}"
    print_info "$description"

    local output
    local exit_code=0
    output=$(cd "$REPO_ROOT" && cargo test -p "$pkg" --test "*" -- "$test_name" --exact 2>&1) || exit_code=$?

    if [ $exit_code -eq 0 ]; then
        # Check if test actually ran (not filtered out)
        if echo "$output" | grep -q "test result:.*0 passed"; then
            # Try without --exact in case the test file name is needed
            output=$(cd "$REPO_ROOT" && cargo test -p "$pkg" -- "$test_name" 2>&1) || exit_code=$?
            if [ $exit_code -eq 0 ] && echo "$output" | grep -q "test result:.*0 passed"; then
                print_skip "test not found"
                return
            fi
        fi
        if echo "$output" | grep -q "SKIP: ay not on PATH"; then
            print_skip "ay not available"
        else
            print_pass "checked"
        fi
    else
        if echo "$output" | grep -q "SKIP: ay not on PATH"; then
            print_skip "ay not available"
        else
            print_fail "test failed"
            # Show last few lines of failure output
            echo "$output" | tail -5 | while IFS= read -r line; do
                print_info "  $line"
            done
        fi
    fi
    echo ""
}

# Run a cargo test filtering by name prefix (for suites)
# Usage: run_test_filter <package> <filter> <display_name> <description>
run_test_filter() {
    local pkg="$1"
    local filter="$2"
    local display_name="$3"
    local description="$4"

    echo -e "  ${BOLD}${display_name}${RESET}"
    print_info "$description"

    local output
    local exit_code=0
    output=$(cd "$REPO_ROOT" && cargo test -p "$pkg" -- "$filter" 2>&1) || exit_code=$?

    if [ $exit_code -eq 0 ]; then
        # Extract test count from output
        local test_line
        test_line=$(echo "$output" | grep "test result:" | tail -1)
        if [ -n "$test_line" ]; then
            local passed
            passed=$(echo "$test_line" | grep -o '[0-9]* passed' | grep -o '[0-9]*')
            if [ -n "$passed" ] && [ "$passed" -gt 0 ]; then
                print_pass "$passed tests passed"
            else
                print_skip "no matching tests"
            fi
        else
            print_pass "completed"
        fi
    else
        if echo "$output" | grep -q "SKIP: ay not on PATH"; then
            print_skip "ay not available"
        else
            print_fail "tests failed"
            echo "$output" | grep "^test .* FAILED" | head -5 | while IFS= read -r line; do
                print_info "  $line"
            done
        fi
    fi
    echo ""
}

# ---------------------------------------------------------------------------
# Tier 1: Error Detection
# ---------------------------------------------------------------------------

run_tier1() {
    print_header "Tier 1: Error Detection"
    echo -e "  ${DIM}Trust finds real bugs by generating verification conditions from${RESET}"
    echo -e "  ${DIM}MIR models and asking the solver for SAT/UNSAT results. Counterexamples show${RESET}"
    echo -e "  ${DIM}concrete inputs that trigger each bug.${RESET}"
    echo ""
    reset_tier_counts

    print_tier_header "T1.1 -- Midpoint Integer Overflow"
    run_test trust-integration-tests \
        "test_real_ay_detects_midpoint_overflow" \
        "buggy_midpoint: (lo + hi) / 2" \
        "VcKind::ArithmeticOverflow{Add} -- the JDK binary search bug (Bloch, 2006)"

    print_tier_header "T1.2 -- Division Safety"
    run_test trust-integration-tests \
        "test_real_ay_proves_constant_division_safe" \
        "div_by_constant: x / 2" \
        "VcKind::DivisionByZero -- constant divisor is statically safe"

    run_test trust-integration-tests \
        "test_real_ay_detects_division_by_variable" \
        "div_by_variable: a / b" \
        "VcKind::DivisionByZero -- variable divisor can be zero"

    print_tier_header "T1.3 -- Full Pipeline (Buggy vs Safe)"
    run_test trust-integration-tests \
        "test_real_ay_full_pipeline_buggy_vs_safe" \
        "buggy_midpoint vs safe_midpoint" \
        "Same computation, two implementations: one overflows, one is checked safe"

    print_tier_header "T1.4 -- Direct Formula Checks"
    run_test trust-integration-tests \
        "test_real_ay_direct_overflow_formula" \
        "direct overflow formula" \
        "SMT formula for (a + b) overflow -- checks SAT (bug exists)"

    run_test trust-integration-tests \
        "test_real_ay_direct_divzero_constant_safe" \
        "direct divzero constant-safe formula" \
        "SMT formula for x/2 == 0 -- checks UNSAT (safe)"

    print_tier_summary "Tier 1"
}

# ---------------------------------------------------------------------------
# Tier 2: Pipeline Model Checks
# ---------------------------------------------------------------------------

run_tier2() {
    print_header "Tier 2: Pipeline Model-Check Showcase"
    echo -e "  ${DIM}Trust checks hand-reviewed models of its own pipeline code. Each model${RESET}"
    echo -e "  ${DIM}approximates a real function in the Trust crate tree and checks for overflow,${RESET}"
    echo -e "  ${DIM}bounds violations, and other safety properties.${RESET}"
    echo ""
    reset_tier_counts

    print_tier_header "SV-1: BvExtract Width Computation"
    run_test trust-integration-tests \
        "test_self_verify_sv1_bv_extract_vc_generation" \
        "trust_types::Formula::BvExtract" \
        "high - low + 1 width computation -- ArithmeticOverflow{Sub}"

    print_tier_header "SV-2: Simplifier Loop Index"
    run_test trust-integration-tests \
        "test_self_verify_sv2_simplifier_loop_vc_generation" \
        "trust_vcgen::simplify loop index" \
        "Loop counter increment -- ArithmeticOverflow{Add}"

    print_tier_header "SV-3: Bloom Filter Bit Index"
    run_test trust-integration-tests \
        "test_self_verify_sv3_bloom_filter_vc_generation" \
        "trust_convergence::BloomFilter" \
        "Modular hash index into bitmap -- ShiftOverflow, IndexOutOfBounds"

    print_tier_header "SV-4: Convergence Accumulator"
    run_test trust-integration-tests \
        "test_self_verify_sv4_convergence_accumulator_vc_generation" \
        "trust_convergence::MetricAccumulator" \
        "Running total accumulation -- ArithmeticOverflow{Add}"

    print_tier_header "Full Pipeline Model-Check Suite"
    run_test trust-integration-tests \
        "test_self_verify_full_suite" \
        "pipeline model-check suite (all 4 models)" \
        "Combined run: VC generation + mock routing for all SV models"

    print_tier_summary "Tier 2"
}

# ---------------------------------------------------------------------------
# Tier 3: ay Solver Component Model Checks
# ---------------------------------------------------------------------------

run_tier3() {
    print_header "Tier 3: ay Solver Component Model Checks"
    echo -e "  ${DIM}Trust routes hand-built ay component models through VC generation${RESET}"
    echo -e "  ${DIM}and optional ay solving. This is a showcase path, not a core${RESET}"
    echo -e "  ${DIM}daily-driver requirement.${RESET}"
    echo ""
    reset_tier_counts

    if [ "$AY_AVAILABLE" != "true" ]; then
        echo -e "  ${YELLOW}ay not found on PATH. Tier 3 requires ay for real SMT solving.${RESET}"
        echo -e "  ${YELLOW}Running mock-backend tests only.${RESET}"
        echo ""
    fi

    print_tier_header "ay BCP (Boolean Constraint Propagation)"
    run_test trust-integration-tests \
        "test_ay_sv1_bcp_propagation_vc_generation" \
        "ay-sat::solver::propagate_bcp" \
        "Trail push overflow, watch-list bounds -- ArithmeticOverflow, IndexOutOfBounds"

    print_tier_header "ay Clause Arena Allocation"
    run_test trust-integration-tests \
        "test_ay_sv2_clause_arena_vc_generation" \
        "ay-sat::arena::ClauseArena::alloc" \
        "Arena capacity check, offset computation -- ArithmeticOverflow, IndexOutOfBounds"

    print_tier_header "ay LRAT Proof Checker"
    run_test trust-integration-tests \
        "test_ay_sv3_lrat_checker_vc_generation" \
        "ay-proof::lrat::LratChecker::check_step" \
        "Clause index lookup, step counter -- IndexOutOfBounds, ArithmeticOverflow"

    print_tier_header "ay Full Suite (Mock Backend)"
    run_test trust-integration-tests \
        "test_ay_self_verify_full_suite" \
        "ay model-check suite (BCP + Arena + LRAT, mock)" \
        "All ay models through VC generation and mock routing"

    if [ "$AY_AVAILABLE" = "true" ]; then
        print_tier_header "ay Full Suite (Real SmtLib Backend)"
        run_test trust-integration-tests \
            "test_ay_self_verify_full_suite_real_smtlib" \
            "ay model-check suite (BCP + Arena + LRAT, real ay)" \
            "All ay models checked by the optional real ay solver"

        print_tier_header "ay Phase 2: Literal/LEB128/VSIDS Models"
        run_test_filter trust-integration-tests \
            "test_ay_phase2" \
            "ay phase 2 models (4 functions)" \
            "Literal encoding, LEB128 decode, VSIDS bump -- ShiftOverflow, ArithmeticOverflow"
    fi

    print_tier_summary "Tier 3"
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

main() {
    local run_tier1=false
    local run_tier2=false
    local run_tier3=false

    # Parse arguments
    if [ $# -eq 0 ]; then
        run_tier1=true
        run_tier2=true
        run_tier3=true
    else
        for arg in "$@"; do
            case "$arg" in
                --tier1) run_tier1=true ;;
                --tier2) run_tier2=true ;;
                --tier3) run_tier3=true ;;
                --quick) run_tier1=true; run_tier2=true ;;
                --help|-h)
                    echo "Usage: $0 [--tier1] [--tier2] [--tier3] [--quick] [--help]"
                    echo ""
                    echo "  Internal/deeper model-check demo for Trust."
                    echo "  Canonical first-run surfaces: README.md, INSTALL.md, targo-trust/README.md"
                    echo ""
                    echo "  --tier1  Error detection (requires ay for real solving)"
                    echo "  --tier2  Pipeline model checks (always available, mock backend)"
                    echo "  --tier3  ay component model checks (requires ay for real solving)"
                    echo "  --quick  Tier 1 + Tier 2"
                    echo ""
                    echo "  No arguments: run all tiers"
                    exit 0
                    ;;
                *)
                    echo "Unknown option: $arg (try --help)"
                    exit 1
                    ;;
            esac
        done
    fi

    local START_TIME
    START_TIME=$(date +%s)

    print_header "Trust Internal Model-Check Showcase"

    echo -e "  ${BOLD}Trust${RESET} -- Rust compiler fork with native VC generation"
    echo -e "  ${DIM}Fork of rust-lang/rust with optional proof backends${RESET}"
    echo -e "  ${YELLOW}Internal/deeper model-check demo; not the canonical first-run path.${RESET}"
    echo -e "  ${DIM}Core daily-driver use does not require Lean5, gamma-crown, or trust-extra.${RESET}"
    echo -e "  ${DIM}Those remain optional proof-backend/provenance gates outside this showcase.${RESET}"
    echo -e "  ${DIM}Start with README.md, INSTALL.md, or targo-trust/README.md for setup and public-facing usage.${RESET}"
    echo ""

    # Environment check
    echo -e "  ${BOLD}Environment:${RESET}"
    echo -e "  Rust:      $(rustc --version 2>/dev/null || echo 'not found')"
    echo -e "  Cargo:     $(cargo --version 2>/dev/null || echo 'not found')"
    check_ay
    echo ""

    # Build first to ensure compilation is cached
    echo -e "  ${DIM}Building trust-integration-tests (first run may take a moment)...${RESET}"
    if ! (cd "$REPO_ROOT" && cargo test -p trust-integration-tests --no-run 2>&1 | tail -1); then
        echo -e "  ${RED}Build failed. Run 'cargo check -p trust-integration-tests' for details.${RESET}"
        exit 1
    fi
    echo ""

    # Run selected tiers
    if [ "$run_tier1" = true ]; then run_tier1; fi
    if [ "$run_tier2" = true ]; then run_tier2; fi
    if [ "$run_tier3" = true ]; then run_tier3; fi

    # Final summary
    local END_TIME
    END_TIME=$(date +%s)
    local ELAPSED=$((END_TIME - START_TIME))

    print_header "Summary"

    local TOTAL=$((PASS_COUNT + FAIL_COUNT + SKIP_COUNT))
    echo -e "  ${BOLD}Total:${RESET}   $TOTAL tests"
    echo -e "  ${GREEN}Passed:${RESET}  $PASS_COUNT"
    echo -e "  ${RED}Failed:${RESET}  $FAIL_COUNT"
    echo -e "  ${YELLOW}Skipped:${RESET} $SKIP_COUNT"
    echo -e "  ${DIM}Elapsed: ${ELAPSED}s${RESET}"
    echo ""

    if [ "$FAIL_COUNT" -gt 0 ]; then
        echo -e "  ${RED}${BOLD}RESULT: FAIL${RESET} -- $FAIL_COUNT test(s) failed"
        exit 1
    elif [ "$PASS_COUNT" -eq 0 ]; then
        echo -e "  ${YELLOW}${BOLD}RESULT: NO TESTS RAN${RESET}"
        exit 1
    else
        echo -e "  ${GREEN}${BOLD}RESULT: PASS${RESET} -- all $PASS_COUNT tests passed"
        exit 0
    fi
}

main "$@"
