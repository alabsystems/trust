#!/usr/bin/env python3
"""Every test lane in the tree must be named by the gate manifest.

A lane that exists but appears in no manifest row is a lane nobody runs, and
nothing announces that: the file sits in the tree looking maintained while no
orchestrator ever invokes it. This walks the on-disk lane inventory and fails
when a lane is unnamed, so adding an e2e script, a gate script, an adversarial
oracle, a witness or elide regression, a `scripts/tests/` test, or a compiletest
suite forces a manifest row in the same change.

Coverage is literal by default: a lane is covered when its repo-relative path
appears verbatim in some row's command. Lanes reached through an aggregate
(a glob runner, a `targo trust` subcommand) are covered by naming that
aggregate in `INDIRECT` below, which keeps the indirection written down instead
of inferred. `MANUAL_ONLY` is the one remaining exit: a tool whose interface
cannot be a row at all, listed with the reason. `DOC_ENFORCEMENT_LANES` adds one
more class: a document that claims a test keeps it honest must name a test that
a manifest row actually runs.

It also validates the manifest's own shape: six pipe-separated columns, a
recognized profile set, and a `last_green` that is either `never` or an ISO
date that is not in the future.

Two rules guard the pre-push gate, which derives its ENTIRE lane list from the
rows carrying the `push` profile: some row must carry that profile, and
`scripts/hooks/pre-push` must name no gate id literally. Either failure
re-creates the hand-maintained second inventory removed on 2026-08-27.

Usage:
    scripts/check_gate_lane_coverage.py
    scripts/check_gate_lane_coverage.py --list-uncovered

Exit codes:
    0   every lane is named and every row is well-formed
    1   an unnamed lane or a malformed row

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import argparse
import re
import sys
from datetime import date, datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
HARNESS = REPO_ROOT / "tests" / "run_trust_comprehensive_harness.sh"

KNOWN_PROFILES = {"all", "manifest", "fast", "push", "quick", "suites", "slow", "release"}

# Lanes that no row names directly, each with the aggregate that does run them.
# A lane belongs here only when the aggregate genuinely executes it; the point
# of the table is that the indirection is stated, not that the lane is excused.
INDIRECT: dict[str, str] = {
    # The whole `tests/e2e_*.sh` corpus runs as one lane.
    "tests/e2e_*.sh": "scripts/run_e2e_shell_corpus.sh",
    # `scripts/tests/*` run as one lane.
    "scripts/tests/*": "scripts/check_script_tests.sh",
    # The corpus fetch is the first thing the calibration lane does; the
    # payload is external, so it cannot be a gate of its own.
    "scripts/js262/fetch_corpus.sh": "scripts/js262/calibrate.sh",
    # `scripts/check_*` checkers reached through an aggregate a row DOES name.
    # Verified by reading the aggregate, not by assuming: the e2e script execs
    # the real checker (not a synthetic copy) inside the corpus lane.
    # tests/e2e_certified_monitor_lock_source_gate.sh runs "$ROOT/scripts/...".
    "scripts/check_lockfile_no_git_sources.sh": "scripts/run_e2e_shell_corpus.sh",
    # The shell is deliberately payload-only and rejects direct callers. The
    # Rust-native release parent performs the controlled-Git authority checks,
    # invokes this exact payload, reopens its sealed output, and alone publishes
    # the native-authority receipt.
    "scripts/stage2_certified_monitor_e2e.sh": (
        "targo-trust trust release validate certified-monitors"
    ),
    # --- classified 2026-08-26, from the catch-all sweep ---
    # compat_check.sh is a 35-line entry point whose last statement is
    # `exec "$PYTHON_BIN" ... compat_check.py`, so the shell row's exit status
    # IS this module's verdict. The pair is covered by naming the shell half.
    "scripts/compat_check.py": "scripts/compat_check.sh",
    # The cutover validator is verdict-bearing but cannot be a row TODAY: it
    # requires `--artifact GATE.json --runs-log ...` and no such artifact exists
    # (docs/ledgers/ is unwritten; the plan marks every ledger PLANNED). Its
    # adversarial suite drives it end to end, in-process AND by subprocess,
    # across 33 fixtures covering defects D1-D9. Re-classify to ROW the day a
    # committed gate artifact exists.
    "scripts/cutover_gate/validate.py": "scripts/cutover_gate/test_validate.py",
    # tests/e2e_trust_local_rustup_install.sh runs the REAL script (not a copy,
    # not a stub) against a genuinely installed sysroot, then asserts that
    # `rustup which --toolchain <name> trustc` resolves inside that sysroot.
    "scripts/rustup-link-trust.sh": "scripts/run_e2e_shell_corpus.sh",
    # tests/e2e_full_verifier_three_suite_sample.sh binds it as
    # RUSTC_PRIVATE_SYSROOT_FILTER. It is a narrow rustc-argv rewriter, so it
    # could never be a row of its own; this records WHERE it is exercised.
    "scripts/trust_rustc_private_sysroot_filter.py": "scripts/run_e2e_shell_corpus.sh",
    # scripts/tests/trust_ir_rowdiff_test.py imports the module and drives the
    # real comparator in-process. What that pins is the comparator's FIELD SET —
    # the defect it was written for, after six scratchpad copies disagreed about
    # which fields count and `spliced`/`instr_count`/`lineage` went unwatched.
    # A real two-artifact comparison still has no scheduled home; give it a row
    # if a sweep ever publishes a standing control artifact.
    "scripts/trust_ir_rowdiff.py": "scripts/check_script_tests.sh",
}

# Lanes no row CAN name, each with the reason the interface forbids it. This is
# not a quiet-the-checker list: an entry must still exist on disk, and it errors
# once a row does name it. Listing a manual tool keeps it in the inventory —
# widening a glob past it would make it invisible again, which is the failure
# this whole file exists to catch.
MANUAL_ONLY: dict[str, str] = {
    "scripts/refresh_two_language_claim_bases.py": (
        "publication tool, not a check: --publish PUSHES a ledger child and its "
        "claim mirrors, and the property a gate would assert (the ledger's active "
        "bases are coherent) is already the fast.two-language-claim-ledger row. "
        "Running it as a lane would make every push mutate shared coordination "
        "refs; its own candidate is validated by that same checker before it "
        "publishes anything"
    ),
    "scripts/trust_dualoracle.sh": (
        "manual single-witness triage: takes <name> <lib.rs> <driver.rs> and "
        "classifies that one witness, so it carries no corpus a gate could run; "
        "the searchers in the `oracle` class generate what it triages"
    ),
}

# Documents that name a test as the thing keeping them true, mapped to that
# test's file and the cargo package that owns it. A claim of the form "this test
# fails if the document drifts" is worth exactly as much as whatever runs the
# test, and docs/TCB.md carried that claim while its test sat in no manifest row
# at all (found 2026-07-25). Both halves are closed here: the document must
# still name the file, and some row must run it. A cargo test target is
# addressed by package plus `--test` selector rather than by path, so this class
# is matched on the selector instead of the literal-path rule used above.
DOC_ENFORCEMENT_LANES: dict[str, tuple[str, str]] = {
    "docs/TCB.md": (
        "crates/trust-integration-tests/tests/tcb_document_exhaustiveness.rs",
        "trust-integration-tests",
    ),
}

# Compiletest suites are directories under `tests/`; these are not suites.
NON_SUITE_TEST_DIRS = {
    "__pycache__",  # interpreter droppings; reporting it trains readers to ignore the red
    "auxiliary",
    "compat",
    "crashes",
    "fixtures",
    "js262",
    # One `.baseline` ledger, consumed by rowed lanes (trust_self_verify_crate.sh,
    # trust_certified_scoreboard.py); `x.py test tests/self-proof` is not a thing.
    # Written down 2026-08-26 because it would otherwise read covered by ACCIDENT:
    # coverage is a substring test, and `release.certified-scoreboard` names
    # `tests/self-proof/certified-scoreboard.baseline`, which contains the
    # directory path. A silent green is the failure this whole file exists to
    # catch, so the exemption is stated rather than collected.
    # A committed CONTROL CORPUS (four native-bundle dumps), not a compiletest
    # suite: `slow.call-summary-census` runs the script that reads it, and that
    # script fails on zero summaries or zero declines, so the corpus is guarded
    # by a rowed lane rather than by being one.
    "trust-call-summary-census",
    "self-proof",
    # Script collections and ledgers, not compiletest suites — `x.py test <dir>`
    # is meaningless for all five. Each RUNNER is rowed instead (`suites.*`), so
    # the lane runs; only the directory-as-suite reading is dropped. Measured
    # 2026-08-27, each by running it: ledger 0, trust-contract 0/0/0,
    # provability-ratchet 0, e6-fragment-probe 1 (toolchain != HEAD),
    # two-language-battery 1 (1 error of 11). The two reds are rowed RED on
    # purpose — rowing only the green ones would be picking the score.
    "e6-fragment-probe",
    "known-red",  # one rustc_mir_transform.txt baseline, consumed by slow.mir-transform-ratchet
    "ledger",
    "trust-contract",
    "trust-provability",
    "two-language-battery",
    "trust-added",
    "trust-comprehensive",
    "trust-elide",
    "trust-falsification",
    "trust-witness",
    "ts-corpus",
    "ts-transform-corpus",
    "upstream-rust",
}


def manifest_rows() -> list[list[str]]:
    """The manifest rows, read out of `emit_gate_manifest`'s quoted heredoc.

    Read rather than executed: the harness runs gates when sourced, and this
    check must be able to inspect the manifest without running anything.
    """
    text = HARNESS.read_text(encoding="utf-8")
    start = text.index("emit_gate_manifest() {")
    body = text[text.index("<<'EOF'", start) + len("<<'EOF'") : text.index("\nEOF\n", start)]
    return [line.split("|") for line in body.strip("\n").split("\n") if line.strip()]


def lane_inventory() -> dict[str, list[Path]]:
    """Every runnable lane in the tree, grouped by the class it belongs to."""
    tests = REPO_ROOT / "tests"
    scripts = REPO_ROOT / "scripts"
    inventory: dict[str, list[Path]] = {
        "e2e": sorted(tests.glob("e2e_*.sh")),
        # Gates, canaries and lanes. A canary is exactly the artifact this checker
        # exists for: `trust_control_canary.sh` was written because the `is_whnf`
        # mint gate sat closed for a month with no instrument reporting it.
        # The pattern was `trust_*_gate.sh` until 2026-08-26, which missed
        # `prove-trust-frontend-gate.sh` and `submodule-coherence-gate.sh` — the
        # same blind-spot class as the orphaned oracles, one character wide
        # (HYPHEN, not underscore). Match the suffix, never a project prefix.
        "gate-script": sorted(
            {
                p
                for suffix in ("gate", "canary", "lane")
                for sep in ("_", "-")
                for p in scripts.rglob(f"*{sep}{suffix}.sh")
                if p.parent != scripts / "tests"
            }
        ),
        # The `scripts/check_*` family: the freeze gate, the provenance gate,
        # the pin/patch/lock coherence gates, the ratchets. This class was
        # MISSING until 2026-08-22, and it is the class most of this repo's
        # soundness gates live in — so the checker whose whole job is "a lane
        # that exists but appears in no manifest row is a lane nobody runs"
        # could not see them. Measured the day it was added: of 24 checkers,
        # 11 were named by a row, 4 more are reached through a named aggregate
        # (INDIRECT above), and NINE were named by nothing at all. Five of the
        # nine were RED when first run — including scripts/check_patch_binds.py,
        # which reports the ay-chc patch UNBOUND (manifest 0.13.0 vs Cargo.lock
        # 0.10.0), i.e. `--locked` cannot hold for that patch and the resolver
        # silently falls back to the original git rev.
        "checker": sorted(
            list(scripts.glob("check_*.sh")) + list(scripts.glob("check_*.py"))
        ),
        # Adversarial oracles: generate programs, compare a verdict against
        # RUNTIME TRUTH. Measured 2026-08-26 — FIVE named by nothing (the four
        # known ones plus scripts/differential/), `trust_falseproof_search.py`
        # dormant since 2026-08-01 while the 2026-08-21 vacuous-hypothesis false
        # proof sat live (`i += 100` modelled as `x == x + 100`, UNSAT, so every
        # obligation in the block proved); that search finds it in ~15 min.
        # Globs stay loose and recursive: the failure mode is the NEXT oracle
        # landing outside the pattern, not these five.
        "oracle": sorted(
            {
                p
                for pattern in (
                    "*oracle*.py", "*oracle*.sh",
                    "*_search.py", "*_search.sh",
                    "*soundness*.py", "*soundness*.sh",
                    "*fuzz*.py", "*fuzz*.sh",
                    "*differential*.py", "*differential*.sh",
                )
                for p in scripts.rglob(pattern)
                if p.parent != scripts / "tests"  # owned by `script-test` below
            }
        ),
        "script-test": sorted(
            p for p in scripts.glob("tests/*") if p.suffix in (".py", ".sh")
        ),
        "witness": sorted((tests / "trust-witness").glob("*.py")),
        "elide": sorted((tests / "trust-elide").glob("*.py")),
        "suite": sorted(
            p
            for p in tests.iterdir()
            if p.is_dir() and p.name not in NON_SUITE_TEST_DIRS
        ),
        "orchestrator": sorted(tests.glob("run_trust_*_suite.sh")),
        "js262": sorted((scripts / "js262").glob("*.sh")),
    }
    # `tests/crashes` is a compiletest suite despite sitting in the exclusion
    # list above, which exists to keep ledger and fixture directories out.
    inventory["suite"].append(tests / "crashes")
    inventory["suite"].sort()

    # CATCH-ALL. Every class above matches on a NAME, so every class above has a
    # next blind spot: `check_*` missed the oracles, `trust_*_gate.sh` missed the
    # two hyphenated gates. Measured 2026-08-26 — 168 scripts under scripts/, 128
    # inventoried, FORTY invisible. Sweep whatever the named classes did not claim
    # so a lane can never hide by being spelled differently; the escape hatch is a
    # written reason (MANUAL_ONLY / INDIRECT), never a silent glob miss.
    claimed = {p for lanes in inventory.values() for p in lanes}
    inventory["unclassified"] = sorted(
        p
        for p in list(scripts.rglob("*.sh")) + list(scripts.rglob("*.py"))
        if p not in claimed
        and p.parent != scripts / "tests"
        and "__pycache__" not in p.parts
        and not _is_tooling(p.relative_to(REPO_ROOT).as_posix())
    )
    return inventory


# Roles that are NOT lanes: they are invoked BY a lane, by git, or by a human
# setting a machine up, and none of them can pass or fail. Exempted by ROLE with a
# written reason rather than by silently widening a glob — the same discipline as
# MANUAL_ONLY, and reviewable in one place. Anything not matched here is a lane
# until someone says otherwise in writing.
TOOLING_ROLES: tuple[tuple[str, str], ...] = (
    ("scripts/lib/", "sourced by other scripts; not independently runnable"),
    ("scripts/hooks/", "hook bodies; git runs them, and pre-push derives its lanes from the manifest's push profile"),
    ("scripts/hooks-pin/", "ditto, the narrow pin-only hook set"),
    ("scripts/install-", "one-shot machine setup, run by a human"),
    ("scripts/dev-", "developer convenience wrappers around x.py"),
    ("scripts/build-", "build drivers and memory governors, not verdict-bearing"),
    ("scripts/__init__.py", "package marker"),
    ("scripts/harvest_mir_corpus.sh", "builds a measurement corpus; produces no verdict"),
    ("scripts/fetch-first-party.sh", "materializes sibling repos for a standalone clone; no verdict"),
    ("scripts/promote-toolchain.sh", "seals and channel-flips a built stage2; mutating promotion, no verdict"),
    ("scripts/trust_clean_corpus_scorecard.py", "measurement scorecard: writes JSON and prints a summary; no pass/fail"),
    ("scripts/harvest_mir_corpus_closed.sh", "corpus builder; produces no verdict"),
    ("scripts/trust_ir_b4_classifier.py", "takes a data_json argument; classifies a wave, judges nothing"),
    # --- classified 2026-08-26, from the catch-all sweep ---
    # EXACT PATHS, not families, even where the ROLE is shared: `_is_tooling`
    # matches by prefix, and every tempting family prefix here would swallow a
    # future gate. `scripts/trust_ir_` covers four reporters AND three verdict
    # lanes (flip-burnin, frontier-table, lineage-reconcile); `scripts/trust-`
    # covers two wrappers today and anything tomorrow. A shared ROLE is recorded
    # by repeating one reason across the paths that share it, which reviews the
    # same and cannot go blind. Widening any of these to a directory or a stem
    # recreates the exact blind spot this file exists to close.
    #
    # Mutating bootstrap/seed materialization: each one PRODUCES a toolchain.
    ("scripts/create_local_genesis_stage0.py", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    ("scripts/recreate_bootstrap.py", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    ("scripts/seed_stage0_after_tests.sh", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    ("scripts/win-genesis/win_genesis.py", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    ("scripts/manual_assemble_stage2_trustc.sh", "mutating bootstrap/seed materialization; produces a toolchain, judges nothing"),
    # Argv-dispatch helpers owned by one shell driver each.
    ("scripts/mint_seed_support.py", "subcommand helper for one shell driver; no standalone verdict"),
    ("scripts/off_stock_rust_audit.py", "subcommand helper for one shell driver; no standalone verdict"),
    # Build plumbing: they forward the wrapped command's status or record a number.
    ("scripts/cargo-concurrency-cap.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/trust_build_lock.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/monitor-build-memory.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/run_measurement_sweep.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/trust-rustc-guard.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/trust_survey.sh", "build plumbing: wrappers, locks and samplers that forward or record"),
    ("scripts/slim_build.py", "disk reclamation: deletes intermediate build trees"),
    ("scripts/trust-session-build.sh", "per-session build-tree setup; writes config, optionally builds"),
    # Analysis instruments. Each prints a table to rank the next slice; the only
    # nonzero exits are input errors. If build memory, the flip frontier or the
    # marginal rate should be ENFORCED, the gate is a threshold over the
    # artifact these emit, not these.
    ("scripts/bench_verifier.py", "A/B microbenchmark; prints timings, no pass/fail threshold"),
    ("scripts/trust_gap.py", "analysis report; nonzero only on bad input, never a verdict"),
    ("scripts/trust_ir_branch_plan_refusal.py", "analysis report; nonzero only on bad input, never a verdict"),
    ("scripts/trust_ir_flip_frontier.py", "analysis report; nonzero only on bad input, never a verdict"),
    ("scripts/trust_ir_marginal_conversion.py", "analysis report; nonzero only on bad input, never a verdict"),
    ("scripts/trust_ir_scc_populations.py", "analysis report; nonzero only on bad input, never a verdict"),
    (
        "scripts/trust_ir_scorecard_diff.py",
        "A/B scorecard diagnostic; reports population deltas and vanished bodies "
        "but defines no pass/fail acceptance threshold",
    ),
    ("scripts/trust_upstream_test_inventory.py", "analysis report; nonzero only on bad input, never a verdict"),
    (
        "scripts/toolchain-provenance-probe.sh",
        "manual post-hoc sealed-toolchain consistency report; prints classifications "
        "but has no pass/fail exit contract or acceptance threshold",
    ),
    # The rest, one role each.
    ("scripts/cutover_gate/gate_schema.py", "importable schema module; no entry point, cannot run"),
    ("scripts/generate_mir_fixtures.sh", "regenerates checked-in MIR fixtures; a generator, not a verdict"),
    ("scripts/remote-burst-setup.sh", "provisions a fresh remote box; apt-get, rustup, clone"),
    ("scripts/sync-first-party.sh", "read-only shim; execs recreate_bootstrap.py --check"),
)


def _is_tooling(rel: str) -> bool:
    return any(
        rel.startswith(pattern) if pattern.endswith(("/", "-")) else rel == pattern
        for pattern, _reason in TOOLING_ROLES
    )


def _named_by(rel: str, commands: str) -> bool:
    """True when some row's command names `rel` as a WHOLE path, not a prefix.

    Coverage was a bare substring test until 2026-08-26, which is fail-OPEN for a
    directory lane: a row naming `tests/self-proof/certified-scoreboard.baseline`
    marked the whole `tests/self-proof` SUITE covered, though nothing runs it as a
    suite. Running one file inside a directory is not running the directory.
    """
    return re.search(re.escape(rel) + r"(?![\w./-])", commands) is not None


def check() -> tuple[list[str], list[str]]:
    errors: list[str] = []
    uncovered: list[str] = []
    rows = manifest_rows()
    if not rows:
        return (["gate manifest is empty"], [])

    today = datetime.now(timezone.utc).date()
    seen_ids: set[str] = set()
    for row in rows:
        if len(row) != 6:
            errors.append(f"row has {len(row)} columns, expected 6: {'|'.join(row)}")
            continue
        gate_id, profiles, _category, required, last_green, _command = row
        if gate_id in seen_ids:
            errors.append(f"{gate_id}: duplicate gate id")
        seen_ids.add(gate_id)
        for profile in profiles.split(","):
            if profile not in KNOWN_PROFILES:
                errors.append(f"{gate_id}: unknown profile {profile!r}")
        if required not in ("true", "false"):
            errors.append(f"{gate_id}: required must be true/false, got {required!r}")
        if last_green != "never":
            if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", last_green):
                errors.append(
                    f"{gate_id}: last_green must be `never` or ISO date, got {last_green!r}"
                )
            else:
                recorded = date.fromisoformat(last_green)
                if recorded > today:
                    errors.append(
                        f"{gate_id}: last_green {last_green} is in the future; a gate "
                        "cannot have passed on a day that has not happened"
                    )

    # This is the product-completion claim, not merely a script covered by the
    # script-test aggregate. Keep its release invocation exact enough that a
    # renamed profile, optional row, or omitted external trust root cannot make
    # the production gate disappear while lane coverage stays green.
    completion_rows = [
        row for row in rows if len(row) == 6 and row[0] == "release.two-language-completion"
    ]
    if len(completion_rows) != 1:
        errors.append(
            "release.two-language-completion: must have exactly one manifest row"
        )
    else:
        _gate_id, profiles, category, required, _last_green, command = completion_rows[0]
        if profiles != "release":
            errors.append(
                "release.two-language-completion: profiles must be exactly `release`"
            )
        if category != "soundness":
            errors.append(
                "release.two-language-completion: category must be `soundness`"
            )
        if required != "true":
            errors.append("release.two-language-completion: must be required")
        expected_command = (
            'TRUST_TOP_VERIFIER_PATH="${TRUST_TWO_LANGUAGE_TOP_VERIFIER:-'
            '/etc/trust/two_language_completion_gate.py}" && '
            'test -n "${TRUST_TWO_LANGUAGE_TOP_VERIFIER_SHA256:-}" && '
            'TRUST_TOP_VERIFIER_ACTUAL="$(/usr/bin/shasum -a 256 '
            '"$TRUST_TOP_VERIFIER_PATH")" && '
            'test "${TRUST_TOP_VERIFIER_ACTUAL%% *}" = '
            '"${TRUST_TWO_LANGUAGE_TOP_VERIFIER_SHA256}" && '
            'python3 "$TRUST_TOP_VERIFIER_PATH" --candidate-verifier '
            'scripts/two_language_completion_gate.py --receipt '
            '"${TRUST_TWO_LANGUAGE_COMPLETION_RECEIPT:-build/two-language-completion/receipt.json}" '
            '--root . --trusted-owner-key '
            '"${TRUST_TWO_LANGUAGE_OWNER_KEY:-/etc/trust/two-language-owner.pub}"'
        )
        if command != expected_command:
            errors.append(
                "release.two-language-completion: command must be exactly the "
                "externally pinned, owner-keyed production completion invocation"
            )

    # scripts/hooks/pre-push derives its whole lane set from `--list push`, so an
    # empty push profile is a gate that reports GREEN having run nothing, and a
    # literal `run_lane <id>` there is the hand-maintained second inventory this
    # collapse removed — two lane sets agreeing only by eye.
    if not [r for r in rows if len(r) == 6 and "push" in r[1].split(",")]:
        errors.append(
            "no row carries the `push` profile; scripts/hooks/pre-push derives its "
            "lanes from it and a gate with no lanes is not a green gate"
        )
    hook_rel = "scripts/hooks/pre-push"
    hook_path = REPO_ROOT / hook_rel
    if not hook_path.exists():
        errors.append(f"{hook_rel}: the installed pre-push gate is gone")
    else:
        for n, line in enumerate(hook_path.read_text(encoding="utf-8").splitlines(), 1):
            if re.match(r"\s*run_lane\s+[A-Za-z]", line):
                errors.append(
                    f"{hook_rel}:{n}: run_lane with a literal gate id; the `push` "
                    "profile in the gate manifest is the only lane list"
                )

    command_list = [row[-1] for row in rows if len(row) == 6]
    commands = "\n".join(command_list)
    for aggregate in INDIRECT.values():
        if aggregate not in commands:
            errors.append(
                f"{aggregate} is the declared aggregate for an indirect lane class "
                "but no manifest row runs it"
            )

    for lane, reason in MANUAL_ONLY.items():
        if not (REPO_ROOT / lane).exists():
            errors.append(f"{lane}: declared manual-only, but the file is gone")
        elif lane in commands:
            errors.append(
                f"{lane}: a manifest row runs it, so the MANUAL_ONLY exemption "
                f"({reason}) no longer holds; drop the entry"
            )

    indirect_classes = {
        "e2e": "tests/e2e_*.sh",
        "script-test": "scripts/tests/*",
    }
    for lane_class, lanes in lane_inventory().items():
        for lane in lanes:
            rel = lane.relative_to(REPO_ROOT).as_posix()
            if _named_by(rel, commands):
                continue
            if lane_class in indirect_classes:
                continue
            if rel in INDIRECT or rel in MANUAL_ONLY:
                continue
            uncovered.append(f"{lane_class}: {rel}")

    for doc, (test_path, package) in DOC_ENFORCEMENT_LANES.items():
        doc_file = REPO_ROOT / doc
        test_file = REPO_ROOT / test_path
        if not doc_file.exists():
            errors.append(f"{doc}: declared doc-enforcement lane, but the document is gone")
            continue
        if not test_file.exists():
            errors.append(f"{doc}: enforcing test {test_path} does not exist")
            continue
        if test_path not in doc_file.read_text(encoding="utf-8"):
            errors.append(
                f"{doc}: no longer names {test_path} as the test that keeps it true; "
                "either restore the claim or drop the pair from DOC_ENFORCEMENT_LANES"
            )
        selector = f"--test {test_file.stem}"
        if not any(
            selector in command and f"-p {package}" in command for command in command_list
        ):
            uncovered.append(f"doc-enforcement ({doc}): {test_path}")

    return (errors, uncovered)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--list-uncovered",
        action="store_true",
        help="Print uncovered lanes and exit 0; for triage, not for gating.",
    )
    args = parser.parse_args()

    errors, uncovered = check()

    if args.list_uncovered:
        for lane in uncovered:
            print(lane)
        return 0

    if errors:
        print("GATE MANIFEST MALFORMED:", file=sys.stderr)
        for error in errors:
            print(f"  {error}", file=sys.stderr)
    if uncovered:
        print("LANES IN NO MANIFEST ROW:", file=sys.stderr)
        for lane in uncovered:
            print(f"  {lane}", file=sys.stderr)
        print(
            "\nEach lane above exists in the tree and no gate runs it. Add a row to\n"
            "`emit_gate_manifest` in tests/run_trust_comprehensive_harness.sh, or add\n"
            "the lane to `INDIRECT` naming the aggregate that already runs it. Only\n"
            "a lane whose interface cannot be a row belongs in `MANUAL_ONLY`, with\n"
            "the reason written down.",
            file=sys.stderr,
        )
    if errors or uncovered:
        return 1

    print(
        "GATE LANE COVERAGE OK: every e2e, gate script, adversarial oracle, script "
        "test, witness/elide regression, compiletest suite, orchestrator, js262 "
        "lane, and declared doc-enforcement test is named by the gate manifest."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
