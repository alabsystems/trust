#!/usr/bin/env python3
"""Focused classification controls for the TrustIR producer scorecard."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]


def load_scorecard_module():
    path = REPO_ROOT / "scripts" / "trust_ir_producer_scorecard.py"
    spec = importlib.util.spec_from_file_location("trust_ir_producer_scorecard", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


scorecard = load_scorecard_module()


def test_unmodeled_observation_marker_outranks_embedded_broad_tokens() -> None:
    note = (
        "returns/traps matched, but THIR side: reachable function `vararg direct call` "
        "contains state; observable-effect comparison is not modeled (coverage-only skip)"
    )
    assert (
        scorecard.classify_note("NotRun", note)
        == "clean-skip-unmodeled-observation"
    )


def test_callable_comparability_marker_has_the_same_stable_class() -> None:
    note = (
        "return comparability failure on input [] (return value 0: "
        "callable/frame identity comparison is not modeled); coverage-only skip"
    )
    assert (
        scorecard.classify_note("NotRun", note)
        == "clean-skip-unmodeled-observation"
    )


def test_unrelated_existing_classes_remain_stable() -> None:
    assert scorecard.classify_note("Agreed", "anything") == "agreed"
    assert (
        scorecard.classify_note("NotRun", "non-scalar parameter type is non-interpretable")
        == "clean-skip-nonscalar-param"
    )


def test_in_fragment_rate_is_secondary_and_headline_never_moves():
    """Trust (fragment honesty): the coroutine-body out-of-fragment split.

    Two invariants, each mutation-provable: (1) a body tagged
    `ClosureEnv(coroutine body)` counts into `bodies_out_of_fragment` and the
    in-fragment denominator shrinks by exactly that count; (2) the HEADLINE
    `lowered_clean_pct` is computed over the FULL denominator -- relabeling a
    body out-of-fragment must never move it.
    """
    import os
    import importlib.util as _u
    spec = _u.spec_from_file_location(
        "scorecard", os.path.join(os.path.dirname(__file__), "..", "trust_ir_producer_scorecard.py"))
    sc = _u.module_from_spec(spec)
    spec.loader.exec_module(sc)
    results = [{
        "outcome": "ok",
        "bodies": [
            {"def": "a", "unsupported": 0, "reasons": [], "kind": "named",
             "mode": "NotRun", "note": "", "symbolic": False,
             "opaque_collapse": False, "equal": False, "samples": 0, "note_class": "unsupported"},
            {"def": "b", "unsupported": 2, "kind": "closure",
             "reasons": ["ClosureEnv(coroutine body)", "Yield"],
             "mode": "NotRun", "note": "", "symbolic": False,
             "opaque_collapse": False, "equal": False, "samples": 0, "note_class": "unsupported"},
            {"def": "c", "unsupported": 1, "reasons": ["Ty"], "kind": "named",
             "mode": "NotRun", "note": "", "symbolic": False,
             "opaque_collapse": False, "equal": False, "samples": 0, "note_class": "unsupported"},
        ],
    }]
    agg = sc.aggregate(results)
    b = agg["bodies"]
    assert b["bodies_out_of_fragment"] == 1
    assert b["lowered_clean"] == 1
    assert b["lowered_clean_pct"] == round(100.0 * 1 / 3, 1), "headline is FULL-denominator"
    assert b["lowered_clean_in_fragment_pct"] == round(100.0 * 1 / 2, 1)
