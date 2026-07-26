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
