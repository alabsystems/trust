#!/usr/bin/env python3
"""The producer scorecard reads the EFFECT-CONSERVATION verdict per body.

`rustc_mir_build::trust_ir_crate_finalize` emits one `trust-ir-lower: effect
conservation` event per body the mainline lowering recorded (target
`rustc_mir_build::builder`, so the sweep's filter already captures it). The
scorecard joins it to the body row and aggregates it over the lowered-clean
bodies: how many the gate keeps, how many it refuses, and why. These pins cover
the event parse (with and without the trailing `detail`), the join, and the
census — including that a body with no event is UNMEASURED, never conserved.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
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

DIFF = (
    " DEBUG rustc_mir_build::builder trust-ir-lower: differential, "
    "def=DefId(0:{i} ~ k[0001]::{name}), equal=true, samples=0, mode=NotRun, note=\"x\"\n"
)
EFFCONS = (
    "  INFO rustc_mir_build::builder trust-ir-lower: effect conservation, "
    "def=DefId(0:{i} ~ k[0001]::{name}), conserved={conserved}, clean=true, spliced={spliced}, "
    "classes={classes}, equivalences={{}}{detail}\n"
)


def stderr(rows):
    out = []
    for i, (name, conserved, spliced, classes, detail) in enumerate(rows, start=3):
        out.append(DIFF.format(i=i, name=name))
        out.append(
            EFFCONS.format(
                i=i,
                name=name,
                conserved="true" if conserved else "false",
                spliced="true" if spliced else "false",
                classes=classes,
                detail=detail,
            )
        )
    return "".join(out)


class EffectConservationParse(unittest.TestCase):
    def test_event_joins_its_body_with_and_without_detail(self):
        text = stderr(
            [
                ("plain", True, True, "", ", detail=0 tag(s): "),
                (
                    "guard_scope",
                    False,
                    True,
                    "abstracted(drop)",
                    ", detail=1 tag(s): Abstracted(drop, a drop at x.rs:3:1)",
                ),
                ("old_compiler_shape", False, False, "not-conserved(call)+abstracted(undef)", ""),
            ]
        )
        bodies, _ = scorecard.parse_bodies(text)
        by = {b["def"]: b for b in bodies}
        self.assertEqual(by["k[0001]::plain"]["effect_conservation"]["classes"], [])
        g = by["k[0001]::guard_scope"]["effect_conservation"]
        self.assertFalse(g["conserved"])
        self.assertEqual(g["classes"], ["abstracted(drop)"])
        self.assertIn("Abstracted(drop", g["detail"])
        o = by["k[0001]::old_compiler_shape"]["effect_conservation"]
        self.assertEqual(o["classes"], ["not-conserved(call)", "abstracted(undef)"])
        self.assertNotIn("detail", o)

    def test_census_counts_refusals_and_keeps_unmeasured_apart(self):
        text = stderr(
            [
                ("a", True, True, "", ""),
                ("b", False, True, "abstracted(drop)", ""),
                ("c", False, False, "not-conserved(call)+abstracted(opaque-lane)", ""),
            ]
        )
        bodies, _ = scorecard.parse_bodies(text)
        # A body the gate never reported must count as unmeasured, not conserved.
        bodies.append({"def": "k::d", "mode": "NotRun", "effect_conservation": None})
        census = scorecard.effect_conservation_census(bodies)
        self.assertEqual(census["measured"], 3)
        self.assertEqual(census["unmeasured"], 1)
        self.assertEqual(census["conserved"], 1)
        self.assertEqual(census["refused"], 2)
        self.assertEqual(census["refused_spliced"], 1)
        self.assertEqual(census["refused_not_conserved"], 1)
        self.assertEqual(census["refused_abstracted_only"], 1)
        self.assertEqual(
            census["class_histogram"],
            {"abstracted(drop)": 1, "not-conserved(call)": 1, "abstracted(opaque-lane)": 1},
        )
        self.assertEqual(census["not_conserved_defs"], ["k[0001]::c"])


if __name__ == "__main__":
    unittest.main()
