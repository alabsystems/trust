# w2-iter-offset-modeled-2026-07-20 — the re-dumped slice-iter family with Rvalue::PtrOffset

Same probe as w2-iter-harvest-2026-07-20, re-dumped with the INC0-rebuilt trustc
(stage2 @ bef750b5e3, TRUST_SEED_STAIRCASE=1). THE CARRIER WORKS END-TO-END:
Iter::next / Iter::new / into_iter / fold now carry Rvalue::PtrOffset{ptr,count}
with ZERO `Unsupported BinOp::Offset` markers.

Verdicts (16 instances): 2 SAFETY_GAP / 14 SHAPE_GAP — UNCHANGED from the
baseline, exactly as INC0's fail-closed sequencing requires: the vcgen
UnsupportedMir-class PtrOffset obligation + recognizer declines hold until the
REFLECTION increment converges PtrOffset onto the intrinsic lane's PtrModel and
mints the real ptr_offset_bounds_vc (e76e5b6590's direct continuation). That
reflection is Iter::next's sole remaining value-path blocker.
