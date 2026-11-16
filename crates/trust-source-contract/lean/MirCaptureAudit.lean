/- Copyright 2026 Andrew Yates. Apache-2.0. Exact transitive axiom guards. -/
import MirCaptureCheck

/-- info: 'TrustMirCaptureOriginal.original_parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirCaptureOriginal.original_parse

/-- info: 'TrustMirCaptureCheck.original_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirCaptureCheck.original_projection

/-- info: 'TrustMirCaptureView.checked_body_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustMirCaptureView.checked_body_exact

/-- info: 'TrustMirCaptureCheck.checked_capture_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirCaptureCheck.checked_capture_return

/-- info: 'TrustMirCaptureCheck.original_capture_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirCaptureCheck.original_capture_return

/-- info: 'TrustMirCaptureCheck.original_bytes_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirCaptureCheck.original_bytes_return
