/- Copyright 2026 Andrew Yates. Apache-2.0. Exact transitive axiom guards. -/
import MirBoolAssignment

/-- info: 'TrustMirBoolAssignment.const_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.const_step

/-- info: 'TrustMirBoolAssignment.copy_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.copy_step

/-- info: 'TrustMirBoolAssignment.store_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.store_step

/-- info: 'TrustMirBoolAssignment.write_image' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.write_image

/-- info: 'TrustMirBoolAssignment.after_memory' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.after_memory

/-- info: 'TrustMirBoolAssignment.assignment_simulates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.assignment_simulates

/-- info: 'TrustMirBoolAssignment.actual_return_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.actual_return_tail

/-- info: 'TrustMirBoolAssignment.actual_root_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.actual_root_prefix

/-- info: 'TrustMirBoolAssignment.actual_root_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustMirBoolAssignment.actual_root_assignment
