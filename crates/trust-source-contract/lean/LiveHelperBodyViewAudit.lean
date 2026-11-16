/- Exact transitive axiom guards for the observed body-data relation. -/
import LiveHelperBodyView

/-- info: 'TrustLiveHelperBodyView.exact_population' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustLiveHelperBodyView.exact_population

/-- info: 'TrustLiveHelperBodyView.exact_move_entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustLiveHelperBodyView.exact_move_entry

/-- info: 'TrustLiveHelperBodyView.declared_branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperBodyView.declared_branch

/-- info: 'TrustLiveHelperBodyView.exact_return' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustLiveHelperBodyView.exact_return

/-- info: 'TrustLiveHelperBodyView.body_path_and_byte_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperBodyView.body_path_and_byte_outcome

/-- info: 'TrustLiveHelperBodyView.source_arm_mutant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperBodyView.source_arm_mutant

/-- info: 'TrustLiveHelperBodyView.wrong_destination_not_entry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustLiveHelperBodyView.wrong_destination_not_entry
