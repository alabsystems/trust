/- Exact transitive axiom guards; no assumed source-preservation premise. -/
import LiveHelperEnumWire

/-- info: 'TrustLiveHelperEnumWire.original_decodes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.original_decodes

/-- info: 'TrustLiveHelperEnumWire.mutant_decodes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.mutant_decodes

/-- info: 'TrustLiveHelperEnumWire.exact_formal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.exact_formal

/-- info: 'TrustLiveHelperEnumWire.declared_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.declared_return

/-- info: 'TrustLiveHelperEnumWire.viewed_return_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.viewed_return_correspondence

/-- info: 'TrustLiveHelperEnumWire.source_mutant_changes_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.source_mutant_changes_first

/-- info: 'TrustLiveHelperEnumWire.source_mutant_not_old_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.source_mutant_not_old_return

/-- info: 'TrustLiveHelperEnumWire.untouched_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.untouched_arm

/-- info: 'TrustLiveHelperEnumWire.wrong_nominal_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.wrong_nominal_identity

/-- info: 'TrustLiveHelperEnumWire.fuel_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustLiveHelperEnumWire.fuel_preserved
