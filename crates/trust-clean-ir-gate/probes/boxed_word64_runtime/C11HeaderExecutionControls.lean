-- Copyright 2026 Andrew Yates | Apache-2.0
import C11HeaderExecution

/-! Constructive projection executions and hostile histories. Neither supplied
interference nor a successful projected execution proves real C11 feasibility,
source ownership, source NoUB, actual TU binding or canonical ARC refinement. -/
namespace C11HeaderExecutionControls
open C11HeaderAST C11HeaderAtomic C11HeaderExecution

def failed : Except e a → Bool
  | .error _ => true
  | .ok _ => false

def machine (initial : UInt32) (schedule : List Packet) : Machine :=
  { atomic := { history := [initial], schedule := schedule },
    macros := [("dropLimit", 0xE0000000), ("incLimit", 0xF0000000)] }
def dropRun (m : Machine) := execute (drop "dropLimit") m
def incRun (m : Machine) := execute (increment "incLimit") m
/-- Observe zero, then another writer stores 7: RMW must return 7, not zero.
The source skips the fence/true branch. -/
theorem drop_observation_is_not_rmw_old :
    (dropRun (machine 0 [{}, { interference := [7] }])).map
      (fun (result, m) => (result, m.atomic.history, m.atomic.events)) =
    .ok (some false, [0, 7, 6], [.load 0 0, .rmw 1 7 6 .release]) := by rfl
/-- The relaxed guard may observe sticky while a later modification is zero.
No RMW/fence is executed merely because the current value differs. -/
theorem sticky_observation_skips_rmw :
    (dropRun (machine 0xE0000000 [{ interference := [0], readFrom := 0 }])).map
      (fun (result, m) => (result, m.atomic.history, m.atomic.events)) =
    .ok (some false, [0xE0000000, 0], [.load 0 0xE0000000]) := by rfl
/-- A nonsticky observation does NOT ensure the later RMW old is nonsticky. -/
theorem sticky_race_is_decremented :
    (dropRun (machine 1 [{}, { interference := [0xE0000000] }])).map
      (fun (result, m) => (result, m.atomic.history, m.atomic.events)) =
    .ok (some false, [1, 0xE0000000, 0xDFFFFFFF],
      [.load 0 1, .rmw 1 0xE0000000 0xDFFFFFFF .release]) := by rfl
/-- OLD zero causes unsigned wrap and an acquire FENCE EVENT; not deallocation. -/
theorem zero_race_wraps_and_fences :
    (dropRun (machine 4 [{}, { interference := [0] }])).map
      (fun (result, m) => (result, m.atomic.history, m.atomic.events)) =
    .ok (some true, [4, 0, 0xFFFFFFFF],
      [.load 0 4, .rmw 1 0 0xFFFFFFFF .release, .fence .acquire]) := by rfl
/-- The source guard cannot rule out overflow after interference. -/
theorem increment_race_wraps :
    (incRun (machine 1 [{}, { interference := [0xFFFFFFFF] }])).map
      (fun (result, m) => (result, m.atomic.history, m.atomic.events)) =
    .ok (none, [1, 0xFFFFFFFF, 0],
      [.load 0 1, .rmw 1 0xFFFFFFFF 0 .relaxed]) := by rfl
/-- Scalar short-circuit: no address/load/RMW/schedule is required. -/
theorem scalar_increment_performs_no_access :
    incRun { (machine 0 []) with scalar := true, headerAccessible := false } =
      .ok (none, { (machine 0 []) with scalar := true, headerAccessible := false }) := by rfl

theorem invalid_address_refused :
    failed (incRun { (machine 0 [{}, {}]) with headerAccessible := false }) = true := by rfl

theorem missing_macro_refused :
    failed (dropRun { (machine 0 [{}, {}]) with macros := [] }) = true := by rfl

theorem invalid_read_from_refused :
    C11HeaderAtomic.load { history := [5], schedule := [{ readFrom := 1 }] } =
      .error .invalidReadFrom := by rfl

theorem backwards_read_refused :
    failed (C11HeaderAtomic.load { history := [5, 6], readFloor := 1, schedule := [{ readFrom := 0 }] }) = true := by rfl

theorem missing_atomic_event_refused :
    failed (dropRun (machine 0 [{}])) = true := by rfl

/-- For ANY two word values, a load can observe the first while the next RMW
returns the second. This is constructive nonvacuity of the projection only;
the interference write still needs a real checked C11 global execution. -/
theorem arbitrary_distinct_observations (observed old : UInt32) :
    (do
      let (loaded, afterLoad) ← C11HeaderAtomic.load
        { history := [observed], schedule := [{}, { interference := [old] }] }
      let (returned, afterRmw) ← C11HeaderAtomic.rmw true 1 .release afterLoad
      pure (loaded, returned, afterRmw.history)) =
    (Except.ok (observed, old, [observed, old, old - 1]) : Except Error _) := by rfl

/-- A proposed read-from on an RMW cannot choose an older/different value:
the RMW always reads its immediate modification-order predecessor. -/
theorem forged_rmw_read_from_is_ignored :
    (C11HeaderAtomic.rmw true 1 .release
      { history := [3], schedule := [{ interference := [8], readFrom := 999 }] }).map
      (fun (old, state) => (old, state.history, state.events)) =
    .ok (8, [3, 8, 7], [.rmw 1 8 7 .release]) := by rfl

#print axioms drop_observation_is_not_rmw_old
#print axioms zero_race_wraps_and_fences
#print axioms increment_race_wraps
end C11HeaderExecutionControls
