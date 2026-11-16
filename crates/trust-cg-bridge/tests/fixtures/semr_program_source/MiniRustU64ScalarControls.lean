/- Complete actual function controls, preserving both worlds and step logs. -/
import MiniRustU64ScalarFixtures
import MiniRustU64AvailabilityControls
noncomputable section
namespace MiniRustU64ScalarControls
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
  MiniRustU64Entry MiniRustU64Call MiniRustU64AllocatedCall MiniRustU64Run
  MiniRustU64Correspondence MiniRustU64Availability MiniRustAllocate8Safety
  MiniRustU64ScalarCorrespondence MiniRustU64ScalarFixtures
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def ConcreteCall (bytes : List Nat) (literal : Nat) : Prop :=
  ∀ (fuel input : Nat) (π : List Nat → Nat), input < modulus 64 →
    SOut.runOracle (entryOracle 3) π
      (enterFromBytes fuel input bytes MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
        [] MiniRustU64AvailabilityControls.outside 8 uninit8 []) =
      .ok (.ok (), exitState MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
        [] MiniRustU64AvailabilityControls.outside 8 32 40 ((input + literal) % modulus 64) input)

theorem concrete_call (bytes : List Nat) (literal : Nat)
    (checked : SemRU64ScalarProfile.Decodes bytes literal) (literalValid : literal < modulus 64) :
    ConcreteCall bytes literal := by
  intro fuel input π inputValid
  exact profile_function_available fuel literal input bytes MiniRustU64Controls.base
    MiniRustU64Controls.caller ⟨0⟩ [] MiniRustU64AvailabilityControls.outside 8 uninit8 []
    checked (by rfl) (by decide) inputValid literalValid 3
    MiniRustU64AvailabilityControls.concrete_high_water (by decide) π

def ZeroComplete : Prop := ConcreteCall zeroBytes 0
theorem zero_complete : ZeroComplete := concrete_call zeroBytes 0 zero_decodes (by decide)

def Fresh8Complete : Prop := ConcreteCall fresh8Bytes 8
theorem fresh8_complete : Fresh8Complete := concrete_call fresh8Bytes 8 fresh8_decodes (by decide)

def MaxComplete : Prop := ConcreteCall maxBytes 18446744073709551615
theorem max_complete : MaxComplete :=
  concrete_call maxBytes 18446744073709551615 max_decodes (by decide)

def RenamedComplete : Prop := ConcreteCall renamed7Bytes 7
theorem renamed_complete : RenamedComplete := concrete_call renamed7Bytes 7 renamed7_decodes (by decide)

def Current63Complete : Prop := ConcreteCall current63Bytes 7
theorem current63_complete : Current63Complete :=
  concrete_call current63Bytes 7 current63_decodes (by decide)

def Original262Complete : Prop := ConcreteCall originalBytes 7
theorem original262_complete : Original262Complete :=
  concrete_call originalBytes 7 original_decodes (by decide)

/-- Closed complete-world claims keep hostile type checks separate from
    universal-model conversion depth. They are instances of the real universal
    function theorem above, not sampled interpreter output or assumed runs. -/
def ClosedCall (bytes : List Nat) (input value : Nat) : Prop :=
  SOut.runOracle (entryOracle 3) (fun _ => 0)
    (enterFromBytes 0 input bytes MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
      [] MiniRustU64AvailabilityControls.outside 8 uninit8 []) =
    .ok (.ok (), exitState MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
      [] MiniRustU64AvailabilityControls.outside 8 32 40 value input)

def ZeroClosed : Prop := ClosedCall zeroBytes 18446744073709551615 18446744073709551615
theorem zero_closed : ZeroClosed := zero_complete 0 18446744073709551615 (fun _ => 0) (by decide)

def Fresh8Closed : Prop := ClosedCall fresh8Bytes 0 8
theorem fresh8_closed : Fresh8Closed := fresh8_complete 0 0 (fun _ => 0) (by decide)

def MaxClosed : Prop := ClosedCall maxBytes 1 0
theorem max_closed : MaxClosed := max_complete 0 1 (fun _ => 0) (by decide)

def RenamedClosed : Prop := ClosedCall renamed7Bytes 0 7
theorem renamed_closed : RenamedClosed := renamed_complete 0 0 (fun _ => 0) (by decide)

def Current63Closed : Prop := ClosedCall current63Bytes 0 7
theorem current63_closed : Current63Closed := current63_complete 0 0 (fun _ => 0) (by decide)

def Original262Closed : Prop := ClosedCall originalBytes 0 7
theorem original262_closed : Original262Closed := original262_complete 0 0 (fun _ => 0) (by decide)

/-- Hostile full-world endpoint differs ONLY by leaving the private argument
    allocation live. The real endpoint retires both; a scalar-result-only or
    projected-world proof cannot establish this counterclaim. -/
def wrongLiveExit (value input : Nat) : MR_Machine :=
  single MiniRustU64Controls.base
    [(MiniRustU64Controls.caller.set_next_block ⟨0⟩).set_next_stmt 0]
    (deadReturnCells
      (callerWorld [] MiniRustU64AvailabilityControls.outside 8 (u64bytes value))
      32 40 value input [⟨.Load, .None, 32, 8⟩, ⟨.Store, .None, 8, 8⟩])

def WrongFullWorld : Prop :=
  SOut.runOracle (entryOracle 3) (fun _ => 0)
    (enterFromBytes 0 0 fresh8Bytes MiniRustU64Controls.base MiniRustU64Controls.caller ⟨0⟩
      [] MiniRustU64AvailabilityControls.outside 8 uninit8 []) =
    .ok (.ok (), wrongLiveExit 8 0)

def WrongScalar : Prop := ClosedCall fresh8Bytes 0 7

end MiniRustU64ScalarControls
