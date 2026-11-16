/- Interval safety and constructive room for the unchanged generated allocator. -/
import MiniRustAllocate8Safety
noncomputable section
namespace MiniRustAllocate8Safety
open SemR MiniRustU64Function MiniRustU64Entry
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Exact interval separation, including the generated zero-sized rule. -/
def IntervalSafe (allocations : List MR_Allocation) (addr : Int) : Prop :=
  ∀ old, old ∈ allocations → old.live = true →
    ((old.addr + Int.ofNat old.data.length ≤ addr ∨ addr + 8 ≤ old.addr) ∧ old.addr ≠ addr)

theorem overlap_false_iff (old : MR_Allocation) (addr : Int) :
    overlap old addr = false ↔
      ((old.addr + Int.ofNat old.data.length ≤ addr ∨ addr + 8 ≤ old.addr) ∧ old.addr ≠ addr) := by
  simp only [Int.ofNat_eq_natCast] at *
  by_cases h1 : old.addr + (old.data.length : Int) ≤ addr
  · simp [overlap, SInt.ble, SInt.beq, h1]
  · by_cases h2 : addr + 8 ≤ old.addr <;>
      simp [overlap, SInt.ble, SInt.beq, h1, h2]

theorem scan_false_iff (allocations : List MR_Allocation) (addr : Int) :
    anyOverlap allocations addr = false ↔
      ∀ old, old ∈ allocations → old.live = true → overlap old addr = false := by
  induction allocations with
  | nil => simp [anyOverlap]
  | cons old rest ih =>
    cases hl : old.live <;> cases ho : overlap old addr <;>
      simp [anyOverlap, hl, ho, ih]

theorem interval_safe_iff (allocations : List MR_Allocation) (addr : Int) :
    IntervalSafe allocations addr ↔ anyOverlap allocations addr = false := by
  rw [scan_false_iff]
  exact forall_congr' (fun old => by simp only [IntervalSafe, overlap_false_iff])

/-- Necessary facts of every accepted callback, not an allocation-success premise. -/
theorem allowed_safe (allocations : List MR_Allocation) (addr : Int)
    (accepted : allocationAllowed allocations addr = true) :
    0 < addr ∧ rem8 addr = 0 ∧ addr + 8 < Int.ofNat (modulus 64) ∧ IntervalSafe allocations addr := by
  cases hp : SInt.ble addr 0 <;>
    cases hr : SInt.beq (rem8 addr) 0 <;>
    cases hb : inRange false 64 (addr + 8) <;>
    cases hs : anyOverlap allocations addr <;>
    simp [allocationAllowed, hp, hr, hb, hs, SBool.not] at accepted
  have hpositive : ¬ addr ≤ 0 := by simpa [SInt.ble] using hp
  have hrem : rem8 addr = 0 := by simpa [SInt.beq] using hr
  have hbounds : 0 ≤ addr + 8 ∧ addr + 8 < Int.ofNat (modulus 64) := by
    simpa [inRange] using hb
  exact ⟨by omega, hrem, hbounds.2, (interval_safe_iff allocations addr).2 hs⟩

/-- Generic safety over every admitted leaf; rejection is retained explicitly. -/
theorem choice_every {α : Type} (bound : Int) (allowed : Int → Bool)
    (make : Int → α) (p : α → Prop)
    (safe : ∀ index, SInt.blt (candidate index) bound = true →
      allowed (candidate index) = true → p (make (candidate index))) :
    EveryResult p (choiceTree bound allowed make) := by
  change ∀ index, EveryResult p _
  intro index
  cases hu : SInt.blt (candidate index) bound <;>
    cases ha : allowed (candidate index)
  · trivial
  · trivial
  · trivial
  · exact safe index hu ha

/-- Complete result shape and address safety, with the old memory preserved. -/
def Allocation8Safe (world : List MR_Allocation) (kind : MR_AllocationKind)
    (result : SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory) : Prop :=
  ∃ index, result = allocated8 world kind (candidate index) ∧
    0 < candidate index ∧ rem8 (candidate index) = 0 ∧
    candidate index + 8 < Int.ofNat (modulus 64) ∧ IntervalSafe world (candidate index)

theorem allocated8_safe (world : List MR_Allocation) (kind : MR_AllocationKind)
    (index : Nat) (accepted : allocationAllowed world (candidate index) = true) :
    Allocation8Safe world kind (allocated8 world kind (candidate index)) := by
  exact Exists.intro index (And.intro (Eq.refl _) (allowed_safe world (candidate index) accepted))

attribute [local irreducible] EveryResult

theorem allocate8Tree_every (world : List MR_Allocation) (kind : MR_AllocationKind) :
    EveryResult (Allocation8Safe world kind) (allocate8Tree world kind) := by
  unfold allocate8Tree
  exact @choice_every (SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory)
    (Int.ofNat (modulus 64)) (allocationAllowed world)
    (allocated8 world kind) (Allocation8Safe world kind)
    (fun index _ accepted => allocated8_safe world kind index accepted)

theorem allocate8_every (fuel : Nat) (world : List MR_Allocation) (kind : MR_AllocationKind) :
    EveryResult (Allocation8Safe world kind)
      (MRf.BasicMemory.allocate (fuel + 4) ⟨world, ()⟩ kind 8 8 () ()) :=
  Eq.mpr (congrArg (EveryResult (Allocation8Safe world kind)) (allocate8_exact fuel world kind))
    (allocate8Tree_every world kind)

theorem uninit8_length : uninit8.length = 8 := rfl

/-- An explicit high-water condition on live outside allocations only. -/
def Below (world : List MR_Allocation) (limit : Nat) : Prop :=
  ∀ old, old ∈ world → old.live = true →
    old.addr + Int.ofNat old.data.length ≤ Int.ofNat limit

theorem allowed_of_gates (world : List MR_Allocation) (addr : Int)
    (hp : SInt.ble addr 0 = false) (hr : SInt.beq (rem8 addr) 0 = true)
    (hb : inRange false 64 (addr + 8) = true) (hs : anyOverlap world addr = false) :
    allocationAllowed world addr = true := by
  simp only [allocationAllowed, hp, hr, hb, hs, SBool.not,
    Bool.false_eq_true, ↓reduceIte]

attribute [local irreducible] allocationAllowed

theorem allowed_of_interval (world : List MR_Allocation) (index : Nat)
    (separate : IntervalSafe world (candidate index))
    (room : candidate index + 8 < Int.ofNat (modulus 64)) :
    allocationAllowed world (candidate index) = true := by
  have hp : SInt.ble (candidate index) 0 = false := by
    simp only [SInt.ble, decide_eq_false_iff_not]
    have := candidate_positive index
    omega
  have hr : SInt.beq (rem8 (candidate index)) 0 = true := by rw [candidate_rem]; rfl
  have hb : inRange false 64 (candidate index + 8) = true := by
    simp only [inRange, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    have := candidate_positive index
    exact ⟨by omega, room⟩
  have hs := (interval_safe_iff world (candidate index)).1 separate
  exact allowed_of_gates world (candidate index) hp hr hb hs

theorem high_water_separate (world : List MR_Allocation) (k index : Nat)
    (below : Below world (8 * k)) (after : k < index + 1) :
    IntervalSafe world (candidate index) := by
  intro old member live
  have h := below old member live
  have nonnegative : 0 ≤ Int.ofNat old.data.length := by
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [candidate_nat]
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add] at *
  constructor
  · left; omega
  · omega

theorem candidate_end_room (k : Nat) (room : 8 * (k + 2) < modulus 64) :
    candidate k + 8 < Int.ofNat (modulus 64) := by
  rw [candidate_nat]
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
  omega

/-- A sufficient, constructive room condition. It is not asserted for a full
    address space, nor falsely claimed necessary for holes below the high-water mark. -/
theorem allowed_from_high_water (world : List MR_Allocation) (k : Nat)
    (below : Below world (8 * k)) (room : 8 * (k + 2) < modulus 64) :
    allocationAllowed world (candidate k) = true :=
  allowed_of_interval world k (high_water_separate world k k below (by omega))
    (candidate_end_room k room)

/-- Adjacent size-eight allocations may touch at the end, but never share
    their starting address, including with live zero-sized outside records. -/
theorem two_allowed_from_high_water (world : List MR_Allocation) (kind : MR_AllocationKind)
    (k : Nat) (below : Below world (8 * k)) (room : 8 * (k + 3) < modulus 64) :
    allocationAllowed world (candidate k) = true ∧
    allocationAllowed (world ++ [⟨uninit8, candidate k, 8, kind, true, ()⟩])
      (candidate (k + 1)) = true := by
  refine ⟨allowed_from_high_water world k below (by omega), ?_⟩
  apply allowed_of_interval
  · intro old member live
    rcases List.mem_append.mp member with prior | fresh
    · exact high_water_separate world k (k + 1) below (by omega) old prior live
    · have same := List.mem_singleton.mp fresh
      subst old
      simp only [uninit8_length]
      simp only [candidate, Int.ofNat_eq_natCast, Int.natCast_add]
      constructor
      · left; omega
      · omega
  · exact candidate_end_room (k + 1) (by omega)

/-- The ordinary oracle has a concrete accepted branch; no successful
    allocation/call/run equality appears as an assumption. -/
theorem choice_run {α : Type} (bound : Int) (allowed : Int → Bool) (make : Int → α)
    (index : Nat) (upper : SInt.blt (candidate index) bound = true)
    (accepted : allowed (candidate index) = true) (π : List Nat → Nat) :
    SOut.runOracle (fun _ => index) π (choiceTree bound allowed make) =
      .ok (make (candidate index)) := by
  unfold choiceTree SOut.runOracle
  dsimp only
  rw [upper, accepted]

theorem allocate8_room (fuel : Nat) (world : List MR_Allocation) (kind : MR_AllocationKind)
    (k : Nat) (below : Below world (8 * k)) (room : 8 * (k + 2) < modulus 64)
    (π : List Nat → Nat) :
    SOut.runOracle (fun _ => k) π
      (MRf.BasicMemory.allocate (fuel + 4) ⟨world, ()⟩ kind 8 8 () ()) =
      .ok (allocated8 world kind (candidate k)) := by
  rw [allocate8_exact]
  apply choice_run
  · have hend := candidate_end_room k room
    have : candidate k < Int.ofNat (modulus 64) := by omega
    simpa [SInt.blt] using this
  · exact allowed_from_high_water world k below room


end MiniRustAllocate8Safety
