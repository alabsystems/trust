/- Allocation facts for the unchanged generated MiniRust allocator.
   No successful-operation premise or compiler admission is introduced. -/
import MiniRustU64Entry

noncomputable section
namespace MiniRustAllocate8Safety
open SemR MiniRustU64Function MiniRustU64Entry
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def uninit8 : List MR_AbstractByte := SList.repeatNat .Uninit 8

def candidate (index : Nat) : Int := (1 + Int.ofNat index) * 8

def rem8 (addr : Int) : Int :=
  SInt.ofSignedNat (SInt.isNeg addr) (SInt.abs addr % 8)

/-- All generated gates, including same-address live zero-sized allocations. -/
def allocationAllowed (allocations : List MR_Allocation) (addr : Int) : Bool :=
  if SInt.ble addr 0 then false else
  if SBool.not (SInt.beq (rem8 addr) 0) then false else
  if SBool.not (inRange false 64 (addr + 8)) then false else
  if anyOverlap allocations addr then false else true

theorem append_model {α : Type} (left right : List α) :
    SList.appendL left right = left ++ right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp only [SList.appendL, List.cons_append, ih]

def allocated8 (allocations : List MR_Allocation) (kind : MR_AllocationKind)
    (addr : Int) : SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory :=
  (.ok (ptr allocations.length addr),
    ⟨allocations ++ [⟨uninit8, addr, 8, kind, true, ()⟩], ()⟩)

/-- The pick/bind shape alone, generic in its bound, result and callback. -/
def choiceWith {α : Type} (bound : Int) (check : Int → SOut (Bool × Unit))
    (make : Int → α) : SOut α :=
  (SPick.choose ⟨1, bound, 8⟩ (fun addr (_ : Unit) => check addr) ()).bind
    (fun result => match result with | (addr, _) => .ok (make addr))

def choiceTree {α : Type} (bound : Int) (allowed : Int → Bool)
    (make : Int → α) : SOut α :=
  .pick (fun index => match SInt.blt (candidate index) bound with
    | false => .reject
    | true => match allowed (candidate index) with
      | false => .reject
      | true => .ok (make (candidate index)))

theorem choice_checked {α : Type} (bound : Int) (check : Int → SOut (Bool × Unit))
    (allowed : Int → Bool) (make : Int → α)
    (checked : ∀ addr, check addr = .ok (allowed addr, ())) :
    choiceWith bound check make = choiceTree bound allowed make := by
  have hceil : SInt.div_ceil 1 8 = SOut.ok 1 := rfl
  simp only [choiceWith, choiceTree, SPick.choose, hceil, SOut.bind_ok']
  change SOut.pick _ = SOut.pick _
  apply congrArg SOut.pick
  funext index
  dsimp only
  rw [checked]
  change ((match SInt.blt (candidate index) bound with
    | false => SOut.reject
    | true => match allowed (candidate index) with
      | true => SOut.ok (candidate index, ())
      | false => SOut.reject).bind
    (fun result => SOut.ok (make result.1))) = _
  cases hu : SInt.blt (candidate index) bound <;>
    cases ha : allowed (candidate index) <;> rfl

theorem choiceTree_congr {α : Type} (bound : Int) (allowed : Int → Bool)
    (make other : Int → α) (same : ∀ addr, make addr = other addr) :
    choiceTree bound allowed make = choiceTree bound allowed other := by
  apply congrArg SOut.pick
  funext index
  cases hu : SInt.blt (candidate index) bound <;>
    cases ha : allowed (candidate index)
  · rfl
  · rfl
  · rfl
  · exact congrArg SOut.ok (same (candidate index))

/-- A characterization of the original demonic tree, not another evaluator. -/
def allocate8Tree (allocations : List MR_Allocation) (kind : MR_AllocationKind) :
    SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory) :=
  choiceTree (Int.ofNat (modulus 64)) (allocationAllowed allocations)
    (allocated8 allocations kind)

theorem candidate_nat (index : Nat) :
    candidate index = Int.ofNat ((index + 1) * 8) := by
  simp only [candidate, Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
  omega

theorem candidate_positive (index : Nat) : 0 < candidate index := by
  rw [candidate_nat]
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add]
  omega

theorem candidate_rem (index : Nat) : rem8 (candidate index) = 0 := by
  rw [candidate_nat]
  simp [rem8, SInt.ofSignedNat, SInt.isNeg, SInt.abs]

theorem candidate_alignment (index : Nat) :
    SAlign.is_aligned 8 (candidate index) = SOut.ok true := by
  rw [candidate_nat]
  have h := SemR.aligned_minirust ((index + 1) * 8) 8 (by decide)
  simpa using h

/-- The original live-allocation scan, kept opaque while composing stages. -/
def scan8 (fuel : Nat) (allocations : List MR_Allocation) (addr : Int) : SOut (Bool × Unit) :=
  SList.anyS allocations
    (fun allocation (_ : Unit) => match allocation.live with
      | true => (MRf.Allocation.overlaps fuel allocation addr 8).bind
          (fun result => .ok (result, ()))
      | false => .ok (false, ())) ()

theorem scan8_checked (fuel : Nat) (allocations : List MR_Allocation) (addr : Int) :
    scan8 (fuel + 2) allocations addr = .ok (anyOverlap allocations addr, ()) := by
  exact scan_overlaps fuel allocations addr

/-- The generated callback, with the same Bool matches and state tuple. -/
def allocationGate (fuel : Nat) (allocations : List MR_Allocation) (addr : Int) :
    SOut (Bool × Unit) :=
  match SInt.ble addr 0 with
  | true => .ok (false, ())
  | false => (SAlign.is_aligned 8 addr).bind (fun aligned =>
    match SBool.not aligned with
    | true => .ok (false, ())
    | false => (MRf.x86_64.PTR_SIZE fuel).bind (fun size =>
      (SInt.in_bounds (addr + 8) .Unsigned size).bind (fun inBounds =>
        match SBool.not inBounds with
        | true => .ok (false, ())
        | false => (scan8 fuel allocations addr).bind
          (fun result => match result with
            | (overlaps, _) => match overlaps with
              | true => .ok (false, ())
              | false => .ok (true, ())))))

theorem allocation_gate_checked (fuel : Nat) (allocations : List MR_Allocation) (addr : Int) :
    allocationGate (fuel + 2) allocations addr = .ok (allocationAllowed allocations addr, ()) := by
  have hp : MRf.x86_64.PTR_SIZE (fuel + 2) = SOut.ok 8 := rfl
  have halign : SAlign.is_aligned 8 addr = SOut.ok (SInt.beq (rem8 addr) 0) := by
    simp [SAlign.is_aligned, SInt.rem, SInt.beq, SInt.abs, rem8, SOut.bind_ok']
  simp only [allocationGate, hp, halign, unsigned_bounds64, scan8_checked, SOut.bind_ok']
  cases h1 : SInt.ble addr 0 <;>
    cases h2 : SInt.beq (rem8 addr) 0 <;>
    cases h3 : inRange false 64 (addr + 8) <;>
    cases h4 : anyOverlap allocations addr <;>
    simp [SBool.not, h1, h2, h3, h4, allocationAllowed]

/-- Literal allocation endpoint before the separately checked list normalization. -/
def allocated8Raw (allocations : List MR_Allocation) (kind : MR_AllocationKind)
    (addr : Int) : SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory :=
  (.ok ⟨addr, some (⟨SList.len allocations⟩, ())⟩,
    (MR_BasicMemory.mk allocations ()).set_allocations
      (SList.push allocations ⟨uninit8, addr, 8, kind, true, ()⟩))

theorem allocated8Raw_eq (allocations : List MR_Allocation) (kind : MR_AllocationKind) (addr : Int) :
    allocated8Raw allocations kind addr = allocated8 allocations kind addr := by
  simp only [allocated8Raw, allocated8, ptr, SList.len, SemR.lenNat_eq,
    SList.push, append_model, MR_BasicMemory.set_allocations]

/-- Only the callback is abstracted; choice and allocation are unchanged. -/
def allocate8With (allocations : List MR_Allocation) (kind : MR_AllocationKind)
    (check : Int → SOut (Bool × Unit)) :
    SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory) :=
  choiceWith (Int.ofNat (modulus 64)) check (allocated8Raw allocations kind)

/-- The generated outer binds with only primitive operations abstracted. -/
def allocatePrim {α : Type} (valid : SOut Bool) (pointer : SOut Int)
    (power : Int → SOut Int) (check : Int → SOut (Bool × Unit))
    (failure : SOut α) (finish : Int → SOut α) : SOut α :=
  valid.bind (fun good => match SBool.not good with
    | true => failure
    | false => pointer.bind (fun size => (power size).bind (fun bound =>
      (SPick.choose ⟨1, bound, 8⟩ (fun addr (_ : Unit) => check addr) ()).bind
        (fun result => match result with | (addr, _) => finish addr))))

/-- This binding to the original generated operation is definitional. -/
theorem actual_allocatePrim (fuel : Nat) (allocations : List MR_Allocation)
    (kind : MR_AllocationKind) :
    MRf.BasicMemory.allocate (fuel + 4) ⟨allocations, ()⟩ kind 8 8 () () =
      allocatePrim (MRf.x86_64.Target.valid_size (fuel + 3) 8)
        (MRf.x86_64.PTR_SIZE (fuel + 3)) (fun size => SInt.pow 2 (SSize.bits size))
        (allocationGate (fuel + 3) allocations)
        (.ok (.err (.Ub "asking for a too large allocation"), ⟨allocations, ()⟩))
        (fun addr => .ok (allocated8Raw allocations kind addr)) := by
  rfl

/-- Small bind algebra, proved before substituting the generated primitives. -/
theorem allocatePrim_normal {α : Type} (valid : SOut Bool) (pointer : SOut Int)
    (power : Int → SOut Int) (check : Int → SOut (Bool × Unit))
    (failure : SOut α) (finish : Int → SOut α)
    (hv : valid = .ok true) (hp : pointer = .ok 8)
    (hw : power 8 = .ok (Int.ofNat (modulus 64))) :
    allocatePrim valid pointer power check failure finish =
      (SPick.choose ⟨1, Int.ofNat (modulus 64), 8⟩
        (fun addr (_ : Unit) => check addr) ()).bind
        (fun result => match result with | (addr, _) => finish addr) := by
  simp only [allocatePrim, hv, SOut.bind_ok', SBool.not]
  rw [hp]
  simp only [SOut.bind_ok']
  rw [hw]
  rfl

/-- Normalize the real allocator using only separately checked primitive laws. -/
theorem actual_allocate8 (fuel : Nat) (allocations : List MR_Allocation) (kind : MR_AllocationKind) :
    MRf.BasicMemory.allocate (fuel + 4) ⟨allocations, ()⟩ kind 8 8 () () =
      allocate8With allocations kind (allocationGate (fuel + 3) allocations) := by
  rw [actual_allocatePrim]
  apply allocatePrim_normal
  · simpa only [Nat.add_assoc] using valid_size8 (fuel + 1)
  · rfl
  · rfl

/-- Instantiate separately checked choice algebra and endpoint normalization. -/
theorem allocate8With_checked (allocations : List MR_Allocation) (kind : MR_AllocationKind)
    (check : Int → SOut (Bool × Unit))
    (checked : ∀ addr, check addr = .ok (allocationAllowed allocations addr, ())) :
    allocate8With allocations kind check = allocate8Tree allocations kind := by
  exact (choice_checked (Int.ofNat (modulus 64)) check (allocationAllowed allocations)
    (allocated8Raw allocations kind) checked).trans
    (choiceTree_congr (Int.ofNat (modulus 64)) (allocationAllowed allocations)
      (allocated8Raw allocations kind) (allocated8 allocations kind)
      (allocated8Raw_eq allocations kind))

/-- Exact equality retains all demonic/rejected branches and the full endpoint. -/
theorem allocate8_exact (fuel : Nat) (allocations : List MR_Allocation)
    (kind : MR_AllocationKind) :
    MRf.BasicMemory.allocate (fuel + 4) ⟨allocations, ()⟩ kind 8 8 () () =
      allocate8Tree allocations kind := by
  rw [actual_allocate8]
  apply allocate8With_checked
  intro addr
  simpa only [Nat.add_assoc] using allocation_gate_checked (fuel + 1) allocations addr

end MiniRustAllocate8Safety
