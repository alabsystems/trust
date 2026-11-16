/- Exact generated allocation semantics for arbitrary layout sizes/alignments.
   Program startup needs zero-sized function pointers and the root return slot,
   in addition to the eight-byte cells of the existing function theorem.
   All choice/rejection branches and complete allocation records are retained.
   No successful allocation, frame, call or program-start premise is assumed. -/
import MiniRustAllocate8Safety

noncomputable section
namespace MiniRustAllocate
open SemR MiniRustU64Function MiniRustU64Entry
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The original interval rule includes equality of starting addresses even
    for zero-sized live allocations. -/
def overlap (size : Nat) (allocation : MR_Allocation) (addr : Int) : Bool :=
  if SInt.ble (allocation.addr + (allocation.data.length : Int)) addr ||
      SInt.ble (addr + (size : Int)) allocation.addr
  then SInt.beq allocation.addr addr else true

theorem allocation_overlap (fuel size : Nat) (allocation : MR_Allocation) (addr : Int) :
    MRf.Allocation.overlaps (fuel + 2) allocation addr ((size : Int)) =
      SOut.ok (overlap size allocation addr) := by
  simp only [MRf.Allocation.overlaps]
  rw [allocation_size fuel]
  simp only [SOut.bind_ok']
  cases h1 : SInt.ble (allocation.addr + (allocation.data.length : Int)) addr <;>
    cases h2 : SInt.ble (addr + (size : Int)) allocation.addr <;>
      simp [overlap, h1, h2]

def anyOverlap (size : Nat) : List MR_Allocation → Int → Bool
  | [], _ => false
  | allocation :: rest, addr =>
    if allocation.live && overlap size allocation addr then true else anyOverlap size rest addr

def scan (fuel size : Nat) (allocations : List MR_Allocation) (addr : Int) : SOut (Bool × Unit) :=
  SList.anyS allocations
    (fun allocation (_ : Unit) => match allocation.live with
      | true => (MRf.Allocation.overlaps fuel allocation addr ((size : Int))).bind
          (fun result => .ok (result, ()))
      | false => .ok (false, ())) ()

theorem scan_checked (fuel size : Nat) (allocations : List MR_Allocation) (addr : Int) :
    scan (fuel + 2) size allocations addr = .ok (anyOverlap size allocations addr, ()) := by
  induction allocations with
  | nil => rfl
  | cons allocation rest ih =>
    simp only [scan, allocation_overlap, SOut.bind_ok'] at ih
    cases hl : allocation.live <;> cases ho : overlap size allocation addr <;>
      simp [scan, SList.anyS, hl, allocation_overlap, SOut.bind_ok', anyOverlap, ho, ih]

def remainder (align : Nat) (addr : Int) : Int :=
  SInt.ofSignedNat (SInt.isNeg addr) (SInt.abs addr % align)

/-- Every original address gate, including the STRICT end-address bound. -/
def allowed (size align : Nat) (allocations : List MR_Allocation) (addr : Int) : Bool :=
  if SInt.ble addr 0 then false else
  if SBool.not (SInt.beq (remainder align addr) 0) then false else
  if SBool.not (inRange false 64 (addr + (size : Int))) then false else
  if anyOverlap size allocations addr then false else true

def gate (fuel size align : Nat) (allocations : List MR_Allocation) (addr : Int) :
    SOut (Bool × Unit) :=
  match SInt.ble addr 0 with
  | true => .ok (false, ())
  | false => (SAlign.is_aligned ((align : Int)) addr).bind (fun aligned =>
    match SBool.not aligned with
    | true => .ok (false, ())
    | false => (MRf.x86_64.PTR_SIZE fuel).bind (fun pointerSize =>
      (SInt.in_bounds (addr + (size : Int)) .Unsigned pointerSize).bind (fun inBounds =>
        match SBool.not inBounds with
        | true => .ok (false, ())
        | false => (scan fuel size allocations addr).bind
          (fun result => match result with
            | (overlaps, _) => match overlaps with
              | true => .ok (false, ())
              | false => .ok (true, ())))))

theorem gate_checked (fuel size align : Nat) (allocations : List MR_Allocation) (addr : Int) :
    gate (fuel + 2) size (align + 1) allocations addr =
      .ok (allowed size (align + 1) allocations addr, ()) := by
  have hp : MRf.x86_64.PTR_SIZE (fuel + 2) = SOut.ok 8 := rfl
  have hnz : (align : Int) + 1 ≠ 0 := by omega
  have ha : SAlign.is_aligned (((align + 1 : Nat) : Int)) addr =
      SOut.ok (SInt.beq (remainder (align + 1) addr) 0) := by
    simp [SAlign.is_aligned, SInt.rem, SInt.beq, SInt.abs, remainder, hnz, SOut.bind_ok']
  simp only [gate, hp, ha, unsigned_bounds64, scan_checked, SOut.bind_ok']
  cases h1 : SInt.ble addr 0 <;>
    cases h2 : SInt.beq (remainder (align + 1) addr) 0 <;>
    cases h3 : inRange false 64 (addr + (size : Int)) <;>
    cases h4 : anyOverlap size allocations addr <;>
      simp [SBool.not, h1, h2, h3, h4, allowed]

def allocated (size align : Nat) (allocations : List MR_Allocation)
    (kind : MR_AllocationKind) (addr : Int) : SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory :=
  (.ok (ptr allocations.length addr),
    ⟨allocations ++ [⟨SList.repeatNat .Uninit size, addr, (align : Int), kind, true, ()⟩], ()⟩)

def rawAllocated (size align : Nat) (allocations : List MR_Allocation)
    (kind : MR_AllocationKind) (addr : Int) : SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory :=
  (.ok ⟨addr, some (⟨SList.len allocations⟩, ())⟩,
    (MR_BasicMemory.mk allocations ()).set_allocations
      (SList.push allocations ⟨SList.repeatNat .Uninit size, addr, (align : Int), kind, true, ()⟩))

theorem rawAllocated_eq (size align : Nat) (allocations : List MR_Allocation)
    (kind : MR_AllocationKind) (addr : Int) :
    rawAllocated size align allocations kind addr = allocated size align allocations kind addr := by
  simp only [rawAllocated, allocated, ptr, SList.len, SemR.lenNat_eq,
    SList.push, MiniRustAllocate8Safety.append_model, MR_BasicMemory.set_allocations]

def prim {α : Type} (align : Nat) (valid : SOut Bool) (pointer : SOut Int)
    (power : Int → SOut Int) (check : Int → SOut (Bool × Unit))
    (failure : SOut α) (finish : Int → SOut α) : SOut α :=
  valid.bind (fun good => match SBool.not good with
    | true => failure
    | false => pointer.bind (fun pointerSize => (power pointerSize).bind (fun bound =>
      (SPick.choose ⟨1, bound, (align : Int)⟩ (fun addr (_ : Unit) => check addr) ()).bind
        (fun result => match result with | (addr, _) => finish addr))))

theorem actual_prim (fuel size align : Nat) (allocations : List MR_Allocation)
    (kind : MR_AllocationKind) :
    MRf.BasicMemory.allocate (fuel + 4) ⟨allocations, ()⟩ kind
      ((size : Int)) ((align : Int)) () () =
    prim align (MRf.x86_64.Target.valid_size (fuel + 3) ((size : Int)))
      (MRf.x86_64.PTR_SIZE (fuel + 3)) (fun pointerSize => SInt.pow 2 (SSize.bits pointerSize))
      (gate (fuel + 3) size align allocations)
      (.ok (.err (.Ub "asking for a too large allocation"), ⟨allocations, ()⟩))
      (fun addr => .ok (rawAllocated size align allocations kind addr)) := by
  rfl

theorem prim_normal {α : Type} (align : Nat) (valid : SOut Bool)
    (pointer : SOut Int) (power : Int → SOut Int) (check : Int → SOut (Bool × Unit))
    (failure : SOut α) (finish : Int → SOut α) (good : Bool)
    (hv : valid = .ok good) (hp : pointer = .ok 8)
    (hw : power 8 = .ok (Int.ofNat (modulus 64))) :
    prim align valid pointer power check failure finish =
      if good then
        (SPick.choose ⟨1, Int.ofNat (modulus 64), (align : Int)⟩
          (fun addr (_ : Unit) => check addr) ()).bind
            (fun result => match result with | (addr, _) => finish addr)
      else failure := by
  simp only [prim, hv, SOut.bind_ok']
  cases good
  · rfl
  · simp only [SBool.not]
    rw [hp]
    simp only [SOut.bind_ok']
    rw [hw]
    rfl

/-- General normalized result: oversized layouts retain the original UB;
    valid layouts retain the entire demonic distribution and all rejected
    candidates. In particular a zero-sized allocation is still an allocation. -/
def tree (size align : Nat) (allocations : List MR_Allocation) (kind : MR_AllocationKind) :
    SOut (SRes MR_TerminationInfo MR_ThinPointer × MR_BasicMemory) :=
  if inRange true 64 ((size : Int)) then
    (SPick.choose ⟨1, Int.ofNat (modulus 64), (align : Int)⟩
      (fun addr (_ : Unit) => .ok (allowed size align allocations addr, ())) ()).bind
        (fun result => .ok (allocated size align allocations kind result.1))
  else .ok (.err (.Ub "asking for a too large allocation"), ⟨allocations, ()⟩)

theorem valid_size (fuel size : Nat) :
    MRf.x86_64.Target.valid_size (fuel + 2) ((size : Int)) =
      SOut.ok (inRange true 64 ((size : Int))) := by
  simp only [MRf.x86_64.Target.valid_size]
  change ((SOut.ok 8).bind fun width => (SInt.in_bounds ((size : Int)) .Signed width).bind
    fun valid => SOut.ok valid) = _
  rw [SOut.bind_ok', signed_bounds64]
  rfl

theorem actual_normal (fuel size align : Nat) (allocations : List MR_Allocation)
    (kind : MR_AllocationKind) :
    MRf.BasicMemory.allocate (fuel + 4) ⟨allocations, ()⟩ kind
      (size : Int) (align : Int) () () =
      if inRange true 64 (size : Int) then
        (SPick.choose ⟨1, Int.ofNat (modulus 64), (align : Int)⟩
          (fun addr (_ : Unit) => gate (fuel + 3) size align allocations addr) ()).bind
            (fun result => .ok (rawAllocated size align allocations kind result.1))
      else .ok (.err (.Ub "asking for a too large allocation"), ⟨allocations, ()⟩) := by
  rw [actual_prim]
  apply prim_normal
  · exact valid_size (fuel + 1) size
  · rfl
  · rfl

theorem choose_congr {α : Type} (align : Nat)
    (check other : Int → SOut (Bool × Unit)) (finish result : Int → α)
    (checks : ∀ addr, check addr = other addr) (results : ∀ addr, finish addr = result addr) :
    ((SPick.choose ⟨1, Int.ofNat (modulus 64), (align : Int)⟩
      (fun addr (_ : Unit) => check addr) ()).bind (fun pair => .ok (finish pair.1))) =
    ((SPick.choose ⟨1, Int.ofNat (modulus 64), (align : Int)⟩
      (fun addr (_ : Unit) => other addr) ()).bind (fun pair => .ok (result pair.1))) := by
  have checksEq : check = other := funext checks
  have resultEq : finish = result := funext results
  rw [checksEq, resultEq]

/-- Exact original allocator, for EVERY nonnegative layout size and EVERY
    positive alignment, every allocation kind and arbitrary complete world.
    No allowed-address flag or successful-execution premise is consumed. -/
theorem allocate_exact (fuel size align : Nat) (allocations : List MR_Allocation)
    (kind : MR_AllocationKind) :
    MRf.BasicMemory.allocate (fuel + 4) ⟨allocations, ()⟩ kind
      ((size : Int)) (((align + 1 : Nat) : Int)) () () =
      tree size (align + 1) allocations kind := by
  rw [actual_normal]
  unfold tree
  cases valid : inRange true 64 ((size : Int))
  · rfl
  · simp only [reduceIte]
    apply choose_congr
    · intro addr
      simpa only [Nat.add_assoc] using gate_checked (fuel + 1) size align allocations addr
    · exact rawAllocated_eq size (align + 1) allocations kind

end MiniRustAllocate
