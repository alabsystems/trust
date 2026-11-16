/- Frame-entry proof predicates over the existing SOut tree.
   These are not a second Rust evaluator or compiler admission authority. -/
import MiniRustU64Step
noncomputable section
namespace MiniRustU64Entry
open SemR MiniRustU64Function MiniRustU64Execution MiniRustU64Return MiniRustU64Step
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every admitted leaf has the checked result property. Reject/no-behavior
    are preserved as such, NOT counted as a successful execution. Availability
    is a separate constructive obligation. Model fuel/refusal/panic fails. -/
def EveryResult {α : Type} (p : α → Prop) : SOut α → Prop :=
  @SOut.rec α (fun _ => Prop) p (fun _ => False) False (fun _ => False)
    True True (fun _ ih => ∀ j, ih j) (fun _ ih => ∀ j, ih j)

theorem every_bind {α β : Type} (p : α → Prop) (q : β → Prop)
    (out : SOut α) (next : α → SOut β) (h : EveryResult p out)
    (checked : ∀ a, p a → EveryResult q (next a)) : EveryResult q (out.bind next) := by
  induction out with
  | ok a => exact checked a h
  | panic message => exact False.elim h
  | fuel => exact False.elim h
  | refused what => exact False.elim h
  | nobehavior => trivial
  | reject => trivial
  | pick k ih =>
    change ∀ j, EveryResult q ((k j).bind next)
    intro j
    exact ih j (h j)
  | predict k ih =>
    change ∀ j, EveryResult q ((k j).bind next)
    intro j
    exact ih j (h j)

theorem bind_associative {α β γ : Type} (out : SOut α)
    (f : α → SOut β) (g : β → SOut γ) :
    (out.bind f).bind g = out.bind (fun a => (f a).bind g) := by
  induction out with
  | ok a => rfl
  | panic message => rfl
  | fuel => rfl
  | refused what => rfl
  | nobehavior => rfl
  | reject => rfl
  | pick k ih =>
    change SOut.pick (fun j => ((k j).bind f).bind g) =
      SOut.pick (fun j => (k j).bind (fun a => (f a).bind g))
    apply congrArg SOut.pick
    exact funext ih
  | predict k ih =>
    change SOut.predict (fun j => ((k j).bind f).bind g) =
      SOut.predict (fun j => (k j).bind (fun a => (f a).bind g))
    apply congrArg SOut.predict
    exact funext ih

/-- Safety is about the canonical oracle interpreter, not labels/counts. -/
theorem every_oracle {α : Type} (p : α → Prop) (out : SOut α)
    (h : EveryResult p out) (δ π : List Nat → Nat) :
    (∃ a, SOut.runOracle δ π out = .ok a ∧ p a) ∨
      SOut.runOracle δ π out = .reject ∨ SOut.runOracle δ π out = .nobehavior := by
  induction out generalizing δ π with
  | ok a => exact .inl ⟨a, rfl, h⟩
  | panic message => exact False.elim h
  | fuel => exact False.elim h
  | refused what => exact False.elim h
  | nobehavior => exact .inr (.inr rfl)
  | reject => exact .inr (.inl rfl)
  | pick k ih =>
    exact ih (δ []) (h (δ [])) (fun history => δ (δ [] :: history))
      (fun history => π (δ [] :: history))
  | predict k ih =>
    exact ih (π []) (h (π [])) (fun history => δ (π [] :: history))
      (fun history => π (π [] :: history))

/-- Arithmetic interval predicate of the actual generated allocation checker.
    Equality below checks it against the original operation, not an axiom. -/
def overlap (allocation : MR_Allocation) (addr : Int) : Bool :=
  if SInt.ble (allocation.addr + Int.ofNat allocation.data.length) addr ||
      SInt.ble (addr + 8) allocation.addr then SInt.beq allocation.addr addr else true

theorem allocation_size (fuel : Nat) (allocation : MR_Allocation) :
    MRf.Allocation.size (fuel + 1) allocation = SOut.ok (Int.ofNat allocation.data.length) := by
  have hz : decide ((allocation.data.length : Int) < 0) = false := by
    simp only [decide_eq_false_iff_not]
    omega
  simp [MRf.Allocation.size, SSize.from_bytes, hz, SList.len, SemR.lenNat_eq,
    SInt.blt, SOption.unwrap, SOut.bind_ok']

theorem allocation_overlap (fuel : Nat) (allocation : MR_Allocation) (addr : Int) :
    MRf.Allocation.overlaps (fuel + 2) allocation addr 8 = SOut.ok (overlap allocation addr) := by
  simp only [MRf.Allocation.overlaps]
  rw [allocation_size fuel]
  simp only [SOut.bind_ok']
  cases h1 : SInt.ble (allocation.addr + (allocation.data.length : Int)) addr <;>
    cases h2 : SInt.ble (addr + 8) allocation.addr <;> simp [overlap, h1, h2]
/-- Interval fold corresponding to the original live-allocation scan. -/
def anyOverlap : List MR_Allocation → Int → Bool
  | [], _ => false
  | allocation :: rest, addr =>
    if allocation.live && overlap allocation addr then true else anyOverlap rest addr

theorem scan_overlaps (fuel : Nat) (allocations : List MR_Allocation) (addr : Int) :
    SList.anyS allocations
      (fun allocation (_ : Unit) => match allocation.live with
        | true => SOut.bind (MRf.Allocation.overlaps (fuel + 2) allocation addr 8)
          (fun result => SOut.ok (result, ()))
        | false => SOut.ok (false, ())) () =
      SOut.ok (anyOverlap allocations addr, ()) := by
  induction allocations with
  | nil => rfl
  | cons allocation rest ih =>
    simp only [allocation_overlap, SOut.bind_ok'] at ih
    cases hl : allocation.live <;> cases ho : overlap allocation addr <;>
      simp [SList.anyS, hl, allocation_overlap, SOut.bind_ok', anyOverlap, ho, ih]

theorem bind_return {α : Type} (out : SOut α) : out.bind SOut.ok = out := by
  induction out with
  | ok a => rfl
  | panic message => rfl
  | fuel => rfl
  | refused what => rfl
  | nobehavior => rfl
  | reject => rfl
  | pick k ih =>
    change SOut.pick (fun j => (k j).bind SOut.ok) = SOut.pick k
    exact congrArg SOut.pick (funext ih)
  | predict k ih =>
    change SOut.predict (fun j => (k j).bind SOut.ok) = SOut.predict k
    exact congrArg SOut.predict (funext ih)

theorem unsigned_bounds64 (x : Int) :
    SInt.in_bounds x .Unsigned 8 = SOut.ok (inRange false 64 x) := by
  have h := mr_can_represent 0 false .u64 x
  simpa [MRf.IntType.can_represent, mrIntTy, sgnOf, IntTy.bits, IntTy.bytes, bind_return] using h

theorem signed_bounds64 (x : Int) :
    SInt.in_bounds x .Signed 8 = SOut.ok (inRange true 64 x) := by
  have h := mr_can_represent 0 true .u64 x
  simpa [MRf.IntType.can_represent, mrIntTy, sgnOf, IntTy.bits, IntTy.bytes, bind_return] using h

theorem valid_size8 (fuel : Nat) :
    MRf.x86_64.Target.valid_size (fuel + 2) 8 = SOut.ok true := by
  have hp : MRf.x86_64.PTR_SIZE (fuel + 1) = SOut.ok 8 := rfl
  simp only [MRf.x86_64.Target.valid_size]
  rw [hp]
  simp only [SOut.bind_ok']
  rw [signed_bounds64]
  rfl

end MiniRustU64Entry
