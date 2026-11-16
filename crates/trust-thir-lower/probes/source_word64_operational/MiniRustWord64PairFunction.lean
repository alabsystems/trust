/- Two-runtime-argument function data and actual generated MiniRust loads.
   These model lemmas grant no Rust-source, physical-ABI or admission authority. -/
import MiniRustU64Function

noncomputable section
namespace MiniRustWord64PairFunction
open SemR MiniRustU64Function
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def function : MR_Function :=
  { locals := [(⟨0⟩, .Int (mrIntTy false .u64)),
      (⟨1⟩, .Int (mrIntTy false .u64)), (⟨2⟩, .Int (mrIntTy false .u64))]
    args := [⟨1⟩, ⟨2⟩], ret := ⟨0⟩, calling_convention := .Rust
    blocks := [(⟨0⟩,
      { statements := [.Assign (.Local ⟨0⟩)
          (.BinOp (.Int .Add) (.Load (.Local ⟨1⟩)) (.Load (.Local ⟨2⟩)))]
        terminator := .Return, kind := .Regular })]
    start := ⟨0⟩ }

def frame (ret left right : MR_ThinPointer) (action : MR_StackPopAction)
    (nextStatement : Int) : MR_StackFrame :=
  ⟨function, [(⟨0⟩, ret), (⟨1⟩, left), (⟨2⟩, right)], action, ⟨0⟩, nextStatement, ()⟩

private theorem active_set_memory (base : MR_Machine) (caller callee : MR_StackFrame)
    (before after : MR_ConcurrentMemory) :
    (active base caller callee before).set_mem after = active base caller callee after := rfl

inductive Local where
  | returned | left | right

def Local.name : Local → MR_LocalName
  | .returned => ⟨0⟩
  | .left => ⟨1⟩
  | .right => ⟨2⟩

def Local.pointer (ret left right : MR_ThinPointer) : Local → MR_ThinPointer
  | .returned => ret
  | .left => left
  | .right => right

/-- Each distinct local is resolved by the generated machine's real dispatcher. -/
theorem eval_local (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (ret left right : MR_ThinPointer) (action : MR_StackPopAction)
    (nextStatement : Int) (mem : MR_ConcurrentMemory) (which : Local) :
    MRf.Machine.eval_place (fuel + 10)
      (active base caller (frame ret left right action nextStatement) mem) (.Local which.name) =
    SOut.ok (.ok (place (which.pointer ret left right), .Int (mrIntTy false .u64)),
      active base caller (frame ret left right action nextStatement) mem) := by
  change MRf.Machine.eval_place_open (MR_rec_130.tie (fuel + 9)) (fuel + 10)
    (active base caller (frame ret left right action nextStatement) mem) (.Local which.name) = _
  cases which <;> simp only [Local.name, MRf.Machine.eval_place_open]
  all_goals rw [active_cur_frame (fuel + 6)]
  all_goals simp only [SOut.bind_ok']
  all_goals simp [frame, function, Local.pointer, SMap.index_at, SMap.get, SMap.getL,
    MR_LocalName.beq, SOption.unwrap, SOut.bind_ok', MRf.ThinPointer.widen, place]

inductive Argument where
  | left | right

def Argument.local : Argument → Local
  | .left => .left
  | .right => .right

def argumentFrame (which : Argument) (ret selected other : MR_ThinPointer)
    (action : MR_StackPopAction) (nextStatement : Int) : MR_StackFrame :=
  match which with
  | .left => frame ret selected other action nextStatement
  | .right => frame ret other selected action nextStatement

/-- Read either actual argument slot while retaining the complete surrounding
    allocation records and the generated Load access, rather than erasing it. -/
theorem load_argument (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (which : Argument) (ret other : MR_ThinPointer)
    (action : MR_StackPopAction) (nextStatement : Int)
    (before after : List MR_Allocation) (addr n : Nat) (accesses : List MR_Access)
    (aligned : addr % 8 = 0) (valid : n < modulus 64) :
    MRf.Machine.eval_value (fuel + 15)
      (active base caller
        (argumentFrame which ret (ptr before.length (Int.ofNat addr)) other action nextStatement)
        (memory before after addr (u64bytes n) accesses)) (.Load (.Local which.local.name)) =
    SOut.ok (.ok (.Int (Int.ofNat n), .Int (mrIntTy false .u64)),
      active base caller
        (argumentFrame which ret (ptr before.length (Int.ofNat addr)) other action nextStatement)
        (memory before after addr (u64bytes n)
          (accesses ++ [⟨.Load, .None, Int.ofNat addr, 8⟩]))) := by
  have hl := typed_load_u64 (fuel + 3)
    (active base caller
      (argumentFrame which ret (ptr before.length (Int.ofNat addr)) other action nextStatement)
      (memory before after addr (u64bytes n) accesses))
    before after addr n accesses aligned valid
  simp only [active_set_memory] at hl
  rw [eval_load_eq (fuel + 13)]
  cases which <;> simp only [argumentFrame, Argument.local]
  all_goals rw [eval_local (fuel + 4)]
  all_goals simp only [Local.pointer, SOut.bind_ok', MRf.Machine.place_load, place, SBool.not]
  all_goals rw [typed_load_alignment_one (fuel + 3) _ before.length addr _ aligned]
  all_goals simp only [argumentFrame] at hl
  all_goals rw [hl]
  all_goals rfl

end MiniRustWord64PairFunction
