/- Actual generated MiniRust function boundary for the canonical U64-add leaf.
   This namespace does not establish Rust/TCX translation or physical ABI. -/
import U64Addition
import SemRMemory

noncomputable section
namespace MiniRustU64Function
open SemR
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The actual MiniRust Rust-convention function, not a second evaluator. -/
def function (literal : Nat) : MR_Function :=
  { locals := [(⟨0⟩, .Int (mrIntTy false .u64)), (⟨1⟩, .Int (mrIntTy false .u64))]
    args := [⟨1⟩], ret := ⟨0⟩, calling_convention := .Rust
    blocks := [(⟨0⟩,
      { statements := [.Assign (.Local ⟨0⟩)
          (.BinOp (.Int .Add) (.Load (.Local ⟨1⟩))
            (.Constant (.Int (Int.ofNat literal)) (.Int (mrIntTy false .u64))))]
        terminator := .Return, kind := .Regular })]
    start := ⟨0⟩ }

private theorem getNat_at_prefix {α : Type} (xs : List α) (x : α) (ys : List α) :
    SList.getNat (xs ++ x :: ys) xs.length = some x := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact ih

private theorem setNat_at_prefix {α : Type} (xs : List α) (x y : α) (ys : List α) :
    SList.setNat (xs ++ x :: ys) xs.length y = some (xs ++ y :: ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa only [List.cons_append, List.length_cons, SList.setNat, ih]

private theorem index_at_prefix {α : Type} (xs : List α) (x : α) (ys : List α) :
    SList.index_at (xs ++ x :: ys) (Int.ofNat xs.length) = SOut.ok x := by
  simp only [SList.index_at, SList.get, getNat_at_prefix, SOut.bind, SOption.unwrap]

private theorem set_at_prefix {α : Type} (xs : List α) (x y : α) (ys : List α) :
    SList.set (xs ++ x :: ys) (Int.ofNat xs.length) y = SOut.ok (xs ++ y :: ys) := by
  simp only [SList.set, setNat_at_prefix]

/-- This slot is private; all records before and after it are arbitrary. -/
def slot (addr : Int) (bytes : List MR_AbstractByte) : MR_Allocation :=
  ⟨bytes, addr, 8, .Stack, true, ()⟩
def ptr (idx : Nat) (addr : Int) : MR_ThinPointer :=
  ⟨addr, some (⟨Int.ofNat idx⟩, ())⟩

/-- The real generated bounds/provenance check on the private full-width slot. -/
theorem check_private_slot (fuel : Nat) (before after : List MR_Allocation)
    (addr : Int) (bytes : List MR_AbstractByte) (length : bytes.length = 8) :
    MRf.BasicMemory.check_ptr (fuel + 2)
      ⟨before ++ slot addr bytes :: after, ()⟩ (ptr before.length addr) 8 =
      SOut.ok (.ok (some (⟨Int.ofNat before.length⟩, (), 0))) := by
  simp [MRf.BasicMemory.check_ptr, ptr, slot, index_at_prefix,
    SOut.bind, SSize.is_zero, SBool.not, SInt.blt, SInt.beq, MRf.Allocation.size,
    SList.index_at, SList.get, getNat_at_prefix,
    SSize.from_bytes, SList.len, SemR.lenNat_eq, length, SOption.unwrap]

private theorem dropNat_length {α : Type} (xs : List α) :
    SList.dropNat xs.length xs = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

private theorem takeNat_length {α : Type} (xs : List α) :
    SList.takeNat xs.length xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

private theorem appendL_eq {α : Type} (xs ys : List α) :
    SList.appendL xs ys = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

/-- A full-width private write preserves every surrounding allocation record. -/
theorem store_private_slot (fuel : Nat) (before after : List MR_Allocation)
    (addr : Nat) (bytes replacement : List MR_AbstractByte)
    (length : bytes.length = 8) (replacementLength : replacement.length = 8)
    (aligned : addr % 8 = 0) :
    MRf.BasicMemory.Memory.store (fuel + 5)
      ⟨before ++ slot (Int.ofNat addr) bytes :: after, ()⟩
      (ptr before.length (Int.ofNat addr)) replacement 8 =
      SOut.ok (.ok (), ⟨before ++ slot (Int.ofNat addr) replacement :: after, ()⟩) := by
  have ha : SAlign.is_aligned 8 (Int.ofNat addr) = SOut.ok true := by
    simpa [aligned] using SemR.aligned_minirust addr 8 (by decide)
  have hd : SList.dropNat 8 bytes = [] := by
    rw [← length]; exact dropNat_length bytes
  simp only [MRf.BasicMemory.Memory.store, MRf.BasicMemory.store, ptr]
  rw [ha]
  simp [SOut.bind, SBool.not, SList.len, SemR.lenNat_eq,
    SSize.from_bytes, SInt.blt, SOption.unwrap, replacementLength,
    check_private_slot, length, SList.index_at, SList.get, getNat_at_prefix,
    slot, SList.write_subslice_at_index, SList.takeNat, SList.dropNat,
    appendL_eq, hd,
    SList.set, setNat_at_prefix, MRf.BasicMemory.check_ptr, SSize.is_zero,
    SInt.beq, MRf.Allocation.size, MR_Allocation.set_extra,
    MR_Allocation.set_data, MR_BasicMemory.set_allocations]

/-- A full-width private read returns the exact bytes and preserves all memory. -/
theorem load_private_slot (fuel : Nat) (before after : List MR_Allocation)
    (addr : Nat) (bytes : List MR_AbstractByte) (length : bytes.length = 8)
    (aligned : addr % 8 = 0) :
    MRf.BasicMemory.Memory.load (fuel + 5)
      ⟨before ++ slot (Int.ofNat addr) bytes :: after, ()⟩
      (ptr before.length (Int.ofNat addr)) 8 8 =
      SOut.ok (.ok bytes, ⟨before ++ slot (Int.ofNat addr) bytes :: after, ()⟩) := by
  have ha : SAlign.is_aligned 8 (Int.ofNat addr) = SOut.ok true := by
    simpa [aligned] using SemR.aligned_minirust addr 8 (by decide)
  have ht : SList.takeNat 8 bytes = bytes := by
    rw [← length]; exact takeNat_length bytes
  simp only [MRf.BasicMemory.Memory.load, MRf.BasicMemory.load, ptr]
  rw [ha]
  simp [SOut.bind, SBool.not, check_private_slot, length,
    SList.index_at, SList.get, getNat_at_prefix, slot,
    SList.set, setNat_at_prefix, SList.subslice_with_length,
    SemR.lenNat_eq, SList.dropNat, ht, MRf.BasicMemory.check_ptr,
    SSize.is_zero, SInt.beq, MRf.Allocation.size, SList.len, SSize.from_bytes,
    SInt.blt, SOption.unwrap, MR_Allocation.set_extra,
    MR_BasicMemory.set_allocations]

/-- Exact initialized byte image used by the generated typed encoder. -/
def imageInts : List Int → List MR_AbstractByte
  | [] => []
  | x :: xs => .Init x none :: imageInts xs

def u64bytes (n : Nat) : List MR_AbstractByte := imageInts (byteInts (leBytes 8 n))

private theorem imageInts_length (xs : List Int) : (imageInts xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [imageInts, List.length_cons, ih]

private theorem byteInts_length (xs : List AByte) : (byteInts xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [byteInts, List.length_cons, ih]

theorem u64bytes_length (n : Nat) : (u64bytes n).length = 8 := by
  rw [u64bytes, imageInts_length, byteInts_length, leBytes_length]

private theorem map_imageInts (xs : List Int) :
    SList.mapS xs (fun x (_ : Unit) => SOut.ok (.Init x none, ())) () =
      SOut.ok (imageInts xs, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [SList.mapS, SOut.bind_ok', ih, imageInts]

private theorem decode_imageInts (fuel : Nat) (xs : List Int) :
    SList.tryMapOptS (imageInts xs)
      (fun x (_ : Unit) => SOut.bind (MRf.AbstractByte.data (fuel + 1) x)
        (fun d => SOut.ok (d, ()))) () = SOut.ok (some xs, ()) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [imageInts, SList.tryMapOptS]
    rw [show MRf.AbstractByte.data (fuel + 1) (.Init x none) = SOut.ok (some x) from rfl]
    simp only [SOut.bind_ok', ih]

theorem layout_u64 (fuel : Nat) :
    MRf.Type.layout (fuel + 3) (.Int (mrIntTy false .u64)) =
      SOut.ok (.Sized 8 8) := by
  rfl

theorem encode_u64 (fuel n : Nat) (valid : n < modulus 64) :
    MRf.Type.encode (fuel + 3) (.Int (mrIntTy false .u64)) (.Int (Int.ofNat n)) =
      SOut.ok (u64bytes n) := by
  have he : SEndian.encode .LittleEndian .Unsigned (Int.ofNat 8) (Int.ofNat n) =
      SOut.ok (some (byteInts (leBytes 8 n))) := by
    simpa [readAt_false, sgnOf, IntTy.bytes] using encode_minirust false .u64 n valid
  change MRf.Type.encode_open (MR_rec_102.tie (fuel + 2)) (fuel + 3)
    (.Int (mrIntTy false .u64)) (.Int (Int.ofNat n)) = _
  simp only [MRf.Type.encode_open,
    mrIntTy, IntTy.bytes, sgnOf, Bool.false_eq_true, reduceIte, MRf.x86_64.ENDIANNESS, SOut.bind_ok']
  rw [he]
  simp only [SOut.bind_ok', SOption.unwrap, map_imageInts]
  rfl

theorem decode_u64 (fuel n : Nat) (valid : n < modulus 64) :
    MRf.Type.decode (fuel + 3) (.Int (mrIntTy false .u64)) (u64bytes n) =
      SOut.ok (some (.Int (Int.ofNat n))) := by
  have hd : SEndian.decode .LittleEndian .Unsigned (byteInts (leBytes 8 n)) =
      SOut.ok (Int.ofNat n) := by
    simpa [readAt_false, sgnOf, IntTy.bytes] using decode_minirust false .u64 n valid
  change MRf.Type.decode_open (MR_rec_120.tie (fuel + 2)) (fuel + 3)
    (.Int (mrIntTy false .u64)) (u64bytes n) = _
  simp only [MRf.Type.decode_open,
    mrIntTy, IntTy.bytes, sgnOf, Bool.false_eq_true, reduceIte, SList.len, SemR.lenNat_eq, u64bytes_length,
    SInt.beq, SBool.not, decide_true, SOut.bind_ok']
  rw [show u64bytes n = imageInts (byteInts (leBytes 8 n)) from rfl, decode_imageInts]
  simp only [SOut.bind_ok', MRf.x86_64.ENDIANNESS]
  rw [hd]
  rfl

theorem check_u64 (fuel : Nat) (machine : MR_Machine) (n : Nat)
    (valid : n < modulus 64) :
    MRf.Machine.check_value (fuel + 3) machine (.Int (Int.ofNat n))
      (.Int (mrIntTy false .u64)) = SOut.ok (.ok ()) := by
  have hc := mr_can_represent (fuel + 1) false .u64 (Int.ofNat n)
  change MRf.Machine.check_value_open (MR_rec_94.tie (fuel + 2)) (fuel + 3)
    machine (.Int (Int.ofNat n)) (.Int (mrIntTy false .u64)) = _
  simp only [MRf.Machine.check_value_open]
  rw [hc]
  have hr : inRange false 64 (Int.ofNat n) = true := by
    simpa only [readAt_false] using readAt_range false 64 (by decide) n valid
  simp only [IntTy.bits]
  rw [hr]
  rfl

def memory (before after : List MR_Allocation) (addr : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access) : MR_ConcurrentMemory :=
  ⟨⟨before ++ slot (Int.ofNat addr) bytes :: after, ()⟩, accesses⟩

private theorem mem_set (machine : MR_Machine) (mem : MR_ConcurrentMemory) :
    (machine.set_mem mem).mem = mem := by cases machine; rfl
private theorem set_mem_set (machine : MR_Machine) (a b : MR_ConcurrentMemory) :
    (machine.set_mem a).set_mem b = machine.set_mem b := by cases machine; rfl

theorem concurrent_store_private_slot (fuel : Nat) (before after : List MR_Allocation)
    (addr : Nat) (bytes replacement : List MR_AbstractByte) (accesses : List MR_Access)
    (length : bytes.length = 8) (replacementLength : replacement.length = 8)
    (aligned : addr % 8 = 0) :
    MRf.ConcurrentMemory.store (fuel + 6) (memory before after addr bytes accesses)
      (ptr before.length (Int.ofNat addr)) replacement 8 .None =
    SOut.ok (.ok (), memory before after addr replacement
      (accesses ++ [⟨.Store, .None, Int.ofNat addr, 8⟩])) := by
  have hs := store_private_slot fuel before after addr bytes replacement length replacementLength aligned
  simp only [ptr] at hs
  have hz : decide ((Int.ofNat 8) < 0) = false := rfl
  simp only [MRf.ConcurrentMemory.store, memory, SList.len, SemR.lenNat_eq,
    replacementLength, SSize.from_bytes, SInt.blt, hz, SOption.unwrap,
    SOut.bind_ok', ptr, MR_ConcurrentMemory.set_accesses]
  rw [hs]
  simp only [SOut.bind_ok', MR_ConcurrentMemory.set_memory, SList.push, appendL_eq]
  rfl

theorem concurrent_load_private_slot (fuel : Nat) (before after : List MR_Allocation)
    (addr : Nat) (bytes : List MR_AbstractByte) (accesses : List MR_Access)
    (length : bytes.length = 8) (aligned : addr % 8 = 0) :
    MRf.ConcurrentMemory.load (fuel + 6) (memory before after addr bytes accesses)
      (ptr before.length (Int.ofNat addr)) 8 8 .None =
    SOut.ok (.ok bytes, memory before after addr bytes
      (accesses ++ [⟨.Load, .None, Int.ofNat addr, 8⟩])) := by
  have hs := load_private_slot fuel before after addr bytes length aligned
  simp only [ptr] at hs
  simp only [MRf.ConcurrentMemory.load, memory, MR_ConcurrentMemory.set_accesses, ptr]
  rw [hs]
  simp only [SOut.bind_ok', MR_ConcurrentMemory.set_memory, SList.push, appendL_eq]

/-- A real generated typed store, including exact encoding and access logging. -/
theorem typed_store_u64 (fuel : Nat) (machine : MR_Machine)
    (before after : List MR_Allocation) (addr n : Nat)
    (bytes : List MR_AbstractByte) (accesses : List MR_Access)
    (length : bytes.length = 8) (aligned : addr % 8 = 0) (valid : n < modulus 64) :
    MRf.Machine.typed_store (fuel + 10)
      (machine.set_mem (memory before after addr bytes accesses))
      (ptr before.length (Int.ofNat addr)) (.Int (Int.ofNat n))
      (.Int (mrIntTy false .u64)) 8 .None =
    SOut.ok (.ok (), machine.set_mem (memory before after addr (u64bytes n)
      (accesses ++ [⟨.Store, .None, Int.ofNat addr, 8⟩]))) := by
  simp only [MRf.Machine.typed_store]
  rw [check_u64 (fuel + 6) _ n valid]
  simp only [SOut.bind_ok', SRes.is_ok]
  rw [encode_u64 (fuel + 6) n valid]
  simp only [SOut.bind_ok', mem_set]
  rw [concurrent_store_private_slot (fuel + 3) before after addr bytes (u64bytes n)
    accesses length (u64bytes_length n) aligned]
  simp only [SOut.bind_ok', set_mem_set]

/-- A real generated typed load, including the full64 validity check. -/
theorem typed_load_u64 (fuel : Nat) (machine : MR_Machine)
    (before after : List MR_Allocation) (addr n : Nat) (accesses : List MR_Access)
    (aligned : addr % 8 = 0) (valid : n < modulus 64) :
    MRf.Machine.typed_load (fuel + 10)
      (machine.set_mem (memory before after addr (u64bytes n) accesses))
      (ptr before.length (Int.ofNat addr)) (.Int (mrIntTy false .u64)) 8 .None =
    SOut.ok (.ok (.Int (Int.ofNat n)), machine.set_mem
      (memory before after addr (u64bytes n)
        (accesses ++ [⟨.Load, .None, Int.ofNat addr, 8⟩]))) := by
  simp only [MRf.Machine.typed_load]
  rw [layout_u64 (fuel + 6)]
  simp only [SOut.bind_ok', MRf.LayoutStrategy.expect_size, mem_set]
  rw [concurrent_load_private_slot (fuel + 3) before after addr (u64bytes n)
    accesses (u64bytes_length n) aligned]
  simp only [SOut.bind_ok', set_mem_set]
  rw [decode_u64 (fuel + 6) n valid]
  simp only [SOut.bind_ok']
  rw [check_u64 (fuel + 6) _ n valid]
  rfl

/-- The actual generated deallocator retires precisely this stack slot. -/
theorem deallocate_private_slot (fuel : Nat) (before after : List MR_Allocation)
    (addr : Int) (bytes : List MR_AbstractByte) (length : bytes.length = 8) :
    MRf.BasicMemory.Memory.deallocate (fuel + 4)
      ⟨before ++ slot addr bytes :: after, ()⟩ (ptr before.length addr) .Stack 8 8 =
    SOut.ok (.ok (), ⟨before ++ (slot addr bytes).set_live false :: after, ()⟩) := by
  simp [MRf.BasicMemory.Memory.deallocate, MRf.BasicMemory.deallocate, ptr,
    SList.index_at, SList.get, getNat_at_prefix, SOut.bind_ok',
    slot, SBool.not, SInt.beq, MR_AllocationKind.beq, MRf.Allocation.size,
    SSize.from_bytes, SInt.blt, SList.len, SemR.lenNat_eq, length, SOption.unwrap,
    MR_Allocation.set_extra, MR_Allocation.set_live,
    SList.set, setNat_at_prefix, MR_BasicMemory.set_allocations]

theorem concurrent_deallocate_private_slot (fuel : Nat) (before after : List MR_Allocation)
    (addr : Nat) (bytes : List MR_AbstractByte) (accesses : List MR_Access)
    (length : bytes.length = 8) :
    MRf.ConcurrentMemory.deallocate (fuel + 5) (memory before after addr bytes accesses)
      (ptr before.length (Int.ofNat addr)) .Stack 8 8 =
    SOut.ok (.ok (),
      ⟨⟨before ++ (slot (Int.ofNat addr) bytes).set_live false :: after, ()⟩, accesses⟩) := by
  simp only [MRf.ConcurrentMemory.deallocate, memory]
  rw [deallocate_private_slot fuel before after (Int.ofNat addr) bytes length]
  rfl

/-- Changing a checked request from alignment8 to alignment1 changes no access
    once both actual generated alignment guards have been proved true. -/
theorem typed_store_alignment_one (fuel : Nat) (machine : MR_Machine)
    (idx addr : Nat) (value : MR_Value) (ty : MR_Type) (aligned : addr % 8 = 0) :
    MRf.Machine.typed_store (fuel + 10) machine (ptr idx (Int.ofNat addr)) value ty 1 .None =
    MRf.Machine.typed_store (fuel + 10) machine (ptr idx (Int.ofNat addr)) value ty 8 .None := by
  have h1 : SAlign.is_aligned 1 (Int.ofNat addr) = SOut.ok true := by
    simpa [Nat.mod_one] using SemR.aligned_minirust addr 1 (by decide)
  have h8 : SAlign.is_aligned 8 (Int.ofNat addr) = SOut.ok true := by
    simpa [aligned] using SemR.aligned_minirust addr 8 (by decide)
  simp only [MRf.Machine.typed_store, MRf.ConcurrentMemory.store,
    MRf.BasicMemory.Memory.store, MRf.BasicMemory.store, ptr, h1, h8]

theorem typed_load_alignment_one (fuel : Nat) (machine : MR_Machine)
    (idx addr : Nat) (ty : MR_Type) (aligned : addr % 8 = 0) :
    MRf.Machine.typed_load (fuel + 10) machine (ptr idx (Int.ofNat addr)) ty 1 .None =
    MRf.Machine.typed_load (fuel + 10) machine (ptr idx (Int.ofNat addr)) ty 8 .None := by
  have h1 : SAlign.is_aligned 1 (Int.ofNat addr) = SOut.ok true := by
    simpa [Nat.mod_one] using SemR.aligned_minirust addr 1 (by decide)
  have h8 : SAlign.is_aligned 8 (Int.ofNat addr) = SOut.ok true := by
    simpa [aligned] using SemR.aligned_minirust addr 8 (by decide)
  simp only [MRf.Machine.typed_load, MRf.ConcurrentMemory.load,
    MRf.BasicMemory.Memory.load, MRf.BasicMemory.load, ptr, h1, h8]

/-- Explicit single-thread function boundary; no surrounding field is erased
    from the state or made into a semantic success premise. -/
def active (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) : MR_Machine :=
  { base with mem := mem, threads := [⟨[caller, callee], .Enabled, []⟩], active_thread := 0 }

def frame (literal : Nat) (ret arg : MR_ThinPointer) (action : MR_StackPopAction)
    (nextStatement : Int) : MR_StackFrame :=
  ⟨function literal, [(⟨0⟩, ret), (⟨1⟩, arg)], action, ⟨0⟩, nextStatement, ()⟩

theorem active_cur_frame (fuel : Nat) (base : MR_Machine) (caller callee : MR_StackFrame)
    (mem : MR_ConcurrentMemory) :
    MRf.Machine.cur_frame (fuel + 3) (active base caller callee mem) = SOut.ok callee := by
  simp [MRf.Machine.cur_frame, MRf.Machine.active_thread, MRf.Thread.cur_frame,
    active, SList.index_at, SList.get, SList.getNat, SOut.bind_ok', SOption.unwrap,
    SList.last]

private theorem active_set_mem (base : MR_Machine) (caller callee : MR_StackFrame)
    (a b : MR_ConcurrentMemory) :
    (active base caller callee a).set_mem b = active base caller callee b := rfl

def place (p : MR_ThinPointer) : MR_Place := ⟨⟨p, none⟩, true⟩

theorem eval_local_return (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (ret arg : MR_ThinPointer) (action : MR_StackPopAction)
    (nextStatement : Int) (mem : MR_ConcurrentMemory) :
    MRf.Machine.eval_place (fuel + 10)
      (active base caller (frame literal ret arg action nextStatement) mem) (.Local ⟨0⟩) =
    SOut.ok (.ok (place ret, .Int (mrIntTy false .u64)),
      active base caller (frame literal ret arg action nextStatement) mem) := by
  change MRf.Machine.eval_place_open (MR_rec_130.tie (fuel + 9)) (fuel + 10)
    (active base caller (frame literal ret arg action nextStatement) mem) (.Local ⟨0⟩) =
    SOut.ok (.ok (place ret, .Int (mrIntTy false .u64)),
      active base caller (frame literal ret arg action nextStatement) mem)
  simp only [MRf.Machine.eval_place_open]
  rw [active_cur_frame (fuel + 6)]
  simp only [SOut.bind_ok']
  simp [frame, function, SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq,
    SOption.unwrap, SOut.bind_ok', active_cur_frame, MRf.ThinPointer.widen, place]

theorem eval_local_argument (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (ret arg : MR_ThinPointer) (action : MR_StackPopAction)
    (nextStatement : Int) (mem : MR_ConcurrentMemory) :
    MRf.Machine.eval_place (fuel + 10)
      (active base caller (frame literal ret arg action nextStatement) mem) (.Local ⟨1⟩) =
    SOut.ok (.ok (place arg, .Int (mrIntTy false .u64)),
      active base caller (frame literal ret arg action nextStatement) mem) := by
  change MRf.Machine.eval_place_open (MR_rec_130.tie (fuel + 9)) (fuel + 10)
    (active base caller (frame literal ret arg action nextStatement) mem) (.Local ⟨1⟩) =
    SOut.ok (.ok (place arg, .Int (mrIntTy false .u64)),
      active base caller (frame literal ret arg action nextStatement) mem)
  simp only [MRf.Machine.eval_place_open]
  rw [active_cur_frame (fuel + 6)]
  simp only [SOut.bind_ok']
  simp [frame, function, SMap.index_at, SMap.get, SMap.getL, MR_LocalName.beq, SInt.beq,
    SOption.unwrap, SOut.bind_ok', active_cur_frame, MRf.ThinPointer.widen, place]

/-- Definitional equations of the existing mutually recursive dispatcher.
    No new value evaluator is introduced. -/
theorem eval_load_eq (fuel : Nat) (machine : MR_Machine) (p : MR_PlaceExpr) :
    MRf.Machine.eval_value (fuel + 2) machine (.Load p) =
    SOut.bind (MRf.Machine.eval_place (fuel + 1) machine p) (fun (r, m) =>
      match r with
      | .err e => SOut.ok (.err e, m)
      | .ok (place, ty) => SOut.bind (MRf.Machine.place_load (fuel + 1) m place ty)
        (fun (value, m2) => match value with
          | .err e => SOut.ok (.err e, m2)
          | .ok value => SOut.ok (.ok (value, ty), m2))) := by
  unfold MRf.Machine.eval_value
  rw [MR_rec_130.tie]
  simp only [MRf.Machine.eval_value_open]
  congr 1
  funext p
  rcases p with ⟨r, m⟩
  cases r with
  | err e => rfl
  | ok value =>
    rcases value with ⟨p, ty⟩
    dsimp only
    congr 1
    funext q
    rcases q with ⟨r, m2⟩
    cases r <;> rfl

theorem eval_const_eq (fuel : Nat) (machine : MR_Machine) (n : Int) (ty : MR_Type) :
    MRf.Machine.eval_value (fuel + 2) machine (.Constant (.Int n) ty) =
      SOut.ok (.ok (.Int n, ty), machine) := rfl

theorem eval_binop_eq (fuel : Nat) (machine : MR_Machine) (op : MR_BinOp)
    (left right : MR_ValueExpr) :
    MRf.Machine.eval_value (fuel + 2) machine (.BinOp op left right) =
    SOut.bind (MRf.Machine.eval_value (fuel + 1) machine left) (fun (r, m) =>
      match r with
      | .err e => SOut.ok (.err e, m)
      | .ok left => SOut.bind (MRf.Machine.eval_value (fuel + 1) m right)
        (fun (r2, m2) => match r2 with
          | .err e => SOut.ok (.err e, m2)
          | .ok right => SOut.bind (MRf.Machine.eval_bin_op (fuel + 1) m2 op left right)
            (fun value => match value with
              | .err e => SOut.ok (.err e, m2)
              | .ok value => SOut.ok (.ok value, m2)))) := by
  unfold MRf.Machine.eval_value
  rw [MR_rec_130.tie]
  simp only [MRf.Machine.eval_value_open]
  congr 1
  funext p
  rcases p with ⟨r, m⟩
  cases r with
  | err e => rfl
  | ok value =>
    dsimp only
    congr 1
    funext q
    rcases q with ⟨r2, m2⟩
    cases r2 with
    | err e => rfl
    | ok value2 =>
      dsimp only
      congr 1
      funext r3
      cases r3 <;> rfl

theorem load_argument (fuel : Nat) (base : MR_Machine) (caller : MR_StackFrame)
    (literal : Nat) (ret : MR_ThinPointer) (action : MR_StackPopAction) (nextStatement : Int)
    (before after : List MR_Allocation) (addr n : Nat) (accesses : List MR_Access)
    (aligned : addr % 8 = 0) (valid : n < modulus 64) :
    MRf.Machine.eval_value (fuel + 15)
      (active base caller (frame literal ret (ptr before.length (Int.ofNat addr)) action nextStatement)
        (memory before after addr (u64bytes n) accesses)) (.Load (.Local ⟨1⟩)) =
    SOut.ok (.ok (.Int (Int.ofNat n), .Int (mrIntTy false .u64)),
      active base caller (frame literal ret (ptr before.length (Int.ofNat addr)) action nextStatement)
        (memory before after addr (u64bytes n)
          (accesses ++ [⟨.Load, .None, Int.ofNat addr, 8⟩]))) := by
  rw [eval_load_eq (fuel + 13), eval_local_argument (fuel + 4)]
  simp only [SOut.bind_ok']
  simp only [MRf.Machine.place_load, place, SBool.not]
  rw [typed_load_alignment_one (fuel + 3) _ before.length addr _ aligned]
  have hl := typed_load_u64 (fuel + 3)
    (active base caller (frame literal ret (ptr before.length (Int.ofNat addr)) action nextStatement)
      (memory before after addr (u64bytes n) accesses))
    before after addr n accesses aligned valid
  simp only [active_set_mem] at hl
  rw [hl]
  rfl

end MiniRustU64Function
