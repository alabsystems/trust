/- Connection to the unchanged generated MiniRust operator model.
   No source observation authentication, ABI or compiler admission. -/
import PairCallerOperational
import SemRMiniRust
noncomputable section
namespace SourceWord64MiniRust
open SemR

theorem reference_add (fuel : Nat) (machine : MR_Machine) (left right : Nat)
    (leftValid : left < modulus 64) (rightValid : right < modulus 64) :
    MRf.Machine.eval_bin_op (fuel + 4) machine (.Int .Add)
      (.Int (Int.ofNat left), .Int (mrIntTy false .u64))
      (.Int (Int.ofNat right), .Int (mrIntTy false .u64)) =
      SOut.ok (SRes.ok (.Int (Int.ofNat ((left + right) % modulus 64)),
        .Int (mrIntTy false .u64))) := by
  simpa [readAt, IntTy.bits] using
    add_minirust fuel machine false .u64 left right leftValid rightValid

/-- The exact ordinary-call claim and linked IR have the result computed by
    the generated reference operator. This does not prove that the untrusted
    source claim is an authentic Rust observation or that a native call uses
    the same physical representation. -/
theorem linked_reference_agreement (fuel depth : Nat) (machine : MR_Machine)
    (left right : Nat) (leftValid : left < modulus 64)
    (rightValid : right < modulus 64) :
    SourceWord64Call.evaluateThrough SourceWord64RecordOriginal.original
      SourceWord64Call.caller [left, right] = some ((left + right) % modulus 64) ∧
    runFunction PairCallerOperational.linked 0
      [.int .u64 left, .int .u64 right] 4 (depth + 1) =
      .ret [.int .u64 ((left + right) % modulus 64)] ∧
    MRf.Machine.eval_bin_op (fuel + 4) machine (.Int .Add)
      (.Int (Int.ofNat left), .Int (mrIntTy false .u64))
      (.Int (Int.ofNat right), .Int (mrIntTy false .u64)) =
      SOut.ok (SRes.ok (.Int (Int.ofNat ((left + right) % modulus 64)),
        .Int (mrIntTy false .u64))) :=
  ⟨SourceWord64Call.caller_evaluates left right leftValid rightValid,
    PairCallerOperational.linked_returns left right depth leftValid rightValid,
    reference_add fuel machine left right leftValid rightValid⟩

#print axioms reference_add
#print axioms linked_reference_agreement
end SourceWord64MiniRust
