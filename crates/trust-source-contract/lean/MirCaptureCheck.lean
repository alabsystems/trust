/- Copyright 2026 Andrew Yates. Apache-2.0.
   Exact captured body -> checked view -> existing byte-step simulation.
   Capture provenance and resolved Rust nominal identity are NOT inferred.
-/
import MirCaptureOriginal
import MirCaptureView
namespace TrustMirCaptureCheck
open TrustMirCaptureJson TrustMirCaptureOriginal TrustMirCaptureView
open TrustMirBoolAssignment TrustMirNominalSwitch TrustMirHelperReturn
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def originalCapture : Capture :=
  ⟨"proof_ref_kind_is_ambiguous", "trust_ir_laws::proof_ref_kind_is_ambiguous", expectedBody true⟩
/-- Checks ALL typed body fields, ordered blocks/statements/targets and nominal
    declaration data, not merely a manually selected assignment. -/
theorem original_projection : projectCapture originalJson = some originalCapture := rfl

def originalChecked : CheckedView originalCapture := ⟨true,rfl⟩
theorem original_checked : checkView originalCapture = some originalChecked ∧
    originalChecked.bodyFlag = true := ⟨rfl,rfl⟩

/-- Consumer of the successful body check. The bytes and source view meet here;
    the external capture's compiler/Rust identity remains an explicit boundary. -/
theorem checked_capture_return (capture : Capture) (checked : CheckedView capture)
    (c : OriginalConstructor) :
    capture.body = expectedBody checked.bodyFlag ∧
    SemR.runFunction (program checked.bodyFlag) 0 [embed c] 10 4 =
      .ret [.bool (sourceValue checked.bodyFlag c)] := by
  exact ⟨checked.bodyEq,(helper_view_return checked.bodyFlag c).2.2.2.2.2.2.2.2.2.2⟩

theorem original_capture_return (c : OriginalConstructor) :
    projectCapture originalJson = some originalCapture ∧
    SemR.runFunction (program true) 0 [embed c] 10 4 = .ret [.bool (sourceValue true c)] :=
  ⟨original_projection,(checked_capture_return originalCapture originalChecked c).2⟩

/-- One connected statement from the exact embedded bytes through the typed
    source body to the existing shared byte execution. No producer identity
    premise or authored source clause is introduced. -/
theorem original_bytes_return (c : OriginalConstructor) :
    parseChars sourceChars = .ok originalJson ∧
    projectCapture originalJson = some originalCapture ∧
    checkView originalCapture = some originalChecked ∧
    originalChecked.bodyFlag = true ∧
    SemR.runFunction (program originalChecked.bodyFlag) 0 [embed c] 10 4 =
      .ret [.bool (sourceValue originalChecked.bodyFlag c)] :=
  ⟨original_parse,original_projection,original_checked.1,original_checked.2,
    (checked_capture_return originalCapture originalChecked c).2⟩

-- Body mutants cannot borrow the original check. The retained first-assignment
-- mutant has its OWN false flag and its OWN already checked semantics.
example : (checkView ⟨originalCapture.ownerName,originalCapture.defPath,expectedBody false⟩).isSome = true := rfl
example : ¬ (expectedBody false = expectedBody true) := by decide
example : (checkView { originalCapture with body := { expectedBody true with arguments := 2 } }).isNone = true := rfl
example : (checkView { originalCapture with body := { expectedBody true with locals := [] } }).isNone = true := rfl
example : (checkView { originalCapture with body := { expectedBody true with blocks := [] } }).isNone = true := rfl
example : projectTy (.obj [("Adt",.obj [("origin",.str "Rust")])]) = none := rfl
end TrustMirCaptureCheck
