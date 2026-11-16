/- Copyright 2026 Andrew Yates. Apache-2.0. Typed-view hostile controls. -/
import MirCaptureView
namespace TrustMirCaptureControls
open TrustMirCaptureView TrustMirBoolAssignment TrustMirNominalSwitch TrustMirHelperReturn
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def capture (body : Body) : Capture := ⟨"helper","crate::helper",body⟩
def rejects (body : Body) : Bool := (checkView (capture body)).isNone

def setLocal (f : Local → Local) : Body :=
  { expectedBody true with locals := (expectedBody true).locals.map f }
def setBlock (f : Block → Block) : Body :=
  { expectedBody true with blocks := (expectedBody true).blocks.map f }
def nominal (f : Nominal → Nominal) : Body := setLocal fun l =>
  if l.index == 1 then { l with ty := .nominal (f expectedNominal) } else l

example : (checkView (capture (expectedBody true))).isSome = true := rfl
example : (checkView (capture (expectedBody false))).isSome = true := rfl
example : rejects { expectedBody true with arguments := 0 } = true := rfl
example : rejects { expectedBody true with result := .i64 } = true := rfl
example : rejects (setLocal fun l => if l.index == 1 then { l with index := 0 } else l) = true := rfl
example : rejects (setLocal fun l => if l.index == 1 then { l with name := some "_0" } else l) = true := rfl
example : rejects (setLocal fun l => if l.index == 3 then { l with ty := .bool } else l) = true := rfl
example : rejects (nominal fun d => { d with name := "lookalike::ObligationKindShape" }) = true := rfl
example : rejects (nominal fun d => { d with discIndexSafe := false }) = true := rfl
example : rejects (nominal fun d => { d with fields := [("__tag",.bool)] }) = true := rfl
example : rejects (nominal fun d => { d with variants := [] }) = true := rfl
example : rejects (nominal fun d => { d with variants := d.variants.reverse }) = true := rfl
example : rejects (nominal fun d => { d with variants := d.variants.map fun v =>
    if v.discriminant == 0 then { v with discriminant := -1 } else v }) = true := rfl
example : rejects (nominal fun d => { d with variants := d.variants.map fun v =>
    if v.discriminant == 0 then { v with discriminant := 18446744073709551616 } else v }) = true := rfl
example : rejects (nominal fun d => { d with variants := d.variants.map fun v =>
    if v.discriminant == 0 then { v with fields := [("payload",.bool)] } else v }) = true := rfl
example : rejects (setBlock fun b => if b.id == 1 then { b with terminator := .goto 11 } else b) = true := rfl
example : rejects (setBlock fun b => if b.id == 10 then { b with terminator := .goto 10 } else b) = true := rfl
example : rejects (setBlock fun b => if b.id == 10 then
    { b with statements := [.assign ⟨0,[]⟩ (.use (.copy ⟨1,[]⟩))] } else b) = true := rfl
example : rejects (setBlock fun b => if b.id == 1 then
    { b with statements := b.statements ++ b.statements } else b) = true := rfl
example : rejects (setBlock fun b => if b.id == 0 then
    { b with statements := [.assign ⟨3,[]⟩ (.discriminant ⟨2,[]⟩)] } else b) = true := rfl
example : rejects (setBlock fun b => if b.id == 0 then
    { b with terminator := .switchInt (.copy ⟨3,[]⟩) [(1,2),(0,1)] 9 } else b) = true := rfl
example : rejects { expectedBody true with blocks := (expectedBody true).blocks.reverse } = true := rfl
example : projectPlace (.obj [("local",.int (-1)),("projections",.arr [])]) = none := rfl
example : projectPlace (.obj [("local",.int 1),("projections",.arr [.str "Deref"])]) = none := rfl
example : projectOperand (.obj [("Move",.null)]) = none := rfl
example : projectTerminator (.obj [("Call",.null)]) = none := rfl
end TrustMirCaptureControls
