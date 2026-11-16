// Trust: the declaration order differs from tag and switch order.
#![allow(dead_code)]
#[repr(u8)]
pub enum Phase {
    #[cfg(not(tag_mutant))]
    Ready = 42,
    #[cfg(tag_mutant)]
    Ready = 43,
    Waiting = 3,
    Gone = 250,
}
pub fn kernel(p: Phase) -> u8 {
    match p {
        Phase::Ready => if cfg!(mutant) { 9 } else { 7 },
        Phase::Waiting => 2,
        Phase::Gone => 0,
    }
}
pub fn tag_kernel(p: u8) -> u8 {
    match p { 42 => 7, 3 => 2, _ => 0 }
}
pub fn folded(p: Phase) -> u8 {
    match p { Phase::Ready | Phase::Waiting | Phase::Gone => 7 }
}
pub fn tag(p: Phase) -> u8 {
    match p { Phase::Ready => 42, Phase::Waiting => 3, Phase::Gone => 250 }
}
pub fn bit(p: Phase) -> u8 {
    match p { Phase::Ready => 1, Phase::Waiting | Phase::Gone => 0 }
}
pub fn signed_tag(p: Phase) -> i8 {
    match p { Phase::Ready => 42, Phase::Waiting => 3, Phase::Gone => -6 }
}
clean {
    -- This is the old scalar theorem, unchanged by the new enum import.
    def spec_tag (p : UInt8) : UInt8 :=
      if p = (42 : UInt8) then 7 else if p = (3 : UInt8) then 2 else 0
    theorem old_tag_is_exact (p : UInt8) : trust_import_enum__tag_kernel p = spec_tag p := rfl

    -- The one new bridge relates the nominal function to its former tag kernel.
    theorem bridge (p : trust_type_enum__Phase) :
      trust_import_enum__kernel p = trust_import_enum__tag_kernel (trust_type_enum__Phase.toTag p) := by
      cases p <;> rfl

    theorem enum_is_exact (p : trust_type_enum__Phase) :
      trust_import_enum__kernel p = spec_tag (trust_type_enum__Phase.toTag p) :=
      Eq.trans (bridge p) (old_tag_is_exact (trust_type_enum__Phase.toTag p))
    theorem folded_is_exact (p : trust_type_enum__Phase) :
      trust_import_enum__folded p = (7 : UInt8) := by
      cases p <;> rfl
    theorem tag_is_exact (p : trust_type_enum__Phase) :
      trust_import_enum__tag p = trust_type_enum__Phase.toTag p := rfl
    theorem bit_is_exact (p : trust_type_enum__Phase) :
      trust_import_enum__bit p =
        @trust_type_enum__Phase.casesOn (fun _ => UInt8) p 1 0 0 := rfl
    theorem signed_tag_is_exact (p : trust_type_enum__Phase) :
      trust_import_enum__signed_tag p =
        @trust_type_enum__Phase.casesOn (fun _ => BitVec 8) p
          (BitVec.ofNat 8 42) (BitVec.ofNat 8 3) (BitVec.ofNat 8 250) := rfl
}
