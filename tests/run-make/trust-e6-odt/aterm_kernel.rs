// Trust: TG11 bridge for aterm-db-core's real P4 peer_check_start kernel.
// Scalar body, Custody discriminants, spec and old theorem are copied from
// aterm cb6a4f0790c7 (2026-11-05), crates/aterm-db-core/src/{lib.rs,
// peer_check_island.rs,peer_check_binding_island.rs}. Only the nominal wrapper
// and bridge are new. No whole-aterm equivalence claim is made by this fixture.
#![allow(dead_code)]
#[repr(u8)]
pub enum Custody { None = 0, Journal = 1, Log = 2 }
pub fn peer_check_start(custody: u8) -> u8 {
    if custody == 0 { 5 } else if custody == 1 { 1 } else if custody == 2 { 1 } else { 6 }
}
pub fn nominal_start(custody: Custody) -> u8 {
    match custody {
        Custody::None => 5,
        Custody::Journal => if cfg!(mutant) { 6 } else { 1 },
        Custody::Log => 1,
    }
}
clean {
    def peer_check_start_spec (c : UInt8) : UInt8 :=
      if c = 0 then 5 else if c = 1 then 1 else if c = 2 then 1 else 6
    theorem peer_check_start_is_exact (c : UInt8) :
      trust_import_aterm_kernel__peer_check_start c = peer_check_start_spec c := rfl
    theorem custody_bridge (c : trust_type_aterm_kernel__Custody) :
      trust_import_aterm_kernel__nominal_start c =
        trust_import_aterm_kernel__peer_check_start (trust_type_aterm_kernel__Custody.toTag c) := by
      cases c <;> rfl
    theorem nominal_start_is_exact (c : trust_type_aterm_kernel__Custody) :
      trust_import_aterm_kernel__nominal_start c = peer_check_start_spec (trust_type_aterm_kernel__Custody.toTag c) :=
      Eq.trans (custody_bridge c) (peer_check_start_is_exact (trust_type_aterm_kernel__Custody.toTag c))
}
