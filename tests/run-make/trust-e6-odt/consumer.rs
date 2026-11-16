// Trust: use the actual imported Rust declaration as B1's expected side.
extern crate e6_odt_aux;
use e6_odt_aux::{Phase, Row, Single};
pub fn ready(p: Phase) -> bool {
    match p { Phase::Ready => true, Phase::Waiting => false }
}
pub fn left(r: Row) -> bool { r.left }
pub fn selected(a: bool, p: Phase, b: bool) -> bool {
    match p { Phase::Ready => a, Phase::Waiting => b }
}
pub fn single(p: Single) -> u8 { match p { Single::Only => 13 } }
clean {
    theorem imported_enum (p : trust_type_e6_odt_aux__Phase) :
      trust_import_consumer__ready p =
        @trust_type_e6_odt_aux__Phase.casesOn (fun _ => Bool) p true false := rfl
    theorem imported_projection (r : trust_type_e6_odt_aux__Row) :
      trust_import_consumer__left r = trust_type_e6_odt_aux__Row.fields.left r := rfl
    theorem mixed_binder_order (a b : Bool) (p : trust_type_e6_odt_aux__Phase) :
      trust_import_consumer__selected a p b =
        @trust_type_e6_odt_aux__Phase.casesOn (fun _ => Bool) p a b := rfl
    theorem single_constructor (p : trust_type_e6_odt_aux__Single) :
      trust_import_consumer__single p = (13 : UInt8) := by
      cases p <;> rfl
}
