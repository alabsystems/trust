// Trust: valid Rust members cannot collide with generated logical helpers.
#![allow(dead_code, non_camel_case_types, non_snake_case)]
#[repr(u8)]
pub enum Names { casesOn = 42, toTag = 3, mk = 250 }
pub struct Row { pub mk: bool, pub casesOn: bool, pub toTag: bool }
pub fn tag(n: Names) -> u8 {
    match n { Names::casesOn => 42, Names::toTag => 3, Names::mk => 250 }
}
pub fn field(r: Row) -> bool { r.casesOn }
clean {
    theorem member_tag : trust_type_reserved__Names.toTag
      trust_type_reserved__Names.constructors.toTag = (3 : UInt8) := rfl
    theorem enum_exact (n : trust_type_reserved__Names) :
      trust_import_reserved__tag n = trust_type_reserved__Names.toTag n := rfl
    theorem field_exact (r : trust_type_reserved__Row) :
      trust_import_reserved__field r = trust_type_reserved__Row.fields.casesOn r := rfl
    theorem field_computes : trust_type_reserved__Row.fields.casesOn
      (trust_type_reserved__Row.mk false true false) = true := rfl
}
