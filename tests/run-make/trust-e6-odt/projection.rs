// Trust: all TG10 scalar carriers are present; named field order matters.
#![allow(dead_code)]
pub struct Row { pub flag: bool, pub a: u8, pub b: u16, pub c: u32, pub d: u64, pub e: i8, pub f: i16, pub g: i32, pub h: i64, pub other: i64 }
pub fn kernel(row: Row) -> i64 {
    #[cfg(mutant)] { row.other }
    #[cfg(not(mutant))] { row.h }
}
clean {
    theorem projection_is_exact (r : trust_type_projection__Row) :
      trust_import_projection__kernel r = trust_type_projection__Row.fields.h r := rfl
}
