//! The verified unit: it depends on an unaudited derive, and compiles only if
//! that derive really expanded.
#[derive(iso_derive::Counted)]
pub struct Record {
    pub id: u32,
    pub flag: bool,
}

const _: () = assert!(Record::FIELDS == 2);

pub fn fields() -> usize {
    Record::FIELDS
}
