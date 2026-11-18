pub enum ScalarTuple {
    A((u32, u8)),
    B((u32, u8)),
}

pub enum FatTuple<'a> {
    A((&'a [u8], u8)),
    B((&'a [u8], u8)),
}

pub fn scalar_payload(value: ScalarTuple) -> u8 {
    match value {
        ScalarTuple::A(pair) => pair.1,
        ScalarTuple::B(pair) => pair.1,
    }
}

pub fn fat_payload(value: FatTuple<'_>) -> u8 {
    match value {
        FatTuple::A(pair) => pair.1,
        FatTuple::B(pair) => pair.1,
    }
}

pub fn rebound_payload(value: ScalarTuple) -> u8 {
    match value {
        ScalarTuple::A(pair) => {
            let alias = pair;
            alias.1
        }
        ScalarTuple::B(pair) => {
            let alias = pair;
            alias.1
        }
    }
}

pub struct Pair {
    pub word: u32,
    pub byte: u8,
}

pub enum StructPayload {
    A(Pair),
    B(Pair),
}

pub fn struct_payload(value: StructPayload) -> u8 {
    match value {
        StructPayload::A(pair) => pair.byte,
        StructPayload::B(pair) => pair.byte,
    }
}

pub fn direct_tuple(word: u32, byte: u8) -> u8 {
    (word, byte).1
}

pub fn direct_struct(word: u32, byte: u8) -> u8 {
    Pair { word, byte }.byte
}

pub fn joined_payload(value: ScalarTuple, c: bool) -> u8 {
    match value {
        ScalarTuple::A(mut pair) => {
            if c {
                pair = (7, 8);
            }
            pair.1
        }
        ScalarTuple::B(mut pair) => {
            if c {
                pair = (7, 8);
            }
            pair.1
        }
    }
}

pub fn havoc_payload(value: ScalarTuple, n: u32) -> u8 {
    match value {
        ScalarTuple::A(mut pair) => {
            for _ in 0..n {
                pair = (7, 8);
            }
            pair.1
        }
        ScalarTuple::B(mut pair) => {
            for _ in 0..n {
                pair = (7, 8);
            }
            pair.1
        }
    }
}


// Same payload shape as the measured AY dt_eta::Fields::len producer failure.
pub struct SliceField {
    pub name: String,
    pub sort: u64,
}

pub enum SlicePayload<'a> {
    Tuples(&'a [(String, u64)]),
    Datatype(&'a [SliceField]),
}

pub fn slice_payload_len(value: SlicePayload<'_>) -> usize {
    match value {
        SlicePayload::Tuples(value) => value.len(),
        SlicePayload::Datatype(value) => value.len(),
    }
}

pub fn direct_tuple_slice_len(value: &[(String, u64)]) -> usize {
    value.len()
}

pub fn direct_field_slice_len(value: &[SliceField]) -> usize {
    value.len()
}
