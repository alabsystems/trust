// Trust: metadata supplies the real signatures, including their bound lifetimes.
pub struct Borrowed<'a> {
    pub value: &'a u64,
}

#[inline(never)]
pub fn consume(value: Borrowed<'_>) -> u64 {
    *value.value
}

#[inline(never)]
pub fn make(value: &u64) -> Borrowed<'_> {
    Borrowed { value }
}

#[inline(never)]
pub fn read(value: &u64) -> u64 {
    *value
}
