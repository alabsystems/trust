//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-FS: a struct literal whose field is a FAT pointer (&[T], &str) seeds its
// aggregate lane with the two-zero null-fat-pointer constant (trust-ir fecd740:
// admitted by shape_matches_ty and materialized by constant_to_value on the same
// zero-only terms as the thin NullPtr arm), on the provably-overwritten lane
// only — the InsertField of the real field value replaces the seed wholesale.

pub struct ExtraSlice<'input> {
    pub slice: &'input [u8],
    pub extra: u32,
}

pub fn build(s: &[u8]) -> u32 {
    let v = ExtraSlice { slice: s, extra: 7 };
    v.extra
}

pub struct WithStr<'a> {
    pub name: &'a str,
    pub id: u64,
}

pub fn tag(n: &str) -> u64 {
    let w = WithStr { name: n, id: 3 };
    w.id
}

fn main() {}
