//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-CD): the CUSTOM-DST CONTAINER unsize — `&Foo<[u8; 3]> → &Foo<[u8]>`,
//! where the pointee CONTAINS the DST in tail position rather than BEING one.
//! `map_ty` already spelled the target `Ty::FatPtr(ContainerLen)` and a body that
//! merely CARRIES one was clean (`cd_carry`); the coercion that MINTS the value was
//! the missing piece: `PtrFromParts { FatPtr(ContainerLen), U64 }` with the source
//! pointer verbatim as the data lane and the statically-known tail length as
//! metadata. DELIBERATELY `ContainerLen`, never `FatPtrKind::Slice` — a `Slice`
//! spelling would claim the data pointer addresses slice CONTENT, and it addresses
//! the CONTAINER header (`container_pointee_ty`'s recorded decision; this is its
//! first producer).
//!
//! ORACLE PARITY: trust-mir-extract's `unsize_target_is_slice_ref` requires the
//! ref's INNER to be `Slice`/`Str`, so the oracle refuses these BODIES at
//! extraction — clean-only / NotRun by construction, no divergence reachable.
//!
//! The dyn-tailed container is the standing negative: `pointee_meta` answers
//! `Vtable` and `map_ty` fail-closes, so the mint is never reached (pinned at
//! corpus scale by `tests/ui/dst/dst-trait.rs` keeping its tags).

pub struct Foo<T: ?Sized> {
    pub head: u32,
    pub tail: T,
}

// The mint.
pub fn cd_pos(f: &Foo<[u8; 3]>) -> &Foo<[u8]> {
    f
}

// Control: carrying the fat type was already clean before the wave.
pub fn cd_carry(f: &Foo<[u8]>) -> &Foo<[u8]> {
    f
}

// Control: the plain slice lane is untouched.
pub fn cd_slice(a: &[u8; 4]) -> &[u8] {
    a
}

pub fn main() {}
